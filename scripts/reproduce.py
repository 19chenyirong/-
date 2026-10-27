#!/usr/bin/env python3
"""check: verify saved text evidence; build: compile proofs; full: regenerate VCs and compile proofs."""
import argparse
from collections import Counter
import datetime as dt
import hashlib
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import sys

from support import (ROOT, WORK, CASES, FUNCTIONS, ALLOWED, check_sources,
                     load, require, run, save_json, sha256)
from coq_audit import index_sources, audit, assumption_names, query_records
from compare_sources import compare_sources


def normalized_hash(path):
    return hashlib.sha256(path.read_text(encoding='utf-8').encode('utf-8')).hexdigest()


def source_index():
    rows, strategies = index_sources(WORK / 'SeparationLogic')
    require(len(rows) == 16 and len(strategies) == 35, '直接 VC 或共享策略数量不同')
    require(Counter(r['proof_kind'] for r in rows) == {'manual': 7, 'auto': 9}, '证明来源数量不同')
    require(all(r['proof_end'] == 'Qed' for r in rows + strategies), '证明未全部以 Qed 结束')
    require([sum(r['function'] == f for r in rows) for f in FUNCTIONS] == [1, 2, 4, 2, 7],
            '逐函数覆盖不同')
    return rows, strategies


def resolve_outputs(directory, records):
    names = sorted({n for r in records for n in assumption_names(directory / r['output'])})
    resolved = {}
    for position, name in enumerate(names, 1):
        content = (directory / f'locations/{position:03d}.out').read_text(encoding='utf-8')
        matches = re.findall(r'^Constant\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$', content, re.M)
        require(len(matches) == 1, f'无法唯一定位假设：{name}')
        resolved[name] = matches[0]
    require(set(resolved.values()) == ALLOWED, '传递依赖不等于固定的三个既有假设')
    return resolved


def check_evidence(directory, lock):
    rows, strategies = source_index()
    summary = load(directory / 'summary.json')
    require(summary['status'] == 'passed', '保存的复现未通过')
    require(summary['vc_count'] == 16 and summary['new_proofs'] == 9 and summary['reused_proofs'] == 7
            and summary['admitted'] == 0, '成果统计不同')
    expected_hashes = {name: info['sha256'] for name, info in lock['files'].items()}
    require(load(directory / 'source-hashes.json') == expected_hashes, '证据对应的源码不同')
    versions = (directory / 'coq-version.stdout.log').read_text()
    require('version 8.20.1' in versions and
            (directory / 'ocaml-version.stdout.log').read_text().strip() == '4.14.2', '工具链版本不同')
    for label in ['coq-version', 'ocaml-version', 'coq-where', 'coqdep', 'build',
                  'print-assumptions', 'locate-assumptions']:
        require(load(directory / f'{label}.status.json')['exit_code'] == 0, f'命令未通过：{label}')
    environment = load(directory / 'environment.json')
    require(environment['initial_compiled_artifacts'] == 0 and environment['coq_sources'] == 133,
            '构建未从纯源码开始')
    expected_sources = {name.removeprefix('src/SeparationLogic/') for name in lock['files']
                        if name.startswith('src/SeparationLogic/') and name.endswith('.v')}
    compiled = re.findall(r'^COQC (.+\.v)$', (directory / 'build.stdout.log').read_text(), re.M)
    artifacts = load(directory / 'compiled-modules.json')
    require(len(compiled) == len(set(compiled)) == 133 and set(compiled) == expected_sources == set(artifacts),
            '新编译模块未完整覆盖源码闭包')
    require(summary['fresh_compiled_modules'] == 133 and
            not (directory / 'coqdep.stderr.log').read_text().strip(), '依赖检查或模块统计不同')
    for name, info in artifacts.items():
        require(info['source_sha256'] == lock['files']['src/SeparationLogic/' + name]['sha256']
                and info['size'] > 0 and re.fullmatch(r'[a-f0-9]{64}', info['vo_sha256']),
                f'编译记录不同：{name}')
    records = load(directory / 'assumptions.json')
    expected = query_records(rows, strategies)
    require(len(records) == len({r['id'] for r in records}) == len(expected) == 172, '假设查询覆盖不同')
    by_id = {r['id']: r for r in records}
    require(set(by_id) == {r['id'] for r in expected}, '假设查询成员不同')
    resolved = resolve_outputs(directory, records)
    require(load(directory / 'resolved-assumptions.json') == resolved, '假设名称解析不同')
    original = {}
    for item in expected:
        record = by_id[item['id']]
        require(all(record[k] == v for k, v in item.items()), f'查询常量或来源不同：{item["id"]}')
        require(record['output'] == f'assumptions/{item["id"]}.out', '查询输出路径不同')
        printed = assumption_names(directory / record['output'])
        require(record['printed_assumptions'] == printed and
                record['assumptions'] == sorted(resolved[n] for n in printed), '原始假设输出与索引不同')
        if record['site'] == 'proof_file':
            original[(record['scope'], record['name'])] = record['assumptions']
    for record in records:
        if record['site'] == 'goal_check':
            require(record['assumptions'] == original[(record['scope'], record['name'])],
                    f'实际模块成员依赖不同：{record["constant"]}')
    require(len(list((directory / 'assumptions').glob('*.out'))) == 172, '原始假设文件数量不同')
    require(summary['assumption_queries'] == 172 and summary['module_members'] == 121 and
            summary['shared_strategies'] == 35 and summary['assumptions'] == sorted(ALLOWED), '审计统计不同')
    for row in rows:
        record = by_id['vc-' + row['vc']]
        row.update(proof_origin='新增证明' if row['proof_kind'] == 'auto' else '作者原有证明',
                   assumptions=record['assumptions'], audit_id=record['id'])
    require(load(directory / 'vc-index.json') == rows, '逐目标证明索引不同')
    require(load(directory / 'comparison.json') == compare_sources(), 'OpenHarmony 源码对照不同')
    if summary['qcp_rerun']:
        generation = load(directory / 'generation.json')
        require(environment['qcp_sha256'] == lock['downloads']['symexec']['sha256'], 'QCP 二进制身份不同')
        require(set(generation) == set(CASES), 'QCP 生成覆盖不同')
        for case, comparisons in generation.items():
            require(load(directory / f'qcp-{case}.status.json')['exit_code'] == 0, f'生成未通过：{case}')
            for suffix in ('goal', 'goal_check'):
                frozen = WORK / f'SeparationLogic/examples/LiteOS/{case}_{suffix}.v'
                require(comparisons[suffix]['generated_lf_sha256'] == normalized_hash(frozen)
                        == comparisons[suffix]['fixed_lf_sha256'], f'重新生成的接口或目标不同：{case}')
    print(f'证据核验通过：16/16 Qed，133 个新编译模块，172 项假设查询；{directory}', flush=True)


def check_manifest():
    path = ROOT / 'MANIFEST.sha256'
    require(path.is_file(), '缺少交付文件 SHA-256 清单')
    expected = {}
    for line in path.read_text(encoding='utf-8').splitlines():
        digest, name = line.split('  ', 1)
        require(name not in expected and not Path(name).is_absolute() and '..' not in Path(name).parts,
                '交付清单含重复或非法路径')
        expected[name] = digest
    excluded = {'.tools', 'runs', '__pycache__', '.git'}
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()
              and not excluded.intersection(p.relative_to(ROOT).parts)
              and p.name != 'MANIFEST.sha256' and p.suffix != '.pyc'}
    require(actual == set(expected), '交付文件集合与 MANIFEST.sha256 不符')
    for name, digest in expected.items():
        require(sha256(ROOT / name) == digest, f'交付文件变化：{name}')
    print(f'文件核验通过：{len(expected)} 个文本文件。', flush=True)


def find_compiler(bin_directory):
    if bin_directory is not None:
        compiler = bin_directory.expanduser().resolve() / 'coqc'
    elif (ROOT / '.tools/coq/_opam/bin/coqc').is_file():
        compiler = ROOT / '.tools/coq/_opam/bin/coqc'
    else:
        found = shutil.which('coqc')
        require(found is not None, '找不到 coqc；请安装工具链或指定 --coq-bin')
        compiler = Path(found).resolve()
    require(compiler.is_file(), f'编译器不存在：{compiler}')
    for tool in ('coqdep', 'ocamlc'):
        require(compiler.with_name(tool).is_file(), f'工具不存在：{tool}')
    require(shutil.which('make'), '需要 GNU make')
    return compiler


def generate(directory, binary, lock):
    require(platform.system() == 'Linux' and platform.machine() in ('x86_64', 'AMD64'), '完整生成需要 Linux x86_64')
    require(binary.is_file() and sha256(binary) == lock['downloads']['symexec']['sha256'],
            '需要固定 QCP symexec；运行 scripts/fetch-qcp.py 或指定 --qcp-bin')
    require(os.access(binary, os.X_OK), 'QCP 文件需要执行权限；可用 fetch-qcp.py --from-file 导入并校验')
    comparisons = {}
    relative = Path('SeparationLogic/examples/LiteOS')
    for case in CASES:
        # A new output file forces QCP to generate its own proof templates.
        for suffix in ('goal', 'goal_check', 'proof_auto', 'proof_manual'):
            (directory / relative / f'{case}_{suffix}.v').unlink(missing_ok=True)
        run(directory, f'qcp-{case}', [binary,
            f'--goal-file={relative}/{case}_goal.v',
            f'--proof-auto-file={relative}/{case}_proof_auto.v',
            f'--proof-manual-file={relative}/{case}_proof_manual.v',
            '-slp', 'QCP_examples/', 'SimpleC.EE', '-IQCP_examples/', '--no-logic-path',
            f'--input-file=QCP_examples/LiteOS/{case}.c', '--no-exec-info'], directory)
        comparisons[case] = {}
        for suffix in ('goal', 'goal_check'):
            name = relative / f'{case}_{suffix}.v'
            generated, fixed = directory / name, WORK / name
            require(generated.is_file() and generated.read_text() == fixed.read_text(),
                    f'生成目标或检查接口偏离固定版本：{name}')
            comparisons[case][suffix] = dict(generated_lf_sha256=normalized_hash(generated),
                                              fixed_lf_sha256=normalized_hash(fixed))
    save_json(directory, 'generation.json', comparisons)
    # Keep generated targets fixed and restore the seven author and nine completed proofs.
    for source in (WORK / 'SeparationLogic').rglob('*.v'):
        shutil.copy2(source, directory / source.relative_to(WORK))


def write_catalog(directory, compiler, resolved):
    stdlib = Path((directory / 'coq-where.stdout.log').read_text().strip())
    catalog = {}
    for constant in sorted(set(resolved.values())):
        if constant.startswith('Coq.'):
            source = stdlib / 'theories/Logic' / (constant.split('.')[-2] + '.v')
            target = directory / 'stdlib-sources' / source.name
            target.parent.mkdir(exist_ok=True)
            shutil.copy2(source, target)
            location = 'stdlib-sources/' + source.name
            category = '标准库外延性公理'
        else:
            source = WORK / 'SeparationLogic/SeparationLogic/CNotation.v'
            location = source.relative_to(ROOT).as_posix()
            category = '既有地址模型参数'
        text = source.read_text()
        declaration = re.search(r'^\s*(?:Axiom|Parameter)\s+' + re.escape(constant.split('.')[-1]) + r'\b', text, re.M)
        require(declaration is not None, f'找不到假设声明：{constant}')
        catalog[constant] = dict(category=category, source=location, sha256=sha256(source),
                                 line=text.count('\n', 0, declaration.start()) + 1)
    save_json(directory, 'assumption-catalog.json', catalog)


def execute(args, lock):
    compiler = find_compiler(args.coq_bin)
    rows, strategies = source_index()
    directory = (args.output or ROOT / 'runs' / dt.datetime.now().astimezone().strftime('%Y%m%dT%H%M%S%z')).resolve()
    require(directory != ROOT and not directory.is_relative_to(WORK)
            and not directory.is_relative_to(ROOT / 'evidence'), '输出目录必须独立于源码和交付证据')
    directory.mkdir(parents=True, exist_ok=False)
    print(f'OUTPUT={directory}', flush=True)
    try:
        shutil.copytree(WORK, directory, dirs_exist_ok=True)
        build = directory / 'SeparationLogic'
        flags = lock['coq_flags']
        for position in range(0, len(flags), 3):
            (build / flags[position + 1]).mkdir(parents=True, exist_ok=True)
        initial = [p for p in build.rglob('*') if p.suffix in ('.vo', '.vos', '.vok', '.glob', '.aux')]
        require(not initial, '隔离目录存在旧编译产物')
        require('version 8.20.1' in run(directory, 'coq-version', [compiler, '--version'], directory),
                '要求 Coq 8.20.1')
        require(run(directory, 'ocaml-version', [compiler.with_name('ocamlc'), '-version'], directory).strip() == '4.14.2',
                '要求 OCaml 4.14.2')
        run(directory, 'coq-where', [compiler, '-where'], directory)
        binary = (args.qcp_bin or ROOT / '.tools/qcp/symexec').expanduser().resolve()
        environment = dict(platform=platform.platform(), coqc=str(compiler), coq_flags=flags,
                           coq_sources=133, initial_compiled_artifacts=0,
                           qcp_sha256=sha256(binary) if args.command == 'full' and binary.is_file() else None)
        save_json(directory, 'environment.json', environment)
        save_json(directory, 'source-hashes.json', {name: info['sha256'] for name, info in lock['files'].items()})
        if args.command == 'full':
            generate(directory, binary, lock)
        names = sorted(p.relative_to(build).as_posix() for p in build.rglob('*.v'))
        require(len(names) == 133, '构建输入不等于 133 个冻结模块')
        for name in names:
            require(sha256(build / name) == lock['files']['src/SeparationLogic/' + name]['sha256'],
                    f'隔离源码改变：{name}')
        dependencies = run(directory, 'coqdep', [compiler.with_name('coqdep'), *flags, *names], build)
        require(not (directory / 'coqdep.stderr.log').read_text().strip(), '所需源码闭包存在依赖诊断')
        (build / 'dependencies.mk').write_text(dependencies)
        targets = [f'examples/LiteOS/{case}_goal_check.vo' for case in CASES]
        command = shlex.join([str(compiler), *flags])
        makefile = ('.DEFAULT_GOAL := audit\ninclude dependencies.mk\n'
                    f'audit: {" ".join(targets)}\n.PHONY: audit\n'
                    f'%.vo: %.v\n\t@echo COQC $<\n\t@{command} "$<"\n')
        (build / 'Makefile').write_text(makefile)
        (directory / 'build-Makefile').write_text(makefile)
        log = run(directory, 'build', ['make', 'SHELL=/bin/bash', '.SHELLFLAGS=-ec', f'-j{args.jobs}', 'audit'], build)
        compiled = re.findall(r'^COQC (.+\.v)$', log, re.M)
        require(len(compiled) == len(set(compiled)) == 133 and set(compiled) == set(names), '新编译模块覆盖不同')
        save_json(directory, 'compiled-modules.json', {
            name: dict(source_sha256=sha256(build / name), vo_sha256=sha256((build / name).with_suffix('.vo')),
                       size=(build / name).with_suffix('.vo').stat().st_size) for name in compiled})
        records, resolved = audit(directory, build, compiler, flags, rows, strategies)
        require(set(resolved.values()) == ALLOWED, '存在未登记的传递假设')
        save_json(directory, 'assumptions.json', records)
        save_json(directory, 'resolved-assumptions.json', resolved)
        write_catalog(directory, compiler, resolved)
        lines = ['# 十六项验证条件', '', '| 函数 | 验证条件 | 证明来源 | 结论 | 假设数 |',
                 '| --- | --- | --- | --- | --- |']
        for row in rows:
            record = next(r for r in records if r['id'] == 'vc-' + row['vc'])
            row.update(proof_origin='新增证明' if row['proof_kind'] == 'auto' else '作者原有证明',
                       assumptions=record['assumptions'], audit_id=record['id'])
            lines.append(f'| `{row["function"]}` | `{row["vc"]}` | {row["proof_origin"]} | Qed | '
                         f'[{len(row["assumptions"])}](assumptions/{record["id"]}.out) |')
        (directory / 'vc-status.md').write_text('\n'.join(lines) + '\n', encoding='utf-8')
        save_json(directory, 'vc-index.json', rows)
        save_json(directory, 'comparison.json', compare_sources())
        summary = dict(status='passed', mode=args.command, qcp_rerun=args.command == 'full',
                       qcp_commit=lock['qcp_commit'], openharmony_commit=lock['openharmony_commit'],
                       coq_version='8.20.1', ocaml_version='4.14.2', vc_count=16, reused_proofs=7,
                       new_proofs=9, admitted=0, fresh_compiled_modules=len(compiled), shared_strategies=35,
                       assumption_queries=len(records), module_members=sum(r['site'] == 'goal_check' for r in records),
                       assumptions=sorted(ALLOWED), functions={f: dict(
                           vc_count=sum(r['function'] == f for r in rows),
                           new_proofs=sum(r['function'] == f and r['proof_kind'] == 'auto' for r in rows)) for f in FUNCTIONS},
                       build_seconds=load(directory / 'build.status.json')['elapsed_seconds'],
                       note='固定规约和逻辑模型下的证明；auto 文件中的九项证明为新增 Coq 证明。')
        save_json(directory, 'summary.json', summary)
        check_evidence(directory, lock)
        check_sources()
        print(f'复现完成：{directory}', flush=True)
    except Exception as error:
        save_json(directory, 'failure.json', dict(status='failed', error=str(error)))
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['check', 'build', 'full'])
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--coq-bin', type=Path, help='包含 coqc、coqdep、ocamlc 的目录')
    parser.add_argument('--qcp-bin', type=Path, help='固定版本 symexec 路径')
    parser.add_argument('--output', type=Path, help='新建输出目录，拒绝覆盖已有目录')
    args = parser.parse_args()
    require(args.jobs >= 1, '--jobs 必须为正整数')
    lock = check_sources()
    if args.command == 'check':
        check_manifest()
        check_evidence(ROOT / 'evidence', lock)
    else:
        execute(args, lock)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print(f'错误：{error}', file=sys.stderr)
        sys.exit(1)
