#!/usr/bin/env python3
"""VC indexing and Coq assumption audit for the three selected LiteOS cases.
Adapted from the project's original analysis script; independent of its old directories.
"""
from pathlib import Path
import re
from support import ROOT, CASES, FUNCTIONS, WORK, STRATEGIES, CATEGORIES, LOGICAL, run

def line_number(text, offset):
    return text.count('\n', 0, offset) + 1


def proof_index(path):
    text = path.read_text(encoding='utf-8')
    matches = list(re.finditer(r'^\s*Lemma\s+(\w+)\s*:\s*(\w+)\s*\.', text, re.M))
    proofs = {}
    for position, match in enumerate(matches):
        end = matches[position + 1].start() if position + 1 < len(matches) else len(text)
        endings = re.findall(r'\b(Qed|Admitted|Defined|Abort)\s*\.', text[match.end():end])
        if match[1] in proofs or len(endings) != 1 or endings[0] == 'Abort':
            raise ValueError(f'Duplicate, unfinished or unrecognized proof: {path}: {match[1]}')
        proofs[match[1]] = dict(target=match[2], proof_end=endings[0],
                               proof_line=line_number(text, match.start() + len(match[0]) - len(match[0].lstrip())))
    return proofs


def index_sources(build):
    proofs_dir = build / 'examples/LiteOS'
    rows = []
    strategies = []
    for case in CASES:
        goal = proofs_dir / f'{case}_goal.v'
        text = goal.read_text(encoding='utf-8')
        definitions = list(re.finditer(r'^Definition\s+(\w+)\s*:=', text, re.M))
        targets = [match[1] for match in definitions]
        declarations = re.findall(r'^\s*Axiom\s+proof_of_(\w+)\s*:\s*(\w+)\s*\.', text, re.M)
        if not targets or len(set(targets)) != len(targets) or len(declarations) != len(targets):
            raise ValueError(f'Duplicate or missing VC interface declarations: {case}')
        if {name for name, target in declarations if name == target} != set(targets):
            raise ValueError(f'VC definitions and interface differ: {case}')
        found = {}
        for kind in ('auto', 'manual'):
            proof = proofs_dir / f'{case}_proof_{kind}.v'
            for name, info in proof_index(proof).items():
                if name in found or name != 'proof_of_' + info['target']:
                    raise ValueError(f'Duplicate or mismatched proof: {name}')
                found[name] = dict(**info, proof_kind=kind, proof_file=proof.relative_to(build).as_posix())
        if set(found) != {'proof_of_' + target for target in targets}:
            raise ValueError(f'Incomplete direct VC proof coverage: {case}')
        check = (proofs_dir / f'{case}_goal_check.v').read_text(encoding='utf-8')
        required = ['Module VC_Correctness : VC_Correct.', f'Include {case}_proof_auto.',
                    f'Include {case}_proof_manual.', 'Include common_strategy_proof.',
                    'Include los_sortlink_strategy_proof.']
        if any(fragment not in check for fragment in required):
            raise ValueError(f'Unexpected goal_check implementation: {case}')
        source = WORK / f'QCP_examples/LiteOS/{case}.c'
        source_text = source.read_text(encoding='utf-8')
        for match in definitions:
            name = match[1]
            function = next((function for function in FUNCTIONS if name.startswith(function + '_')), None)
            if function is None:
                raise ValueError(f'Unknown function: {name}')
            category = name[len(function) + 1:]
            kind = next((kind for kind in CATEGORIES if category.startswith(kind + '_')), None)
            if kind is None:
                raise ValueError(f'Unclassified VC: {name}')
            info = found['proof_of_' + name]
            rows.append(dict(case=case, function=function, vc=name, category=kind,
                             category_description=CATEGORIES[kind], goal_file=goal.relative_to(build).as_posix(),
                             goal_line=line_number(text, match.start()), source=source.relative_to(ROOT).as_posix(),
                             source_lines=[position for position, line in enumerate(source_text.splitlines(), 1)
                                           if re.search(r'\bvoid\s+' + function + r'\s*\(', line)], **info))
    for strategy in STRATEGIES:
        goal = build / f'examples/{strategy}_strategy_goal.v'
        text = goal.read_text(encoding='utf-8')
        declarations = re.findall(r'^\s*Axiom\s+(\w+)\s*:\s*(\w+)\s*\.', text, re.M)
        proof = build / f'examples/{strategy}_strategy_proof.v'
        found = proof_index(proof)
        if len(declarations) != len(found) or {name: info['target'] for name, info in found.items()} != dict(declarations):
            raise ValueError(f'Shared strategy interface and proofs differ: {strategy}')
        for name, info in found.items():
            strategies.append(dict(strategy=strategy, name=name, proof_file=proof.relative_to(build).as_posix(), **info))
    return rows, strategies


def assumption_names(path):
    text = path.read_text(encoding='utf-8')
    if 'Closed under the global context' in text:
        if 'Axioms:' in text:
            raise ValueError(f'Ambiguous Print Assumptions output: {path}')
        return []
    if text.count('Axioms:\n') != 1:
        raise ValueError(f'Missing or ambiguous Print Assumptions header: {path}')
    block = text.split('Axioms:\n', 1)[1]
    names = re.findall(r"^([A-Za-z_][A-Za-z0-9_'.]*)\s*:", block, re.M)
    if not names or len(set(names)) != len(names):
        raise ValueError(f'Missing or duplicate assumption names: {path}')
    return names


def imports():
    return ''.join(f'Require Import {LOGICAL}.{case}_goal_check.\n' for case in CASES)


def query_records(rows, strategies):
    records = []
    for row in rows:
        name = 'proof_of_' + row['vc']
        records.append(dict(id=f'vc-{row["vc"]}', scope='direct_vc', site='proof_file', case=row['case'],
                            name=name, constant=f'{LOGICAL}.{row["case"]}_proof_{row["proof_kind"]}.{name}',
                            proof_end=row['proof_end']))
        records.append(dict(id=f'module-{row["case"]}-{name}', scope='direct_vc', site='goal_check', case=row['case'],
                            name=name, constant=f'{LOGICAL}.{row["case"]}_goal_check.VC_Correctness.{name}',
                            proof_end=row['proof_end']))
    for strategy in strategies:
        name = strategy['name']
        records.append(dict(id=f'strategy-{name}', scope='shared_strategy', site='proof_file', name=name,
                            constant=f'SimpleC.EE.{strategy["strategy"]}_strategy_proof.{name}',
                            proof_end=strategy['proof_end']))
        for case in CASES:
            records.append(dict(id=f'module-{case}-{name}', scope='shared_strategy', site='goal_check', case=case,
                                name=name, constant=f'{LOGICAL}.{case}_goal_check.VC_Correctness.{name}',
                                proof_end=strategy['proof_end']))
    return records


def audit(directory, build, compiler, flags, rows, strategies):
    (directory / 'assumptions').mkdir()
    records = query_records(rows, strategies)
    commands = [imports(), 'Set Printing Width 120.\n', 'Set Printing Depth 1000.\n']
    for record in records:
        record['output'] = f'assumptions/{record["id"]}.out'
        commands.append(f'Redirect "../assumptions/{record["id"]}" Print Assumptions {record["constant"]}.\n')
    (build / 'AuditAssumptions.v').write_text(''.join(commands), encoding='utf-8')
    run(directory, 'print-assumptions', [str(compiler), *flags, 'AuditAssumptions.v'], build)
    for record in records:
        record['printed_assumptions'] = assumption_names(directory / record['output'])
    names = sorted({name for record in records for name in record['printed_assumptions']})
    (directory / 'locations').mkdir()
    commands = [imports(), 'Set Printing Width 120.\n']
    for position, name in enumerate(names, 1):
        commands.append(f'Redirect "../locations/{position:03d}" Locate {name}.\n')
    (build / 'AuditLocations.v').write_text(''.join(commands), encoding='utf-8')
    run(directory, 'locate-assumptions', [str(compiler), *flags, 'AuditLocations.v'], build)
    resolved = {}
    for position, name in enumerate(names, 1):
        text = (directory / f'locations/{position:03d}.out').read_text(encoding='utf-8')
        matches = re.findall(r'^Constant\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$', text, re.M)
        if len(matches) != 1:
            raise ValueError(f'Cannot uniquely resolve assumption {name}: {text}')
        resolved[name] = matches[0]
    for record in records:
        record['assumptions'] = sorted(resolved[name] for name in record['printed_assumptions'])
    for record in records:
        if record['site'] == 'goal_check':
            original = next(item for item in records if item['site'] == 'proof_file'
                            and item['scope'] == record['scope'] and item['name'] == record['name'])
            if original['assumptions'] != record['assumptions']:
                raise ValueError(f'Module implementation assumptions differ: {record["constant"]}')
    return records, resolved
