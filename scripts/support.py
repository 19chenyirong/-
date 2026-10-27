"""Shared paths, source checks and command recording (Python standard library only)."""
from pathlib import Path
import datetime as dt
import hashlib
import json
import re
import shlex
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / 'src'
CASES = ('LOS_ListInit', 'List_Add', 'LOS_ListDelete')
FUNCTIONS = ('LOS_ListInit', 'LOS_ListAdd', 'LOS_ListTailInsert', 'LOS_ListHeadInsert', 'LOS_ListDelete')
STRATEGIES = ('common', 'los_sortlink')
CATEGORIES = {
    'safety': '纯算术安全条件', 'return': '返回后置条件',
    'partial_solve': '调用或赋值前的资源整理',
    'which_implies': '堆谓词展开与边界暴露', 'derive': '不同层次规约的派生',
}
LOGICAL = 'SimpleC.EE.LiteOS'
ALLOWED = {
    'Coq.Logic.FunctionalExtensionality.functional_extensionality_dep',
    'Coq.Logic.PropExtensionality.propositional_extensionality',
    'SimpleC.SL.CNotation.eval_addr_expr',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def save_json(directory, name, value):
    (Path(directory) / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def check_sources():
    lock = load(ROOT / 'sources.lock.json')
    expected = set(lock['files'])
    actual = {p.relative_to(ROOT).as_posix() for base in ('src', 'references')
              for p in (ROOT / base).rglob('*') if p.is_file()}
    require(actual == expected, '源码或参考文件集合与锁定清单不符')
    for name, info in lock['files'].items():
        require(sha256(ROOT / name) == info['sha256'], f'源码哈希不匹配：{name}')
    require(len(list((WORK / 'SeparationLogic').rglob('*.v'))) == lock['coq_source_count'] == 133,
            'Coq 源码闭包应为 133 个模块')
    for path in (WORK / 'SeparationLogic/examples/LiteOS').glob('*_proof_*.v'):
        text = re.sub(r'\(\*.*?\*\)', '', path.read_text(), flags=re.S)
        require(not re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort)\b', text),
                f'直接证明含未完成证明或新假设：{path.name}')
    return lock


def run(directory, label, command, cwd):
    command = [str(part) for part in command]
    started = dt.datetime.now().astimezone().isoformat()
    timer = time.monotonic()
    with (directory / f'{label}.stdout.log').open('wb') as out, (directory / f'{label}.stderr.log').open('wb') as err:
        result = subprocess.run(command, cwd=cwd, stdout=out, stderr=err)
    status = dict(command=command, shell_command=shlex.join(command), cwd=str(cwd), started=started,
                  ended=dt.datetime.now().astimezone().isoformat(), exit_code=result.returncode,
                  elapsed_seconds=round(time.monotonic() - timer, 3))
    save_json(directory, f'{label}.status.json', status)
    print(f'{label}: exit={result.returncode}, {status["elapsed_seconds"]}s', flush=True)
    require(result.returncode == 0, f'{label} 执行失败，日志目录：{directory}')
    return (directory / f'{label}.stdout.log').read_text(encoding='utf-8')
