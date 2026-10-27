#!/usr/bin/env python3
"""Download the fixed Linux x86_64 QCP executable and verify its SHA-256."""
import argparse
import os
from pathlib import Path
import shutil
import sys
import tempfile
import urllib.request
from support import ROOT, load, require, sha256


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=ROOT / '.tools/qcp')
    parser.add_argument('--from-file', type=Path, help='导入已有固定工件并校验哈希')
    args = parser.parse_args()
    info = load(ROOT / 'sources.lock.json')['downloads']['symexec']
    if args.from_file is not None:
        require(args.from_file.is_file() and sha256(args.from_file) == info['sha256'], '导入工件的 SHA-256 不符')
    args.directory.mkdir(parents=True, exist_ok=True)
    target = args.directory / 'symexec'
    if target.exists():
        require(sha256(target) == info['sha256'], f'已有文件哈希不符，未覆盖：{target}')
    else:
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(dir=args.directory, delete=False) as stream:
                temporary = Path(stream.name)
                if args.from_file is not None:
                    with args.from_file.open('rb') as source:
                        shutil.copyfileobj(source, stream)
                else:
                    request = urllib.request.Request(info['url'], headers={'User-Agent': 'QCP-LiteOS-reproduction'})
                    with urllib.request.urlopen(request, timeout=60) as response:
                        while block := response.read(1024 * 1024):
                            stream.write(block)
            require(temporary.stat().st_size == info['size'] and sha256(temporary) == info['sha256'],
                    '下载文件与固定工件不符')
            os.replace(temporary, target)
        finally:
            if temporary is not None and temporary.exists():
                temporary.unlink()
    target.chmod(target.stat().st_mode | 0o111)
    print(target.resolve())


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print(f'错误：{error}', file=sys.stderr)
        sys.exit(1)
