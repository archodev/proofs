"""Install the pinned public Kirov dependency in a freshly extracted project."""
from pathlib import Path
from hashlib import sha256
import os
import shutil
import subprocess
import tarfile
import tempfile

PROJECT = Path(__file__).resolve().parent
REVISION = '8ce1ec28aed1c78b3b39d0bae26e2858c82f5143'
URL = 'https://github.com/mrdouglasny/jacobian-challenge.git'
RELATIVE = Path('vendor/kirov-dolbeault-port')
TARGET = PROJECT / RELATIVE

def digest(directory):
    total = sha256()
    for path in sorted(directory.rglob('*')):
        relative = path.relative_to(directory)
        if path.is_file() and '.lake' not in relative.parts and '.git' not in relative.parts:
            total.update(relative.as_posix().encode() + b'\0' + sha256(path.read_bytes()).digest())
    return total.hexdigest()

def select_modules(directory):
    modules = set((PROJECT / 'dependency.modules').read_text().splitlines())
    for name in modules:
        if not (directory / name).is_file():
            raise SystemExit(f'Missing imported dependency module: {name}')
    for module in (directory / 'KirovDolbeault').rglob('*.lean'):
        if module.relative_to(directory).as_posix() not in modules:
            module.unlink()
    # The compiler-recorded import closure supplies a complete independent Lake root.
    imports = ['import ' + name[:-5].replace('/', '.') for name in sorted(modules)]
    (directory / 'KirovDolbeault.lean').write_text('\n'.join(imports) + '\n')

def run(*args, cwd, **kwargs):
    return subprocess.run(args, cwd=cwd, check=True, **kwargs)

if __name__ == '__main__':
    expected = (PROJECT / 'dependency.sha256').read_text().strip()
    if TARGET.exists():
        if digest(TARGET) != expected:
            raise SystemExit('The installed dependency differs from the checked source.')
        print('Pinned Kirov source verified.')
    else:
        with tempfile.TemporaryDirectory(dir=PROJECT) as tmp:
            base = Path(tmp)
            repo = base / 'upstream'
            repo.mkdir()
            run('git', 'init', '-q', cwd=repo)
            run('git', 'fetch', '-q', '--depth=1', URL, REVISION, cwd=repo)
            rev = run('git', 'rev-parse', 'FETCH_HEAD', cwd=repo, capture_output=True, text=True)
            if rev.stdout.strip() != REVISION:
                raise SystemExit('Dependency revision mismatch.')
            archive = base / 'vendor.tar'
            run('git', 'archive', '--format=tar', '-o', str(archive), REVISION, str(RELATIVE), cwd=repo)
            with tarfile.open(archive) as tf:
                for member in tf:
                    if member.isdir() and Path(member.name) in RELATIVE.parents:
                        continue
                    if not Path(member.name).is_relative_to(RELATIVE) or '..' in Path(member.name).parts:
                        raise ValueError(member.name)
                    if member.isdir() or member.isfile():
                        tf.extract(member, base, filter='data')
                    else:
                        raise ValueError(member.name)
            run('git', 'apply', '--whitespace=nowarn', str(PROJECT / 'dependency.patch'), cwd=base)
            select_modules(base / RELATIVE)
            if digest(base / RELATIVE) != expected:
                raise SystemExit('Patched dependency does not have the expected digest.')
            TARGET.parent.mkdir(exist_ok=True)
            os.rename(base / RELATIVE, TARGET)
        print('Pinned Kirov source installed and verified.')
