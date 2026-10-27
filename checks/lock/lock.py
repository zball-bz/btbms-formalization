#!/usr/bin/env python3
"""Statement lock (user gate G2).

`lock.py` verifies the locked inputs against `statement.lock.json`; `lock.py --write` records the
lock. Only root writes the lock, and only after the user signs off a statement gate. The tracker
imports `verify` and `fingerprint` so that the board cannot show an intact lock, or current Lean
status, when the inputs have changed.

Locked inputs (T-019 review):
  * the statement files and project configuration, by file hash;
  * every package Lake actually resolves (from `lean/lake-manifest.json`, relative to `lean/`),
    as one digest over its Lean sources and configuration;
  * the Lean toolchain the checks run (`bin/` and the core sources under `src/`).
Any symlink inside a hashed tree is refused (fail closed), so no source can hide behind an alias
into a skipped build directory (T-019 follow-up). The compiled toolchain libraries and `.olean`
files are trusted, not hashed.
"""
import hashlib
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LEAN_DIR = ROOT / 'lean'
LOCK = HERE / 'statement.lock.json'
LEAN_HOME = Path(os.environ.get('BTBMS_LEAN_HOME', '/home/dev/ggg/.tools/lean-4.33.1-linux'))

LOCKED = [
    'lean/BTBMS/Syntax.lean',
    'lean/BTBMS/Expansion.lean',
    'lean/BTBMS/Mahlo.lean',
    'lean/BTBMS/Statement.lean',
    'lean/lean-toolchain',
    'lean/lakefile.toml',
    'lean/lake-manifest.json',
    'checks/lock/LockCheck.lean',
    'checks/lock/lock.py',
    'checks/lock/check.sh',
]
CONFIG_NAMES = {'lakefile.lean', 'lakefile.toml', 'lean-toolchain', 'lake-manifest.json'}
SKIP_DIRS = {'.lake', '.git'}  # skipped at a hashed tree's root only


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class LockError(Exception):
    pass


def tree_digest(root, keep):
    """Digest over (relative path, file hash) of every kept file under root.

    Only the root's own build and VCS directories (`root/.lake`, `root/.git`) are skipped; a
    directory with the same name deeper down can hold importable sources (`BTBMS.«.lake».X`) and
    is hashed. Raises LockError on any symlink below root."""
    h = hashlib.sha256()
    count = 0
    root = Path(root)
    for dirpath, dirnames, filenames in os.walk(root):
        top = Path(dirpath) == root
        dirnames[:] = sorted(d for d in dirnames if not (top and d in SKIP_DIRS))
        for name in dirnames + filenames:
            if (Path(dirpath) / name).is_symlink():
                raise LockError(f'unsupported symlink in a locked tree: {Path(dirpath) / name}')
        for name in sorted(filenames):
            p = Path(dirpath) / name
            if keep(p):
                h.update(f'{p.relative_to(root)}\0{sha256(p)}\n'.encode())
                count += 1
    return f'{h.hexdigest()} ({count} files)'


def packages():
    """Path packages exactly as Lake resolves them from the manifest."""
    manifest = json.loads((LEAN_DIR / 'lake-manifest.json').read_text())
    out = {}
    for p in manifest['packages']:
        if p['type'] != 'path':
            raise SystemExit(f"package {p['name']}: only path packages are supported by the lock")
        out[p['name']] = (LEAN_DIR / p['dir']).resolve()
    return out


def current():
    entries = {p: sha256(ROOT / p) for p in LOCKED}
    for name, path in sorted(packages().items()):
        entries[f'package:{name}'] = tree_digest(
            path, lambda f: f.suffix == '.lean' or f.name in CONFIG_NAMES)
    entries['toolchain:bin'] = tree_digest(LEAN_HOME / 'bin', lambda f: True)
    entries['toolchain:src'] = tree_digest(LEAN_HOME / 'src', lambda f: True)
    return entries


def fingerprint():
    """Everything the Lean status depends on: locked inputs plus all project Lean sources."""
    h = hashlib.sha256(json.dumps(current(), sort_keys=True).encode())
    h.update(tree_digest(LEAN_DIR, lambda f: f.suffix == '.lean').encode())
    h.update(sha256(HERE / 'Status.lean').encode())
    return h.hexdigest()


def verify():
    """Return (ok, problems)."""
    if not LOCK.exists():
        return False, ['no lock recorded']
    recorded = json.loads(LOCK.read_text())['inputs']
    try:
        now = current()
        tree_digest(LEAN_DIR, lambda f: f.suffix == '.lean')  # refuses symlinked project sources
    except LockError as e:
        return False, [str(e)]
    problems = [f'{p}: changed' for p in recorded if now.get(p) != recorded[p]]
    problems += [f'{p}: not in lock' for p in now if p not in recorded]
    return not problems, problems


def main():
    args = sys.argv[1:]
    if args == ['--lean-home']:
        print(LEAN_HOME)
        return
    if args == ['--fingerprint']:
        print(fingerprint())
        return
    if args == ['--write']:
        LOCK.write_text(json.dumps({
            'gate': 'G2',
            'signed_off_by': 'user',
            'date': '2026-10-27',
            'reviewed_in': ['tracker/review/codex-statement-review.md',
                            'tracker/review/codex-lock-review.md'],
            'pins': {'lean': 'v4.33.1', 'mathlib': 'eba3d887fc52c98627f4b81507c0efc3096e91b9',
                     'cu': '7f5a7d03d63d9769172f17350bbe8303996e5b53'},
            'inputs': current(),
        }, indent=1) + '\n')
        print(f'lock written: {LOCK.relative_to(ROOT)}')
        return
    ok, problems = verify()
    print('lock intact' if ok else 'LOCK BROKEN:\n  ' + '\n  '.join(problems))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
