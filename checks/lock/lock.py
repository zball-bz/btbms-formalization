#!/usr/bin/env python3
"""Statement lock (user gate G2).

`lock.py` verifies the locked files against `statement.lock.json`; `lock.py --write` records the
lock. Only root writes the lock, and only after the user signs off a statement gate. The tracker
imports `verify` so that the board cannot show an intact lock when the files have changed.
"""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LOCK = HERE / 'statement.lock.json'
MATHLIB = Path('/home/dev/ggg/.deps/lean-4.33.1/mathlib')

# Paths relative to the repo root, plus the Mathlib files that define the hypothesis notions.
LOCKED = [
    'lean/BTBMS/Syntax.lean',
    'lean/BTBMS/Expansion.lean',
    'lean/BTBMS/Mahlo.lean',
    'lean/BTBMS/Statement.lean',
    'lean/lean-toolchain',
    'lean/lakefile.toml',
    'lean/lake-manifest.json',
    'checks/lock/LockCheck.lean',
]
MATHLIB_LOCKED = [
    'Mathlib/SetTheory/Cardinal/Cofinality/Club.lean',
    'Mathlib/SetTheory/Cardinal/Regular.lean',
]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current():
    files = {p: sha256(ROOT / p) for p in LOCKED}
    files.update({f'mathlib:{p}': sha256(MATHLIB / p) for p in MATHLIB_LOCKED})
    return files


def verify():
    """Return (ok, problems)."""
    if not LOCK.exists():
        return False, ['no lock recorded']
    recorded = json.loads(LOCK.read_text())['files']
    now = current()
    problems = [f'{p}: changed' for p in recorded if now.get(p) != recorded[p]]
    problems += [f'{p}: not in lock' for p in now if p not in recorded]
    return not problems, problems


def main():
    if sys.argv[1:] == ['--write']:
        LOCK.write_text(json.dumps({
            'gate': 'G2',
            'signed_off_by': 'user',
            'date': '2026-10-27',
            'reviewed_in': ['tracker/review/codex-statement-review.md'],
            'pins': {'lean': 'v4.33.1', 'mathlib': 'eba3d887fc52c98627f4b81507c0efc3096e91b9',
                     'cu': '7f5a7d03d63d9769172f17350bbe8303996e5b53'},
            'files': current(),
        }, indent=1) + '\n')
        print(f'lock written: {LOCK.relative_to(ROOT)}')
        return
    ok, problems = verify()
    print('lock intact' if ok else 'LOCK BROKEN:\n  ' + '\n  '.join(problems))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
