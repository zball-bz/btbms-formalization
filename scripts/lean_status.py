#!/usr/bin/env python3
"""Build the Lean library, audit it, and record per-declaration status in tracker/lean-status.json.

The record is the only source of Lean progress for tracker/refresh.py; never edit it by hand.
It is published atomically and only after every step succeeds (T-019 follow-up):
  1. an in-progress record replaces any older one first;
  2. the input fingerprint is taken (checks/lock/lock.py);
  3. `lake build`;
  4. the lock/export audit `checks/lock/LockCheck.lean` (exact exported types, axiom policy);
  5. the declaration extraction `checks/lock/Status.lean`, parsed and validated;
  6. the fingerprint is taken again and must be unchanged.
Any failure publishes a failed record with the reason.
"""
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'tracker' / 'lean-status.json'
sys.path.insert(0, str(ROOT / 'checks' / 'lock'))
import lock  # noqa: E402

DECL_KEYS = {'name': str, 'kind': str, 'module': str, 'direct_sorry': bool, 'axioms': list}


def publish(record):
    record['generated'] = datetime.now(timezone.utc).isoformat(timespec='seconds')
    record['head'] = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', '--short', 'HEAD'],
                                    capture_output=True, text=True).stdout.strip()
    tmp = OUT.with_suffix('.json.tmp')
    tmp.write_text(json.dumps(record, indent=1) + '\n')
    os.replace(tmp, OUT)


def fail(reason, **extra):
    publish({'state': 'failed', 'reason': reason, 'build_ok': False, 'audit_ok': False,
             'decls': [], **extra})
    sys.exit(f'FAILED: {reason}; recorded in {OUT.relative_to(ROOT)}')


def run(*cmd):
    env = dict(os.environ, PATH=f"{lock.LEAN_HOME / 'bin'}:{os.environ['PATH']}")
    env.pop('BTBMS_FINAL', None)
    return subprocess.run(cmd, cwd=ROOT / 'lean', env=env, capture_output=True, text=True)


def main():
    publish({'state': 'running', 'build_ok': False, 'audit_ok': False, 'decls': []})
    try:
        before = lock.fingerprint()
    except lock.LockError as e:
        fail(str(e))
    build = run('lake', 'build')
    if build.returncode:
        fail('lake build failed', log=build.stdout[-4000:] + build.stderr[-4000:])
    audit = run('lake', 'env', 'lean', '../checks/lock/LockCheck.lean')
    audit_log = (audit.stdout + audit.stderr).strip().splitlines()
    if audit.returncode:
        fail('lock/export audit failed', build_ok=True, log='\n'.join(audit_log[-40:]))
    extract = run('lake', 'env', 'lean', '../checks/lock/Status.lean')
    if extract.returncode:
        fail('declaration extraction failed', build_ok=True, audit_ok=True, log=extract.stderr[-4000:])
    try:
        decls = json.loads(extract.stdout)
        if not isinstance(decls, list) or not decls:
            raise ValueError('expected a nonempty JSON array')
        for d in decls:
            for k, t in DECL_KEYS.items():
                if not isinstance(d.get(k), t):
                    raise ValueError(f'bad field {k!r} in {d!r:.200}')
    except ValueError as e:
        fail(f'declaration extraction output invalid: {e}', build_ok=True, audit_ok=True)
    try:
        after = lock.fingerprint()
    except lock.LockError as e:
        fail(str(e))
    if after != before:
        fail('inputs changed during generation; rerun')
    lock_ok, problems = lock.verify()
    publish({'state': 'ok', 'build_ok': True, 'audit_ok': True, 'audit': audit_log,
             'lock_ok': lock_ok, 'lock_problems': problems, 'fingerprint': before, 'decls': decls})
    direct = sum(d['direct_sorry'] for d in decls)
    trans = sum('sorryAx' in d['axioms'] for d in decls)
    print(f"{len(decls)} declarations: {direct} with a direct sorry, {trans} depending on sorry; "
          f"audit ok; lock {'intact' if lock_ok else 'BROKEN'}")


if __name__ == '__main__':
    main()
