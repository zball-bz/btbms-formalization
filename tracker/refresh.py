#!/usr/bin/env python3
"""Validate tracker/ledger.json and regenerate index.html, GAPS.md and STATUS.md.

The ledger is the single source of truth and only root (Claude) edits it.
Statuses that can be derived are checked here rather than trusted:
  * a gap is `confirmed` only if two different reviewers found it independently;
  * a gap is `closed` only if someone other than the repair author checked the repair;
  * a task is `done` only if its evidence files exist.
Lean status (phase 4) will be derived from the Lean sources, never set by hand.
"""
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
LEDGER = HERE / 'ledger.json'

TASK_STATUSES = ['todo', 'doing', 'blocked', 'review', 'done']
GAP_STATUSES = ['suspected', 'confirmed', 'disputed', 'refuted', 'repaired', 'closed']
SEVERITIES = ['fatal', 'repairable', 'exposition', 'unknown']
SIMPLIFICATION_STATUSES = ['proposed', 'agreed', 'rejected', 'applied']
DECISION_STATUSES = ['open', 'decided']
PEOPLE = {'claude', 'codex', 'user'}


def check(ledger):
    errors = []
    tasks = {t['id']: t for t in ledger['tasks']}
    for t in ledger['tasks']:
        if t['status'] not in TASK_STATUSES:
            errors.append(f"{t['id']}: unknown status {t['status']}")
        if t['owner'] not in PEOPLE:
            errors.append(f"{t['id']}: unknown owner {t['owner']}")
        for d in t.get('deps', []):
            if d not in tasks:
                errors.append(f"{t['id']}: unknown dependency {d}")
        if t['status'] == 'done':
            missing = [e for e in t.get('evidence', []) if not (ROOT / e).exists()]
            if not t.get('evidence'):
                errors.append(f"{t['id']}: done without evidence")
            if missing:
                errors.append(f"{t['id']}: evidence missing on disk: {missing}")
    for g in ledger['gaps']:
        if g['status'] not in GAP_STATUSES:
            errors.append(f"{g['id']}: unknown status {g['status']}")
        if g['severity'] not in SEVERITIES:
            errors.append(f"{g['id']}: unknown severity {g['severity']}")
        finders = set(g.get('found_by', [])) | set(g.get('confirmed_by', []))
        if g['status'] == 'confirmed' and len(finders) < 2:
            errors.append(f"{g['id']}: confirmed needs two independent reviewers, has {sorted(finders)}")
        if g['status'] == 'closed':
            checker, author = g.get('fix_checked_by'), g.get('fix_by')
            if not checker or checker == author:
                errors.append(f"{g['id']}: closed needs a fix check by someone other than {author}")
    gap_ids = {g['id'] for g in ledger['gaps']}
    for n in ledger['nodes']:
        for g in n.get('gaps', []):
            if g not in gap_ids:
                errors.append(f"{n['id']}: unknown gap {g}")
    for s in ledger.get('simplifications', []):
        if s['status'] not in SIMPLIFICATION_STATUSES:
            errors.append(f"{s['id']}: unknown status {s['status']}")
    for d in ledger.get('decisions', []):
        if d['status'] not in DECISION_STATUSES:
            errors.append(f"{d['id']}: unknown status {d['status']}")
        if d['status'] == 'decided' and not d.get('answer'):
            errors.append(f"{d['id']}: decided without an answer")
    return errors


def git_head():
    try:
        return subprocess.run(['git', '-C', str(ROOT), 'rev-parse', '--short', 'HEAD'],
                              capture_output=True, text=True, check=True).stdout.strip()
    except subprocess.CalledProcessError:
        return None


def gaps_md(ledger):
    lines = ['# Gap register', '',
             'Generated from `tracker/ledger.json` by `tracker/refresh.py`; do not edit by hand.', '',
             '| ID | Status | Severity | Location | Summary | Found by | Confirmed by |',
             '|---|---|---|---|---|---|---|']
    for g in ledger['gaps']:
        lines.append('| {id} | {status} | {severity} | {loc} | {summary} | {f} | {c} |'.format(
            f=', '.join(g.get('found_by', [])), c=', '.join(g.get('confirmed_by', [])),
            **{k: g.get(k, '') for k in ('id', 'status', 'severity', 'loc', 'summary')}))
    if not ledger['gaps']:
        lines.append('| — | | | | No gaps recorded yet. | | |')
    for g in ledger['gaps']:
        lines += ['', f"## {g['id']} — {g['summary']}", '']
        for key in ('detail', 'fix', 'refs'):
            if g.get(key):
                val = g[key] if isinstance(g[key], str) else ', '.join(g[key])
                lines.append(f'**{key.capitalize()}:** {val}')
                lines.append('')
    lines += ['', '# Decisions', '', '| ID | Owner | Status | Question | Answer / impact |', '|---|---|---|---|---|']
    for d in ledger.get('decisions', []):
        lines.append(f"| {d['id']} | {d['owner']} | {d['status']} | {d['question']} | {d.get('answer') or d.get('impact', '')} |")
    lines += ['', '# Simplifications', '', '| ID | Status | Summary | Found by |', '|---|---|---|---|']
    for s in ledger.get('simplifications', []):
        lines.append(f"| {s['id']} | {s['status']} | {s['summary']} | {', '.join(s.get('found_by', []))} |")
    lines += ['', '# Risks', '', '| ID | Risk | Mitigation |', '|---|---|---|']
    for r in ledger.get('risks', []):
        lines.append(f"| {r['id']} | {r['summary']} | {r.get('mitigation', '')} |")
    return '\n'.join(lines) + '\n'


def status_md(ledger, stats):
    lines = ['# Status snapshot', '',
             f"Generated {stats['generated']} at commit `{stats['head']}`. Hand-written context lives in `CURRENT.md`.", '',
             f"Phase: **{ledger['meta']['phase']}**", '']
    for s in TASK_STATUSES:
        rows = [t for t in ledger['tasks'] if t['status'] == s]
        if rows:
            lines.append(f'## {s} ({len(rows)})')
            lines += [f"- {t['id']} [{t['owner']}] {t['title']}" for t in rows]
            lines.append('')
    return '\n'.join(lines)


def main():
    ledger = json.loads(LEDGER.read_text())
    errors = check(ledger)
    if errors:
        print('ledger check failed:', *errors, sep='\n  ')
        sys.exit(1)
    stats = {
        'generated': datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'head': git_head() or 'uncommitted',
        'tasks': {s: sum(t['status'] == s for t in ledger['tasks']) for s in TASK_STATUSES},
        'gaps': {s: sum(g['status'] == s for g in ledger['gaps']) for s in GAP_STATUSES},
        'open_user_decisions': sum(d['status'] == 'open' and d['owner'] == 'user' for d in ledger.get('decisions', [])),
    }
    payload = json.dumps({'ledger': ledger, 'stats': stats}, ensure_ascii=False)
    html = (HERE / 'template.html').read_text().replace('/*DATA*/null', payload.replace('</', '<\\/'))
    (HERE / 'index.html').write_text(html)
    (HERE / 'GAPS.md').write_text(gaps_md(ledger))
    (HERE / 'STATUS.md').write_text(status_md(ledger, stats))
    print(f"ok: {len(ledger['tasks'])} tasks, {len(ledger['gaps'])} gaps, {len(ledger['nodes'])} claims")


if __name__ == '__main__':
    main()
