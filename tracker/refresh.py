#!/usr/bin/env python3
"""Validate tracker/ledger.json and regenerate index.html, GAPS.md and STATUS.md.

The ledger is the single source of truth and only root (Claude) edits it.
Statuses that can be derived are checked here rather than trusted:
  * a gap is `confirmed` only if two different reviewers found it independently;
  * a gap is `closed` only if someone other than the repair author checked the repair;
  * a task is `done` only if its evidence files exist.
Lean status is derived, never set by hand: the statement lock is re-verified from file hashes
(`checks/lock/lock.py`), and per-declaration sorry/axiom data comes from `tracker/lean-status.json`,
which `scripts/lean-status.sh` regenerates from the build. A claim's Lean status follows from the
declarations it maps to (`lean_decls` in the ledger).
"""
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
LEDGER = HERE / 'ledger.json'
LEAN_STATUS = HERE / 'lean-status.json'
sys.path.insert(0, str(ROOT / 'checks' / 'lock'))
import lock  # noqa: E402

TASK_STATUSES = ['todo', 'doing', 'blocked', 'review', 'done']
GAP_STATUSES = ['suspected', 'confirmed', 'disputed', 'refuted', 'repaired', 'closed']
SEVERITIES = ['fatal', 'repairable', 'exposition', 'unknown']
SIMPLIFICATION_STATUSES = ['proposed', 'agreed', 'rejected', 'applied']
DECISION_STATUSES = ['open', 'decided']
WEIGHTS = {'S': 1, 'M': 2, 'L': 4, 'XL': 8}
DONE_STATES = {'proved', 'defined'}
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
    node_ids = {n['id'] for n in ledger['nodes']}
    for n in ledger['nodes']:
        for g in n.get('gaps', []):
            if g not in gap_ids:
                errors.append(f"{n['id']}: unknown gap {g}")
        for u in n.get('uses', []):
            if u not in node_ids:
                errors.append(f"{n['id']}: uses unknown node {u}")
        if n.get('difficulty', 'S') not in WEIGHTS:
            errors.append(f"{n['id']}: unknown difficulty {n['difficulty']}")
    if not errors and layers(ledger['nodes']) is None:
        errors.append('node graph has a cycle')
    for s in ledger.get('simplifications', []):
        if s['status'] not in SIMPLIFICATION_STATUSES:
            errors.append(f"{s['id']}: unknown status {s['status']}")
    for d in ledger.get('decisions', []):
        if d['status'] not in DECISION_STATUSES:
            errors.append(f"{d['id']}: unknown status {d['status']}")
        if d['status'] == 'decided' and not d.get('answer'):
            errors.append(f"{d['id']}: decided without an answer")
    return errors


STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
# Worst first: a claim shows the worst state among its declarations.
LEAN_STATES = ['axiom (untrusted)', 'assumes extra axioms', 'stated', 'proved modulo sorry', 'proved', 'defined']


def decl_state(d):
    if d['kind'] == 'axiom':
        return 'axiom (untrusted)'
    if set(d['axioms']) - STANDARD_AXIOMS - {'sorryAx'}:
        return 'assumes extra axioms'
    if d['direct_sorry']:
        return 'stated'
    if 'sorryAx' in d['axioms']:
        return 'proved modulo sorry'
    return 'defined' if d['kind'] in ('def', 'inductive') else 'proved'


def lean_stats(ledger):
    """Lock state, declaration status from the last build, and each claim's derived Lean status.

    The status record counts only if it was generated successfully (build, lock/export audit,
    extraction), its fingerprint matches the current inputs, and the lock is intact; otherwise
    every derived state is reported as unknown."""
    ok, problems = lock.verify()
    status = json.loads(LEAN_STATUS.read_text()) if LEAN_STATUS.exists() else {}
    try:
        fingerprint = lock.fingerprint()
    except lock.LockError as e:
        fingerprint = None
        problems = problems + [str(e)]
    if not status:
        problem = 'no status recorded; run scripts/lean-status.sh'
    elif status.get('state') == 'running':
        problem = 'status generation in progress (or interrupted)'
    elif status.get('state') != 'ok':
        problem = f"last generation failed: {status.get('reason', 'unknown reason')}"
    elif not (status.get('build_ok') and status.get('audit_ok')):
        problem = 'record lacks a passing build and lock/export audit'
    elif fingerprint is None or status.get('fingerprint') != fingerprint:
        problem = 'stale: Lean sources or dependencies changed since the last scripts/lean-status.sh'
    elif not ok:
        problem = 'statement lock broken'
    else:
        problem = None
    decls = [] if problem else status['decls']
    for d in decls:
        d['state'] = decl_state(d)
    by_name = {d['name']: d for d in decls}

    claims = {}
    for n in ledger['nodes']:
        names = n.get('lean_decls', [])
        if not names:
            claims[n['id']] = 'not stated'
        elif problem:
            claims[n['id']] = 'unknown (status not current)'
        elif all(x not in by_name for x in names):
            claims[n['id']] = 'planned'
        elif any(x not in by_name for x in names):
            claims[n['id']] = f"partial ({sum(x in by_name for x in names)}/{len(names)} declared)"
        else:
            states = {by_name[x]['state'] for x in names}
            claims[n['id']] = next(s for s in LEAN_STATES if s in states)
    main = by_name.get('BTBMS.mainTheorem')
    return {
        'lock_ok': ok and fingerprint is not None, 'lock_problems': problems, 'status_problem': problem,
        'status_generated': status.get('generated'), 'status_head': status.get('head'),
        'decls': decls,
        'sorry_decls': None if problem else sum(d['direct_sorry'] for d in decls),
        'main_axioms': main['axioms'] if main else None,
        'claims': claims,
    }


def layers(nodes):
    """Layer of each node (0 = uses nothing; otherwise one more than its deepest use), or None on a cycle."""
    uses = {n['id']: n.get('uses', []) for n in nodes}
    layer, busy = {}, set()

    def visit(i):
        if i in layer:
            return layer[i]
        if i in busy:
            raise ValueError(i)
        busy.add(i)
        layer[i] = 1 + max((visit(u) for u in uses[i]), default=-1)
        busy.discard(i)
        return layer[i]
    try:
        for i in uses:
            visit(i)
    except ValueError:
        return None
    return layer


def longest_chain(nodes, target, weight):
    """Heaviest dependency chain ending at `target`, as a list of node ids from its start."""
    by_id = {n['id']: n for n in nodes}
    memo = {}

    def best(i):
        if i not in memo:
            tails = [best(u) for u in by_id[i].get('uses', [])]
            w, chain = max(tails, key=lambda t: t[0], default=(0, []))
            memo[i] = (w + weight(by_id[i]), chain + [i])
        return memo[i]
    return best(target)


def plan_stats(ledger, claims):
    """Progress over the lemma plan, derived from the node graph and the claims' Lean states."""
    nodes = ledger['nodes']
    if not nodes or 'MAIN' not in {n['id'] for n in nodes}:
        return None
    layer = layers(nodes)
    by_id = {n['id']: n for n in nodes}
    needed, todo = set(), ['MAIN']
    while todo:  # only nodes on a chain to the main theorem count; the rest are optional
        i = todo.pop()
        if i not in needed:
            needed.add(i)
            todo += by_id[i].get('uses', [])
    optional = [n['id'] for n in nodes if n['id'] not in needed]
    nodes = [n for n in nodes if n['id'] in needed]
    known = not any(c.startswith('unknown') for c in claims.values())
    done = {i for i, c in claims.items() if c in DONE_STATES}
    umbrella = [n for n in nodes if not n.get('lean_decls')]  # done once everything it groups is done
    for _ in umbrella:
        done |= {n['id'] for n in umbrella if all(u in done for u in n.get('uses', []))}
    ready = [n['id'] for n in nodes if known and n['id'] not in done and all(u in done for u in n.get('uses', []))]
    units = {}
    for n in nodes:
        u = units.setdefault(n.get('unit', '?'), {'nodes': 0, 'weight': 0, 'done': 0, 'ready': 0})
        u['nodes'] += 1
        u['weight'] += WEIGHTS[n.get('difficulty', 'S')]
        u['done'] += n['id'] in done
        u['ready'] += n['id'] in ready
    w = lambda n: WEIGHTS[n.get('difficulty', 'S')]
    left = lambda n: 0 if n['id'] in done else w(n)
    return {
        'known': known, 'needed': len(nodes), 'optional': optional,
        'done': len(done & needed) if known else None, 'ready': ready if known else None,
        'layers': layer, 'units': units,
        'critical_path': longest_chain(nodes, 'MAIN', lambda n: 1)[1],
        'weighted_path': longest_chain(nodes, 'MAIN', w),
        'remaining_path': longest_chain(nodes, 'MAIN', left) if known else None,
        'total_weight': sum(w(n) for n in nodes),
    }


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
        'lean': lean_stats(ledger),
    }
    stats['plan'] = plan_stats(ledger, stats['lean']['claims'])
    payload = json.dumps({'ledger': ledger, 'stats': stats}, ensure_ascii=False)
    html = (HERE / 'template.html').read_text().replace('/*DATA*/null', payload.replace('</', '<\\/'))
    (HERE / 'index.html').write_text(html)
    (HERE / 'GAPS.md').write_text(gaps_md(ledger))
    (HERE / 'STATUS.md').write_text(status_md(ledger, stats))
    lean = stats['lean']
    print(f"ok: {len(ledger['tasks'])} tasks, {len(ledger['gaps'])} gaps, {len(ledger['nodes'])} claims; "
          f"lock {'intact' if lean['lock_ok'] else 'BROKEN'}; "
          + (f"Lean status {lean['status_problem']}" if lean['status_problem']
             else f"{lean['sorry_decls']} declarations with a direct sorry")
          + (f"; plan {plan['done']}/{plan['needed']} needed nodes done, {len(plan['ready'])} ready"
             if (plan := stats['plan']) and plan['known'] else ''))


if __name__ == '__main__':
    main()
