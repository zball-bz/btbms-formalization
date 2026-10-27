# Current handoff

Read this first at the start of every session (Claude, Codex). Root (Claude) maintains it.

## Where we are
- Phase P1 (Review). Two blind reviews are running against `tracker/review/BRIEF.md`:
  Claude → `tracker/review/claude-review.md`, Codex → `tracker/review/codex-review.md`.
- Neither reviewer reads the other's file until root merges them (T-004).

## Conventions
- Only root edits `tracker/ledger.json`, `tracker/CURRENT.md`, and (later) the Lean root and
  integration scripts. Workers write only the files their task names.
- Status comes from evidence: run `python3 tracker/refresh.py`; it refuses a ledger that
  claims a gap is confirmed by one reviewer, or a task done without evidence on disk.
- A finding by one reviewer becomes `confirmed` only after the other reviewer finds it when
  shown the location, not the conclusion.
- One commit per integration step.

## Next
1. Finish both reviews (T-002, T-003).
2. Merge into claim inventory + gap register (T-004); blind cross-check (T-005).
3. In parallel: differential test of §1 against BTBM.ts (T-006), reuse audit (T-007),
   Mathlib survey (T-008).
