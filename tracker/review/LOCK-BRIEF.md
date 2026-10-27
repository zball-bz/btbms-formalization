# T-019 brief: check the statement lock (small)

The user signed off the Lean statement (gate G2). To let the proof change without touching the
signed-off text, Claude split it in commit d1f7c39:
- `lean/BTBMS/Statement.lean` now holds `Std`, `Std.lt`, and the Prop definitions
  `MainTheorem` and `PaperTheorem`, plus the proved implication `MainTheorem.paper`.
- `lean/BTBMS/Main.lean` holds `std_isWellOrder` (the `sorry`), `mainTheorem : MainTheorem`, and
  `paperTheorem : PaperTheorem`.
- `checks/lock/` holds the lock: `lock.py` checks file hashes against `statement.lock.json`;
  `LockCheck.lean` checks by `rfl` that the Prop definitions are the types you reviewed in T-014;
  `check.sh` runs both.

Questions:
1. Is `MainTheorem` (and `PaperTheorem`) exactly the statement you reviewed in T-014? Compare
   with `git show 82c3f01:lean/BTBMS/Statement.lean`.
2. Does the lock catch what it should? Could the main theorem be "proved" by changing something
   the lock does not cover? Consider the files covered, universe parameters, the `rfl` check,
   `Main.lean` being unlocked, and the Mathlib files the hypothesis depends on.
3. Do `checks/lock/Status.lean` and `scripts/lean-status.sh` report `sorry` usage faithfully?
   Could a declaration that depends on `sorry` show as proved?

Deliverable: `tracker/review/codex-lock-review.md`, one verdict per question, required changes
(if any), and `STATUS: COMPLETE` at the end. Write only that file and `scratch/codex/`.

Do not read `blueprint/`: you will review it blind later (T-017).

## Follow-up (after your review)
Claude fixed the five required changes (gap G-008 in the ledger; see its `fix` field):
`checks/lock/LockCheck.lean`, `checks/lock/lock.py`, `checks/lock/check.sh` (new `--final`),
`checks/lock/Status.lean`, `scripts/lean-status.sh`, `tracker/refresh.py`.
Check the fix independently: rerun your scratch exploits and try new ones against the new
mechanism. Append a "Follow-up" section to `tracker/review/codex-lock-review.md` with a verdict
per required change and `STATUS: COMPLETE`. Still do not read `blueprint/`.
