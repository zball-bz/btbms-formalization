# Current handoff

Read this first at the start of every session (Claude, Codex). Root (Claude) maintains it.

## Where we are (2026-10-27)
- **P1 (Review)** is nearly done.
  - Both blind reviews are in: `tracker/review/claude-review.md` (committed first) and
    `tracker/review/codex-review.md`.
  - They are merged into `tracker/ledger.json` → `tracker/GAPS.md` and the board.
- **Verdict of both reviewers:** no fatal gap and no counterexample to the main claim on Std.
  Six gaps are recorded:
  - five confirmed: G-001…G-005, of which two are repairable (G-002, G-003) and three are
    exposition only;
  - one suspected: G-006, awaiting a blind cross-check.
- **Bounded evidence:**
  - Claude: cofinality restricted to E ∈ Std, 276,818,685 pairs, no failure.
  - Codex: reference vs independent §1 implementation, 59,995 operations, no mismatch;
    occurrence-graph identity, 93,076 comparisons; finite invariants including 84,291
    admissible caps.
  - Both test suites live in `scratch/` and still need packaging (T-010).
- **Running:** T-005, Codex answering `tracker/review/CROSSCHECK-1.md` (S-3, G-006).

## Waiting on the user
- **D-1:** host-Lean semantic theorem, or object-theory derivation ZFC + Mahlo ⊢ WO(Std) as in KP1Y?
- **D-2:** keep the paper's n-Mahlo hypothesis, or prove the stronger weakly-n-Mahlo version (S-1)?
- T-008 (Mathlib survey) is blocked on D-1. T-007 (reuse audit) informs D-1 and can run before it.

## Conventions
- Only root edits `tracker/ledger.json`, `tracker/CURRENT.md`, and (later) the Lean root and
  integration scripts. Workers write only the files their task names.
- Status comes from evidence: run `python3 tracker/refresh.py`. It refuses a ledger that claims a
  gap is confirmed by one reviewer, a task done without evidence on disk, or a decision
  marked decided without an answer.
- A single-reviewer finding becomes `confirmed` only after the other reviewer finds it when
  shown the location, not the conclusion.
  - Exception, recorded as "non-blind" in the gap entry: an explicit counterexample or a
    one-line argument checked directly.
- One commit per integration step.

## Next
1. Integrate T-005 and update G-006 and S-3.
2. T-007 reuse audit (Codex), then T-010 packaging (Codex).
3. After D-1/D-2: P2 repairs, a simplified-proof write-up, then gate G1.
