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
  - one closed: G-006. Codex supplied the explicit induction predicates and Claude checked
    them.
  - S-3 (Claude's proposed simplification of the base case) was refuted by Codex and is rejected.
- **Bounded evidence:**
  - Claude: cofinality restricted to E ∈ Std, 276,818,685 pairs, no failure.
  - Codex: reference vs independent §1 implementation, 59,995 operations, no mismatch;
    occurrence-graph identity, 93,076 comparisons; finite invariants including 84,291
    admissible caps.
  - Both test suites live in `scratch/` and still need packaging (T-010).
- **Reuse audit (T-007) done:** `tracker/review/reuse-audit.md`.
  - Estimates: H 40k–90k new LOC; O 110k–250k.
  - Best H base: Mathlib plus the Apache-2.0 CU library in `1Y-Well-Ordering-Lean/vendor/cu`
    (collapse, condensation for full elementarity, history budgets).
  - Best O base: KP1Y/YesMetaZFC.
- **Running:** T-010, Codex packaging all bounded checks into `checks/`.

## Decisions
- **D-1 = H** (user, 2026-10-27): a host-Lean theorem
  `(∀ n, ∃ κ, n-Mahlo κ) → WellFounded (<) on Std`, with the hypothesis stated in the same
  universe as the J-hierarchy.
- **D-2** (root default, user may override): the main theorem uses weakly n-Mahlo cardinals,
  and the paper's version is a corollary.
- Pinned base (from T-007): Mathlib eba3d887 + CU 7f5a7d0, as vendored in
  `1Y-Well-Ordering-Lean/vendor`, at Lean 4.33.1.
  - Only the 1Y import closure is prebuilt (891 of the Mathlib modules).
  - `Mathlib/SetTheory/Cardinal/Cofinality/Club.lean` is present in the source but not built.
  - Do not write into the 1Y tree.

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
1. Integrate T-010.
2. T-008 library survey on the pinned revisions, then T-012 project setup.
3. P2: repaired and simplified proof write-up (G-002, G-003, G-006 lemmas, S-1, S-2, S-4), then gate G1.
