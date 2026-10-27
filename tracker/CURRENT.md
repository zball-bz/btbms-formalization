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
- **Lean statement:** `lean/BTBMS/Statement.lean` (commit 82c3f01).
  - Codex's independent fidelity review (`tracker/review/codex-statement-review.md`, with its
    follow-up) finds it faithful, with no remaining required change.
  - **Gate G2 passed** (user go-ahead, 2026-10-27). The statement is **locked**:
    `checks/lock/check.sh` verifies the hashes in `checks/lock/statement.lock.json` and the
    elaborated statements. The locked files are Syntax, Expansion, Mahlo and Statement (with the
    Prop definitions `MainTheorem` and `PaperTheorem`). The proof goes in `lean/BTBMS/Main.lean`,
    and `mainTheorem : MainTheorem` must end up sorry-free.
- **Lean progress is derived from the build:** `scripts/lean-status.sh` writes
  `tracker/lean-status.json`, and `refresh.py` maps it to claims through `lean_decls`.
- **Blueprint (T-016) done:** `blueprint/`, summary in `blueprint/INTEGRATION.md`.
  - The plan has 302 nodes plus MAIN, all in `tracker/ledger.json` with `uses` edges and planned
    `lean_decls`. The board's Plan tab derives the per-unit counts, the heaviest chain and the
    nodes that are ready to prove.
  - The integrated Lean skeleton (Spine + U1–U5) typechecks with `sorry` proofs only.
  - Only three definitions still have `sorry` bodies: the two order instances (proof fields)
    and `Hier.jInterface` (waits on D-4).
  - Four open arguments are recorded as suspected gaps G-009…G-012. The repairs of
    G-001…G-005 are written, and Codex's review (T-017) checks them.

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
- **D-4 (user, open):** which hierarchy to use for the main-theorem route.
  - Part B is the paper's J-hierarchy: about 18k–37k LOC.
  - Part C is the reflection hierarchy, S-7 / P-U4-1: about 2.5k–5k LOC. No statement changes,
    but §5 itself would go uncertified.
  - Root recommends Part C.

## Verification policy (from 2026-10-28)
- **Lean is the verifier of proofs.** A lemma counts as verified only when its Lean proof
  compiles with no `sorry` and no new axiom; `refresh.py` derives this. Proof plans get no
  further informal verification rounds: three layers of drafter, adversarial checker and
  reviewer kept growing without converging.
- **Bounded tests screen statements for falsity only.**
  - Run them once, when a statement is new or changed, on one shared corpus.
  - Hard budget per batch: at most 4 processes and 10 minutes.
  - No open-ended "as large as feasible" pools. Every counterexample found so far had size ≤ 18.
- **Codex reviews statement changes (diffs), not proofs**, with one round per change.
- **Risky nodes are formalized first**, so that an open argument shows up as a precise stuck
  goal rather than as another informal write-up.
- **Workflows:** at most about 8 agents, and every agent prompt carries the compute cap.

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

## Result (2026-10-28)
- **The main theorem is formally verified.** `checks/lock/check.sh --final` passes on main. It
  reports, for both `BTBMS.mainTheorem` and `BTBMS.paperTheorem`: the statement lock is intact,
  the type is exactly the locked `MainTheorem` / `PaperTheorem`, and the axioms are only
  `propext`, `Classical.choice` and `Quot.sound`.
- **The proof** lives in `lean/BTBMS/Plan/{Spine,U1..U5}.lean` and `lean/BTBMS/Main.lean`. The
  hierarchy is Part C (the reflection hierarchy, D-4).
- **Cleanup done the same day:**
  - The 17 `sorry` declarations off the main theorem's path are deleted. The project now has
    4,027 declarations, none with or depending on `sorry`.
  - The duplicated phase-copy machinery is removed: `OrdStep` extends `OrdData`, and 3,705 lines
    are gone.
  - The prover worktrees and their `prove/*` branches are removed.
