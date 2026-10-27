# Status snapshot

Generated 2026-10-27T15:04:46+00:00 at commit `c190873`. Hand-written context lives in `CURRENT.md`.

Phase: **P4 Formalize**

## todo (1)
- T-008 [claude] Library survey: what Mathlib provides for ordinals, clubs, stationary sets, Mahlo cardinals

## doing (1)
- T-022 [claude] Prove the plan in Lean: batches of nodes in separate worktrees, verified by lake build; done when checks/lock/check.sh --final passes

## blocked (1)
- T-020 [claude] Close the blueprint's open arguments G-009..G-012 and bounded-test the untested integration statements

## done (19)
- T-001 [claude] Set up repo, pinned reference fetch, tracker
- T-002 [claude] Blind review of the paper (Claude)
- T-003 [codex] Blind review of the paper (Codex)
- T-004 [claude] Merge reviews into claim inventory and gap register
- T-005 [codex] Blind cross-check: each single-reviewer finding goes to the other reviewer without the conclusion
- T-006 [codex] Differential test harness: paper's E[n] (independent implementation) vs reference BTBM.ts
- T-007 [codex] Reuse audit: kp-simplified-verification, dh-bms-wf-formal, 1Y-Well-Ordering-Lean
- T-009 [user] Gate G1: waived by the user (D-5); proceed to formalization
- T-010 [codex] Package bounded checks (reference diff, graph identity, finite invariants, cofinality) into checks/ with pinned inputs and one command
- T-011 [user] Decide D-1 (host Lean vs object theory) and D-2 (hypothesis strength)
- T-012 [claude] Set up the Lean 4.33.1 project with pinned Mathlib + narrow CU imports (no edits to the 1Y vendor tree)
- T-013 [claude] Formalize the main statement in Lean (definitions, order, operation, Std, Mahlo, theorem with sorry)
- T-014 [codex] Independent statement-fidelity review of the Lean statement
- T-015 [user] Gate G2: sign off the Lean statement; then it is locked
- T-016 [claude] Blueprint (lemma plan): spine + five units drafted, adversarially verified, integrated
- T-017 [codex] Blind review of the blueprint (statements and proofs, without the verification notes)
- T-018 [claude] Move the skeleton into lean/BTBMS/Plan (Part C, Part B and off-chain nodes dropped, false statements corrected); every node mapped to Lean declarations
- T-019 [codex] Check the statement lock (split into locked Prop defs + unlocked proof file; lock and status scripts)
- T-021 [claude] Correct the false statements BP-01..BP-05 and provider gaps BP-08/BP-09; rerun Codex's counterexample files against the amended skeleton
