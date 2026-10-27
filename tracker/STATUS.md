# Status snapshot

Generated 2026-10-27T11:04:44+00:00 at commit `3d727dc`. Hand-written context lives in `CURRENT.md`.

Phase: **P2 Repair & simplify (blueprint)**

## todo (4)
- T-008 [claude] Library survey: what Mathlib provides for ordinals, clubs, stationary sets, Mahlo cardinals
- T-009 [user] Gate G1: sign off the repaired, simplified proof (the blueprint)
- T-017 [codex] Blind review of the blueprint (statements and proofs, without the verification notes)
- T-018 [claude] Compiling sorry skeleton of the whole claim graph; every node mapped to Lean declarations

## doing (1)
- T-016 [claude] Blueprint (lemma plan): spine + five units drafted, adversarially verified, integrated

## done (14)
- T-001 [claude] Set up repo, pinned reference fetch, tracker
- T-002 [claude] Blind review of the paper (Claude)
- T-003 [codex] Blind review of the paper (Codex)
- T-004 [claude] Merge reviews into claim inventory and gap register
- T-005 [codex] Blind cross-check: each single-reviewer finding goes to the other reviewer without the conclusion
- T-006 [codex] Differential test harness: paper's E[n] (independent implementation) vs reference BTBM.ts
- T-007 [codex] Reuse audit: kp-simplified-verification, dh-bms-wf-formal, 1Y-Well-Ordering-Lean
- T-010 [codex] Package bounded checks (reference diff, graph identity, finite invariants, cofinality) into checks/ with pinned inputs and one command
- T-011 [user] Decide D-1 (host Lean vs object theory) and D-2 (hypothesis strength)
- T-012 [claude] Set up the Lean 4.33.1 project with pinned Mathlib + narrow CU imports (no edits to the 1Y vendor tree)
- T-013 [claude] Formalize the main statement in Lean (definitions, order, operation, Std, Mahlo, theorem with sorry)
- T-014 [codex] Independent statement-fidelity review of the Lean statement
- T-015 [user] Gate G2: sign off the Lean statement; then it is locked
- T-019 [codex] Check the statement lock (split into locked Prop defs + unlocked proof file; lock and status scripts)
