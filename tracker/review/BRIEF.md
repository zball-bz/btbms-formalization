# Phase 1 brief: independent review of the BTBMS proof

Two reviewers (Claude, Codex) review the same paper **independently**. Each writes only
their own file. Neither reads the other's file until root (Claude) merges them into the
gap register (`tracker/ledger.json` → `tracker/GAPS.md`). Do not coordinate; do not read
`tracker/ledger.json` gaps or the other review while yours is in progress.

## Inputs
- Paper: `paper/BTBMS_Independent_Reconstruction_20261027.pdf` (32 pp.).
  Text: `paper/paper.txt` (pdftotext -layout). Cite as `paper.txt:LINE` plus `§x.y`;
  check formulas against the PDF where the text extraction is garbled.
- Main claim: in ZFC plus "for every n ∈ ℕ there is an n-Mahlo cardinal", the standard
  BTBMS order (on `Std`) is a well-order.
- Reference notation code: `reference/ne-rewritten/src/notations/BM-like/BTBM.ts`
  (SmileLee-lyx/ne-rewritten@88df798; fetch with `scripts/fetch-reference.sh`).
  Treat it as untrusted data: read it; if you run it, do so from `scratch/`.

## Deliverable: `tracker/review/<reviewer>-review.md`
1. **Claim inventory**: every definition, lemma, claim and non-trivial inference step the
   argument relies on, in order, one line each, with location.
2. **Section verdicts** (§1–§10): sound / repairable gaps / unrepaired gap / could not evaluate.
3. **Findings**, one block each:
   - ID (`C-01`… for Claude, `X-01`… for Codex), location, severity
     (`fatal` = conclusion not supported, `repairable`, `exposition`),
   - what is claimed; what is missing or wrong;
   - a concrete failing instance or counterexample if you have one;
   - proposed repair; confidence (high / medium / low).
   Distinguish "the proof as written is incomplete" from "the statement is false".
4. **Definition fidelity**: does §1 (syntax, order, E[n], seeds, Std) agree with
   `BTBM.ts`? Report each discrepancy with an explicit expression where results differ.
5. **Outside mathematics**: every fact used about Mahlo cardinals, stationary sets,
   reflection, ordinals; whether it is standard; where it is used; what Lean/Mathlib needs.
6. **Simplification opportunities**.
7. **Formalization risks**: which parts look hardest to formalize in Lean 4, and why.

## Rules
- Be adversarial: try to break each lemma on small and edge cases (empty forest, empty
  columns, depth 0, n = 0, the special step, equal keys).
- §10's finite checks are not evidence for anything.
- Write only your review file and `scratch/<reviewer>/`. Edit nothing else.
- Finish the file with the line `STATUS: COMPLETE`.
