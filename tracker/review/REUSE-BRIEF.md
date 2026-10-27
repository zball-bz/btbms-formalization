# T-007 brief: reuse audit

Goal: decide what existing local Lean work can be reused for the BTBMS formalization, under
**both** answers to decision D-1 (see `tracker/GAPS.md` → Decisions):

- **(H) host Lean:** a Lean theorem `(∀ n, ∃ κ, n-Mahlo κ) → WellFounded (<) on Std`, likely
  with Mathlib.
- **(O) object theory:** a Hilbert derivation ZFC + {n-Mahlo} ⊢ WO(Std) inside a deep embedding,
  as KP1Y did for KPω.

## Candidates (read-only; do not modify them)
- `/home/dev/ggg/kp-simplified-verification`: KP1Y, Lean 4.33.1, object-level KPω derivations on
  `third_party/YesMetaZFC`. Start from `README.md`, `GOAL.md`, `LIBRARY-AND-REUSE.md`,
  `tracker/OUTLINE.md` and `tracker/INTERFACES.md`.
- `/home/dev/ggg/dh-bms-wf-formal`: `lean/Bm4`, Lean 4.30.0, including `SetTheory/`.
- `/home/dev/ggg/1Y-Well-Ordering-Lean`: `formalization/`, `y1/`, `vendor/`.

## Deliverable: `tracker/review/reuse-audit.md`
1. Per candidate: what it proves (main theorem statements, verbatim), foundation (Mathlib or
   not, deep or shallow embedding), Lean version, size, license/provenance constraints.
2. A table mapping our claim inventory (IDs in `tracker/ledger.json` → `nodes`, also in the
   Claims view of `tracker/index.html`) to reusable modules. Give, per row: module path,
   what it provides, the fit (direct / adapt / idea only), and the estimated adaptation work.
   Focus on §5–§6 (J/L hierarchy, Σ1 Skolem hulls, condensation-like collapse, satisfaction and
   truth tables, R/FR reflection edges, clubs/stationarity) and §1–§4 (BMS-like syntax,
   expansions, scan/ancestry machinery).
3. For (H) and (O) separately: a rough size estimate of new work, reusing what is reusable.
   Name the three largest new components and the main technical risk of each.
4. Toolchain: can one project build against the reusable parts at a single Lean version?
   Which version, and what breaks?

## Rules
- Write only `tracker/review/reuse-audit.md` and `scratch/codex/`. Do not edit the candidate
  projects. Do not run `lake build` on them (KP1Y convention: single-module checks only, via
  their scripts).
- Quote theorem statements exactly; separate what you verified from what you infer.
- End with `STATUS: COMPLETE`.
