# BTBMS well-ordering formalization

Goal: check, repair, simplify and formalize in Lean 4 the proof in
`paper/BTBMS_Independent_Reconstruction_20261027.pdf` that, assuming an n-Mahlo cardinal
for every n, the standard BTBMS order is a well-order.

- Progress board: open `tracker/index.html` (regenerate: `python3 tracker/refresh.py`).
- Handoff / next steps: `tracker/CURRENT.md`. Gap register: `tracker/GAPS.md`.
- Reference notation code (not vendored; upstream has no license):
  `scripts/fetch-reference.sh src/notations/BM-like/BTBM.ts` → `reference/`.
