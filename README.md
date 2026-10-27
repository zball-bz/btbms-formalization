# BTBMS well-ordering formalization

A Lean 4 proof that, if there is a weakly n-Mahlo cardinal for every n, the standard BTBMS
expressions are well-ordered by the syntax order: the main theorem of
`paper/BTBMS_Independent_Reconstruction_20261027.pdf` (§9), formalized as `BTBMS.mainTheorem`.
The paper's form, with n-Mahlo cardinals over inaccessibles, follows as `BTBMS.paperTheorem`.

The paper is by **test_alpha0** (known as measurable_cardinal on Discord).

**Status (2026-10-28): proved.** No `sorry` anywhere in the project (4,027 declarations); the
main theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## The statement

The statement is in four locked files, `lean/BTBMS/{Syntax,Expansion,Mahlo,Statement}.lean`
(about 440 lines); `checks/lock/check.sh` refuses any change to them.

```lean
def MainTheorem : Prop :=
  (∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) → IsWellOrder Std Std.lt
```

- `Forest`, the order `<`: paper §1.1.
- `expand` (the operation `E[n]`): a port of `FS` in the reference implementation `BTBM.ts`
  (SmileLee-lyx/ne-rewritten@88df798). On standard expressions it agrees with the paper's §1.2
  operation, proved in Lean as `Scan.expand_eq_paperOp` and `Closure.isStd_iff_paper`.
- `seed`, `IsStd`, `Std`: paper §1.3. `IsWeaklyMahlo`, `IsMahlo`, `StationaryIn`: paper §6.2.

The statement was checked against the paper and `BTBM.ts` before it was locked: differential
tests against the reference (`checks/lean/run.sh`, 580,021 cases, no mismatch) and an
independent review (`tracker/review/codex-statement-review.md`).

The proof is in `lean/BTBMS/Plan/{Spine,U1,U2,U3,U4,U5}.lean` and `lean/BTBMS/Main.lean`. It
follows the paper except that a reflection hierarchy replaces the paper's J-hierarchy (§5);
see decision D-4 in `tracker/ledger.json`.

## Verifying

Requirements: Lean `v4.33.1` and these dependency commits (Lake path packages; Mathlib is the
unmodified upstream commit):

| Package | Repository | Commit |
|---|---|---|
| mathlib | leanprover-community/mathlib4 | `eba3d887fc52c98627f4b81507c0efc3096e91b9` |
| batteries | leanprover-community/batteries | `2c810760f0a0c4536b397dbe30ca9b2f2f467366` |
| aesop | leanprover-community/aesop | `57d3325be72a842920813bcb40f96a6f7393c185` |
| Qq | leanprover-community/quote4 | `ee41917ae11d38479fb8fb24745f7ca4bf0a784d` |
| plausible | leanprover-community/plausible | `b1c4a69a7e247ab7df20460212001673d74f08c0` |
| LeanSearchClient | leanprover-community/LeanSearchClient | `0498c7c070c143a3bf7379f4d99a2c63bb9d9715` |
| importGraph | leanprover-community/import-graph | `18a90119a5d316358fde6c86e0ca24e59212e32c` |
| proofwidgets | leanprover-community/ProofWidgets4 | `b1436dc749e722c9920036b52cdc43b3451d0b69` |
| Cli | leanprover/lean4-cli | `da07ca808b6718cb2aed14dba154e5a08b8f8ecf` |

`lean/lakefile.toml` expects them at `../.deps/lean-4.33.1/<package>` relative to this
repository. `checks/lock/check.sh` uses the Lean installation in `BTBMS_LEAN_HOME` (default
`/home/dev/ggg/.tools/lean-4.33.1-linux`). Then:

```sh
cd lean && lake build                # build everything
checks/lock/check.sh --final         # from the repository root
```

`check.sh --final` must print `lock intact`, and for `BTBMS.mainTheorem` and
`BTBMS.paperTheorem`: `type exact; axioms [propext, Classical.choice, Quot.sound]; proof
complete`. The lock also fingerprints the dependency trees and toolchain, so a different
installation of the same commits may report a fingerprint change; the type and axiom check is
the part that certifies the theorem.

## Layout

- `paper/`: the paper (PDF and extracted text).
- `lean/`: the statement, the proof, and the differential-test executable (`DiffTest.lean`).
- `checks/`: the statement lock, the differential tests, and bounded checks of the paper's
  claims (finite falsification attempts, not proofs).
- `blueprint/`: the proof plan the formalization followed.
- `tracker/`: the claim ledger, gap register and progress board (`tracker/index.html`).
- Reference notation code (not vendored; upstream has no license):
  `scripts/fetch-reference.sh src/notations/BM-like/BTBM.ts` → `reference/`.
