# Codex statement-lock review — T-019

I read `tracker/CURRENT.md` first, then `tracker/review/LOCK-BRIEF.md`. I did not read `blueprint/`. All executable mutations below were made only in scratch copies; the real Lean sources, checks, dependencies and tracker data were not changed.

**Conclusion:** the statement split preserves the approved mathematics, but the lock and progress mechanism need hardening before they can certify proof completion. In particular, the current exported-proof check accepts a clean theorem of type `True` through a separate admitted coercion.

| Question | Verdict |
|---|---|
| 1. Is the split statement the T-014 statement? | **Faithful.** |
| 2. Does the lock catch the relevant changes? | **Incomplete; required changes.** Listed-file hashes and the Prop `rfl` checks work, but exported constant types, axiom acceptance and the actual dependency closure are not adequately guarded. |
| 3. Does status faithfully report `sorry` use? | **Correct for fresh transitive-sorry data, incomplete overall.** Wrappers do not hide `sorryAx`; stale data can show a presently admitted declaration as proved, custom axioms are called proved, and opaque bodies are omitted from the direct flag. |

## 1. Statement equivalence

I compared the actual source with `git show 82c3f01:lean/BTBMS/Statement.lean`.

The old weak theorem's type was

```lean
(∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) → IsWellOrder Std Std.lt
```

This is exactly the body of `MainTheorem` at `Statement.lean:34–35`. The old strong corollary's type is exactly `PaperTheorem` at lines 38–39, replacing only `IsWeaklyMahlo` by `IsMahlo`. `Std` and `Std.lt` retain their original definitions. Syntax, Expansion and Mahlo are byte-identical to commit 82c3f01. The new proved `MainTheorem.paper` at lines 42–43 performs the same witness conversion as the former corollary.

The universe u remains a genuine parameter of each premise; it has not been fixed to zero or moved up a level. Moving the admitted proof to `Main.lean` does not change these propositions. The current actual wrappers at `Main.lean:18–20` have the right types.

`LockCheck.lean:11–14` checks these two Prop equations by `rfl` at arbitrary u. These checks are valid: proof irrelevance does not identify arbitrary propositions. No statement-definition change or renewed mathematical G2 review is needed merely because of this split.

## 2. Lock coverage and a concrete exported-type bypass

### What works

`lock.py:19–32,45–53` verifies the four definition files, toolchain/config/manifest files, `LockCheck.lean`, and two Mathlib files. Missing or changed listed entries and extra current entries are rejected. The real repository currently reports `lock intact`.

Ordinary universe drift is caught by the current exported-term examples: in scratch I changed the exports to fixed-universe `MainTheorem.{0}` and `PaperTheorem.{0}`, without coercions. `check.sh` exited **1**, reporting that those types do not match `MainTheorem.{u}` and `PaperTheorem.{u}`. Leaving `Main.lean` unlocked is otherwise appropriate: implementations and intermediate proof lemmas should be free to change while the endpoint stays fixed.

### Required: inspect the exported constant's type, not merely an elaborated term

`LockCheck.lean:17–18` currently uses

```lean
example : MainTheorem.{u} := mainTheorem
example : PaperTheorem.{u} := paperTheorem
```

Lean may insert coercions when elaborating the right-hand terms. These examples therefore do **not** establish that the exported constants themselves have the required types.

I replaced only the **scratch** `Main.lean` by:

```lean
import BTBMS.Statement
namespace BTBMS
universe u
instance auditCoerceMain : Coe True MainTheorem.{u} := ⟨fun _ => by sorry⟩
instance auditCoercePaper : Coe True PaperTheorem.{u} := ⟨fun _ => by sorry⟩
theorem mainTheorem : True := True.intro
theorem paperTheorem : True := True.intro
end BTBMS
```

The unchanged full `checks/lock/check.sh` exited **0**. It printed `lock intact`, warnings that the two anonymous examples use `sorry`, and:

```
'BTBMS.mainTheorem' does not depend on any axioms
```

A fresh status run and the actual tracker classifier called both exports **proved**, with empty axiom lists. The coercion instances were separately marked stated, but the main theorem's row was clean. The Prop definitions and their `rfl` equations never changed.

Thus even a whitelist applied only to the printed axioms of `mainTheorem` would not close this hole. Check the raw, universe-instantiated `ConstantInfo.type` of the fully qualified exported constants against the expected propositions, using rigid universe parameters and definitional equality **without term elaboration/coercion insertion**. Alternatively a named guard theorem can be audited for its full dependencies, but that alone does not ensure the exported constant has the promised type. Ordinary type ascriptions and `exact mainTheorem` can also insert coercions.

Evidence: `scratch/codex/lock-coercion-actual.log` and `lock-coercion-status.json`.

### Required: reject unapproved axioms at proof acceptance

In a separate scratch test, I kept the correct exported types but introduced

```lean
axiom auditShortcut : MainTheorem.{u}
```

and defined the exports from it. `check.sh` again exited **0**; it only printed the new axiom dependency. `tracker/refresh.py:87–91` labels both the postulate and its dependent theorems **proved**, since it only treats `sorryAx` specially.

The lock can remain an integrity check that passes while intentional proof holes exist. However, proof completion needs an explicit transitive axiom whitelist, normally `propext`, `Classical.choice`, `Quot.sound`, and must reject `sorryAx` and every unapproved new axiom. The Mahlo assumption is already a premise, so it requires no extra global postulate. Progress should classify postulates and their dependents as assumed/untrusted, not proved.

Evidence: `lock-custom-axiom.log`, `lock-custom-axiom-status.json` under scratch.

### Required: bind the lock to the actual semantic dependency closure

Only Mathlib `Club.lean` and `Regular.lean` are hashed. Important unlocked dependencies include:

- `Order/RelClasses.lean:271–272`: the conclusion `IsWellOrder`;
- `Order/DirSupClosed.lean:49–50`: the closure part of clubs;
- `Order/Bounds/Defs.lean:62–63`: cofinality;
- the transitive Cardinal/Ordinal definitions and initial-ordinal interpretation.

The Prop `rfl` examples still refer to these same identifiers if their meanings change. The textual pins in `statement.lock.json` are recorded metadata; `verify()` does not verify a package tree against them. Adding a few more immediate files would still leave the same transitive problem.

There is also a path mismatch risk: `lock.py:16` hashes a hardcoded absolute Mathlib tree rather than resolving the package used by Lake. In the relocated scratch project, the unchanged manifest selects the scratch `.deps` copy, while `lock.py` still hashes the original absolute directory. Appending a comment to the scratch copy of **Regular.lean itself** changed the actual dependency's bytes, yet `verify()` returned `(True, [])`. This probe demonstrates incorrect dependency binding, not a claim that the comment changed mathematics. The paths happen to agree in the current real workspace.

Use the actual resolved dependency locations and a verified content manifest for the statement's transitive dependency closure (or the whole pinned package), under the chosen trusted compiler. Treat the checker and approved lock record as trusted, root-reviewed inputs. This is not a cryptographic defense against someone deliberately rewriting both the verifier and its baseline; `--write` authorization remains a workflow rule.

## 3. Sorry reporting and freshness

### Fresh transitive reporting is correct

`Status.lean:26–31` records the direct flag and `collectAxioms n`. The installed collector traverses theorem, definition and opaque bodies and imported dependency metadata (`Lean/Util/CollectAxioms.lean:55–66,149–154`). `refresh.py:87–90` correctly classifies direct holes as stated and indirect `sorryAx` as proved modulo sorry.

The current real records correctly show `std_isWellOrder` with direct sorry, and `mainTheorem`/`paperTheorem` with indirect sorry. The wrappers do not hide the hole. Filtering auxiliary/private declarations out of the displayed table does not erase their axiom dependencies from a public theorem.

Scratch probes using the actual collector/classifier gave:

| Declaration | Direct flag | Transitive result | Tracker state |
|---|---:|---|---|
| theorem with `by sorry` | true | `sorryAx` | stated |
| theorem using that theorem | false | `sorryAx` | proved modulo sorry |
| `opaque opaqueHole : True := by sorry` | **false** | `sorryAx` | proved modulo sorry |
| theorem using `opaqueHole` | false | `sorryAx` | proved modulo sorry |
| `axiom injected : False` | false | `BTBMS.injected` | **proved** |
| theorem derived from `injected` | false | `BTBMS.injected` | **proved** |

The custom-axiom classification is the acceptance defect described above; it is not a failure of transitive `sorryAx` collection.

### A presently admitted declaration can display as proved from stale data

`lean-status.sh:8–16` generates accurate data after a successful build/extraction, but `refresh.py:83` reads the last JSON without checking source or build fingerprints. Its saved HEAD is informational, not enforced, and HEAD alone would miss dirty edits. A failed build/extraction leaves the older successful JSON in place.

I confirmed this using the real `lean_stats` function with a minimal scratch ledger. After saving the clean `mainTheorem : True` status, I restored the **actual original Main.lean**, rebuilt, and confirmed the current main theorem prints `sorryAx`. Without regenerating status, `lean_stats` still returned:

```
lock_ok = True
claims["T9.1"] = "proved"
main_axioms = []
```

This is a concrete stale-report instance of the requested failure. A genuine previously proved lemma edited to `by sorry` has the same issue; the problem is not limited to the coercion example. Evidence: `lock-restored-current.log` and `lock-stale-status-result.json`.

Record and verify the relevant source/dependency/build fingerprint, or regenerate status successfully immediately before publishing current progress. On failure, mark the current result failed/stale rather than continuing to present historical success as current. Keep old reports as history if useful.

### The direct flag misses opaque bodies

`Status.lean:24–25` extracts values only from `.thmInfo` and `.defnInfo`, although it emits `.opaqueInfo` rows. The minimal fix is to add `.opaqueInfo o => some o.value`. I verified that change in a scratch probe: the opaque direct hole then reports true. Its transitive hole was already detected, so this bug affects the promised direct-body field and direct count, not fresh transitive proof acceptance. The shell summary at `lean-status.sh:17` should say “direct sorry declarations” and preferably give the transitive count separately.

## Required changes

1. **Exact exported-type guard:** inspect both exported constants' actual types at the intended general universe, without coercion-capable term elaboration. Preserve the valid Prop `rfl` checks.
2. **Axiom-aware progress and final acceptance:** classify postulates/unapproved dependencies explicitly; enforce the approved transitive axiom whitelist and no `sorryAx` for proof completion. Integrity checking may still permit incomplete proofs during development.
3. **Resolved, transitive dependency pinning:** hash the actual dependency sources used by Lake, including the definitions underlying both the hypothesis and conclusion; verify the package/content pins, not only their labels.
4. **Freshness:** bind status to the checked source/dependency snapshot and invalidate current-success status on failed/stale generation. A commit hash alone is insufficient.
5. **Opaque direct holes:** include opaque values in `direct_sorry` and label the direct-hole count accurately.

These repairs concern the guard and progress machinery. **No change to the approved `MainTheorem` or `PaperTheorem` propositions is required.** The current definition split is faithful; a successful present lock command must not yet be interpreted as proof completion.

The unchanged lock passed on the baseline and on the two deliberately invalid proof implementations in scratch; the ordinary fixed-universe export failed as expected. Original reviewed files were hash-checked after the probes. `blueprint/` remained unread throughout.

STATUS: COMPLETE
