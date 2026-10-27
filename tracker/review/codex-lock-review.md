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

## Follow-up

Reviewed commit **55faa50f8b9ca1ab2bae78bab92cceccb1dad317** independently. I replayed the original exploits in scratch copies, tested the new `--final` mode, and tried additional source/status failure cases. **Changes 1, 2 and 5 are fixed. Changes 3 and 4 are substantially improved but are not yet complete.** No bypass of the corrected stored-type/axiom checks in the documented `check.sh --final` command was found. The remaining defects concern coverage of actual source inputs and the progress-generation pipeline.

`blueprint/` remained unread. No real Lean, checks, dependency or tracker-status file was modified.

| Original required change | Verdict | Recheck result |
|---|---|---|
| 1. Exact exported-type guard | **Fixed** | The old coercion exploit, a plain `mainTheorem : True`, and a fixed-universe export are all rejected. |
| 2. Axiom-aware progress and final acceptance | **Fixed for the original defect** | The shortcut axiom is rejected; axiom rows/dependents are now untrusted/extra-axiom states. The normal admitted baseline passes the development check and fails `--final` on `sorryAx`. |
| 3. Resolved transitive dependency pinning | **Partially fixed** | Relocated package changes are detected and ordinary dependency sources are covered. A directory-symlink source alias can still evade the source walk and fingerprint. |
| 4. Current, failure-aware status | **Partially fixed** | Ordinary dirty-source edits invalidate old data, and nonzero build/extraction failures record failure. But fresh progress does not require the exported-type/lock audit to pass; source aliases can hide a new hole; malformed or large JSON can preserve an older success record. |
| 5. Opaque direct holes | **Fixed** | The opaque-body probe now reports `direct_sorry=true` and “stated”; its dependent theorem remains “proved modulo sorry.” Direct and transitive counts are separately labelled. |

### Verified repairs

`LockCheck.lean:36–47` now reads the actual constants, requires theorem declarations, and compares their stored types with the named propositions at their single universe parameter. No proof-term elaboration or coercion occurs in that comparison. The stricter syntactic check is safe for the chosen public signature. The valid Prop `rfl` checks remain in place.

The full scratch replays returned:

| Program/check | Exit |
|---|---:|
| Original admitted Main, normal integrity check | 0, explicitly incomplete |
| Original admitted Main, `--final` | 1, rejects `sorryAx` |
| Former `True` exports plus admitted coercions | 1, wrong stored type |
| Correctly typed exports supplied by `auditShortcut` axiom | 1, BTBMS axiom rejected |
| Exports specialized to universe 0 | 1, wrong universe/type |
| Plain `True` exports without coercions | 1, wrong stored type |
| Mutation of Regular.lean in the relocated project's resolved Mathlib copy | 1, package digest changed |

The new classifier also reports `axiom injected : False` as **axiom (untrusted)** and its theorem wrapper as **assumes extra axioms**. It no longer mistakes either for a proof. The collector's opaque-value case and count labels work as requested. Evidence: `scratch/codex/lock-followup-replay-results.json`, its named logs, and `lock-status-probe/followup-classified.json`.

### Remaining A — current progress does not require the exported-type audit

The exact-type guard is effective when invoked, but `scripts/lean-status.sh:13–15` still runs only `lake build` and `Status.lean`. It neither runs `LockCheck.lean` nor records successful validation of the exported target types. `refresh.py:102–112` also does not use a false `lock.verify()` result to invalidate progress; only `build_ok` and fingerprint equality control `status_problem`.

I tested the clean, axiom-free scratch exports

```lean
theorem mainTheorem : True := True.intro
theorem paperTheorem : True := True.intro
```

The new lock command correctly exited 1. Nevertheless a **fresh** `scripts/lean-status.sh` exited 0, printed zero direct and transitive holes, and the actual `lean_stats` function returned:

```
lock_ok = True
status_problem = None
main_axioms = []
claims["T9.1"] = "proved"
```

This is not stale JSON and is not a bypass of `--final`; it is a missing connection between the effective guard and the authoritative progress claim. A successful build proves the constant's actual `True` type, not its expected ledger target.

**Required fix:** run the nonfinal lock/export audit as part of status generation, record its outcome, and require that outcome plus an intact approved lock before calling the main target proved. A separate `guard_ok`/audit field is preferable to silently redefining `build_ok`; diagnostics can still be retained when the audit fails. Freshness acceptance must reject older records that lack the required audit evidence.

### Remaining B — an imported source can be omitted through a directory symlink

`lock.py:47–58` calls `os.walk` without following directory symlinks and skips `.lake`. The following supported source layout is consequently invisible to the fingerprint:

```
lean/BTBMS/AuditLinked/  ->  lean/.lake/audit-linked-source/
                                      Basic.lean
```

The copied Main imports `BTBMS.AuditLinked.Basic`. Initially the linked source proves `auditLinkedProof : True` with `True.intro`; I generated a fresh status. I then changed only that actual `.lean` source to `by sorry` and ran the real `lake build` successfully. A fresh `#print axioms` shows `sorryAx`, but `lock.fingerprint()` is unchanged and `lock.verify()` remains intact. Reading the earlier status through the current tracker function still reports this leaf as **proved**, with no status problem.

This was confirmed through the actual Lake/status pipeline, not only a standalone hash test, and no compiled artifact or JSON was forged. The compiler freshly built both versions from the changed source. An outside-root symlink was rejected by Lean; the confirmed case uses the internal skipped-directory target above. Evidence: `scratch/codex/lock-followup-linked-pipeline-result.json` and the `lock-followup-linked-*` logs; the independent companion probe is under `lock-followup-symlink/`.

**Required fix:** fail closed on unsupported source-directory symlinks, or follow and hash their actual source targets with cycle handling. In either design, do not allow active Lean source to be hidden under an excluded build directory through a visible alias. Resolving the package root is not sufficient for links below it. This is the remaining source-coverage/freshness issue; normal resolved package paths and ordinary source files are now handled correctly.

### Remaining C — status serialization can fail before invalidating old success

The complete JSON array is still passed as one command-line argument (`lean-status.sh:16`) and parsed before any replacement record is written (`:19–23`). Controlled producer tests of the unmodified writer give:

| Producer outcome | Script exit | Previous success record |
|---|---:|---|
| Build exits nonzero | 1 | Replaced with `build_ok=false` |
| Extraction exits nonzero | 1 | Replaced with `build_ok=false` |
| Extraction exits zero with malformed JSON | 1 | **Preserved**, because JSON parsing fails before the write |
| Extraction exits zero with valid JSON for 2,000 declarations | 126 | **Preserved**, because launching Python fails with `Argument list too long` |

The last case is a practical library-size limit. These tests used controlled lock/producer stubs only to exercise the actual shell/Python writer; they do not claim a fake compiler passed the real proof gate. If proof sources changed since the old record, the ordinary fingerprint check still makes that record stale. Thus this test alone does not establish a false current proof, but it contradicts the promised failure invalidation and prevents reporting larger developments.

**Required fix:** establish an in-progress/failed record before generation, pass JSON by file/stdin rather than argv, validate/parse within failure handling, and atomically publish success only after the build, required audit and extraction have succeeded. Evidence: `scratch/codex/lock-followup-status-harness/results.json` and accompanying logs.

### Scope and disposition

The ordinary source-edit freshness test now gives **unknown (status not current)** as intended. Fresh transitive `sorry` detection remains correct. The remaining A/B cases explain why current progress can still say proved; they are not failures of `collectAxioms`.

As in the first review, a genuine compiler and its compiled artifacts remain trusted. Hashing toolchain `bin/` and `src/` is not a complete fingerprint of dynamic libraries/core `.olean` files under `lib/lean`; I treat this as a trust-boundary note, not another required anti-tampering project. Likewise the new exact export check and final whitelist are not being reopened by these findings.

**G-008 should remain open for the three focused repairs above.** No change to the approved mathematical propositions is required. All reviewed real source hashes remained unchanged, and only this follow-up and scratch evidence were written.

STATUS: COMPLETE

## Follow-up 2

Reviewed **27ec925b542e9572f98b1eb43d6d1048fa5261cd** independently, including real scratch-project builds/status runs and controlled writer tests. **A and C are fixed. B rejects the old symlink case but still omits a valid class of imported source paths. One required source-coverage repair remains.** The approved mathematical statements are unchanged; `blueprint/` remained unread.

| Item from the previous follow-up | Verdict | Evidence |
|---|---|---|
| A. Progress requires the target/lock audit | **Fixed** | Plain `True` exports, the old coercion exports and the shortcut axiom now make status generation fail. The tracker returns unknown, not proved. A broken statement lock also suppresses progress. |
| B. Active-source fingerprint coverage | **Partially fixed** | The original directory symlink is rejected. However, an ordinary, nonsymlink source file under `lean/BTBMS/.lake/` can be imported successfully and changed to `sorry` without changing the fingerprint. |
| C. Failure-safe status serialization | **Fixed for the reported failures** | Malformed JSON replaces old success with a failed record; valid output for 2,000 declarations succeeds without an argv-size error. Build, audit, extraction and fingerprint failures no longer preserve the older success. |

### A — actual pipeline replay

`scripts/lean_status.py:56–65` now runs the build, the exact exported-type/axiom audit, and extraction. `refresh.py:110–123` requires the successful state, both build/audit flags, the current fingerprint, and an intact lock.

In the full scratch copy:

- The unchanged admitted baseline passes the normal integrity check and status generation; its main claim remains **proved modulo sorry**. `--final` still correctly exits 1 on `sorryAx`.
- `mainTheorem : True` / `paperTheorem : True` now make `lean-status.sh` exit 1 with `lock/export audit failed`; the actual tracker function returns **unknown (status not current)**.
- The former coercion and shortcut-axiom implementations also make status generation exit 1.
- Changing a locked source leaves the collector able to record diagnostics, but `lock_ok=false` and the tracker reports **statement lock broken**, with no proved claim.
- The old visible-directory-symlink layout now fails before collection and reports an unsupported symlink.

Evidence: `scratch/codex/lock-fu2-replay-results.json` and its listed `lock-fu2-*.log` files. This closes the previous separation between a working type guard and a progress path that did not consume it.

### B — new source omission with no symlink

The remaining issue is `lock.py:60–61`: it prunes **every directory whose basename is `.lake` or `.git`**, not just an actual build/VCS root. Lean permits quoted module components, so this is a valid source/import pair:

```
lean/BTBMS/.lake/Hidden.lean
```

```lean
import BTBMS.«.lake».Hidden
```

This ordinary directory is inside the BTBMS source tree, **not** the project's actual cache `lean/.lake/`. There are no symlinks in the probe's Lean tree.

I tested the following sequence through the real Lake/status pipeline in scratch:

1. The copied Main imports the module, whose source initially proves `hiddenProof : True` with `True.intro`.
2. The new status script successfully builds, audits the correct main exports, extracts declarations, and publishes `state=ok`, `build_ok=true`, `audit_ok=true`. The leaf reports no axioms.
3. Only that actual source body is changed to `by sorry`.
4. A real `lake build` succeeds, and fresh `#print axioms BTBMS.hiddenProof` shows `sorryAx`.
5. Nevertheless, the source fingerprint is unchanged, the lock is intact, and the current tracker function accepts the saved report with:

   ```
   status_problem = None
   claims["audit-leaf"] = "proved"
   ```

This is not forged JSON or a modified compiled artifact: both versions are compiled normally from their respective `.lean` sources. It is not a bypass of the fresh final-theorem axiom audit; it is another concrete failure to detect that a reported declaration's active source acquired a hole.

**Required repair:** do not use directory basenames alone to exclude possible Lean sources. Hash valid active source paths, or reject unsupported imported layouts explicitly. A narrower exclusion of actual known cache/VCS roots, combined with ensuring no active source is supplied by excluded paths, is sufficient in principle; an import-closure inventory is another approach. Merely adding further symlink checks will not address this ordinary-directory case.

Reproducer, source, logs and successful pre-edit audit metadata are in `scratch/codex/lock-fu2-hidden-full/`; `result.json` records the unchanged fingerprint, live `sorryAx` and false current “proved” state. The source/import mechanism and the failure remain within the original requirement to fingerprint actual proof inputs.

### C — writer replay and failure behavior

The new writer publishes an in-progress marker first, captures extraction output directly rather than passing it through argv, and atomically replaces the record. Replaying the old controlled producer tests gives:

| Outcome | Exit | Published result |
|---|---:|---|
| Nonzero build, audit or extraction | 1 | Failed record; previous success replaced |
| Malformed JSON | 1 | Failed record; previous success replaced |
| Valid 2,000-declaration JSON | 0 | Successful 259,146-byte record; no argument-length failure |
| Fingerprint error or change during generation | 1 | Failed record; previous success replaced |

These writer tests use controlled producers to exercise serialization, not a fake compiler claiming to pass the real proof guard. Evidence: `scratch/codex/lock-fu2-writer-harness/results.json`.

Further artificial schema tests found only nonblocking defensive-validation issues: a nonobject row can leave the initial running marker, which the tracker treats as unknown; a nested non-string axiom item can cause a reader error. The actual typed `Status.lean` producer does not emit those schemas. Neither reproduced the previous unsafe preservation of success, so I am not treating these as additional required proof-acceptance repairs.

### Disposition

**Keep G-008 open only for the active-source coverage issue in B.** A and C, and the earlier exact-type, axiom-whitelist and opaque-hole fixes, passed the relevant rechecks. No change to `MainTheorem` or `PaperTheorem` is required, and no new compiler/cache trust requirement is introduced by this remaining source-file case.

All mutations and outputs were confined to scratch copies and this appended review. The real reviewed source hashes remained unchanged, and `blueprint/` was not read.

STATUS: COMPLETE

## Follow-up 3

Reviewed **2e90d99de03bb74ea7f32dbc9ce438be5be02175**. The exact previous nested-directory case is fixed, and both defensive JSON validation changes pass. **B is still incomplete for supported imports that traverse into the actual excluded root cache.** No new required writer change was found, and the mathematical statement remains unchanged.

| Item | Verdict | Evidence |
|---|---|---|
| Previous `BTBMS/.lake/Hidden.lean` case | **Fixed** | Its source edit now changes the fingerprint; the actual tracker reports unknown/stale instead of proved. |
| Complete active-source coverage (B) | **Partially fixed** | Valid quoted parent-traversal imports reach `lean/.lake/Hidden.lean`, which remains excluded. A fresh build detects its new `sorryAx`, but the saved status still appears current and proved. |
| Nonobject declaration row validation | **Fixed** | The controlled case now exits 1, publishes a failed record and yields unknown progress. |
| Non-string axiom-item validation | **Fixed** | The controlled case now exits 1 with a failed record, rather than accepting data that crashes the reader. |

### What the patch fixes

The root test at `lock.py:64–65` correctly distinguishes a nested directory named `.lake` from the hashed root's own cache. I replayed the full old case using the current build/status pipeline: after `lean/BTBMS/.lake/Hidden.lean` changes from `True.intro` to `by sorry`, the fingerprint changes and the recorded leaf becomes **unknown (status not current)**. The normal integrity check still passes the admitted baseline; `--final` correctly rejects its `sorryAx`.

The writer's explicit object and axiom-string checks (`lean_status.py:71–77`) fix both reported defensive cases. All 13 controlled writer regressions pass, including failed build/audit/extraction, malformed JSON, fingerprint changes and successful 2,000-declaration output. Evidence: `scratch/codex/lock-fu3-old-case-result.json` and `lock-fu3-writer-harness/results.json`.

### Remaining B: a supported traversal import

Lean 4.33.1 and Lake accept both of these import names:

```lean
import BTBMS.«..».«.lake».Hidden
import BTBMS.«../.lake».Hidden
```

They retain the known `BTBMS` module prefix but resolve their source to the actual root cache path **`lean/.lake/Hidden.lean`**, not the now-hashed nested `lean/BTBMS/.lake/` path. A direct `import «.lake».Hidden` is rejected as an unknown module prefix; the prefix-plus-traversal variants are accepted. This behavior was verified with actual Lake builds, not assumed from filesystem normalization.

The full current-project reproduction uses the first import and an ordinary, nonsymlink source file:

```lean
namespace BTBMS
theorem traversalProof : True := True.intro
end BTBMS
```

The current status script successfully builds, audits the main exports, extracts declarations and publishes a current successful record. Then only this source body is changed to `by sorry` and the project is rebuilt normally. Fresh `#print axioms BTBMS.traversalProof` shows `sorryAx`, but:

```
fingerprint unchanged
lock_ok = True
status_problem = None
claims["audit-leaf"] = "proved"
```

There are no symlinks or forged `.olean`/JSON files. Both proof artifacts were produced by the real compiler from the corresponding source. This remains a source-current progress failure, not a bypass of a fresh final-theorem axiom audit or a demand to distrust the compiler.

Evidence: `scratch/codex/lock-fu3-path-probes/results.json` records both accepted import variants; `lock-fu3-traversal-full/` contains the full current-pipeline driver, source, logs and `result.json`, including the successful pre-edit audit metadata.

### Required repair and disposition

**B needs active-source coverage enforcement, not another directory-name exception.** Either:

- resolve imported source paths and require every active `.lean` input to be fingerprinted, including one under an otherwise excluded cache; or
- reject unsupported path-manipulating import layouts before accepting status, handling normalized traversal and separators inside quoted module components generally—not just the two demonstrated spellings.

The project need not support these import names. Explicit rejection is sufficient. A source inventory that hashes all actual Lean inputs, rather than excluding them because they reside in a cache-named directory, is also valid; compiled `.olean` artifacts can remain outside that inventory.

**G-008 should remain open only for this source-coverage item.** A/C and the earlier stored-type, axiom and opaque-hole repairs remain accepted. No change to `MainTheorem`, `PaperTheorem`, or the JSON writer is required by this follow-up.

All mutations and generated evidence were confined to scratch copies. The real reviewed sources remained unchanged, and `blueprint/` was not read.

STATUS: COMPLETE

## Follow-up 4

Reviewed **3d727dc3db9fa2e2dd59f698c2dfcf46b19bd5a8** independently. **Verdict: fixed. No remaining required T-019 change was found within the approved package/source layout and the previously stated trusted-compiler/compiled-artifact boundary. I recommend closing G-008.** This supersedes the remaining-B dispositions above; it does not assert that the admitted mathematical theorem has been proved.

### Why the restriction closes the reported path cases

`LockCheck.lean:28–32` validates the actual parsed `Lean.Name` components. Every string component must be nonempty, must not start with a digit, and may contain only alphanumeric characters, underscore or apostrophe; numeric Name components are rejected. The installed `Char.isAlphanum` uses ASCII letter/digit ranges. Hence accepted components contain no dot, slash, backslash, colon, whitespace or other path-manipulating character. They cannot represent `..`, `.lake`, `.git`, an absolute path, or a separator-containing traversal such as `../.lake`.

Lean's `modToFilePath` joins those components to the module's source base (`Lean/Util/Path.lean:45–51`). With the approved package configurations' ordinary source roots, the accepted components stay on the standard paths covered by the source walk. Existing symlink rejection prevents ordinary visible names from aliasing an excluded source. The conservative restriction may reject otherwise legal Unicode/punctuation module names; rejecting unsupported layouts is an acceptable repair and does not restrict Unicode declarations or the mathematics inside files.

Crucially, `LockCheck.lean:40–42` checks **all modules in the import closure**, before the later BTBMS-only axiom-declaration scan. A normally named intermediate module cannot conceal a bad transitive import. The status generator already requires this audit to pass before publishing an acceptable record. Because the audited checker is itself included in the fingerprint, old reports made under the permissive checker do not remain current after this change.

### Full-pipeline replays

I used unchanged source copies in `scratch/codex/lock-fu4-work/` and the real Lean/Lake/status pipeline:

| Case | Result |
|---|---|
| Baseline integrity check and status collection | Pass; main theorem correctly remains proved modulo sorry |
| Baseline `check.sh --final` | Exit 1, correctly rejects the existing `sorryAx` |
| `BTBMS.«..».«.lake».PartProbe` | Audit/status exit 1; unsupported module name; progress unknown |
| `BTBMS.«../.lake».SlashProbe` | Audit/status exit 1; unsupported module name; progress unknown |
| `BTBMS.«.lake».NestedProbe` | Audit/status exit 1; deliberately unsupported name; progress unknown |
| Normal `BTBMS.AuditBridge` importing the traversal module | Audit/status exit 1; transitive bad import is caught |
| Normal `BTBMS.AuditPlain.Module_2` with a proved helper | Pass; the helper is reported proved |
| Editing that ordinary helper to `by sorry` after collection | Fingerprint mismatch; saved progress becomes unknown/stale |

The negative runs were checked for the actual `unsupported module name` audit error, not merely an unrelated build failure. Evidence: `scratch/codex/lock-fu4-replay-results.json`, `lock-fu4-replay.py`, and the corresponding logs.

An additional **26-case kernel-checked policy matrix** passed using the exact copied predicate. It covers both traversal spellings, separators, absolute paths, empty/dotted/numeric/digit-start components and ordinary underscore/apostrophe identifiers. The cases and proof log are in `scratch/codex/lock-fu4-policy-cases.json`, `lock-fu4-policy-probe.lean` and `lock-fu4-policy-probe.log`.

### Disposition

The stored-type, axiom-policy, status-audit integration, failure-safe writer, opaque-hole handling and now the supported-source-path restriction address the required changes recorded in this review. **No additional repair is required before using the tooling for the agreed workflow.** Final mathematical proof acceptance still requires the genuine `--final` audit to pass; it currently fails as expected because the main proof is intentionally admitted.

All real reviewed sources remained unchanged. Only this appended review and scratch evidence were written, and `blueprint/` remained unread.

STATUS: COMPLETE
