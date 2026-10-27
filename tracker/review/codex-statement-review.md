# Codex statement-fidelity review — T-014

**Gate recommendation: hold G2 until the raw-operation mismatch below is repaired and its regression cases pass.** The well-order theorem type, the strong Mahlo corollary, the order, and the intended standard domain appear faithful. However, `expand` does **not** satisfy the agreed D-3 contract on all natural-labelled raw forests: it sometimes returns `none` when the reference returns a forest. This is a concrete implementation discrepancy, not a counterexample to the paper's well-order statement or a demonstrated difference on Std.

I checked the definitions against the paper and pinned `BTBM.ts`, rather than accepting the Lean comments. No file in `lean/` or `checks/` was edited. Source citations below abbreviate `lean/BTBMS/{Syntax,Expansion,Mahlo,Statement,Sanity}.lean`; `paper.txt` means `paper/paper.txt`. The reviewed source hashes are in `scratch/codex/statement-source-sha256.json`.

## Verdicts

| Question | Verdict | Main reason |
|---|---|---|
| 1. Order | faithful | The actual recursive comparator is parent, then height, then remaining entries/columns, with proper prefix smaller. Relative normalization uses a single fixed host. |
| 2. Operation | not-faithful | Agreement holds on the intended nonempty V∧I/paper domain, but root search misses a further raw child forest. Correcting the fuel alone also exposes signed-offset arithmetic that the current Nat subtraction cannot express. |
| 3. Std | faithful-with-note | The inductive predicate is exactly finite successful reachability from all seeds. The empty self-loop adds no expression. The raw discrepancy is outside V,I; standard-domain equality relies on the independent finite closure/agreement argument, still to be formalized. |
| 4. Mahlo hypothesis | faithful | `IsMahlo` is the paper's strong finite hierarchy; `StationaryIn` uses the full ordinary club/stationary notion on ordinals below the initial ordinal of κ. The weak implication is correct. |
| 5. The theorem and universes | faithful-with-note | `IsWellOrder` asserts well-foundedness and strict total comparability of the actual Std order. Universe polymorphism is the normal ambient-universe conditional form of the approved host theorem, not an object-ZFC derivation. The strength/unprovability docstring overclaims what is established. |
| 6. Ways to prove the wrong thing | faithful-with-note | No smaller finite/test-only Std, wrong order, impossible-by-type premise, or vacuous stationarity was found. The explicit `sorry` remains the known proof placeholder; successful builds do not validate the theorem. The raw D-3 bug still needs correction before locking the definitions. |

## 1. Order

`Syntax.lean:15–16` has one inductive constructor with columns of entries `(label, subtree)`. With `Forest := Tree Nat` at line 69, this represents precisely the finite forest/column/entry syntax of `paper.txt:59`, §1.1. There is no quotient, admissibility filter, depth bound, or coinductive constructor. In particular `.node []` is the empty forest, while `.node [[]]` has one empty column.

The relevant implementation is `Syntax.lean:33–49`:

- `cmpCols` treats `[]` as less than every nonempty column list, compares the first columns, and uses the remaining list only on equality.
- `cmpCol` treats an empty column as a proper prefix, compares parents first, recursively compares heights second, and only then compares the remaining entries.
- `Ordering.then` in the installed Lean source (`Init/Data/Ord/Basic.lean:94–97`) returns the later comparison only if the earlier result is `.eq`. `Ord Nat` uses natural comparison (`:480–481`). Thus the nesting of `.then` has the claimed precedence.
- The LT instance at `Syntax.lean:75` is literally `Tree.cmp compare a b = .lt`. It does not use size order, generation order, or an expansion-step relation.

This is exactly `paper.txt:62`, §1.1 and `BTBM.ts:445–455` (`value`, then `height`, then lexicographic lists). The termination of the comparator is structural recursion on finite data; it supplies no illicit well-foundedness assumption about the order being compared.

`Tree.map` at `Syntax.lean:54–63` uses the same function in every subtree. Consequently `relKey a H` at 85–86 uses the **same a at every depth**, as required at `paper.txt:75–85`, §1.1 and `BTBM.ts:40–67`. Its subtraction occurs only in the branch p≥a. `keyLabelCmp` compares Bool and then Nat; the actual Bool comparator has false<true (`Init/Data/Ord/Basic.lean:486–490`). Recursive key comparison therefore has the reference's mark/value/height ordering (`BTBM.ts:91–99`).

Concrete checks include `∅ < seed 0`, `seed 1 < seed 2`, and `keyLabelCmp (false,100) (true,0)=.lt`; all were checked using the definitions. The supplied test also passed 200,000 comparison pairs and 13 seeds, although that finite sample is not the justification for the clause-by-clause conclusion.

As with the paper, the mathematical domain is finite natural-labelled syntax. JavaScript machine-number/array/resource limits and the special `Infinity` sentinel are not additional members of `Forest`. The discrepancy in question 2 uses tiny integers and does not depend on any such machine-limit interpretation.

## 2. Operation

### Concrete failure of the raw reference contract

`Expansion.lean:71–81` claims that root search can succeed only within the first `tl+1` forests and uses exactly that many attempts. The claim is false for a raw expression whose stopping entry has a **nonempty height ending in an empty column**.

The reference's `tail_layer` stops before such a height because it has no last entry (`BTBM.ts:105–125`). But `root_layer` can enter that height and find one of its columns before a subsequent call to `next_layer` would throw (`BTBM.ts:143–154`). Thus root search may succeed at depth `tl+1`, requiring `tl+2` attempts. This is separate from whether the parent satisfies V.

Use zero-based `(parent,height)` entry notation and `∅=[]`:

| Input | n | Actual reference `FS` output | Actual Lean `expand` |
|---|---:|---|---|
| `E₀=[[],[(2,[[]])]]` | 0 | `some [[]]` when translated to Option notation | `none` |
| `E₁=[[],[(2,[[(3,∅)],[]])]]` | 1 | `some [[],[(3,∅)],[]]` | `none` |
| `E₂=[[],[(2,[[(3,[[(2,∅)]])],[]])]]` | 1 | `some [[],[(3,[[(1,∅)]])],[]]` | `none` |

For E₀, the outer stopping number is t=1 and `tailLayer=0`. Root r=2 is found by the reference in the attached one-empty-column forest at depth 1. The scan is performed, the n=0 loop is skipped, and the entire outer stopping column is deleted. Lean checks only the outer forest of length 2 and returns `none` before reaching the successful root. The reference performs root search **before** its parameter loop (`BTBM.ts:247`, 258); n=0 does not bypass lookup.

E₁ shows this is not just a zero-parameter issue: its root is the first column of a two-column child forest, so the reference's earlier-root branch succeeds. E₂ additionally shows why changing the fuel alone is insufficient. There t=1, r=2, so the reference uses d=−1 and changes the retained root entry's height parent 2 to 1. At `Expansion.lean:183`, `let d := t-r` is Nat subtraction, giving 0. With only the lookup repaired, that height would incorrectly remain parent 2.

The smallest variant is `E=[[(1,[[]])]]`, n=0: reference output is ∅, while Lean returns `none`. All these cases violate V and I; none is asserted standard. They refute the universal raw contract in `Expansion.lean:6–11,71–73,164–165`, not the main well-order theorem.

The actual TypeScript outputs and JSONL cases are saved in `scratch/codex/statement-expansion-cases.json` and `.jsonl`. Four separate scratch Lean counterexample theorems confirm the relevant `expand` results are `none`; their axiom lists contain no `sorryAx` or native-computation axiom. Running the newly built differential executable on the eight return-only regression cases gives `cases=8 mismatches=8`.

An additional deterministic raw test, **without V filtering**, tested 3,000 forests at n=0,1,2,3. The reference returned 7,513 times and threw 4,487 times; Lean had **80 mismatches**, exactly the 80 successful reference returns in the extra-layer situation. All returned reference expressions in that sample remained natural-labelled. This is further bounded evidence for the identified bug, not an exhaustive equivalence proof.

### Why the supplied differential test passes

`checks/lean/gen-random.mjs` selects every parent from `here`, the visible preceding columns (lines 17–22). It therefore enforces V, even though it permits I violations. Standard generation also stays in V. Neither generator can produce r>t pointing into the extra child forest. The comment that the random test covers “every case where the reference throws” must be read as its sampled V-domain cases; it does not establish the universal raw exception contract.

The supplied test passed 100,000 standard operation cases, 200,000 random V operation cases (including 597 reference throws), and 200,013 order/key/seed cases. Those results are compatible with the bug. The order generator's neighboring pool index does not in general guarantee a long common syntax prefix, despite its comment; this is a coverage caveat rather than a definition error.

### Clause-by-clause check on the paper's intended domain

On nonempty V∧I inputs, or more generally the paper-defined route with visible r<t, I found no operation discrepancy. The relevant reasoning is:

| Lean implementation | Checked correspondence |
|---|---|
| `lastEntry?`, `nextLayer`, `skipLayers`, `leftCount`, lines 27–44 | Same last-column/last-entry route and sum of prior forest lengths. Defaults on unavailable helpers are not used along the computed legal route. |
| `tailLayer`, lines 49–60 | −1 for an empty forest/last column; otherwise 1 plus the last entry's height depth. This matches the reference. Under I, the stopped height is actually empty, as in paper §1.2. |
| `tailNum`, `rootAt`, lines 64–69 | The computed stopping forest has a last entry, so `getD 0` does not fabricate its root. The sum-minus-one column formula is correct. |
| `rootLayerAux`, lines 74–81 | For visible r<t, lookup succeeds in the first `tl+1` forests. After a failed comparison, the next `left` is ≤r, so `r-left` is exact. This justification does not cover the extra raw child described above. |
| `shiftVal`, `mapLast`, `replaceAt`, lines 86–105 | Every parent ≥r is shifted at every depth; only the last-column/last-entry route receives replacement; Z itself is not shifted. Each replacement column exists on legal operation calls. |
| `ascendReplace`, lines 109–112 | Missing or negative depth means no replacement, just shifting. This agrees with a reference depth counter that never reaches zero. Shift amounts are nonnegative on r<t inputs. |
| `isSpecial`, lines 118–122 | Exactly positive depth, singleton stopping column, empty height and direct-owner parent. At positive computed depth `leftCount>0`, so owner subtraction is exact. |
| `expandSpecial`, lines 126–137 | Retains strict containers, shortens C by its last column, and inserts n+1 shortened entries for empty P or n for nonempty P. The n=0 cases agree. Its arbitrary tl=0 helper fallback is not invoked by `expand`'s special branch. |
| `scanCount`, `rootAppendingStart`, lines 144–157 | lt advances source only, eq advances both, gt advances query only; returned count selects the actual source suffix. Source keys use r and query keys use t. |
| `iterDown`, lines 160–162 | Evaluates stages n,n−1,…,1 with the preceding accumulator Z, not stages in ascending order. |
| Dispatch, lines 166–178 | Empty self-loop and outer-empty-column deletion match the chosen reference extension; special dispatch precedes root lookup. The raw root lookup failure is the defect above. |
| Ordinary earlier root, lines 179–192 | Found indices are valid; query uses phase j−1; restored outer parents remain unchanged; restored heights use phase j; body has the correct continuation depth and inserted Z. |
| Ordinary owner root, lines 193–200 | Rejects an exhausted root only for n>0, matching the reference's in-loop throw. Only the final restored height contains the continuation hole. Zero deletes the entire stopping column, including Q. |

These correspond to `paper.txt:86–133`, §1.1–§1.2 and `BTBM.ts:157–288`. On this domain `rl≤tl` and r<t, so the Nat differences used for depths and d do not silently truncate a negative mathematical value.

A separate helper-specification boundary needs clarification: `replaceAt r d Z 0 .empty = .empty` (`Expansion.lean:97–100`) agrees with the reference's empty-loop behavior. The paper's displayed formula `A(F)=T(F[:-1])⌢Z`, read without a present-column hypothesis, gives Z for F=∅ (`paper.txt:90`, §1.1). No legal expansion replacement uses an absent column, so this does not affect the standard operation. The helper's paper-equivalence contract should require an existing replacement route/column rather than claiming that unrestricted equation.

## 3. Seeds and Std

`branch i 0` is one entry `(i,∅)` and `branch i (k+1)` adds one containing entry before the branch starting at i+1 (`Expansion.lean:205–207`). Consequently `seed 0=.node [[]]`, while `seed (m+1)=.node [[],branch 0 m]` has exactly m+1 singleton entries with parents 0,…,m. This agrees with every L_m in `paper.txt:139–140`, §1.3 and `BTBM.ts:31–38`.

The actual elaborated constructors of `IsStd` are exactly:

```lean
BTBMS.IsStd.seed : ∀ (m : Nat), IsStd (seed m)
BTBMS.IsStd.expand : ∀ {e e' : Forest} (n : Nat),
  IsStd e → expand e n = some e' → IsStd e'
```

These are `Expansion.lean:216–218`; there is no additional constructor for arbitrary forests, admissible forests, downward closure, test-generated states or an infinite limit. All natural seed indices and parameters are admitted without a fixed bound. Induction on an IsStd proof yields a seed and a finite parameter list of successful expansions; conversely induction on that list constructs IsStd. Equality with `some e'` cannot add an output for `none`.

The empty forest is already reached from seed 0 by deletion; I checked this using the actual definitions in scratch. A self-loop at ∅ adds no new forest and can be erased from any generation witness. `Std` is the subtype `{e : Forest // IsStd e}` (`Statement.lean:22`); proof irrelevance ensures different generation proofs do not create differently ordered copies of the same expression.

The raw mismatch does not by itself show that this Std is too small. The paper's finite closure theorem (`paper.txt:301–303`, §3.2) makes paper standards V,I. Using the legal-domain code agreement, finite generation induction identifies the Lean and paper standard sets in both directions, treating the empty self-loop separately. This uses the finite closure theorem, **not** the desired well-order or Mahlo hypothesis. No standard counterexample was found. The formal proof of this agreement/closure remains a future obligation; it is not already provided by the test sample or the bare constructors.

## 4. Mahlo hypothesis and stationarity

### The hierarchy

`Mahlo.lean:40–43` is exactly the paper's recurrence (`paper.txt:971–975`, §6.2):

- At zero, κ is strongly inaccessible.
- At n+1, κ is again strongly inaccessible, and the initial ordinals of n-Mahlo cardinals below κ are stationary in κ.

I inspected Mathlib's actual `Cardinal.IsInaccessible` (`SetTheory/Cardinal/Regular.lean:371–377`) and its equivalence theorem `isInaccessible_def` at 397–399. It means uncountable, regular and strong limit. The field named `isStrongPrelimit` does not weaken this: the other fields provide positivity and the library proves strong-limitness at 391–392.

For `x : Set.Iio κ.ord`, the successor's membership condition is

```
∃ μ : Cardinal.{u}, IsMahlo n μ ∧ μ.ord = x.1,
where x.1 < κ.ord.
```

`Cardinal.ord_lt_ord` and `ord_injective` in Mathlib's `SetTheory/Ordinal/Basic.lean:1128–1136` show this selects **exactly** the previous Mahlo cardinals μ<κ. It neither includes κ itself nor replaces a cardinal by every ordinal of the same cardinality. The equality to an initial ordinal is important and is present.

`IsWeaklyMahlo` at lines 33–36 uses uncountable regular cardinals as its base and the same stationary recurrence. That is the accepted D-2 strengthening, not a claim that the two hierarchies are definitionally equal. `IsMahlo.isWeaklyMahlo` at 45–48 correctly inducts on n: an inaccessible is uncountable regular, and predecessor strong-Mahlo witnesses are predecessor weak-Mahlo witnesses; stationarity is preserved by set inclusion via the proved `StationaryIn.mono`. There is no substitution of unboundedness for stationarity. The implication's axiom print has only standard Lean axioms and no `sorryAx`.

### StationaryIn on the interval type

`Mahlo.lean:24–25` applies Mathlib `IsStationary` to the actual ordered subtype of ordinals below κ.ord. In the pinned Mathlib source:

- `IsCofinal C` means `∀x, ∃y∈C, x≤y` (`Order/Bounds/Defs.lean:62–63`).
- `DirSupClosed C` requires closure under least upper bounds of nonempty directed subsets, whenever their LUB lies in the ambient type (`Order/DirSupClosed.lean:49–50`).
- `IsClub` is exactly these two properties (`Cardinal/Cofinality/Club.lean:36–42`).
- `IsStationary S` requires `(S∩C).Nonempty` for **every** such club C (`:178–179`).

On a linear order every nonempty subset is directed. Thus closure here is the usual closure under suprema that remain **below κ**. It does not require κ itself to belong to the club: κ is not in `Iio κ.ord`. It does not force 0 into every club: the empty supremum is excluded. At either Mahlo base κ is uncountable regular, hence κ.ord is limit and the interval has no maximum; cofinality is therefore the usual unboundedness below κ. This is the standard notion used in the paper.

There is no vacuous “there are no clubs” interpretation. The whole interval is always club. At κ=0 the ambient interval is empty and its empty subset is club, so no set is stationary there; both Mahlo bases exclude that endpoint anyway. The empty stationary set is false at every κ, and the whole interval is stationary when nonempty.

Although `Ordinal.{u}` lives in `Type (u+1)`, its initial segment is small: the actual theorem `Ordinal.small_Iio` gives `Small.{u} (Set.Iio o)` (`Ordinal/Basic.lean:546–547`). The subtype contains every ordinal below κ.ord, and the `Set` quantifier in IsStationary ranges over its full subsets, not a restricted class of definable/coded clubs. Its larger presentation universe does not create an omitted-set loophole.

I additionally compiled probes, importing the freshly rebuilt Mahlo definitions without using the admitted main theorem:

1. `∃ κ : Cardinal.{u}, IsWeaklyMahlo 0 κ`, witnessed by ℵ₁.
2. `¬ IsWeaklyMahlo 1 (ℵ₁ : Cardinal.{u})`: a predecessor witness would have to be an uncountable cardinal strictly below ℵ₁.
3. `¬ StationaryIn κ ∅` for every κ.
4. `StationaryIn κ Set.univ` for uncountable κ.
5. `¬ StationaryIn κ {0}` for uncountable κ, using the explicit club `{x : Iio κ.ord | 0<x.1}`.

The last two negative tests rule out accidental identification of stationarity with mere nonemptiness or of level one with level zero. They are not a consistency proof for the full finite-Mahlo premise.

## 5. The theorem and universe parameters

`Std.lt a b := a.1 < b.1` (`Statement.lean:25`) is the literal restriction of the forest syntax order. Mathlib's definition is:

```
IsWellOrder α r extends IsWellFounded α r, Std.Trichotomous r
```

This is `Order/RelClasses.lean:271–272`. Its fields provide `WellFounded r` and comparability of distinct elements. Irreflexivity/asymmetry follow from well-foundedness; transitivity and strict total order are derived at 274–283. Thus `IsWellOrder Std Std.lt` says that the entire standard syntax order is a strict well-order, not merely that selected expansion trajectories terminate or that one initial segment is well-ordered.

The strong corollary (`Statement.lean:34–36`) has the actual premise

```lean
∀ n : Nat, ∃ κ : Cardinal.{u}, IsMahlo n κ
```

and uses the proved implication to invoke the weak theorem at the **same universe u**. The uniform Nat quantifier is present. Subject to the accepted host-Lean choice D-1, this is the intended paper-form conditional theorem (`paper.txt:1478`, §9); D-2 is visible in the separate stronger theorem rather than silently replacing the paper's hypothesis.

A universe-polymorphic declaration is a family of conditional theorems at a chosen ambient universe. It does not require the premise simultaneously in every universe. Its cardinals/ordinals are those small enough for that universe; the premise explicitly asks for the relevant witnesses there. Std stays `Type 0`, appropriate for finite natural-labelled syntax, and changing the semantic universe neither truncates Std nor changes its order.

This is not literally a syntactic derivation in object ZFC, nor a certification that an eventual Lean proof uses exactly ZFC+Mahlo and no stronger ambient type-theoretic resources. That consequence was already accepted with D-1. Universe-local cardinal hypotheses are a faithful host formulation, but a claim about exact object-theory or consistency strength would require additional work and is not encoded in this theorem type.

### What Lean's universes can discharge

The docstring at `Statement.lean:12–14` should not be accepted as a proved unprovability/strength theorem. Concrete parts of the premise are available:

- Weak level zero exists at every u: ℵ₁ is uncountable regular.
- Mathlib proves `Cardinal.IsInaccessible.univ`. Its exact type matters:

```lean
Cardinal.univ.{u, v} : Cardinal.{max (u + 1) v}
```

  It is a cardinal of a **larger** universe, not a witness in the same lower `Cardinal.{u}`. The scratch probe proves `∃ κ : Cardinal.{u+1}, IsMahlo 0 κ` using `Cardinal.univ.{u,u+1}`.
- Finite universe lifts can provide inaccessible witnesses at higher types, but do not themselves provide the positive-Mahlo **stationarity** clauses. A term-level variable n cannot be used as a varying universe index inside the uniform Nat quantifier. No same-universe `univ` instantiation or inspected library theorem supplies the full premise automatically.

So “universes discharge none of the premise” would be wrong, while “the full finite-Mahlo premise is an explicit assumption” is correct. Replace the broad absolute claim about Lean's unprovability/rough strength by these precise type-level facts, or mark any stronger metatheoretical assertion as requiring a separate justification.

## 6. Potential ways to prove a different or vacuous theorem

I specifically checked the following possible failures:

- **A too-small domain:** no fixed bound on seeds, parameters, depth or expression size occurs in IsStd. It does not refer to the finite-check output files. `none` only blocks an unsuccessful operation; it does not identify an expression with ∅.
- **An easier relation:** Std.lt is the syntax relation, not subterm order, size order or expansion reachability. Raw Forest lexicographic order itself admits descending chains (for example, increasingly many empty outer columns before `[(0,∅)]`); the intended restriction to Std matters and has not been replaced by a generic structural-well-foundedness instance.
- **A fake stationary predicate:** the full club quantifier, nonempty intersections, strict below-κ interval, strong base and nontrivial weak levels are present and pass the checks above.
- **Universe or proof-field tricks:** the universe parameter does not omit any finite syntactic expressions, and subtype proof irrelevance does not add duplicate ordered elements. The premise is not false merely because of a universe-type mismatch.
- **A circular instance or finished theorem masquerading as an assumption:** no instance grants the target well-order before the theorem. There is, however, the intentional `sorry` at `Statement.lean:31`. Both `std_isWellOrder` and its strong corollary currently print axioms `[propext, sorryAx, Classical.choice, Quot.sound]`. The build is therefore a statement/type check, not a mathematical proof. Later proof acceptance must remove this dependency throughout the final theorem's closure.

I found no mechanism that turns a genuine proof of the audited **standard-domain** conclusion into a proof about a different finite subset or a trivial hypothesis. The raw API discrepancy still matters to the agreed definition contract and must not be hidden by these otherwise favorable conclusions.

## Required changes before the definition lock

1. **Repair the missing raw root case in `Expansion.lean`.** Allow root lookup to inspect the no-last-entry child forest at depth tl+1. Do not fix only the fuel: handle the corresponding negative integer offset t−r. A small extra-layer branch can keep the public Nat-labelled Forest type: if its root is the final (empty) column, n>0 throws and n=0 deletes; if it is an earlier column, the negative continuation depth prevents inserting previous Z, so every positive-n output is the j=1 result. Its shifted fields p≥r become `p−(r−t)`, which are nonnegative. Alternatively use a justified signed intermediate implementation. Preserve lookup failure before the n=0 loop; blindly short-circuiting all n=0 inputs would introduce another raw mismatch.
2. **Add deterministic raw non-V regression cases to the Lean differential coverage.** Include E₀ at n=0 and n=1, E₁ at n=1,2, and E₂ at n=1,2, plus `E₃=[[],[(4,[[(3,∅)],[]])]]` at n=0, whose root lies beyond even the extra child forest and must still throw. This last negative case was separately executed and agrees with Lean `none`. Keep the V-only random corpus if useful, but do not describe it as coverage of every raw error/return case. The supplied scratch JSONL provides the successful-return counterexamples.
3. **Correct the associated documentation claims.** Remove the false `tl+1` maximum-success explanation and describe failure of the actual root lookup rather than equating it with a root being non-visible; qualify `replaceAt`'s equation with the paper's A by existence of its replacement column/route; replace or qualify the unsupported universe/unprovability claim at `Statement.lean:12–14`. These corrections require no change to the order, seeds, Mahlo predicates, implication, or well-order theorem type.

The finite-witness characterization of IsStd, standard closure/definedness, and the paper/reference agreement theorem should be explicit later proof obligations. They need not be replaced by more bounded tests, and this review does not demand completing the entire mathematical proof before approving a corrected statement.

## Build and experimental evidence

To obey the write restriction, I copied the unchanged project sources and test scripts into `scratch/codex/statement-work/project/`, copied the pinned dependency workspace into `scratch/codex/statement-work/.deps/`, and used the installed 4.33.1 compiler. The original and copied reviewed source SHA-256s agree. Build artifacts, generated JSONL and logs are all under `scratch/codex/`; no original Lean/checks source was changed.

- The requested `PATH=... lake build`, run inside the copied `lean/`, exited 0: **959 jobs**, with only the expected main-statement `sorry` warning. Log: `scratch/codex/statement-build.log`.
- The byte-identical copied `checks/lean/run.sh` exited 0: **100,000 standard**, **200,000 random V**, and **200,013 order/key/seed** cases, all zero mismatches. Log: `scratch/codex/statement-differential.log`.
- The same freshly built executable on the directed return-only regression corpus exited 1: **8 cases, 8 mismatches**. Log: `scratch/codex/statement-counterexample-difftest.log`.
- The independent raw-natural corpus exited 1: **12,000 cases, 80 mismatches**, all predicted by the extra-layer root case. Generator/counts/log: `scratch/codex/statement-raw-fuzz.mjs`, `statement-raw-fuzz-counts.json`, `statement-raw-fuzz-lean.log`.
- Kernel-checked raw counterexample proofs have no `sorryAx`; logs and sources are under `scratch/codex/statement-expansion-lean/`. The freshly rebuilt main theorem/Std probes and Mahlo/nonvacuity probes exited 0; logs: `scratch/codex/statement-probes.log`, `statement-mahlo-rebuilt.log`.

Passing finite tests is not proof of statement fidelity. Here the decisive evidence for the required operation change is a source-level omitted branch with explicit, independently executed counterexamples; the favorable verdicts are supported by the definition-by-definition arguments above.

STATUS: COMPLETE

## Follow-up

Reviewed commit **82c3f010a5681c87fef816a9d1753e31367a01bb** independently against the pinned reference. **The previous G2 hold is resolved: I recommend proceeding to the statement-lock decision. No remaining required change was found.** This section supersedes the original operation verdict and hold recommendation above; the earlier text records the pre-fix definitions.

| Follow-up question | Verdict | Evidence |
|---|---|---|
| 1. Exact extra-layer behavior | faithful | The complete lookup bound, empty-query reduction, zero-parameter case, owner-root throw and j=1-only result all match the reference, as derived below. |
| 2. Original independent raw corpus | pass | Regenerated byte-identically; the new executable passes all 12,000 cases, including the 80 that failed before the fix. |
| 3. Remaining required changes before lock | none | The operation defect and associated documentation/coverage requirements are addressed. The intentional `sorry` remains a later proof obligation, not an unresolved statement-definition repair. |

### Extra-layer branch: source-level verification

Let ℓ be the computed stopping depth, let F₀,…,Fℓ be its route forests, and let H be the stopping entry's height. By the actual `tail_layer` definition (`BTBM.ts:105–125`), H has no last entry: it is empty, or its last column is empty. Its starting column number is t+1.

1. **The lookup bound is now complete.** The reference checks F₀,…,Fℓ and then H. If r is not found there, its next `next_layer` call throws. Thus `rootLayerAux` with fuel ℓ+2 (`Expansion.lean:80–87`) checks exactly every forest in which lookup can succeed. Every failed comparison preserves `left≤r`, so the returned natural subtraction `r-left` is exact. The totalized `nextLayer` used after failure in H cannot invent a successful lookup: the next fuel is zero. If the new dispatch `tl<rl` is taken (`:208`), then necessarily

   ```
   rl = ℓ+1,    eRoot = H,    r = t+1+ri > t,
   ```

   and H is nonempty with an empty final column. The old `rl≤ℓ` branch is unaffected.

2. **The reference query in this case is genuinely empty.** In `BTBM.ts:249–252`, `skip_layers(H,ℓ-rl)=skip_layers(H,-1)=H`: a negative loop bound executes no iteration. Its `col_tail` is therefore H's empty final column, so `appending=0` and U is the whole root column. This remains true even when the original stopping column has a nonempty prefix Q. Ignoring that original Q in `expandExtraLayer` is correct.

3. **n=0 succeeds only after successful lookup.** The reference's zero-iteration loop leaves Z empty, then deletes the entire original stopping column. `expandExtraLayer` line 184 does exactly that. Lookup still occurs first (`:204–208`), so a root beyond H correctly gives `none` even at zero; the implementation has not introduced an unconditional n=0 shortcut.

4. **The final-column root throws exactly for positive n.** If `ri=H.cols.length-1`, the root column is empty. Hence `appending=0=col_root.length`, and the reference throws only on entering its positive loop (`BTBM.ts:269–270`). The guard order at `Expansion.lean:184–185` matches this: zero deletes; positive n returns `none`. An earlier empty root column is still allowed, as it should be.

5. **For an earlier root, only the j=1 tail is observable.** Its reference continuation depth is ℓ−rl=−1. `ascend_replace` never reaches depth zero, so it never inserts the previous `new_tail`; recursive route depths only become more negative. Every iteration thus constructs a tail from the original root column and following forest, independently of the previous Z. The last iteration is j=1, for every positive n. This justifies replacing the whole loop by the expression at `Expansion.lean:187–190`.

6. **The downward shift and its scope are exact.** Put k=r−t. For any field that is shifted, p≥r gives

   ```
   p − k = p − (r−t) = p−r+t ≥ t ≥ 0.
   ```

   Therefore `shiftDownVal r (r-t)` (`:102,187`) agrees with the reference's signed final shift; Nat subtraction does not truncate an observable negative value. The head correctly retains each root entry's outer parent while shifting its entire height (`:188`). The body shifts all parents in every following column and descendant (`:189`). Reference stages j>1 can temporarily contain negative labels, but those tails are discarded and never rescanned; omitting them is valid.

7. **The enclosing syntax is restored correctly.** Line 190 calls `replaceAt 0 0` at the original depth ℓ, exactly the reference's final replacement (`BTBM.ts:288`). This preserves the strict containers and other original prefix material at any nesting depth, not only at ℓ=0.

These are invariants of the helper's actual call from `expand`; the helper is not claimed to model arbitrary independently supplied `eRoot`, depth and index arguments. The usual paper/V,I branch still has nonnegative t−r and is unchanged. Since standards stay in that domain by the finite closure argument, the repair does not alter the intended standard set or well-order proposition.

### Independent reruns

All builds and executions used unchanged source copies under `scratch/codex/statement-followup-work/`, with a copied dependency workspace and Lean 4.33.1. The reviewed original `lean/` and `checks/` files were not modified, and their hashes agree with the built copies (`statement-followup-source-sha256.json`).

- **Build:** `lake build` exited 0, 959 jobs; only the expected warning for the admitted main theorem. Log: `statement-followup-build.log`.
- **My original corpus:** I reran `statement-raw-fuzz.mjs`, verified that its generator, JSONL and counts were byte-identical to the original corpus, and ran the new executable on that JSONL. Result: **12,000 cases, 0 mismatches**; previously 80 mismatches. It still contains 7,513 reference returns and 4,487 throws. Logs/hashes: `statement-followup-corpus-generation.log`, `statement-followup-own-raw.log`, `statement-followup-original-corpus-sha256.json`.
- **Original successful-return counterexamples:** **8 cases, 0 mismatches**, previously 8 mismatches. Log: `statement-followup-old-regressions.log`.
- **Additional independently constructed directed cases:** **25 cases, 0 mismatches** (16 reference returns, 9 throws). These cover a nested stop ℓ=1, r−t=3, a nonempty original Q, earlier and final empty roots, beyond-child failures, and n=10 with discarded negative intermediate labels. Corpus/log: `statement-followup-extra-cases.jsonl`, `statement-followup-extra-lean.log`.
- **Updated supplied test script:** **580,021 cases, 0 mismatches**: 100,000 standard, 200,000 random V, 200,013 order/key/seed, and 80,008 fixed/raw cases. Its negative-output skip count was zero. Log: `statement-followup-differential.log`.

All filenames in this list are under `scratch/codex/`. Passing these finite tests is not proof; the branch derivation above is the independent justification for the repaired definition.

### Remaining statement-lock assessment

The root-search and replacement docstrings now state the relevant domains correctly. The universe docstring (`Statement.lean:12–15`) distinguishes the available level-zero facts from the explicit same-universe finite-Mahlo premise and no longer asserts the previous rough consistency-strength/unprovability characterization. The new fixed cases and arbitrary-parent corpus address the prior V-only coverage omission.

The original Q2 verdict is therefore updated from **not-faithful** to **faithful**, under the same finite-natural/structural-exception interpretation used in the initial review. The original order, Std, Mahlo and theorem verdicts otherwise stand. **There is no further required source or statement change before G2 on the evidence of this review.** Actual proof completion, removal of `sorryAx`, and the later formal closure/agreement lemmas remain separate obligations; approval to lock the statement does not certify those proofs.

STATUS: COMPLETE
