# U1 — syntax, occurrences, scans (paper §1–§2, txt:57-252)

**Companion Lean file:** `blueprint/lean/U1.lean`, appended after `blueprint/lean/Spine.lean`.
It typechecks with the command of the task (0 errors; only `declaration uses 'sorry'` warnings).
Helper: `scratch/blueprint/U1/check.sh`.

## Overview

U1 proves the finite facts of §1–§2 that every other unit uses.

- **Order** (D1.1, D1.4): `Tree.cmp` is a lawful total comparator for any lawful label
  comparator (D1.1a). This gives the proof fields of the spine's instances
  `Forest.instLinearOrder` and `Key.instLinearOrder`, and relabelling lemmas (D1.4a).
- **Occurrences** (D1.2): stack lemmas for the spine's address representation (D1.2b), the
  bodies of `truncAfter`/`setHeight` (D1.2c), and the terminal route (D1.2d).
- **Word library** (S-6, U1 half): ν, boundaries, the raw two-cursor scan and its traces
  (D2.1, L2.1, L2.3b, L2.5). Everything is generic over a linear order and used at `Key` and
  `WithTop Key`.
- **Compact words and safe prefixes** (C1.8, D1.9). A generic word `gword` over any label type
  (N1.2) proves order embedding once. It serves both forests and keys, and gives the sign
  criterion L2.5c.
- **The operation** (D1.5, D1.6, G-001). `paperOp` is written from §1.2 alone, with real bodies
  (D1.6). Its branch data are specified (D1.6b). Agreement with the locked `expand` is proved
  from the weakest hypotheses that make the paper's route and root defined (D1.6c), and then on
  nonempty V∧I inputs (D1.6a).
- **Scan conditions** (D2.2, D2.3), then **path nesting, barrier, capping** with the explicit
  G-006 induction predicates (`NestPred`, `BarPred` = `CutBound ∧ ReturnBound`, `RevPred`) and
  the first-divergence argument (L2.2a, L2.3a, L2.4a, L2.4b). The task's form of definedness,
  `expand E n ≠ none` on V, I, A, S, is L2.4c.
- **Testing** (N1.1): decidable mirrors of V, I, H, A, S and L, and a generator of standard
  expressions.

**Conventions used throughout.**

- *Bodies owed to the spine.* The spine declares seven definitions with `sorry` bodies owed by
  U1: `Tree.truncAfter`, `Tree.setHeight`, `Scan.safePrefix`, `Scan.stepKind`, `Scan.stopData`,
  `Scan.rootData` and `Scan.paperOp`. A unit file may not redeclare them, so U1 gives their real
  bodies as `…Body`. Bridge theorems `…_eq_body` state equality; they become `rfl` when T-018
  substitutes the bodies (SCR-2). Every other lemma is stated with the spine name.
  **Integration:** SCR-2 is applied. The `…Body` definitions and their helpers now live in
  `Spine.lean`, the seven spine names are defined by them, and every bridge holds by `rfl`
  (checked in `scratch/blueprint/all/rfl_check.lean`).
- *Precise informal definitions.* Every definition with a `sorry` body in the spine has a real
  body here, so the Lean text is the precise definition. Each entry also paraphrases it.
- *Hypotheses.* Every hypothesis is in the Lean signature. No lemma uses a `getD` default
  without stating it.
- *Induction measures.* Only those allowed by spine §c.0 are used:
  - structural recursion on trees, lists and addresses;
  - `Nat` strong induction on printed column numbers, entry indices and list lengths;
  - lexicographic `Nat × Nat`;
  - induction on `IsStd`.
- *Evidence.* Bounded `#eval!` tests of every finite statement with a real body ran in
  `scratch/blueprint/U1/` (files `tests-*.lean`, harness `evaltest*.lean`). The `!` is needed
  only because the spine's instance proofs are still `sorry`. All tests pass; the counts are
  quoted under **Testable**. They are evidence for the statements, not proofs.

**Planned files** (spine §e, plus two additions marked *new*): `Scan/Order.lean`,
`Scan/Occurrence.lean`, `Scan/Words.lean`, `Scan/Conditions.lean`, `Scan/CompactWord.lean`,
`Scan/Step.lean`, `Scan/Agreement.lean`, `Scan/Paths.lean`, `Scan/Capping.lean`,
`Scan/Seeds.lean` (*new*: D1.7, D1.7a) and `Scan/Dec.lean` (*new*: N1.1, testing only).

---

## Part A — Order and keys

### D1.1a Lawful comparators on trees   (paper: new)

**Fidelity:** new. It makes precise "this defines a computable linear order by recursion on the
two finite trees being compared" (txt:63-64).

**Statement.** Let `α, β` be types and `c : α → α → Ordering`. Let `Tree.cmp c` be the locked
comparison (`Syntax.lean`, mutual `cmp`/`cmpCols`/`cmpCol`).

1. If `c` is oriented (`Std.OrientedCmp c`), then `cmp c s t = (cmp c t s).swap` for all trees
   `s, t`.
2. If `c` is reflexive (`Std.ReflCmp c`), then `cmp c s s = .eq`.
3. If `c` is lawful (`Std.LawfulEqCmp c`), then `cmp c s t = .eq → s = t`.
4. If `c` is transitive (`Std.TransCmp c`), then `(cmp c s t).isLE` and `(cmp c t w).isLE`
   imply `(cmp c s w).isLE`.
5. Hence the instances `Std.OrientedCmp`, `Std.TransCmp`, `Std.ReflCmp` and `Std.LawfulEqCmp`
   hold for `Tree.cmp c`.
6. (`cmp_map`) Let `f : α → β` and `c' : β → β → Ordering` satisfy
   `∀ x y, c' (f x) (f y) = c x y`. Then `cmp c' (map f s) (map f t) = cmp c s t`.
7. (`map_injective`) If `f` is injective, then so is `Tree.map f`.

**Proof.**
1. Item 1 is proved by mutual structural induction on the left argument, following the three
   equations groups of `cmp`, `cmpCols` and `cmpCol`.
   - Base clauses: `[]` against `[]` gives `.eq`, and `.eq.swap = .eq`. `[]` against
     `_ :: _` gives `.lt`, and the reversed clause gives `.gt = .lt.swap`.
   - Step `cmpCols (x :: xs) (y :: ys)`: rewrite with the induction hypotheses for
     `cmpCol x y` and `cmpCols xs ys`, then apply core `Ordering.swap_then`:
     `(o₁.then o₂).swap = o₁.swap.then o₂.swap`.
   - Step `cmpCol ((p, h) :: es) ((q, k) :: fs)`: apply `Ordering.swap_then` twice, with
     `Std.OrientedCmp.eq_swap` for `c p q` and the induction hypotheses for `cmp c h k` and
     `cmpCol c es fs`.
2. Item 2 uses the same induction; every step is `Ordering.eq.then Ordering.eq = .eq`.
3. Item 3 uses the same induction. Core `Ordering.then_eq_eq` splits `o₁.then o₂ = .eq` into
   `o₁ = .eq ∧ o₂ = .eq`. Lawfulness of `c` gives equal labels, and the induction hypotheses
   give equal heights and equal tails.
<!-- U1-verify: changed -->
4. Item 4 is proved together with two strict variants. For a comparison function `κ` (one of
   `cmp c`, `cmpCols c`, `cmpCol c`) and a first argument `s`, write:
   - (T1) `(κ s t).isLE → (κ t w).isLE → (κ s w).isLE`;
   - (T2) `κ s t = .lt → (κ t w).isLE → κ s w = .lt`;
   - (T3) `(κ s t).isLE → κ t w = .lt → κ s w = .lt`.

   T1 alone is not inductive. In a `then`-composite with first components `κ₁ s t = .lt` and
   `κ₁ t w = .eq`, T1 for `κ₁` gives only `(κ₁ s w).isLE`. If `κ₁ s w` were `.eq`, the second
   component `κ₂ s' w'` would be unconstrained, because the hypotheses say nothing about
   `κ₂ s' t'`. T2 excludes this case. Item 4 is therefore proved as follows.
   1. **Composite lemma** (pure `Ordering` case analysis, with core
      `Ordering.isLE_then_iff_or`: `(o₁.then o₂).isLE ↔ o₁ = .lt ∨ (o₁ = .eq ∧ o₂.isLE)`, and
      `Ordering.then_eq_lt`). Let `a = κ₁ s t`, `b = κ₁ t w`, `a' = κ₁ s w` satisfy T1–T3. Let
      `A = κ₂ s₂ t₂`, `B = κ₂ t₂ w₂`, `A' = κ₂ s₂ w₂` satisfy T1–T3. Then `a.then A`,
      `b.then B` and `a'.then A'` satisfy T1–T3. The cases:
      - `a = .lt`: then `b.isLE` (from the second hypothesis), and T2 for `κ₁` gives
        `a' = .lt`;
      - `a = .eq`, `b = .lt`: T3 for `κ₁` gives `a' = .lt`;
      - `a = b = .eq`: T1 for `κ₁` gives `a' ∈ {.lt, .eq}`. If `a' = .lt`, the composite is
        `.lt`. If `a' = .eq`, the composites are `A`, `B`, `A'`, and T1–T3 for `κ₂` apply.
   2. **Mutual structural induction** on `s`, generalizing `t` and `w`. It proves T1–T3
      simultaneously for `cmp c`, `cmpCols c` and `cmpCol c` at first argument `s`.
      - Clauses with an empty list. `cmpCols [] u ∈ {.eq, .lt}` for every `u`,
        `cmpCols [] (_ :: _) = .lt`, and `cmpCols (_ :: _) [] = .gt`; the same holds for
        `cmpCol`.
        - For `s = []`: T1 holds since `κ [] w` is never `.gt`. For T2, `κ [] t = .lt` forces
          `t ≠ []`; then `(κ t w).isLE` forces `w ≠ []`, so `κ [] w = .lt`. For T3,
          `κ t w = .lt` forces `w ≠ []`, so `κ [] w = .lt`.
        - For `s ≠ []`, the hypothesis `(κ s t).isLE` forces `t ≠ []`, and then
          `(κ t w).isLE` forces `w ≠ []`. All empty cases are vacuous.
      - Step `cmpCols (x :: xs) (y :: ys) (z :: zs)`: apply the composite lemma. The first
        components are `cmpCol c x y`, `cmpCol c y z`, `cmpCol c x z`, by the induction
        hypothesis at `x`. The second components are those of `cmpCols` on `xs`, by the
        induction hypothesis at `xs`.
      - Step `cmpCol ((p, h) :: es) ((q, k) :: fs) ((o, l) :: gs)`: apply the composite lemma
        twice, following `((c p q).then (cmp c h k)).then (cmpCol c es fs)`.
        - The label components `c p q`, `c q o`, `c p o` satisfy T1–T3 by `Std.TransCmp c`:
          `Std.TransCmp.isLE_trans`, `Std.TransCmp.lt_of_lt_of_isLE` and
          `Std.TransCmp.lt_of_isLE_of_lt`.
        - The height components satisfy T1–T3 by the induction hypothesis at `h`.
        - The tail components satisfy T1–T3 by the induction hypothesis at `es`.
      - Step `cmp c (.node a) (.node b) = cmpCols c a b`: the statement for `cmpCols` at `a`.

   T1 at the forest level is item 4.
5. Item 5 packages items 1–4 into the four instances.
6. Item 6 is proved by mutual structural induction, unfolding `Tree.map`, `mapCols` and
   `mapCol` against the three comparison functions, rewriting with `hf` at each label pair.
7. Item 7 is proved by mutual structural induction, using `Tree.node.inj`, `List.cons.inj`,
   `Prod.mk.inj` and `hf`.

**Uses:** none (locked `Syntax.lean` and core only).

**Lean:** `Tree.cmp_eq_swap`, `Tree.cmp_self`, `Tree.eq_of_cmp_eq`, `Tree.cmp_isLE_trans`,
`Tree.instOrientedCmp`, `Tree.instTransCmp`, `Tree.instReflCmp`, `Tree.instLawfulEqCmp`,
`Tree.cmp_map`, `Tree.map_injective`. File `Scan/Order.lean`.

**Difficulty:** M. The nested mutual induction for transitivity is the bulk, about 250 LOC.

**Testable:** yes. Check orientation and transitivity of `Tree.cmp compare` on pairs and
triples from `Scan.stdUpTo 4 3 2` (N1.1). Pairwise word/forest order agreement was checked on
30,000 pairs (see C1.8).

### D1.1 Forests, columns, entries; syntax order   (paper: txt:57-64)

**Fidelity:** as in paper. These are the proof fields of the spine instance; the spine fixes the
definitions.

**Statement.**
1. `Forest.instLinearOrder` (spine) satisfies `le_refl`, `le_trans`, `le_antisymm`, `le_total`
   and `lt_iff_le_not_ge`, where:
   - `a < b` is the locked `instLTForest`: `Tree.cmp compare a b = .lt`;
   - `a ≤ b` is `Tree.cmp compare a b ≠ .gt`.
2. `Forest.empty_lt` (spine): `E ≠ Tree.empty → Tree.empty < E`.
3. `Forest.lt_iff_cmp` (spine) and `Forest.le_iff_cmp` are both `Iff.rfl`.
<!-- U1-verify: changed -->
4. `Forest.compare_eq_cmp`: `compare a b = Tree.cmp compare a b`. The spine instance does not
   set `compare`, so it is Mathlib's default `compareOfLessAndEq`, built with the instance's own
   `toDecidableLT`.
   - That decidability instance is not syntactically the locked `instDecidableLtForest`, so even
     `compare a b = compareOfLessAndEq a b`, as elaborated, is not `rfl`.
   - The proof (step 7) therefore uses only Mathlib's `compare_*_iff_*` lemmas, valid for every
     `LinearOrder`.

**Proof.** Put `c = compare` on `Nat`. Core supplies `Std.TransCmp c` and `Std.LawfulEqCmp c`
(`Nat.instTransOrd`, `Nat.instLawfulEqOrd`). Recall that `o ≠ .gt ↔ o.isLE = true`.
1. `le_refl`: `cmp c a a = .eq ≠ .gt` [D1.1a item 2].
2. `le_trans`: [D1.1a item 4].
3. `le_antisymm`: from `cmp c a b ≠ .gt` and `cmp c b a ≠ .gt`, orientation [D1.1a item 1]
   gives `cmp c a b ≠ .lt`. Hence `cmp c a b = .eq`, and `a = b` by [D1.1a item 3].
4. `le_total`: if `cmp c a b = .gt`, then `cmp c b a = .lt ≠ .gt` [D1.1a item 1].
5. `lt_iff_le_not_ge`: `cmp c a b = .lt ↔ (cmp c a b ≠ .gt ∧ cmp c b a = .gt)` [D1.1a item 1].
6. `empty_lt`: `E ≠ .node []` gives `E = .node (col :: cols)`. Then the defining equation
   `cmpCols c [] (_ :: _) = .lt` gives the result.
<!-- U1-verify: changed -->
7. `compare_eq_cmp`: case on `o = cmp c a b`, using Mathlib `compare_lt_iff_lt`,
   `compare_eq_iff_eq` and `compare_gt_iff_gt`.
   - If `o = .lt`, then `a < b` (`Forest.lt_iff_cmp`).
   - If `o = .eq`, then `a = b` [D1.1a item 3].
   - If `o = .gt`, then `cmp c b a = .lt` [D1.1a item 1], that is `b < a`.

**Uses:** D1.1a.

**Lean:** spine `Forest.instLinearOrder` (fields), `Forest.empty_lt`, `Forest.lt_iff_cmp`;
U1 `Forest.le_iff_cmp`, `Forest.compare_eq_cmp`. File `Scan/Order.lean`.

**Difficulty:** S — field-by-field applications of D1.1a.

**Testable:** yes. `decide` on small instances (`lean/BTBMS/Sanity.lean` already checks
`seed 1 < seed 2` and `∅ < seed 0`), and pairwise checks on `stdUpTo`.

### D1.4a Key labels and relabelling   (paper: new)

**Fidelity:** new. These are the label-level facts behind txt:84-85.

**Statement.**
1. `keyLabelCmp x y = compare (toLex x) (toLex y)` on `Bool ×ₗ Nat`, and
   `keyCmp x y = Tree.cmp compare x y` on `Tree (Lex (Bool × Nat))`. Both hold by `rfl`.
2. `keyLabelCmp` is `Std.TransCmp` and `Std.LawfulEqCmp`.
3. `relLabel a p := if p < a then (false, p) else (true, p - a)`, and
   `relKey a H = H.map (relLabel a)` (`rfl`).
4. `keyLabelCmp (relLabel a p) (relLabel a q) = compare p q` for all `a p q : Nat`.

**Proof.**
1. Item 1: `rfl` (checked by the typechecker).
2. Item 2: by item 1, `keyLabelCmp` is `compare` of the Mathlib linear order
   `Prod.Lex.instLinearOrder Bool Nat`. Mathlib provides `Prod.Lex.instTransOrdLex` for
   transitivity. Lawfulness follows from `compare_eq_iff_eq` of a `LinearOrder`.
3. Item 3: `rfl`.
4. Item 4 is a case split on `p < a` and `q < a`:
   - both: `compare false false = .eq`, then `compare p q`;
   - `p < a ≤ q`: `.lt` on both sides;
   - `q < a ≤ p`: `.gt` on both sides;
   - neither: `compare (p - a) (q - a) = compare p q`, since `a ≤ p` and `a ≤ q`
     (`Nat.sub_lt_sub_iff_right` and its `=` form).

**Uses:** none.

**Lean:** `keyLabelCmp_eq`, `keyCmp_eq_cmp_lex`, `keyLabelCmp_transCmp`,
`keyLabelCmp_lawfulEqCmp`, `relLabel`, `relKey_eq_map`, `keyLabelCmp_relLabel`. File
`Scan/Order.lean`.

**Difficulty:** S — four-way case split and two `rfl`s.

**Testable:** yes. Exhaustive over `a, p, q < 8` by `decide`.

### D1.4 Relative key h_a   (paper: txt:81-85)

**Fidelity:** as in paper.

**Statement.**
1. `Key.instLinearOrder` (spine) satisfies the five order axioms, with `x < y :↔
   keyCmp x y = .lt` (`Key.lt_iff_keyCmp`, `Iff.rfl`) and `x ≤ y :↔ keyCmp x y ≠ .gt`.
2. `keyCmp (relKey a H) (relKey a H') = Tree.cmp compare H H'` (`keyCmp_relKey`).
3. `relKey_lt_iff` (spine): `relKey a H < relKey a H' ↔ H < H'`.
4. `relKey_injective a`.
<!-- U1-verify: changed -->
5. `Key.compare_eq_keyCmp`: `compare x y = keyCmp x y`. The spine instance leaves `compare` at
   its default `compareOfLessAndEq` (checked by `rfl`). This bridge is needed wherever a key sign
   computed with `keyCmp` (L2.5c) feeds a statement phrased with `compare` (L2.5 (3)).

**Proof.**
1. Item 1 repeats the five steps of the D1.1 proof with `c = keyLabelCmp`, the instances of
   [D1.4a item 2] and the `Tree.cmp` instances of [D1.1a item 5].
2. Item 2: `relKey_eq_map` [D1.4a item 3], then `Tree.cmp_map` [D1.1a item 6] with
   `hf := keyLabelCmp_relLabel a` [D1.4a item 4].
3. Item 3: unfold both `<` relations (`Key.lt_iff_keyCmp`, `Forest.lt_iff_cmp`) and rewrite
   with item 2.
4. Item 4: `Tree.map_injective` [D1.1a item 7]. `relLabel a` is injective: equal labels have
   equal flags. In the false case the values are equal. In the true case `p - a = q - a` with
   `a ≤ p` and `a ≤ q`, so `p = q`.
<!-- U1-verify: changed -->
5. Item 5 is the D1.1 step 7 argument, with `keyCmp`, `Key.lt_iff_keyCmp`, and items 1–3 of
   [D1.1a] for `c = keyLabelCmp` (instances of [D1.4a item 2]).

**Uses:** D1.1a, D1.4a, D1.1 (step 7, repeated).

**Lean:** spine `Key.instLinearOrder` (fields), `relKey_lt_iff`; U1 `Key.lt_iff_keyCmp`,
`keyCmp_relKey`, `relKey_injective`, `Key.compare_eq_keyCmp`. File `Scan/Order.lean`.

**Difficulty:** S — instance fields by D1.1a, one rewrite.

**Testable:** yes. `keyCmp (relKey a E) (relKey a F) = Tree.cmp compare E F` held on 36,000
triples (120 × 60 forests, `a ∈ {0,1,2,3,5}`).

---

## Part B — Occurrences

### D1.2a Address types   (paper: new, spine)

**Fidelity:** new (spine, R-3).

**Statement.** The FIRM real-bodied vocabulary of spine §c.2:
- `ColAddr`, `EntryAddr`, `Role`, `EntryAddr.heightPath`, `Role.path`, `Role.inEntry`;
- `ColAddr.num`, `ColAddr.resolveAux`, `ColAddr.resolve`, `ColAddr.container`, `ColAddr.rep`,
  `ColAddr.reps0`;
- `Tree.forestAt`, `Tree.colAt`, `Tree.entryAt`, `Tree.heightAt`, `Tree.rolesF`,
  `Tree.rolesCols`, `Tree.rolesCol`, `Tree.roles`, `Tree.colAddrs`, `Tree.entryAddrs`,
  `Tree.size`.

**Proof.** Definitions; complete in the spine.

**Uses:** none.

**Lean:** spine names. File `Scan/Occurrence.lean`.

**Difficulty:** S — already written in the spine.

**Testable:** n/a.

### D1.2b Stacks, containment, accessors, roles   (paper: new)

**Fidelity:** new. These are the lemmas behind "a number on the visible stack denotes a unique
occurrence" (txt:69) and behind codex-crosscheck-1 Q2 ("restricting σ to the prefix through a
visited column leaves all its lower visible occurrences unchanged").

**Statement.** Let `c = ⟨[(c₀,i₀),…,(c_{m-1},i_{m-1})], j⟩` be a column address and `base` a
natural number. Write `start_k = base + Σ_{l<k} (c_l + 1)`.

1. `OnStack c o` holds iff one of the following holds:
   - there are `k < m` and `(ck, ik) = c.path[k]` with `o.path = c.path.take k` and
     `o.col ≤ ck`;
   - `o.path = c.path` and `o.col < c.col`.
2. `resolve_spec`: `c.resolve base q = some o ↔ OnStack c o ∧ o.num base = q`.
3. `num_lt_of_onStack`: `OnStack c o → o.num base < c.num base`.
4. `onStack_inj`: two stack occurrences with the same number are equal.
5. `resolve_num`, `resolve_lt`: `resolve base q = some o` gives `o.num base = q` and
   `q < c.num base`.
6. `resolve_isSome_iff`: `(c.resolve base q).isSome ↔ base ≤ q ∧ q < c.num base`.
7. `resolve_of_resolve_lt`: if `c.resolve base x = some o` and `q < x`, then
   `o.resolve base q = c.resolve base q`.
8. `container_spec`: `q.container c = some e ↔ e.col = q ∧ e.heightPath <+: c.path`.
9. `EntryAddr.Contains e c :⇔ e.heightPath <+: c.path`. Then:
   - `resolve_host`: `e.Contains c → c.resolve 0 (e.col.num 0) = some e.col`;
   - `contains_of_resolve`: if `e.Contains c`, `c.resolve 0 z = some o` and
     `e.col.num 0 < z`, then `e.Contains o`;
   - `contains_iff_container`: `e.Contains c ↔ e.col.container c = some e`.
10. Accessors, for an arbitrary `t : Tree α`:
    - `mem_colAddrs_iff`: `c ∈ t.colAddrs ↔ (t.colAt c).isSome`;
    - `mem_entryAddrs_iff`: `e ∈ t.entryAddrs ↔ (t.entryAt e).isSome`;
    - `mem_roles_iff`;
    - `roles_nodup` (`roles_nodup`†);
    - `forestAt_append`: `forestAt (π ++ π') = (forestAt π).bind (·.forestAt π')`;
    - `forestAt_heightPath`: `t.forestAt e.heightPath = t.heightAt e`;
    - `colAt_of_entryAt`.

**Proof.**
1. Item 2 is proved by induction on the remaining path in `resolveAux start pre rest j q`,
   with the invariant `pre = c.path.take k` and `start = start_k` after `k` levels.
   - At a containing level, the guard `start ≤ q ≤ start + ck` returns `⟨pre, q - start⟩`.
     This is the first disjunct of `OnStack`, and `num base ⟨pre, q - start⟩ = q` because
     `num base ⟨take k, x⟩ = start_k + x`.
   - At the last level, the guard `start ≤ q < start + j` gives the second disjunct.
   - Conversely, an `OnStack` occurrence of number `q` fails every guard at levels before its
     own: their numbers are at most `start_l + c_l < start_{l+1} ≤ q`. It passes the guard at
     its own level.
2. Item 3: a first-disjunct occurrence at level `k` has number `start_k + o.col ≤ start_k + ck
   < start_{k+1} ≤ c.num base`. A second-disjunct occurrence has number
   `start_m + o.col < start_m + j = c.num base`.
3. Item 4: the number is strictly increasing in (level, column) lexicographically, by the
   arithmetic of step 2, hence injective on stack occurrences.
4. Item 5: from item 2 and item 3.
5. Item 6: the intervals `[start_k, start_k + c_k]` for `k < m`, followed by
   `[start_m, start_m + j)`, partition `[base, c.num base)`. Apply item 2.
6. Item 7: let `o` be at level `k` of `c`'s stack, in the first disjunct of item 1. Then the
   stack occurrences of `o` are:
   - the levels `< k` of `c`'s stack, which are equal by `o.path = c.path.take k`;
   - the columns `0 … o.col - 1` at level `k`.

   These are exactly the stack occurrences of `c` with number `< x`. Every deeper level of
   `c` has numbers `≥ start_{k+1} > x`. Items 2 and 4 then give equal results. The
   second-disjunct case is the same computation at level `m`.
7. Item 8: unfold `container`. The conditions `c.path.drop |q.path| = (k, i) :: _`,
   `c.path.take |q.path| = q.path` and `k = q.col` together say
   `q.path ++ [(q.col, i)] <+: c.path` (`List.prefix_iff_eq_take`, `List.take_append_drop`).
8. Item 9, `resolve_host`: from `c.path = e.col.path ++ (e.col.col, e.idx) :: rest`, `e.col` is
   a first-disjunct stack occurrence at level `|e.col.path|`. Apply item 2.
9. Item 9, `contains_of_resolve`: let `k = |e.col.path|`. At level `k`, `e.col` is the
   containing column `c_k`, the largest-numbered stack occurrence of levels `≤ k`. So `o`,
   with number `> e.col.num 0`, lies at a level `k' > k` (items 2 and 3). Its path
   `c.path.take k'` extends `c.path.take (k+1) = e.heightPath`.
10. Item 9, `contains_iff_container`: item 8.
11. Item 10:
    - `mem_colAddrs_iff`, `mem_entryAddrs_iff` and `mem_roles_iff` are proved by mutual
      induction over `rolesF`/`rolesCols`/`rolesCol`. A role is emitted at `(π, c[, i])`
      exactly when `forestAt π` exists and has that column (and entry).
    - `roles_nodup`: by the same induction, every role emitted by `rolesF π` has a path
      extending `π`. Sibling calls use incomparable extensions `π ++ [(c, i)]`, and `ord` and
      `slot` roles differ, so emitted roles are pairwise distinct.
    - `forestAt_append`: induction on `π`.
    - `forestAt_heightPath`: `forestAt_append` with a one-step path.
    - `colAt_of_entryAt`: unfold `entryAt`.

**Uses:** D1.2a.

**Lean:** `ColAddr.OnStack`, `ColAddr.resolve_spec`, `ColAddr.num_lt_of_onStack`,
`ColAddr.onStack_inj`, `ColAddr.resolve_num`, `ColAddr.resolve_lt`,
`ColAddr.resolve_isSome_iff`, `ColAddr.resolve_of_resolve_lt`, `ColAddr.container_spec`,
`EntryAddr.Contains`, `EntryAddr.resolve_host`, `EntryAddr.contains_of_resolve`,
`EntryAddr.contains_iff_container`, `Tree.mem_colAddrs_iff`, `Tree.mem_entryAddrs_iff`,
`Tree.mem_roles_iff`, `Tree.roles_nodup`, `Tree.forestAt_append`, `Tree.forestAt_heightPath`,
`Tree.colAt_of_entryAt`. File `Scan/Occurrence.lean`.

**Difficulty:** M. About 400 LOC: the `resolveAux` arithmetic and the mutual role induction.

**Testable:** yes, with 0 failures:
- on 3,200 forests: every `q < c.num 0 + 3` resolves iff `q < c.num 0`, to an existing column
  of number `q`; and `roles_nodup` holds;
- on 800 of them: `resolve_of_resolve_lt` holds for every `x < c.num 0`, and `resolve_host`
  and `contains_of_resolve` hold for every containing pair.

### D1.2 Column numbering, visibility, occurrences   (paper: txt:65-69)

**Fidelity:** as in paper, with occurrences represented by addresses (spine decision 2, R-3).

**Statement.**
1. Numbering: the outer forest starts at `0`, and a height attached to column `a` starts at
   `a + 1`. This is the definition `ColAddr.num 0`.
2. Visibility: the visible stack of a column `c` is `OnStack c` [D1.2b item 1], and its numbers
   are exactly `0 … c.num 0 - 1` [D1.2b item 6].
3. Uniqueness: a number on the visible stack denotes a unique occurrence [D1.2b items 2, 4].

**Proof.** Item 1 is a definition. Items 2 and 3 are D1.2b items 1, 2, 4 and 6.

**Uses:** D1.2a, D1.2b.

**Lean:** no declaration of its own: its definitions are those listed under D1.2a (spine) and
its lemmas are those of D1.2b. File `Scan/Occurrence.lean`.

**Difficulty:** S — restatement of D1.2b.

**Testable:** yes, through D1.2b.

### D1.2c `truncAfter` and `setHeight`   (paper: new; spine §c.2 bodies)

**Fidelity:** new. These are the bodies owed by U1 for the §4 record equations.

**Statement.**
1. `Tree.truncAux π j i t`:
   - at a containing step `(c, i₀) :: rest`: keep the columns `0…c`; in column `c` keep the
     entries `0…i₀`, and replace the height of entry `i₀` by `truncAux rest j i` of it;
   - at the last level: keep the columns `0…j`, and in column `j` the entries `0…i`.

   `truncAfterBody t e` is `truncAux e.col.path e.col.col e.idx t` if `e` is an entry of `t`,
   and `t` otherwise.
2. `Tree.setAux h π j i t` replaces, along the same path, the height of entry `i` of column `j`
   by `h` (`List.modify`). `setHeightBody t e h` is that if `e` is an entry, else `t`.
3. Bridges `truncAfter_eq_body` and `setHeight_eq_body`.
4. `truncAfter_roles`† (`e ∈ t.entryAddrs`):
   `(t.truncAfter e).roles = t.roles.takeWhile (· != .slot e) ++
   (t.roles.dropWhile (· != .slot e)).takeWhile (·.inEntry e)`. That is: the roles strictly
   before `U_e`, then `U_e` and the roles of `e`'s height.
5. `entryAt_truncAfter`: `truncAfter` keeps `e` with its height.
6. `entryAt_setHeight`: the entry `e` becomes `(p, h)`.

**Proof.**
<!-- U1-verify: changed -->
1. Item 4 is proved in a form generalized over the address prefix. The role recursion emits
   absolute addresses, while `truncAux` descends with relative paths, so the induction
   hypothesis must apply inside a height.
   - For a prefix `π` and a relative entry address `e` of a tree `s`, put
     `e^π := ⟨⟨π ++ e.col.path, e.col.col⟩, e.idx⟩`.
   - Claim: `rolesF π (truncAux e.col.path e.col.col e.idx s)` equals
     `(rolesF π s).takeWhile (· != .slot e^π) ++ ((rolesF π s).dropWhile (· != .slot e^π)).takeWhile (·.inEntry e^π)`.
   - The claim is proved by induction on `e.col.path`, generalizing `π` and `s`, following
     `truncAux` against `rolesF`/`rolesCols`/`rolesCol` (spine §c.2). At a containing step
     `(c, i₀)` the induction hypothesis is used with prefix `π ++ [(c, i₀)]` on the height of
     entry `i₀`.
   - Item 4 is the case `π = []`, `s = t`.

   The two cases of the induction:
   - At a containing step `(c, i₀)`, the roles of the kept part are, in order:
     - the roles of columns `0…c-1`, unchanged;
     - `A_c`;
     - the slots and heights of entries `0…i₀-1`, unchanged;
     - `U_{e'}` and, by the induction hypothesis, the truncated height.

     These are the first roles of `t.roles` in reading order.
   - At the last level, the kept roles are those before `U_e`, then `U_e`, then the full
     height of `e`.
   - The roles inside `e` follow `U_e` contiguously and are exactly those with
     `Role.inEntry · e`. By [D1.2b item 10], role paths extend the forest path, and
     `heightPath e` is a prefix of the path of exactly the roles inside `e`.
2. Item 5 is proved by the same induction, with `List.getElem?_take` and
   `List.getElem?_append_left`.
3. Item 6 is proved by induction on the path with `List.getElem?_modify`.

**Uses:** D1.2b.

**Lean:** `Tree.truncAux`, `Tree.truncAfterBody`, `Tree.setAux`, `Tree.setHeightBody`,
`Tree.truncAfter_eq_body`, `Tree.setHeight_eq_body`, `Tree.truncAfter_roles`,
`Tree.entryAt_truncAfter`, `Tree.entryAt_setHeight`. File `Scan/CompactWord.lean` (spine §e).
**Integration note:** At integration, SCR-2: these body definitions moved verbatim into `Spine.lean`; they remain U1-owned.

**Difficulty:** M. Two path inductions against the role recursion.

**Testable:** yes. For every entry of 3,200 forests: `truncAfter_roles`, `entryAt_truncAfter`
and `entryAt_setHeight` hold, and the word of `truncAfterBody` is a prefix of the word
(0 failures).

### D1.2d The terminal last-column, last-entry route   (paper: new)

**Fidelity:** new. It characterizes the spine's fuel-based `routeCols` (txt:98-99, 220-221).

**Statement.**
1. `Tree.lastStep? F` is `some (|F| - 1, |col| - 1)` when the last column `col` of `F` is
   nonempty, and `none` otherwise.
2. `Scan.IsRoutePath E π :⇔ ∀ d < |π|, ∃ F, E.forestAt (π.take d) = some F ∧
   F.lastStep? = π[d]?`.
3. `Scan.mem_routeCols_iff`: `c ∈ routeCols E ↔ IsRoutePath E c.path ∧
   ∃ F, E.forestAt c.path = some F ∧ |F.cols| = c.col + 1`.
4. `Scan.mem_colAddrs_of_mem_routeCols`.

**Proof.**
1. Fuel adequacy. Each recursive call of `routeColsAux` emits one column address, and these
   are distinct column roles of `E`. So for every `fuel ≥ (number of column roles) + 1`, the
   output does not depend on the fuel. Prove this by induction on `fuel`, generalizing the
   forest and the prefix. Also `E.size ≥` the number of column roles, since `size` is the
   length of `roles` and every column role is in `roles` [D1.2b item 10].
2. With adequate fuel, prove item 3 by induction along `routeColsAux F π`. The emitted head is
   `⟨π, |F| - 1⟩`, and the recursion enters the height of the last entry with
   `π ++ [(|F| - 1, |col| - 1)] = π ++ [F.lastStep?.get]`.
3. Item 4: item 3 gives `colAt` defined; then [D1.2b item 10].

**Uses:** D1.2b.

**Lean:** `Tree.lastStep?`, `Scan.IsRoutePath`, `Scan.mem_routeCols_iff`,
`Scan.mem_colAddrs_of_mem_routeCols`. File `Scan/Occurrence.lean`.

**Difficulty:** S — the fuel lemma is the only step that is not an unfolding.

**Testable:** yes. For every column of 7,000 forests (standard, random V∧I and raw), membership
in `routeCols` agrees with the characterization (0 failures).

---

## Part C — Conditions V, I, H

### D1.3 Conditions V, I, H   (paper: txt:70-75)

**Fidelity:** as in paper.

**Statement.** Spine definitions:
- `CondV E`: every entry's parent resolves on its column's stack.
- `CondI E`: every column of a nonempty height attached to the column `a = e.col.num 0` is
  nonempty, with first parent `≥ a`. Outer columns may be empty.
- `CondH E`: consecutive entries satisfy `EntryLe` (nonincreasing: parent first, then height).

**Proof.** Definitions.

**Uses:** D1.2a, D1.1 (the `≤` in `EntryLe`).

**Lean:** spine `Scan.CondV`, `Scan.CondI`, `Scan.EntryLe`, `Scan.CondH`. File
`Scan/Conditions.lean`.

**Difficulty:** S — spine definitions.

**Testable:** via N1.1 mirrors.

### D1.3a V as a numeric bound   (paper: new)

**Fidelity:** new. Every smaller number is visible, so "visible parent `p < c`" (txt:71)
reduces to `p < c`.

**Statement.** `condV_iff_lt`: `CondV E ↔ ∀ e ∈ E.entryAddrs, ∀ p h, E.entryAt e = some (p, h) →
p < e.col.num 0`.

**Proof.**
1. Rewrite each `(e.col.resolve 0 p).isSome` with `resolve_isSome_iff` at `base = 0`
   [D1.2b item 6]; the lower bound `0 ≤ p` is trivial.

**Uses:** D1.2b, D1.3.

**Lean:** `Scan.condV_iff_lt`. File `Scan/Conditions.lean`.

**Difficulty:** S — one rewrite with D1.2b item 6.

**Testable:** yes (`condVb`, N1.1).

---

## Part D — The generic word library (S-6, U1 half)

All statements in Part D are over an arbitrary `[LinearOrder α]`. Consumers instantiate
`α := Key` and `α := WithTop Key`. Lists carry the core lexicographic order `List.lt`
(`List.instLT`), which agrees with Mathlib's `List.instLinearOrder` (checked by `rfl` in
`scratch/blueprint/U1/probe2.lean`). In that order a proper prefix is smaller.
`Noninc l :⇔ l.Pairwise (fun x y => y ≤ x)`.

### D2.1a The ν library   (paper: new)

**Fidelity:** new. It is the "reductions" component of the S-6 word library.

**Statement.**
1. `nuStep acc x := (acc.reverse.dropWhile (· < x)).reverse ++ [x]`, and
   `nu l = l.foldl nuStep []` (`rfl`).
2. `nu_append_singleton`: `nu (l ++ [x]) = nuStep (nu l) x`.
3. `nuStep_eq_takeWhile` (`Noninc acc`): `nuStep acc x = acc.takeWhile (x ≤ ·) ++ [x]`.
4. `nu_noninc`: `Noninc (nu l)`.
5. `nu_of_noninc`: `Noninc l → nu l = l`.
6. `nu_append_nu`: `nu (nu l ++ m) = nu (l ++ m)`.
7. `lt_nuStep` (`Noninc acc`): `acc < nuStep acc x`.
8. `le_of_mem_nuStep` (`Noninc acc`): every letter of `nuStep acc x` is `≥ x`.
9. `cutQuery_succ` (`k < |ks|`): `cutQuery ks (k+1) = nuStep (cutQuery ks k) ks[k]`.
10. `cutQuery_noninc`.
<!-- U1-verify: changed -->
11. `nu_map`: if `f : α → β` is `StrictMono` between linear orders, then
    `nu (l.map f) = (nu l).map f`. Corollaries `cutQuery_map` and `boundary_map`:
    `cutQuery (ks.map f) k = (cutQuery ks k).map f`, and likewise for `boundary`. These are the
    "commute with ν" of txt:333 (used by U2 for the maps `κ_j`) and the coercion
    `Key → WithTop Key`.

**Proof.**
1. Item 2: `List.foldl_append`, and `foldl` over a singleton.
2. Item 3: in a nonincreasing `acc`, the letters `≥ x` form a prefix `T = acc.takeWhile (x ≤ ·)`.
   The rest `D` consists of letters `< x`: its first letter fails `x ≤ ·`, and later letters
   are `≤` it. So `acc.reverse = D.reverse ++ T.reverse`. `dropWhile (· < x)` removes exactly
   `D.reverse`, because the last letter of `T` is `≥ x`. Reversing gives `T`.
<!-- U1-verify: changed -->
3. Item 4: right induction on `l` (`List.reverseRecOn`). The step is item 2, then item 3 on
   `nu l`, which is nonincreasing by the induction hypothesis. `T` is a sublist of a
   nonincreasing list (`List.Pairwise.sublist`), all its letters are `≥ x` (core
   `List.all_takeWhile` with `List.all_eq_true`), and `List.pairwise_append` closes the step.
4. Item 5: right induction. If `Noninc (l ++ [x])`, then `Noninc l` and every letter of `l` is
   `≥ x`. So `nuStep l x = l.takeWhile (x ≤ ·) ++ [x] = l ++ [x]`, by item 3 and core
   `List.takeWhile_append_of_pos` with `l₂ = []`. (Mathlib's `List.takeWhile_eq_self_iff` is in
   `Mathlib.Data.List.TakeWhile`, which the pinned dependency build does not contain.)
5. Item 6: right induction on `m`. The base is `nu (nu l) = nu l`, by items 4 and 5. The step
   is item 2.
6. Item 7: by item 3, `acc = T ++ D` and `nuStep acc x = T ++ [x]`.
   - If `D = []`, then `acc = T` is a proper prefix of `T ++ [x]`, hence smaller.
   - If `D = d :: _`, then `d < x` decides at position `|T|` after the common prefix `T`
     (`List.Lex.rel` under `T`).
<!-- U1-verify: changed -->
7. Item 8: a letter of `T` satisfies `x ≤ ·` (`List.all_takeWhile`, `List.all_eq_true`), or it
   is `x`.
8. Item 9: `ks.take (k+1) = ks.take k ++ [ks[k]]`, then item 2.
9. Item 10: item 4.
<!-- U1-verify: changed -->
10. Item 11: right induction on `l` with item 2 on both sides. It remains to show
    `nuStep (acc.map f) (f x) = (nuStep acc x).map f`.
    - `List.map_reverse` turns `(acc.map f).reverse` into `acc.reverse.map f`.
    - `List.dropWhile_map` turns the `dropWhile` of the mapped list into the map of a
      `dropWhile` with the composed predicate.
    - That predicate is `decide (f y < f x) = decide (y < x)`, by `StrictMono.lt_iff_lt`.
    - Finally use `List.map_append`.

    `cutQuery_map` and `boundary_map` follow from item 11 and `List.map_take`.

**Uses:** none.

**Lean:** `Scan.Noninc`, `Scan.nuStep`, `Scan.nu_eq_foldl`, `Scan.nu_append_singleton`,
`Scan.nuStep_eq_takeWhile`, `Scan.nu_noninc`, `Scan.nu_of_noninc`, `Scan.nu_append_nu`,
`Scan.lt_nuStep`, `Scan.le_of_mem_nuStep`, `Scan.cutQuery_succ`, `Scan.cutQuery_noninc`,
`Scan.nu_map`, `Scan.cutQuery_map`, `Scan.boundary_map`. File `Scan/Words.lean`.

**Difficulty:** M. About 200 LOC of list lemmas.

**Testable:** yes. Exhaustive over the 121 words of length `≤ 4` over `{0,1,2}`: `nu`
nonincreasing and idempotent, strict increase (0 failures).

### D2.1 ν reduction; boundaries strictly increase   (paper: txt:157-164)

**Fidelity:** as in paper.

**Statement.**
1. Spine definitions `nu`, `cutQuery ks k = ν(ks[0..k-1])` (`= B_c(k-1)`) and
   `boundary ks i = ν(ks[0..i])` (`= B_c(i)`); `cutQuery_zero : cutQuery ks 0 = []`;
   `boundary_eq_cutQuery : boundary ks i = cutQuery ks (i+1)` (both `rfl`).
2. `cutQuery_lt_succ` (spine): `k < |ks| → cutQuery ks k < cutQuery ks (k+1)`.
3. `cutQuery_strictMono`: `j < k ≤ |ks| → cutQuery ks j < cutQuery ks k`.
4. `cutQuery_mono`: `j ≤ k → cutQuery ks j ≤ cutQuery ks k` (no length bound).
5. `boundary_ne_nil`: `i < |ks| → boundary ks i ≠ []`.

**Proof.**
1. Item 2: `cutQuery_succ` [D2.1a item 9], then `lt_nuStep` [D2.1a item 7] with
   `cutQuery_noninc` [D2.1a item 10].
2. Item 3: induction on `k - j` with item 2 and transitivity of `<` on lists.
3. Item 4: for `k ≤ |ks|`, use item 3 or equality. For `k > |ks|`,
   `cutQuery ks k = nu ks = cutQuery ks |ks|` (`List.take_of_length_le`); then the first case
   with `min j |ks|`.
4. Item 5: `boundary ks i = cutQuery ks (i+1) = nuStep _ ks[i]` [D2.1a item 9], which ends in
   `ks[i]`.

**Uses:** D2.1a.

**Lean:** spine `Scan.nu`, `Scan.cutQuery`, `Scan.boundary`, `Scan.cutQuery_lt_succ`; U1
`Scan.cutQuery_zero`, `Scan.boundary_eq_cutQuery`, `Scan.cutQuery_strictMono`,
`Scan.cutQuery_mono`, `Scan.boundary_ne_nil`. File `Scan/Words.lean`.

**Difficulty:** S — short consequences of D2.1a.

**Testable:** yes (exhaustive, as in D2.1a).

### L2.1a Cursor bookkeeping   (paper: new)

**Fidelity:** new.

**Statement.**
1. `cursor_le_length`: `cursor src qry ≤ |src|`.
2. `cursor_take`: `cursor (src.take k) qry = min k (cursor src qry)`.
3. `qcursor src qry` is the final query cursor, with the same recursion as the spine's
   `cursor`. `qcursor_le_length`: `qcursor src qry ≤ |qry|`.
4. `cursor_append_of_exhausted`: if `cursor src qry = |src|`, then:
   - `cursor (src ++ src') qry = |src| + cursor src' (qry.drop (qcursor src qry))`;
   - `qcursor (src ++ src') qry = qcursor src qry + qcursor src' (qry.drop (qcursor src qry))`.
5. `cursor_append_of_lt`: `cursor src qry < |src| → cursor (src ++ src') qry = cursor src qry`.
6. `cursor_singleton_cons` (`Noninc (y :: V)`):
   - `x < y → cursor [x] (y :: V) = 1 ∧ qcursor [x] (y :: V) = 0`;
   - `x = y → cursor = 1 ∧ qcursor = 1`;
   - `y < x → cursor [x] (y :: V) = 0`.
7. `cursor_nil_right`: `cursor src [] = 0`.

**Proof.** Every item is functional induction on the recursion of `cursor`/`qcursor`
(`cursor.induct`, well-founded on `|xs| + |ys|`).
1. Item 1: each branch adds `1` exactly when the source shrinks by one.
2. Item 2: induction generalizing `k`. At `x :: xs`, `y :: ys` with `k = k' + 1`, the three
   branches give `min k' a + 1 = min (k'+1) (a+1)`, or the query-only branch with an unchanged
   source.
3. Item 4: until the source cursor reaches `|src|`, every comparison reads a letter of `src`.
   At the state `(|src|, qcursor src qry)` the run on `src ++ src'` continues as a fresh run on
   `src'` against `qry.drop (qcursor src qry)`.
4. Item 5: a run stopping with source cursor `< |src|` stopped because its query was
   exhausted. The same run on `src ++ src'` stops at the same state.
5. Item 6:
   - The first two cases are single steps of the equations.
   - In the third, every letter of `V` is `≤ y < x`, by `Noninc`. So the query-only branch is
     taken until `V` ends (induction on `V`), and `cursor [x] [] = 0` (item 7).
6. Item 7: the equation `| _ :: _, [] => 0`, and `cursor [] _ = 0`.

**Uses:** none.

**Lean:** `Scan.cursor_le_length`, `Scan.cursor_take`, `Scan.qcursor`,
`Scan.qcursor_le_length`, `Scan.cursor_append_of_exhausted`, `Scan.cursor_append_of_lt`,
`Scan.cursor_singleton_cons`, `Scan.cursor_nil_right`. File `Scan/Words.lean`.

**Difficulty:** S — functional inductions.

**Testable:** yes. Exhaustive over words of length `≤ 4` (sources `≤ 3` and `≤ 2`, queries
`≤ 4`) over `{0,1,2}` (0 failures).

### L2.5a Trace bookkeeping   (paper: new)

**Fidelity:** new.

**Statement.**
1. `trace_last`: `(trace src qry).getLast? = some (cursor src qry, qcursor src qry)`.
2. `cursor_eq_of_trace_eq`: equal traces give equal final source cursors.
<!-- U1-verify: changed -->
3. `trace_fst_le_cursor`: if `(i, j) ∈ trace src qry`, then `i ≤ cursor src qry`. No visited
   state is past the final source cursor.

**Proof.**
1. Item 1: functional induction on `traceFrom` (generalizing the start state), against the
   equations of `cursor`/`qcursor` [L2.1a item 3].
2. Item 2: apply item 1 to both traces, then `Option.some.inj`.
<!-- U1-verify: changed -->
3. Item 3: functional induction on `traceFrom i₀ j₀ src qry`, generalizing the start state.
   The invariant: every listed first coordinate is at most `i₀ + cursor src qry`. The head state
   has first coordinate `i₀`. Each recursive branch either keeps `i₀` (query-only move) or
   passes to `i₀ + 1` with a source shorter by one, and adds `1` to the cursor. These are the
   equations of `cursor`. Take `i₀ = j₀ = 0`.

**Uses:** L2.1a.

**Lean:** `Scan.trace_last`, `Scan.cursor_eq_of_trace_eq`, `Scan.trace_fst_le_cursor`. File
`Scan/Words.lean`.

**Difficulty:** S — one functional induction.

**Testable:** yes (exhaustive, 0 failures).

### L2.1b Exhaustion is lexicographic comparison   (paper: new; txt:170-173)

**Fidelity:** new. It makes precise "after reducing both nonincreasing lists, exhaustion is
precisely lexicographic comparison".

**Statement.** `cursor_eq_length_iff`: for `Noninc W`,
`cursor src W = |src| ↔ nu src ≤ W`.

**Proof.** Prove by right induction on `src` (`List.reverseRecOn`) that one of two alternatives
holds. Write `j := qcursor src W`.
- **(a)** `cursor src W = |src|`, and `nu src = W.take j ++ T` for some `T` with:
  - `Noninc T`;
  - `j < |W| → ∀ t ∈ T, t < W[j]`;
  - `j = |W| → T = []`.
- **(b)** `cursor src W < |src|` and `W < nu src`.

1. Base `src = []`: alternative (a), with `j = 0` and `T = []`.
2. Step `src ++ [x]` from (b): `cursor (src ++ [x]) W = cursor src W < |src| + 1`
   [L2.1a item 5]. Also `W < nu src < nuStep (nu src) x = nu (src ++ [x])`
   [D2.1a items 7, 2, 4]. So (b) holds.
3. Step `src ++ [x]` from (a), with `j = |W|`. Then `T = []` and `nu src = W`. By
   [L2.1a items 4, 7], `cursor (src ++ [x]) W = |src| + cursor [x] [] = |src|`. Also
   `W < nuStep W x` [D2.1a item 7 with `Noninc W`]. So (b) holds.
4. Step `src ++ [x]` from (a), with `j < |W|`. Put `y = W[j]`. Then `W.drop j = y :: V` with
   `Noninc (y :: V)` (`List.Pairwise.drop`). By [L2.1a item 4],
   `cursor (src ++ [x]) W = |src| + cursor [x] (y :: V)`. Every letter of `W.take j` is
   `≥ y` (`Noninc W`). By [D2.1a item 3] applied to the nonincreasing `nu src`,
   `nu (src ++ [x]) = (W.take j ++ T).takeWhile (x ≤ ·) ++ [x]`.
   - `x < y`: `cursor [x] (y :: V) = 1` and `qcursor = 0` [L2.1a item 6]. So the run is
     exhausted and the new `j` is `j`. The `takeWhile` keeps all of `W.take j`, since its
     letters are `≥ y > x`, and then `T.takeWhile (x ≤ ·)`. Put
     `T' = T.takeWhile (x ≤ ·) ++ [x]`: it is nonincreasing, and its letters are `< y`. So (a)
     holds.
   - `x = y`: `cursor = 1` and `qcursor = 1` [L2.1a item 6], so the new `j` is `j + 1`. All of
     `T` is dropped (its letters are `< y = x`), and all of `W.take j` is kept. The result is
     `W.take j ++ [y] = W.take (j+1)` (`List.take_succ`). (a) holds with `T' = []`.
   - `y < x`: `cursor [x] (y :: V) = 0` [L2.1a item 6], so the new cursor is `|src| <
     |src| + 1`. The letters of `T` are `< y < x`, so the `takeWhile` stops inside `W.take j`,
     at the length `j' ≤ j` of `(W.take j).takeWhile (x ≤ ·)`, and `W[j'] < x`: if `j' < j` by
     the stop, and if `j' = j` because `W[j] = y < x`. So
     `nu (src ++ [x]) = W.take j' ++ [x] > W` at position `j'`. (b) holds.
5. Conclusion from the alternative for `src`:
   - Under (a): if `T = []`, `nu src = W.take j ≤ W` (a prefix). If `T = t :: _`, then
     `j < |W|` and `t < W[j]`, so `nu src < W` at position `j`. Either way the cursor is
     `|src|` and `nu src ≤ W`.
   - Under (b): the cursor is `< |src|`, and `¬ nu src ≤ W`.

**Uses:** D2.1a, L2.1a.

**Lean:** `Scan.cursor_eq_length_iff`. File `Scan/Words.lean`.

**Difficulty:** M. About 150 LOC, mostly list-position arguments.

**Testable:** yes. Exhaustive over all pairs of words of length `≤ 4` over `{0,1,2}` with
nonincreasing query (0 failures).

### L2.1c Query reduction   (paper: new; txt:174-176)

**Fidelity:** new.

**Statement.**
1. `cursor_delete`: for `x < y`, `cursor src (A ++ x :: y :: B) = cursor src (A ++ y :: B)`.
2. `cursor_nu` (spine): `cursor ks (nu W) = cursor ks W`.

**Proof.**
1. Item 1 is a nested induction: outer on `A`, inner on `src`, following the equations of
   `cursor`.
   - Base `A = []`, induction on `src`. The source `[]` gives `0 = 0`. For `s :: ss`, compare
     `s` with `x`:
     - `s < x`: then `s < y`; both sides are `cursor ss (·) + 1`; apply the inner induction
       hypothesis.
     - `s = x`: the left side is `cursor ss (y :: B) + 1`. Since `s = x < y`, the right side
       is the same.
     - `s > x`: the left side is `cursor (s :: ss) (y :: B)`, which is the right side.
   - Step `A = a :: A'`, at `src = s :: ss`, by the branch on `(s, a)`:
     - `s < a`: inner induction hypothesis (same query, shorter source);
     - `s = a` and `s > a`: outer induction hypothesis at `A'`.
2. Item 2: right induction on `W`, proving for every continuation `C` that
   `cursor src (nu W ++ C) = cursor src (W ++ C)`.
   - Base: `nu [] = []`.
   - Step `W ++ [y]`: `nu W = T ++ D` with `nuStep (nu W) y = T ++ [y]`, where every letter
     of `D` is `< y` [D2.1a items 1, 3]. Then
     `cursor src (T ++ D ++ y :: C) = cursor src (T ++ y :: C)`, by `|D|` applications of
     item 1 that delete the last letter of `D`, which is followed by `y` (right induction on
     `D`). Finally apply the induction hypothesis with continuation `y :: C`. Take `C = []`.

**Uses:** D2.1a.

**Lean:** `Scan.cursor_delete`, spine `Scan.cursor_nu`. File `Scan/Words.lean`.

**Difficulty:** S — two short nested inductions (about 80 LOC).

**Testable:** yes. `cursor_delete` over all `A, B` of length `≤ 2`, `src` of length `≤ 3` and
`x, y < 3`; `cursor_nu` over all pairs of words of length `≤ 4` (0 failures).

### L2.1 Scan boundary lemma   (paper: txt:165-176)

**Fidelity:** as in paper.

**Statement.** For a reduced (`Noninc`) query `W`:
1. `cursor_spec` (spine):
   `cutQuery ks (cursor ks W) ≤ W ∧ (cursor ks W < |ks| → W < cutQuery ks (cursor ks W + 1))`.
   This is `B_c(i-1) ≤ W < B_c(i)`, or `i = m` when `B_c(m-1) ≤ W`.
2. `cursor_unique`: if `i ≤ |ks|`, `cutQuery ks i ≤ W` and
   `(i < |ks| → W < cutQuery ks (i+1))`, then `cursor ks W = i`.
3. `cursor_le_of_lt_cutQuery`: `v < |ks| → W < cutQuery ks (v+1) → cursor ks W ≤ v`.
4. `le_cursor_of_cutQuery_le`: `v ≤ |ks| → cutQuery ks v ≤ W → v ≤ cursor ks W`.
5. `cursor_mono`: for `Noninc W`, `Noninc Z` and `W ≤ Z`, `cursor ks W ≤ cursor ks Z`.
6. `cursor_nu` (spine, L2.1c).

**Proof.** Put `c = cursor ks W`.
1. `c ≤ |ks|` [L2.1a item 1].
2. `cursor (ks.take c) W = min c c = c = |ks.take c|` [L2.1a item 2].
3. Hence `cutQuery ks c = nu (ks.take c) ≤ W` [L2.1b].
4. If `c < |ks|`: `cursor (ks.take (c+1)) W = c ≠ c + 1` [L2.1a item 2]. So
   `¬ cutQuery ks (c+1) ≤ W` [L2.1b], that is `W < cutQuery ks (c+1)`. This proves item 1.
5. Item 2: suppose `i < c`. Then `cutQuery ks (i+1) ≤ cutQuery ks c ≤ W` [D2.1 item 4, step 3],
   contradicting the upper bound at `i`. Suppose `c < i`. Then `c < |ks|` and
   `W < cutQuery ks (c+1) ≤ cutQuery ks i ≤ W` [step 4, D2.1 item 4], a contradiction.
6. Item 3: if `c ≥ v + 1`, then `cutQuery ks (v+1) ≤ cutQuery ks c ≤ W` [D2.1 item 4, step 3],
   contradicting `W < cutQuery ks (v+1)`.
7. Item 4: `cursor (ks.take v) W = v` by [L2.1b] (with `nu (ks.take v) = cutQuery ks v ≤ W`),
   and it equals `min v c` [L2.1a item 2]. So `v ≤ c`.
8. Item 5: let `j = cursor ks W` and `i = cursor ks Z`, and suppose `i < j`. Then `i < |ks|`
   and `Z < cutQuery ks (i+1) ≤ cutQuery ks j ≤ W ≤ Z`, by item 1 at `Z`, [D2.1 item 4] and
   item 1 at `W`. A contradiction.

**Uses:** L2.1a, L2.1b, L2.1c, D2.1, D2.1a.

**Lean:** spine `Scan.cursor_spec` (item 6 is stated and owned by L2.1c); U1 `Scan.cursor_unique`,
`Scan.cursor_le_of_lt_cutQuery`, `Scan.le_cursor_of_cutQuery_le`, `Scan.cursor_mono`. File
`Scan/Words.lean`.

**Difficulty:** S — short consequences of L2.1a and L2.1b.

**Testable:** yes. `cursor_spec`, `cursor_nu`, `cursor_take` and `cursor_eq_length_iff`
exhaustively over the 14,641 pairs of words of length `≤ 4` over `{0,1,2}`, and `cursor_mono`
over all nonincreasing pairs (0 failures).

### L2.3b Word observation   (paper: txt:211-213)

**Fidelity:** as in paper.

**Statement.**
1. `nu_append_lt`: if `Noninc W`, `W < nu (P ++ [K])` and `J < K`, then
   `nu (W ++ [J]) < nu (P ++ [K])`.
2. `boundary_lt_of_cut`: if `k < |ksc|`, `u < |ksa|`, `cutQuery ksc k < boundary ksa u` and
   `ksc[k] < ksa[u]`, then `boundary ksc k < boundary ksa u`.

**Proof.**
1. `nu (W ++ [J]) = W' ++ [J]` with `W' = W.takeWhile (J ≤ ·)`, a prefix of `W`
   [D2.1a items 2, 5, 3]. Put `q = |W'|`.
2. `D := nu (P ++ [K]) = nuStep (nu P) K`. All letters of `D` are `≥ K > J`
   [D2.1a items 2, 8, 4].
3. Case on the order `W < D`.
   - (i) `W` is a proper prefix of `D`. Then `W'` is a prefix of `D` with `q < |D|`, and
     `J < D[q]` (step 2). So `W' ++ [J] < D`.
   - (ii) There is a first difference at `p < min(|W|, |D|)`, with `W[p] < D[p]`.
     - If `q ≤ p`: `W' = D.take q` and `J < D[q]`, so `W' ++ [J] < D`.
     - If `q > p`: `W' ++ [J]` agrees with `W` through position `p`, so it agrees with `D`
       before `p` and has `W[p] < D[p]` at `p`.
4. Item 2:
   - `boundary ksc k = nu (ksc.take k ++ [ksc[k]]) = nu (cutQuery ksc k ++ [ksc[k]])`
     [D2.1a item 6].
   - `boundary ksa u = nu (ksa.take u ++ [ksa[u]])`.
   - `cutQuery ksc k` is `Noninc` [D2.1a item 10]. Apply item 1.

**Uses:** D2.1a.

**Lean:** `Scan.nu_append_lt`, `Scan.boundary_lt_of_cut`. File `Scan/Words.lean`.

**Difficulty:** S — one case analysis on the lexicographic order.

**Testable:** yes. Exhaustive over `P` of length `≤ 3`, nonincreasing `W` of length `≤ 3`, and
`K, J < 3` (0 failures).

### L2.5 Exact trace facts (1)–(3)   (paper: txt:237-245)

**Fidelity:** as in paper.

**Statement.**
1. `trace_map`† (1): if `f : α → β` is `StrictMono` between linear orders, then
   `trace (src.map f) (qry.map f) = trace src qry`. Corollary `cursor_map`.
2. `trace_cap_top`† (2): for `[LinearOrder β] [OrderTop β]`, `src ≠ []` and
   `cursor src qry < |src|`, `trace (src.dropLast ++ [⊤]) qry = trace src qry`.
3. `trace_agree`† (3): assume
   - `src₁.take u = src₂.take u`;
   - `u < |src₁|` and `u < |src₂|`;
   - `∀ y ∈ qry, compare src₁[u] y = compare src₂[u] y`;
   - `cursor src₁ qry ≤ u`.

   Then `trace src₁ qry = trace src₂ qry`.

**Proof.**
1. (1): functional induction on `traceFrom` (generalizing the state `(i, j)`). The branch at
   `(x, y)` is decided by `x < y` and `x = y`, which `f` preserves and reflects
   (`StrictMono.lt_iff_lt`, `StrictMono.injective`). `cursor_map` follows by
   [L2.5a item 2].
2. (2): write `src = S ++ [s]` (`List.dropLast_append_getLast`). Prove, for every prefix list
   `A` and query `qry`, that `traceFrom i j (A ++ [s]) qry = traceFrom i j (A ++ [⊤]) qry`,
   provided the run of `A ++ [s]` is not exhausted. The induction follows `traceFrom`.
   - While the source part is `a :: A'`, the comparison reads `a` in both runs, so the same
     branch is taken. Non-exhaustion passes to the recursive call by the cursor equations.
   - When the source part is `[s]` against `y :: ys`: if `s ≤ y`, the run consumes `s` and is
     exhausted, contradicting the hypothesis. So `y < s ≤ ⊤`. Hence `⊤ > y` too, and both runs
     take the query-only branch.
   - When the query is `[]`, both traces are `[(i, j)]`.
3. (3): induction following `traceFrom` of `src₁`, with the invariant that the source cursor
   is `≤ u`.
   - At positions `< u` both sources show the same letter (`hpre`), so the same branch is
     taken.
   - At position `u`, the branch is decided by `compare src_k[u] y_j`, equal for `k = 1, 2`
     (`hsign`, with `compare_lt_iff_lt` and `compare_eq_iff_eq`).
<!-- U1-verify: changed -->
   - A branch `x_u ≤ y_j` would move the source cursor to `u + 1`, contradicting `hrun`: the
     final cursor of a run is at least every cursor it visits [L2.5a item 3]. So from `(u, j)` only
     query-only moves occur, identical in both runs, until the query ends.
   - `hu₂` guarantees that `src₂` has a letter at `u`.

**Uses:** L2.5a.

**Lean:** `Scan.trace_map`, `Scan.cursor_map`, `Scan.trace_cap_top`, `Scan.trace_agree`. File
`Scan/Words.lean`.

**Difficulty:** M. Three inductions over the two-cursor recursion, about 250 LOC.

**Testable:** yes. Exhaustive (0 failures):
- (1) with `f x = 2x + 1` over all pairs of words of length `≤ 4`;
- (2) in `WithTop Nat`;
- (3) over all `src₁, src₂` of length `≤ 4`, queries of length `≤ 3` and `u < 4`.

### L2.5b The generic cursor is the locked `scanCount`   (paper: new)

**Fidelity:** new.

**Statement.** `cursor_eq_scanCount`†: `scanCount xs ys = cursor xs ys` for `xs ys : List Key`.

**Proof.**
1. Functional induction on `scanCount` (`scanCount.induct`). At `x :: xs`, `y :: ys`:
   - `keyCmp x y = .lt ↔ x < y` (`Key.lt_iff_keyCmp`, D1.4);
   - `keyCmp x y = .eq ↔ x = y` [D1.1a items 2, 3 with D1.4a item 2];
   - otherwise `.gt`.

   These are exactly the branches `if x < y … else if x = y … else` of `cursor`.

**Uses:** D1.1a, D1.4a, D1.4.

**Lean:** `Scan.cursor_eq_scanCount`. File `Scan/Words.lean`.

**Difficulty:** S — one functional induction.

**Testable:** yes, through the agreement tests of D1.6c.

---

## Part E — Compact words and safe prefixes

### N1.2 The generic compact word   (paper: new)

**Fidelity:** new. It is S-6 engineering: one word definition for forests and keys.

**Statement.**
1. `GAtom α := Nat ×ₗ Nat ×ₗ WithBot α`.
2. `gwordAt e` is defined as `wordAt` (txt:143-146), with label `⊥` in the empty-column atom:
   - an empty column gives `(2e, 0, ⊥)`;
   - a first entry gives `(2e, 1, ↑p)`, followed by the height's word at depth `e + 1`;
   - a later entry gives `(2e+1, 0, ↑p)`, followed by the height's word at depth `e + 1`.

   `gword := gwordAt 0`.
3. `GAtom.map f` relabels the third coordinate by `WithBot.map f`.
4. `toGAtom : WordAtom → GAtom Nat` sends `(a, b, p)` to `(a, b, ⊥)` if `a` is even and
   `b = 0`, and to `(a, b, ↑p)` otherwise.
5. `WordAtom.WF A`: `A` has one of the shapes `(2e, 0, 0)`, `(2e, 1, p)` or `(2e+1, 0, p)`.
6. Laws:
   - `gword_map`: `gword (t.map f) = (gword t).map (GAtom.map f)`;
   - `gword_eq_map_word`: `gword E = (word E).map toGAtom`;
   - `mu_eq_length_gword`;
   - `word_wf`: every atom of a word is well formed;
   - `toGAtom_strictMonoOn`: `toGAtom` is strictly increasing on `{A | A.WF}`.

**Proof.**
1. `gword_map`: mutual induction over `gwordAt`/`gwordCols`/`gwordCol`/`gwordLater` against
   `Tree.map`/`mapCols`/`mapCol`. Every atom's label is relabelled, and `⊥ ↦ ⊥`.
2. `gword_eq_map_word`: mutual induction against `wordAt`/`wordCols`/`wordCol`/`wordLater`
   (spine).
   - `(2e, 0, 0)` maps to `(2e, 0, ⊥)`: `2e` is even and the marker is `0`.
   - `(2e, 1, p)` maps to `(2e, 1, ↑p)`: the marker is `1`.
   - `(2e+1, 0, p)` maps to `(2e+1, 0, ↑p)`: `2e+1` is odd.
3. `mu_eq_length_gword`: `List.length_map`.
4. `word_wf`: the same mutual induction; every emitted atom has one of the three shapes.
5. `toGAtom_strictMonoOn`: let `A < B` be well formed.
   - If their first two coordinates differ, `toGAtom` keeps them, so the lexicographic order
     is decided there.
   - If they agree: with even first coordinate and marker `0`, both are `(2e, 0, 0)`, so
     `A = B`, a contradiction. Otherwise both labels are `↑p_A` and `↑p_B` with `p_A < p_B`
     (`WithBot.coe_lt_coe`).

**Uses:** none.

**Lean:** `Scan.GAtom`, `Scan.gwordAt`, `Scan.gwordCols`, `Scan.gwordCol`, `Scan.gwordLater`,
`Scan.gword`, `Scan.GAtom.map`, `Scan.toGAtom`, `Scan.WordAtom.WF`, `Scan.gword_map`,
`Scan.gword_eq_map_word`, `Scan.mu_eq_length_gword`, `Scan.word_wf`,
`Scan.toGAtom_strictMonoOn`. File `Scan/CompactWord.lean`.

**Difficulty:** S — mutual inductions that only track atom shapes.

**Testable:** yes. `gword_eq_map_word`, `mu_eq_length_gword` and `gword_shift` checked on 1,000
forests (0 failures).

### N1.3 List order lemmas   (paper: new)

**Fidelity:** new.

**Statement.**
1. `list_map_lt_iff`: suppose `f` is `StrictMonoOn S` and every letter of `l₁` and `l₂` lies in
   `S`. Then `l₁.map f < l₂.map f ↔ l₁ < l₂`.
2. `list_lt_of_take_eq`: suppose `|Y| < |X₁|` and
   `X₁.take (|Y|+1) = X₂.take (|Y|+1)`. Then `(X₁ < Y ↔ X₂ < Y) ∧ X₁ ≠ Y ∧ X₂ ≠ Y`.

**Proof.**
1. Item 1: induction on `l₁, l₂` along the constructors of `List.Lex` (`nil`, `cons`, `rel`).
   On `S`, `x = y ↔ f x = f y` (`StrictMonoOn.injOn`) and `x < y ↔ f x < f y`
   (`StrictMonoOn.lt_iff_lt`).
2. Item 2:
   - First prove `X < Y ↔ X.take (|Y|+1) < Y` for every `X`, by induction on `Y` along
     `List.Lex`. The first difference of `X` and `Y` occurs at an index `≤ |Y|`, or `Y` is a
     proper prefix of `X`.
   - Rewrite both sides with `h`.
   - `X_k ≠ Y`, since `|X_k.take (|Y|+1)| = |Y| + 1`. For `X₂` this length follows from `h`.

**Uses:** none.

**Lean:** `Scan.list_map_lt_iff`, `Scan.list_lt_of_take_eq`. File `Scan/CompactWord.lean`.

**Difficulty:** S — standard `List.Lex` inductions.

**Testable:** yes (small lists by `decide`).

### C1.8a The generic word is an order embedding   (paper: new; txt:147-151)

**Fidelity:** new. This is the argument of txt:147-151, stated with explicit continuations.

**Statement.** For `[LinearOrder α]`:
1. `gwordAt_fst_ge`: every atom of `gwordAt e t` has first coordinate `≥ 2e`.
2. `gwordAt_append_lt_iff`: suppose the first atoms of the continuations `xs` and `ys` (if any)
   have first coordinate `< 2e`. Then
   `gwordAt e s ++ xs < gwordAt e t ++ ys ↔ Tree.cmp compare s t = .lt ∨ (s = t ∧ xs < ys)`.
3. `gwordAt_append_inj`: under the same hypotheses,
   `gwordAt e s ++ xs = gwordAt e t ++ ys → s = t ∧ xs = ys`.
4. `gword_lt_iff`: `gword s < gword t ↔ Tree.cmp compare s t = .lt`. Also `gword_injective`.

**Proof.**
1. Item 1: mutual induction. Atoms at depth `e` have first coordinate `2e` or `2e+1`; atoms of
   heights have `≥ 2(e+1)`.
2. Items 2 and 3 are proved simultaneously by mutual structural induction on the left tree,
   generalizing the right tree and both continuations. There are three auxiliary statements,
   matching `cmpCols`, `cmpCol` and the tail recursion of `cmpCol`.
   - **Cols(e).** Hypothesis: continuation heads `< 2e`. Conclusion:
     `gwordCols e a ++ xs < gwordCols e b ++ ys ↔ cmpCols compare a b = .lt ∨
     (a = b ∧ xs < ys)`.
   - **Col(e).** Hypothesis: continuation heads `< 2e + 1`. Same form, with `gwordCol` and
     `cmpCol`. After a column comes either a column atom `(2e, …)` or the outer continuation.
   - **Later(e).** Hypothesis: continuation heads `< 2e + 1`. Same form, with `gwordLater`
     and `cmpCol` on the tail entry lists.

   Steps:
   - Cols, `[]` against `[]`: reduces to `xs < ys`.
   - Cols, `[]` against `b₀ :: _`: the right side starts with an atom of first coordinate
     `2e`, the left continuation's head is `< 2e` or absent, so the left side is smaller. And
     `cmpCols [] (_ :: _) = .lt`. The reversed case is symmetric (both sides false).
   - Cols, `a₀ :: as` against `b₀ :: bs`: apply Col(e) to `a₀, b₀` with continuations
     `gwordCols e as ++ xs` and `gwordCols e bs ++ ys`. Their heads are `2e` or `< 2e`, so
     `< 2e + 1`. Then Cols(e) on `as, bs`. `Ordering.then_eq_lt` matches
     `(cmpCol a₀ b₀).then (cmpCols as bs) = .lt`.
   - Col, `[]` against `[]`: both give `(2e, 0, ⊥)`, then the continuations.
   - Col, `[]` against `(q, k) :: _`: `(2e, 0, ⊥) < (2e, 1, ↑q)` by the marker, and
     `cmpCol [] (_ :: _) = .lt`.
   - Col, `(p, h) :: es` against `(q, k) :: fs`: first atoms `(2e, 1, ↑p)` and `(2e, 1, ↑q)`.
     - If `p ≠ q`, the comparison is decided by `compare p q ≠ .eq`, as in `cmpCol`.
     - If `p = q`, apply the forest statement at depth `e + 1` to `h, k`, with continuations
       `gwordLater e es ++ xs` and `gwordLater e fs ++ ys`. Their heads are `2e + 1` or
       `< 2e + 1`, so `< 2(e+1)`. Then Later(e) on `es, fs`. This matches
       `((compare p q).then (cmp h k)).then (cmpCol es fs)`.
   - Later: the same three cases, with first atoms `(2e+1, 0, ↑p)`. Against `[]`, the
     continuation head is `< 2e + 1` or absent, so `[]` is smaller, as `cmpCol [] (_ :: _)`.
   - Injectivity (item 3) follows the same cases: atoms of different shapes differ.
3. Item 4: `e = 0` and `xs = ys = []` (the head conditions are vacuous); `[] < []` is false.
   `gword_injective` is item 3 with empty continuations.

**Uses:** N1.2, D1.1a (only for the reading of `Tree.cmp`).

**Lean:** `Scan.gwordAt_fst_ge`, `Scan.gwordAt_append_lt_iff`, `Scan.gwordAt_append_inj`,
`Scan.gword_lt_iff`, `Scan.gword_injective`. File `Scan/CompactWord.lean`.

**Difficulty:** M. The nested mutual induction with continuations, about 400 LOC.

**Testable:** yes. Through C1.8 on forests (30,000 pairs). The key form is exercised by
L2.5c (26,343 instances).

### C1.8 The compact word is injective and order-preserving   (paper: txt:143-151)

**Fidelity:** as in paper.

**Statement.** Spine definitions `wordAt`, `word`, `mu`. Spine `word_lt_iff`:
`word E < word F ↔ E < F`. Spine `word_injective`.

**Proof.**
1. `word E < word F ↔ gword E < gword F`: `gword = (word ·).map toGAtom` [N1.2]; all atoms are
   well formed [N1.2 `word_wf`] and `toGAtom` is strictly increasing on them
   [N1.2 `toGAtom_strictMonoOn`]; then [N1.3 item 1].
2. `gword E < gword F ↔ Tree.cmp compare E F = .lt` [C1.8a item 4], which is `E < F`
   (`Forest.lt_iff_cmp`, D1.1).
3. Injectivity: `word E = word F` gives `gword E = gword F` (`congrArg (List.map toGAtom)`),
   and then `E = F` [C1.8a `gword_injective`].

**Uses:** N1.2, N1.3, C1.8a, D1.1.

**Lean:** spine `Scan.word_lt_iff`, `Scan.word_injective`, `Scan.word`, `Scan.mu`. File
`Scan/CompactWord.lean`.

**Difficulty:** S — three-step composition of N1.2, N1.3 and C1.8a.

**Testable:** yes. On 30,000 pairs of forests, `word E < word F ↔ E < F` and
`word E = word F ↔ E = F` (0 failures).

### D1.9a Safe-prefix bookkeeping   (paper: new)

**Fidelity:** new.

**Statement.**
1. `spF k E : Forest × Nat` is a budgeted walk, with `spCols`, `spCol` and `spLater` (mutual,
   structural). It returns the truncated forest and the unused budget.
   - A column is kept only if the budget is positive: its first atom is consumed.
   - An entry is kept only if the budget is positive: its atom is consumed. Its height is
     truncated by the remaining budget.
   - Once the budget reaches `0`, all later context is dropped.
2. `spF_spec e k E`: `wordAt e (spF k E).1 = (wordAt e E).take k` and
   `(spF k E).2 = k - |wordAt e E|`.
3. `word_truncAfter_prefix`: `word (E.truncAfter e) <+: word E`.

**Proof.**
1. Item 2 is proved by mutual induction with the analogous statements for `spCols`, `spCol`
   (which requires `k ≥ 1`) and `spLater`, at depth `e`.
   - `spCols`, `k = 0`: `[] = take 0` with remainder `0`.
   - `spCols`, `col :: rest` with `k ≥ 1`: `spCol` gives word `(colword).take k` and remainder
     `k₁ = k - |colword|`.
     - If `k₁ = 0`, then `k ≤ |colword|`, and `spCols 0 rest = ([], 0)` gives
       `(colword ++ restword).take k`.
     - If `k₁ > 0`, then core `List.take_append`
       (`take k (l₁ ++ l₂) = take k l₁ ++ take (k - |l₁|) l₂`) combines the induction
       hypothesis on `rest`. <!-- U1-verify: changed -->
   - `spCol`, `[]`: the atom `(2e, 0, 0)` and `k ≥ 1`.
   - `spCol`, `(p, h) :: rest`: the atom `(2e, 1, p)`, then the induction hypothesis on `h` at
     depth `e+1` with budget `k-1`, and on `spLater`.
   - `spLater`: like `spCols`, with the entry atom `(2e+1, 0, p)`.
   - A kept entry with remaining budget `0` gets the height `(spF 0 h).1 = ∅`, whose word is
     `[]`.
2. Item 3 is proved by induction on `e.col.path` following `truncAux` [D1.2c], via the bridge.
   - At the last level: `word (cols.take j ++ [col.take (i+1)])` consists of the words of
     columns `0…j-1` and of entries `0…i` of column `j`. This is a prefix, because later
     entries and columns come later in the word (core `List.prefix_append`,
     `List.prefix_append_of_prefix`). <!-- U1-verify: changed -->
   - At a containing level: the kept columns and entries precede the truncated height. That
     height's word is a prefix by the induction hypothesis, and nothing follows it.

**Uses:** D1.2c.

**Lean:** `Scan.spF`, `Scan.spCols`, `Scan.spCol`, `Scan.spLater`, `Scan.spF_spec`,
`Scan.word_truncAfter_prefix`. File `Scan/CompactWord.lean`.
**Integration note:** At integration, SCR-2: these body definitions moved verbatim into `Spine.lean`; they remain U1-owned.

**Difficulty:** M — a four-function mutual induction with budget arithmetic (about 200 LOC).

**Testable:** yes. `word (safePrefixBody E k) = (word E).take k` for every `k ≤ µ(E) + 1` on
3,200 forests, and prefix-ness for every truncation (0 failures).

### D1.9 Safe prefix   (paper: txt:152-153)

**Fidelity:** as in paper.

**Statement.**
1. `safePrefixBody E k := (spF k E).1`, with the bridge `safePrefix_eq_body`.
2. `word_safePrefix` (spine): `word (safePrefix E k) = (word E).take k`.
3. `safePrefix_of_le`: `µ(E) ≤ k → safePrefix E k = E`.
4. `safePrefix_le`: `safePrefix E k ≤ E`.
5. `colAt_safePrefix` ("cannot create an empty internal column", txt:153): every column `col'`
   of a safe prefix at address `c` comes from a column `col` of `E` at `c` with:
   - `|col'| ≤ |col|`;
   - `col' = [] → col = []`;
   - every kept entry keeps its parent, and its height is a safe prefix of the original
     height.
6. `truncAfter_safePrefix` (spine): `e ∈ E.entryAddrs → ∃ k, E.truncAfter e = safePrefix E k`.

**Proof.**
1. Item 2: the bridge and [D1.9a item 2] at `e = 0`.
2. Item 3: item 2 and `List.take_of_length_le` give `word (safePrefix E k) = word E`; then
   `word_injective` [C1.8].
3. Item 4: a prefix of a list is `≤` it in lexicographic order. Then `word_lt_iff` [C1.8] gives
   the strict case, and `word_injective` [C1.8] the equality case.
4. Item 5: induction on `c.path` following `spF`, via the bridge. A kept column is
   `(spCol k col).1`, which starts with the first entry of `col` when `col` is nonempty and is
   `[]` exactly when `col = []`. Kept entries are `(p, (spF k' h).1) = (p, safePrefixBody h k')`.
5. Item 6: put `k := |word (E.truncAfter e)|`. Then
   `word (safePrefix E k) = (word E).take k = word (E.truncAfter e)`, by item 2 and
   [D1.9a item 3] with `List.prefix_iff_eq_take`. Conclude by `word_injective` [C1.8].

**Uses:** D1.9a, C1.8, D1.2c.

**Lean:** `Scan.safePrefixBody`, `Scan.safePrefix_eq_body`, spine `Scan.word_safePrefix`,
`Scan.safePrefix_of_le`, `Scan.safePrefix_le`, `Scan.colAt_safePrefix`, spine
`Scan.truncAfter_safePrefix`. File `Scan/CompactWord.lean`.
**Integration note:** At integration, SCR-2: these body definitions moved verbatim into `Spine.lean`; they remain U1-owned.

**Difficulty:** S — short consequences of D1.9a and C1.8.

**Testable:** yes, with 0 failures:
- `colAt_safePrefix` on every prefix of 600 forests;
- `truncAfter_safePrefix` (some `k ≤ µ(E)`) for every entry of 800 forests.

### L2.5c The sign criterion   (paper: txt:246-249)

**Fidelity:** as in paper. The thresholds `r` (sources) and `t` (query) are arbitrary,
following "owner normalization changes neither atom positions nor word lengths".

**Statement.** `sign_of_agreement`†: suppose `µ(J) < µ(A₁)` and
`(word A₁).take (µ(J)+1) = (word A₂).take (µ(J)+1)`. Then
`keyCmp (relKey r A₁) (relKey t J) = keyCmp (relKey r A₂) (relKey t J)`, and this value is
`≠ .eq`.
<!-- U1-verify: changed -->

`sign_of_agreement_compare`: under the same hypotheses,
`compare (↑(relKey r A₁) : WithTop Key) ↑(relKey t J) =
compare (↑(relKey r A₂) : WithTop Key) ↑(relKey t J)`. This is the sign hypothesis `hsign` of
`trace_agree` [L2.5 (3)] at `α = WithTop Key`, for the query key `↑(relKey t J)`. It is the
form in which txt:246-249 verifies the sign hypothesis of trace fact (3) in a key system.

**Proof.**
1. Every key comparison is a comparison of generic words. `keyCmp K K' = Tree.cmp compare K K'`
   over `Lex (Bool × Nat)` [D1.4a item 1]. By [C1.8a item 4] and [D1.1a items 2, 3], it is
   `.lt`, `.eq` or `.gt` exactly when `gword K <`, `=` or `>` `gword K'`.
2. `gword (relKey r A) = (word A).map (GAtom.map (relLabel r) ∘ toGAtom)`
   [D1.4a item 3, N1.2 `gword_map`, `gword_eq_map_word`]. In particular
   `|gword (relKey t J)| = µ(J)`.
3. From the hypothesis and `List.map_take`:
   `(gword (relKey r A₁)).take (µJ+1) = (gword (relKey r A₂)).take (µJ+1)`.
4. Apply [N1.3 item 2] with `X_k = gword (relKey r A_k)` and `Y = gword (relKey t J)`; the
   length hypothesis comes from step 2. This gives `(X₁ < Y ↔ X₂ < Y)`, `X₁ ≠ Y` and `X₂ ≠ Y`.
5. By step 1, both comparisons are `≠ .eq` and they agree on `.lt`, so they are equal.
<!-- U1-verify: changed -->
6. `sign_of_agreement_compare`: for `K, K' : Key`,
   `compare (↑K : WithTop Key) ↑K' = compare K K'`. This follows from Mathlib `cmp_eq_compare`
   (both sides) and `StrictMono.cmp_map_eq` with `WithTop.coe_strictMono`. Then
   `compare K K' = keyCmp K K'` [D1.4 item 5]. Conclude with the first conjunct of the main
   statement.

**Uses:** N1.2, N1.3, C1.8a, D1.4a, D1.1a, D1.4.

**Lean:** `Scan.sign_of_agreement`, `Scan.sign_of_agreement_compare`. File
`Scan/CompactWord.lean`.

**Difficulty:** S — composition of C1.8a, N1.2 and N1.3.

**Testable:** yes. 26,343 instances from heights of standard expressions, with
`r ∈ {1,2,3}` and `t ∈ {2,3,4}` (0 failures).

---

## Part F — Shifts, the operation, seeds

### D1.5 Shifts T_{r,d} and replacement A_{r,d,ℓ,Z}   (paper: txt:86-94)

**Fidelity:** as in paper.

**Statement.**
1. `shift r d F := Tree.map (shiftVal r d) F` (spine), with the locked `shiftVal`.
2. `Hole := {outer, depth}` and `Hole.fill h r d Z := replaceAt r d Z h.depth h.outer`
   (spine, locked `replaceAt`).
   - At depth `0` and `F ≠ ∅` this is `T_{r,d}(F[:-1]) ⌢ Z` (txt:89-91).
   - At positive depth only the last entry of the last column is followed (`mapLast`), and the
     other heights are shifted (txt:92-93).

Note: on `F = ∅` at depth 0, `replaceAt` returns `∅`, while txt:90 would give `Z`. Every use in
this unit and in `paperOp` fills a hole on the route, whose forests are nonempty [D1.6b
`stopData_spec`, D1.2d], so the divergence is never reached.

**Proof.** Definitions.

**Uses:** none.

**Lean:** spine `Scan.shift`, `Scan.Hole`, `Scan.Hole.fill`. File `Scan/Step.lean`.

**Difficulty:** S — spine definitions.

**Testable:** n/a.

### D1.5a Shift and hole laws   (paper: new, S-6)

**Fidelity:** new. These are the "proved fill/shift law" of S-6.

**Statement.**
1. `shiftVal_zero`, `shift_zero : shift r 0 F = F`.
2. `shift_add : shift r d (shift r d' F) = shift r (d + d') F`.
3. `mapLast_eq : mapLast f g l = l.dropLast.map f ++ (l.getLast?.map g).toList`.
4. `Hole.put h Z := replaceAt 0 0 Z h.depth h.outer`, the unshifted placement.
5. `Hole.fill_eq_put : h.fill r d Z = (⟨shift r d h.outer, h.depth⟩ : Hole).put Z`.
6. `Hole.fill_zero : h.fill 0 0 Z = h.put Z`.
7. `word_put` (`h.depth < |routeCols h.outer|`):
   `word (h.put Z) = word (h.put ∅) ++ wordAt h.depth Z`.
8. `gword_shift : gword (shift r d F) = (gword F).map (GAtom.map (shiftVal r d))`.

**Proof.**
1. Item 1: unfold `shiftVal` (both branches give `p`). `Tree.map id = id` by mutual induction.
2. Item 2: `shiftVal r d (shiftVal r d' p) = shiftVal r (d+d') p`, by cases: `p ≥ r` (then
   `p + d' ≥ r`) or `p < r`. Then `Tree.map f ∘ Tree.map g = Tree.map (f ∘ g)` by mutual
   induction.
3. Item 3: induction along the three equations of the locked `mapLast`.
4. Item 5 is proved by induction on `depth` following `replaceAt`.
   - Depth `0`: both sides are `.node (cols.dropLast.map _ ++ Z.cols)`. The right side maps
     `shiftVal 0 0` after `shiftVal r d`, which is `shiftVal r d` (item 1). If `cols = []`,
     both sides are `∅`.
   - Depth `k+1`: rewrite both `mapLast`s with item 3. The last entries are
     `(shiftVal r d p, replaceAt r d Z k h)` and
     `(shiftVal 0 0 (shiftVal r d p), replaceAt 0 0 Z k (shift r d h))`; apply the induction
     hypothesis.
5. Item 6: item 5 and item 1.
6. Item 7: generalize to `wordAt e (h.put Z) = wordAt e (h.put ∅) ++ wordAt (e + h.depth) Z`,
   and induct on `depth`.
   - Depth `0`: `outer.cols ≠ []`, because `routeCols` is nonempty. Then `wordCols` over an
     append (induction on the column list) and item 1.
   - Depth `k+1`: by [D1.2d] the last column is nonempty, and the route continues into the
     height of its last entry. That height's word is the last part of the forest's word: in
     `wordCol`/`wordLater` it follows the entry's atom, and no later entry or column follows.
     Apply the induction hypothesis to that height at depth `e + 1`.
7. Item 8: [N1.2 `gword_map`].

**Uses:** D1.5, D1.2d, N1.2.

**Lean:** `Scan.shiftVal_zero`, `Scan.shift_zero`, `Scan.shift_add`, `Scan.mapLast_eq`,
`Scan.Hole.put`, `Scan.Hole.fill_eq_put`, `Scan.Hole.fill_zero`, `Scan.word_put`,
`Scan.gword_shift`. File `Scan/Step.lean`.

**Difficulty:** M. `word_put` is the only nontrivial item.

**Testable:** yes. `fill_eq_put` (with `r = 1`, `d = 2`, `Z = seed 2`) and `word_put` (with
`Z = seed 3`) at every route depth of 800 forests (0 failures).

### D1.6 The fundamental operation E[n]   (paper: txt:95-137)

**Fidelity:** repaired (G-001). The paper's `E[n]` is partial. `paperOp` returns `none`
exactly in these cases:
- on `∅` (txt:96);
- where the route is stuck: a forest without columns, or an empty last column below depth 0
  (X-02);
- where the root is not visible;
- on owner-root exhaustion with `n ≥ 1` (txt:129).

Everything else is §1.2 verbatim.

**Statement** (real bodies; the precise definition is the Lean text):
1. Route. `stopF π F`, with `stopCols` and `stopCol` (mutual, structural): follow the last
   column, then the last entry, of the forest at address prefix `π`.
   - At an entry with height `.node []`, stop with:
     - `depth = |π|`;
     - `col = ⟨π, ci⟩`, where `ci` is the last column index;
     - `t = col.num 0`;
     - `r` = the entry's parent;
     - `Q` = the entries before it.
   - At an entry with a nonempty height, continue with `π ++ [(ci, ei)]`.
   - A forest without columns, or an empty last column, gives `none`.

   `stopDataBody E := stopF [] E`. This is txt:98-104; `t = Σ_{i≤ℓ}|E_i| - 1` holds by
   D1.6c item 5.
2. `specialStop sd := 0 < depth ∧ Q = [] ∧ r + col.col + 1 = t`. Here `|F_ℓ| = col.col + 1`,
   so the last conjunct is `r = t - |F_ℓ|`, the direct owner's number (txt:105).
3. `stepKindBody E`:
   - `none` on `∅`;
   - `deletion` if the last outer column is empty (txt:96-97);
   - `special` if the stop is special;
   - `ordinary` if the stop is not special and `col.resolve 0 r` is `some`;
   - `none` otherwise.

   The special test precedes the root lookup, as txt:105 precedes txt:113.
4. `rootDataBody E`, defined for ordinary steps, records:
   - the visible root `o = ⟨π_j, i⟩`;
   - `layer = |o.path|` and `idx = o.col`;
   - `owner = (o.col + 1 = |F_j|)`;
   - `cursor`: the raw scan of the root keys `h_r(H_i)` against the query keys `h_t(J)`
     (txt:113-124).
5. `ordStep sd rd F U k Z` is one pass of txt:125-131, with `d = t - r`.
   - Head: `T_{r,(k-1)d}(Q)` (`Tree.mapCol (shiftVal r ((k-1)d))`), then the entries of `U`
     with heights `T_{r,kd}`.
   - Body case (`owner = false`): the forest is the head followed by the columns of
     `Hole.fill ⟨F[i+1:], ℓ - j⟩ r (kd) Z`.
   - Owner case: the last restored height is `Hole.fill ⟨H, ℓ - j - 1⟩ r (kd) Z`, and the
     forest is the head alone.

   `ordLoop step n Z` runs `k = n, …, 1`. `ordZ E sd rd n := ordLoop (ordStep …) n ∅`, with
   `U = R.drop cursor`.
6. `specialOut E sd n`: with `col = P ⌢ [(p, F_ℓ)]` the owner column, the result is
   `Hole.fill ⟨E, ℓ - 1⟩ 0 0 (.node [P ⌢ (p, F_ℓ[:-1])^{n+ε}])`, where `ε = 1` iff `P = []`
   (txt:107-111).
7. `ordinaryOut E sd rd n`: `none` iff `owner ∧ n ≠ 0 ∧ R.drop cursor = []`; otherwise
   `Hole.fill ⟨E, ℓ⟩ 0 0 (ordZ E sd rd n)` (txt:132-133).
8. `paperOpBody`: dispatch on `stepKindBody`. Bridges: `stopData_eq_body`,
   `stepKind_eq_body`, `rootData_eq_body`, `paperOp_eq_body`.

**Proof.** Definitions.

**Uses:** D1.2a, D1.4, D1.5, D2.1 (the generic `cursor`).

**Lean:** `Scan.stopF`, `Scan.stopCols`, `Scan.stopCol`, `Scan.stopDataBody`,
`Scan.specialStop`, `Scan.stepKindBody`, `Scan.rootDataBody`, `Scan.ordStep`,
`Scan.ordLoop`, `Scan.ordZ`, `Scan.specialOut`, `Scan.ordinaryOut`, `Scan.paperOpBody`,
`Scan.stopData_eq_body`, `Scan.stepKind_eq_body`, `Scan.rootData_eq_body`,
`Scan.paperOp_eq_body`. File `Scan/Step.lean`.
**Integration note:** At integration, SCR-2: these body definitions moved verbatim into `Spine.lean`; they remain U1-owned.

**Difficulty:** M. About 150 LOC; already written.

**Testable:** yes, with 0 mismatches:
- `paperOpBody E n = expand E n` on the nonempty forests among 3,200 V∧I forests (standard and
  random), for `n < 4`: 12,524 operations;
- on the 2,334 of 6,000 raw forests (3,066 of the 6,000 outside V∧I) whose route stops, under
  the hypotheses of D1.6c items 12–13.

### D1.6b Branch data specifications   (paper: new)

**Fidelity:** new. These are the branch facts consumed by U2, U3 and U5.

**Statement.**
1. `stopData_spec`†: if `stopData E = some sd`, then:
   - `E.colAt sd.col = some (sd.Q ++ [(sd.r, ∅)])`;
   - `sd.depth = |sd.col.path|`;
   - `sd.t = sd.col.num 0`;
   - `sd.col ∈ routeCols E`, `(routeCols E).getLast? = some sd.col`, and
     `|routeCols E| = sd.depth + 1`.
2. `stopData_isSome` (`CondI E`, last outer column `col ≠ []`): `(stopData E).isSome`.
3. `stopData_eq_none_of_lastCol`: `stopData E = none` on `∅` and on an empty last outer column.
4. Branch characterizations:
   - `stepKind_deletion_iff`: `stepKind E = some .deletion ↔ E.cols.getLast? = some []`;
   - `stepKind_special_iff`: special iff some `sd` has `stopData E = some sd` and
     `specialStop sd = true`;
   - `stepKind_ordinary_iff`: ordinary iff some `sd, o` have `stopData E = some sd`,
     `specialStop sd = false` and `sd.col.resolve 0 sd.r = some o`.
5. `rootData_spec`†: if `stopData E = some sd` and `rootData E = some rd`, then:
   - `sd.col.resolve 0 sd.r = some rd.col`;
   - `rd.layer = |rd.col.path|` and `rd.idx = rd.col.col`;
   - `rd.col.num 0 = sd.r < sd.t`;
   - `rd.col ∈ E.colAddrs`;
   - `rd.cursor = cursor (rootKeys E rd) (queryKeys sd)`;
   - `rd.owner ↔` the root column is the last column of its forest.
6. `rootData_owner_iff`: `rd.owner ↔ ∃ u, ⟨rd.col, u⟩.Contains sd.col ∧ u + 1 = |R|`.
7. `rootData_layer_lt` (owner case): `rd.layer < sd.depth`. `rootData_layer_le`:
   `rd.layer ≤ sd.depth`.
8. `ownerEntry_spec` (special step, `sd.ownerEntry = some oe`):
   - `oe.Contains sd.col` and `oe.heightPath = sd.col.path`;
   - `oe.col.num 0 = sd.r`;
   - `oe` is the last entry of its column, and its height `F_ℓ` ends in the column
     `[(sd.r, ∅)]`.
9. Outputs:
   - `paperOp_deletion`;
   - `paperOp_special`† and `paperOp_ordinary`†: the outputs of D1.6 items 6 and 7;
   - `paperOp_ordinary_zero`: `paperOp E 0 = some (Hole.put ⟨E, ℓ⟩ ∅)`.

**Proof.**
1. Item 1 is proved by induction along `stopF`/`stopCols`/`stopCol` (via the bridge), with this
   invariant: at a call `stopCols π ci cols`, `cols` is the list of columns of
   `E.forestAt π`, from index `ci` on.
   - `stopCols` walks to the last column, so `col = ⟨π, |F| - 1⟩`.
   - `stopCol` walks to the last entry, accumulating `Q = col.dropLast`.
   - The stop happens at `.node [] = Tree.empty`.
   - Each recursion appends the step `(|F| - 1, |col| - 1) = F.lastStep?`, which gives
     `IsRoutePath`.
   - The route statements then follow from [D1.2d], and `t = num` holds by construction.
2. Item 2 is proved by induction along `stopF`. Depth 0 uses `hlast` and `hne`. A recursion
   enters a nonempty height `G` of an entry of `E` [D1.2b item 10]. By `CondI` [D1.3], every
   column of `G` is nonempty, so `stopCol` never meets `[]`.
3. Item 3: `stopCols [] = none`, and `stopCol [] = none` on the last column.
4. Item 4: unfold `stepKindBody` through the bridges. A stop forces a nonempty last outer
   column (item 3, contrapositive).
5. Item 5: unfold `rootDataBody`.
   - `num = r` and `r < t` follow from [D1.2b items 5, 2] and item 1.
   - `rd.col ∈ colAddrs`: `o.path` is a prefix of `sd.col.path`, so `forestAt o.path` exists
     [D1.2b `forestAt_append`]; `o.col ≤` the last index on the route [D1.2d]; then
     [D1.2b item 10].
   - The cursor equation unfolds `rootKeys`/`queryKeys`.
6. Item 6: `o` is on the stack of `sd.col` [D1.2b item 2].
   - At a containing level `k < ℓ`: `o.col ≤ c_k = |F_k| - 1` (route, [D1.2d]). So `owner ↔
     o.col = c_k ↔ o` contains `sd.col`, with entry index `c.path[k].2`, the last entry.
   - At the own level: `o.col < sd.col.col = |F_ℓ| - 1`. This is neither owner nor
     containing.
7. Item 7: from item 6 and the two disjuncts of [D1.2b item 1].
8. Item 8:
   - Special gives `depth > 0`, so the path is nonempty, and `heightPath oe = sd.col.path`
     (`List.dropLast_append_getLast`).
   - The number: `num (sd.col) = num (oe.col) + 1 + sd.col.col`, by unfolding `ColAddr.num`
     on `path ++ [(ci, ei)]`. Combined with `specialStop`, this gives `oe.col.num 0 = r`.
   - The last entry and the last column come from the route [D1.2d]. `F_ℓ` ends in
     `Q ++ [(r, ∅)] = [(r, ∅)]`, by item 1 and `Q = []`.
9. Item 9: unfold `paperOpBody` through the bridges.
   - `paperOp_special`: `specialOut` with `hoe`, `hcol` and `hlast`.
   - `paperOp_ordinary_zero`: `n = 0` makes the `none` test false, `ordZ … 0 = ∅`, and
     `Hole.fill_zero` [D1.5a item 6].

**Uses:** D1.6, D1.2b, D1.2d, D1.3, D1.5a.

**Lean:** `Scan.stopData_spec`, `Scan.stopData_isSome`, `Scan.stopData_eq_none_of_lastCol`,
`Scan.stepKind_deletion_iff`, `Scan.stepKind_special_iff`, `Scan.stepKind_ordinary_iff`,
`Scan.rootData_spec`, `Scan.rootData_owner_iff`, `Scan.rootData_layer_lt`,
`Scan.rootData_layer_le`, `Scan.ownerEntry_spec`, `Scan.paperOp_deletion`,
`Scan.paperOp_special`, `Scan.paperOp_ordinary`, `Scan.paperOp_ordinary_zero`. File
`Scan/Step.lean`.

**Difficulty:** L. About 500 LOC of route invariants.

**Testable:** yes, with 0 failures:
- items 1, 5, 6 and 7 on 3,200 forests;
- item 8 on all special steps of 9,200 forests;
- item 2 on 3,200 forests;
- `paperOp_ordinary_zero` on 9,200 forests.

### D1.6c Agreement sub-lemmas   (paper: new)

**Fidelity:** new (G-001, D-3). Each item compares one locked helper of `expand` with the
paper's data. None of them uses V or I.

**Statement.** Assume `stopData E = some sd`, and write `ℓ = sd.depth`.
1. `tailLayer_of_stopData`: `tailLayer E = ℓ`.
2. `tailLayer_neg_iff` (`E ≠ ∅`): `tailLayer E < 0 ↔ E.cols.getLast? = some []`.
3. `skipLayers_of_stopData`: for `d ≤ ℓ`, `E.forestAt (sd.col.path.take d) =
   some (skipLayers E d)`. Also `skipLayers_add`.
4. `leftCount_eq_sum` (no hypothesis): `leftCount E d = Σ_{k<d} |skipLayers E k|`.
5. `tailNum_of_stopData`: `tailNum E ℓ = sd.t`.
6. `rootAt_of_stopData`: `rootAt E ℓ = sd.r`.
7. `isSpecial_of_stopData`: `isSpecial E ℓ = specialStop sd`.
8. `expandSpecial_of_stopData` (`specialStop sd`):
   `some (expandSpecial n ℓ E) = specialOut E sd n`.
9. `rootLayer_of_resolve` (`sd.col.resolve 0 sd.r = some o`):
   `rootLayer E sd.r ℓ = some (|o.path|, o.col)`.
10. `rootAppendingStart_of_rootData`: with `rootData E = some rd`,
    `rootAppendingStart R sd.r (sd.Q ++ [(sd.r, ∅)]) sd.t = rd.cursor`.
11. `ascendReplace_ofNat`: `ascendReplace r d (some ↑k) Z F = Hole.fill ⟨F, k⟩ r d Z`.
    `iterDown_eq_ordLoop`: the two loops are equal.
12. `expand_eq_paperOp_special` (`specialStop sd`): `expand E n = paperOp E n`.
13. `expand_eq_paperOp_ordinary` (`specialStop sd = false`, root visible):
    `expand E n = paperOp E n`.
14. `resolve_root_of_condV` (`CondV E`): `(sd.col.resolve 0 sd.r).isSome`.

**Proof.**
1. Item 1 is proved by induction along the route [D1.6b item 1]. `tailLayerCols` on a nonempty
   column list reduces to the last column (equations `[c]` and `_ :: rest@(_ :: _)`), and
   `tailLayerCol` to the last entry. A route entry with nonempty height `G` contributes
   `1 + tailLayer G`. At the stopping entry `tailLayer ∅ = -1`, giving `1 + (-1) = 0`.
2. Item 2: `E ≠ ∅` gives nonempty columns, and `tailLayer` reduces to the last column.
   `tailLayerCol [] = -1`. A nonempty column gives `1 + tailLayer h ≥ 0`, because
   `tailLayer h ≥ -1` for every `h`: by mutual induction, every clause is `-1` or `1 + (≥ -1)`.
3. Item 3: `skipLayers_add` by induction on `a`. For the main claim, induct on `d`: the step
   `sd.col.path[d]` is `(F_d).lastStep?` [D1.2d], which is the height of the last entry of the
   last column, i.e. `nextLayer F_d` (locked `lastEntry?`, `nextLayer`). Use
   `skipLayers E (d+1) = nextLayer (skipLayers E d)` (`skipLayers_add` with `b = 1`).
4. Item 4: induction on `d` generalizing `E`, using
   `leftCount E (d+1) = |E| + leftCount (nextLayer E) d`, `List.range_succ_eq_map`, and
   `skipLayers (nextLayer E) k = skipLayers E (k+1)`.
5. Item 5: `tailNum E ℓ = leftCount E ℓ + |F_ℓ| - 1 = Σ_{k<ℓ}|F_k| + |F_ℓ| - 1`, by items 4
   and 3. On the other side, `sd.t = sd.col.num 0 = Σ_{k<ℓ}(c_k + 1) + c_ℓ`, with
   `c_k = |F_k| - 1` and `c_ℓ = sd.col.col = |F_ℓ| - 1` [D1.6b item 1, D1.2d]. Every route
   forest is nonempty, so `c_k + 1 = |F_k|`.
6. Item 6: `lastEntry? F_ℓ = some (r, ∅)` [item 3, D1.6b item 1].
7. Item 7: `isSpecial` tests `ℓ ≠ 0` and that the last column of `F_ℓ` is `[(v, h)]` with
   `h.cols = []` and `v = leftCount E ℓ - 1`.
   - The last column `Q ++ [(r, ∅)]` is a singleton iff `Q = []`; then `v = r` and `h = ∅`.
   - `leftCount E ℓ - 1 = t - (sd.col.col + 1)` [items 4, 5].
   - `r = t - (col.col + 1) ↔ r + col.col + 1 = t` when `t ≥ col.col + 1`. This holds when
     `ℓ > 0`, since `leftCount ≥ |F_0| ≥ 1`. When `ℓ = 0`, both sides are false by their first
     conjunct.
<!-- U1-verify: changed -->
8. Item 8 is proved through a statement about an arbitrary forest `G` and depth `m ≥ 1`. The
   recursion of `expandSpecial` enters the height of the last entry, whose stop data is not
   `sd`.
   - Define `zSp n G m` as follows. Let `col` be the last column of `skipLayers G (m-1)`, and
     `(p, Fl)` its last entry. Then
     `zSp n G m := .node [col.dropLast ++ List.replicate (n + if col.dropLast = [] then 1 else 0) (p, .node Fl.cols.dropLast)]`.
   - Claim: if every `skipLayers G k` with `k < m` has a nonempty last column, then
     `expandSpecial n m G = replaceAt 0 0 (zSp n G m) (m - 1) G`.
   - The claim is proved by induction on `m`, generalizing `G`. The two equations of
     `expandSpecial` are treated below.
   - Item 8 follows at `G = E`, `m = ℓ`.
     - The nonempty-last-column hypothesis holds along the route: `skipLayers E k` is the
       route forest `F_k` for `k ≤ ℓ` (item 3), and route forests have nonempty last columns
       [D1.6b item 1, D1.2d].
     - `zSp n E ℓ` is the forest that `specialOut E sd n` places. By [D1.6b item 8] and
       item 3, `E.colAt oe.col` is the last column of `skipLayers E (ℓ-1)`.
   - Equation `k + 2`: descend one level, keeping `cols.dropLast` and `col.dropLast`. This
     matches `replaceAt 0 0` at depth `k + 1` after `mapLast_eq` [D1.5a item 3] and
     `Tree.map (shiftVal 0 0) = id` [D1.5a item 1].
   - The last equation builds `cols.dropLast ++ [first ++ replicate n ne]`, with
     `ne = (p, .node F_ℓ.cols.dropLast)` and `first = if P = [] then [ne] else P`.
   - `replaceAt 0 0` at depth `0` gives `cols.dropLast ++ [P ++ replicate (n + ε) ne]`.
     The two agree by `List.replicate_succ`.
   - `specialOut`'s lookups are given by [D1.6b item 8].
9. Item 9: `rootLayerAux r (ℓ + 2) E 0 0` visits layer `k` with `left = Σ_{l<k}|F_l|` [item 4]
   and `cur = F_k` [item 3]. `resolveAux` visits the same levels with
   `start = Σ_{l<k}(c_l + 1) = left`.
   - At a containing level, resolve's guard `q ≤ start + c_k` is `r < left + |F_k|`.
   - At the own level, resolve requires `q < left + |F_ℓ| - 1`, and then
     `r < left + |F_ℓ|` holds too.

   So both stop at the level `j = |o.path|`, with index `r - left = o.col`. The fuel `ℓ + 2`
   exceeds `j`.
10. Item 10: unfold `rootAppendingStart`. Then `List.dropLast_concat`,
    `cursor_eq_scanCount` [L2.5b], `rd.col.num 0 = r` [D1.6b item 5], and the cursor equation
    of [D1.6b item 5].
11. Item 11: `ascendReplace` matches `some (Int.ofNat k)`. `iterDown_eq_ordLoop` by induction
    on `n` (the equations coincide).
12. Item 12: `E ≠ ∅`, since a stop exists, so `expand` takes the branch `_`.
    `tailLayer E = ℓ ≥ 0` [item 1], so it is not the deletion branch, and
    `tl = ℓ` (`Int.toNat_natCast`). `isSpecial = true` [item 7]. Item 8 gives the output. On
    the other side, `paperOp_eq_body`, and `stepKindBody E = some .special`, because the last
    outer column is nonempty [D1.6b item 3] and `specialStop sd` holds.
13. Item 13: as item 12 up to `isSpecial = false` [item 7].
    - `t` and `r` agree [items 5, 6]. `rootLayer = some (j, i)` with `j = |o.path| ≤ ℓ`
      [item 9, D1.6b item 7], so the test `tl < rl` is false.
    - `eRoot = F_j` [item 3], and `colRoot` is column `o`. `colTail` is the stopping column
      [`skipLayers_add`, item 3, D1.6b item 1]. `app = rd.cursor` [item 10].
    - The owner test `ri != |eRoot| - 1` is `rd.owner = false` [D1.6b item 5].
    - The exhaustion test `app == |colRoot|` is `(colRoot.drop app).isEmpty`, since
      `app ≤ |colRoot|` [L2.1a item 1].
    - Body step: `ascendReplace r (jd) (some (↑ℓ - ↑j))` equals `Hole.fill ⟨F[i+1:], ℓ - j⟩`
      by `Int.ofNat_sub` (`j ≤ ℓ`) and item 11.
    - Owner step: `mapLast_eq` [D1.5a item 3], and `↑ℓ - ↑j - 1 = ↑(ℓ - j - 1)`, since
      `j < ℓ` [D1.6b item 7].
    - The head columns are syntactically equal, the loops agree [item 11], and the final
      `replaceAt 0 0 Z ℓ E` is `Hole.fill ⟨E, ℓ⟩ 0 0 Z` by definition.
14. Item 14: the closing entry `⟨sd.col, |Q|⟩` is an entry with parent `r`
    [D1.6b item 1, D1.2b item 10]. `CondV` gives `isSome`.

**Uses:** D1.6, D1.6b, D1.5a, D1.2b, D1.2d, L2.5b, L2.1a, D1.3.

**Lean:** `Scan.tailLayer_of_stopData`, `Scan.tailLayer_neg_iff`, `Scan.skipLayers_of_stopData`,
`Scan.skipLayers_add`, `Scan.leftCount_eq_sum`, `Scan.tailNum_of_stopData`,
`Scan.rootAt_of_stopData`, `Scan.isSpecial_of_stopData`, `Scan.expandSpecial_of_stopData`,
`Scan.rootLayer_of_resolve`, `Scan.rootAppendingStart_of_rootData`, `Scan.ascendReplace_ofNat`,
`Scan.iterDown_eq_ordLoop`, `Scan.expand_eq_paperOp_special`,
`Scan.expand_eq_paperOp_ordinary`, `Scan.resolve_root_of_condV`. File `Scan/Agreement.lean`.

**Difficulty:** L. About 700 LOC of unfolding the locked port.

**Testable:** yes. Items 1–9, and 12–13 under their own hypotheses only, on 6,000 raw forests
(3,066 outside V∧I), 3,000 random V∧I forests and 200 standard forests (0 failures).

### D1.6a The agreement lemma and branch contracts   (paper: new, spine; G-001)

**Fidelity:** repaired (G-001, D-3).

**Statement.** The spine contracts:
1. `expand_eq_paperOp`: for `E ≠ ∅` with `CondV E` and `CondI E`, `expand E n = paperOp E n`.
2. `expand_empty` (`rfl`).
3. `stepKind_isSome`: on nonempty V∧I inputs.
4. `stopData_of_stepKind`, `rootData_of_ordinary`, `ownerEntry_of_special`.
5. `expand_deletion`.

**Proof.**
1. Item 1 is a case analysis on the last outer column `col` (`E ≠ ∅`).
   - `col = []`: `tailLayer E < 0` [D1.6c item 2], so `expand` deletes the column. Also
     `paperOp E n = some (.node E.cols.dropLast)` [D1.6b items 4, 9].
   - `col ≠ []`: `stopData E = some sd` [D1.6b item 2, using `hI`]. If `specialStop sd`, apply
     [D1.6c item 12]. Otherwise the root is visible [D1.6c item 14, using `hV`]; apply
     [D1.6c item 13].
2. Item 3: the same case analysis, ending in `deletion`, `special` or `ordinary`
   [D1.6b item 4].
3. Item 4: unfold `stepKindBody` and `rootDataBody`. For `ownerEntry_of_special`:
   `specialStop` gives `depth > 0`, so the path is nonempty [D1.6b item 1].
4. Item 5: `stepKind ∅ = none`, so `E ≠ ∅`. The last column is empty [D1.6b item 4], so
   `tailLayer < 0` [D1.6c item 2].

**Uses:** D1.6b, D1.6c.

**Lean:** spine `Scan.expand_eq_paperOp`, `Scan.expand_empty`, `Scan.stepKind_isSome`,
`Scan.stopData_of_stepKind`, `Scan.rootData_of_ordinary`, `Scan.ownerEntry_of_special`,
`Scan.expand_deletion`. File `Scan/Agreement.lean`.

**Difficulty:** S — case analysis over D1.6b and D1.6c.

**Testable:** yes. 12,524 operations on nonempty V∧I forests (0 mismatches).

### D1.7a Seeds and generation witnesses   (paper: new)

**Fidelity:** new.

**Statement.**
1. `seed_ne_empty`.
2. `seed_cols`: `(seed m).cols = if m = 0 then [[]] else [[], branch 0 (m-1)]`.
3. `branch_spec`: `branch i k = [(i, if k = 0 then ∅ else .node [branch (i+1) (k-1)])]`.
4. `isStd_iff_witness`:
   `IsStd E ↔ ∃ m ns, ns.foldlM (fun F n => expand F n) (seed m) = some E`.

**Proof.**
1. Items 1–3: cases on `m` and `k`, then `rfl`.
2. Item 4, (→): induction on `IsStd`. A seed has `ns = []`. For `IsStd.expand`, append `n`
   (`List.foldlM_append`; `foldlM` over `[n]` is `expand e n`).
3. Item 4, (←): for all `ns` and `F`, `IsStd F` and `ns.foldlM … F = some E` imply `IsStd E`.
   Induction on `ns` with `List.foldlM_cons` and `IsStd.expand`.

**Uses:** none (locked `Expansion.lean`).

**Lean:** `seed_ne_empty`, `seed_cols`, `branch_spec`, `isStd_iff_witness`. File
`Scan/Seeds.lean` (new).

**Difficulty:** S — `rfl` and one induction on the witness.

**Testable:** yes. `seed_cols` for `m < 8` (0 failures).

### D1.7 Seeds L_m, Std, generation witness   (paper: txt:138-142)

**Fidelity:** as in paper. The paper's "at column i the parent is i − 1": in
`seed (m+1) = [[], branch 0 m]`, column 1 has parent 0 and the height attached to column `i`
starts at column `i + 1`, whose parent is `i` [D1.7a item 3].

**Statement.** Locked `seed`, `IsStd`, `Std`. The paper's Std is `IsStd` (U2, T3.2a
`isStd_iff_paper`). A generation witness is a seed index and a parameter list [D1.7a item 4].

**Proof.** Definitions; D1.7a.

**Uses:** D1.7a.

**Lean:** locked `seed`, `branch`, `IsStd`, `Std`. File `Scan/Seeds.lean`.

**Difficulty:** S — locked definitions.

**Testable:** yes, through D1.7a.

---

## Part G — Scan conditions

### D2.2 g_W, ancestors, condition A   (paper: txt:177-193)

**Fidelity:** as in paper. The spine definitions accept any query. Every lemma that needs a
reduced query assumes `Noninc` (txt:177).

**Statement.** Spine definitions `KeySys`, `actualKeys`, `routeCols`, `capKeys`, `resp`
(`g_W`), `Edge`, `Path` (reflexive-transitive, read on the stack of the tested column),
`parents`, `CondAK`, `CondA`.

**Proof.** Definitions. The two claims of the paper are D2.2a:
- txt:179-180, "V makes every nontrivial edge decrease": `edge_lt`;
- txt:191-193, "A implies p_i ≤ p_{i−1}": `parents_antitone`.

**Uses:** D1.2a, D1.4, D2.1.

**Lean:** spine names. File `Scan/Conditions.lean`.

**Difficulty:** S — spine definitions.

**Testable:** via N1.1.

### D2.2a Responses, edges and paths   (paper: new)

**Fidelity:** new.

**Statement.**
1. `cutStart E c k` is `x(c,k)`: `c.num 0 - 1` if `k = 0`, else the parent of entry `k - 1`.
2. `AAt E ks c i` is A at entry `i`. `condAK_iff : CondAK E ks ↔ ∀ c ∈ E.colAddrs, ∀ i,
   AAt E ks c i` (`Iff.rfl`).
3. `respEdge E ks c W x := (c.resolve 0 x).bind (resp E ks · W)`, and `edge_iff`: an edge is a
   value of this partial function (edges are deterministic).
4. `resp_eq_some`; `length_actualKeys`; `length_capKeys`; `parents_getElem?`.
5. `edge_lt` (V): `Edge E ks c W x p → p < x`. `path_le` (V): `Path … x y → y ≤ x`.
6. `cutStart_lt` (V, `c ∈ colAddrs`, `k ≤ |parents E c|`, `0 < c.num 0`):
   `cutStart E c k < c.num 0`.
7. `edge_congr_stack`, and `path_congr_stack` (V): if the stacks of `c` and `c'` resolve every
   `q < x₀` identically and `x < x₀`, then edges and paths from `x` agree.
8. `parents_antitone` (V, `CondAK E ks`): `p_{i+1} ≤ p_i`.

**Proof.**
1. Items 2–4: unfold (`Option.bind_eq_some_iff`, `Option.map_eq_some_iff`, `List.length_map`).
   <!-- U1-verify: changed -->
   - `length_capKeys`: `dropLast ++ (getLast?.map _).toList` has the original length.
   - `parents_getElem?`: `List.getElem?_map`.
2. Item 5, `edge_lt`: an edge yields an entry `⟨o, cursor⟩` with parent `p` [item 4,
   D1.2b item 10]. `CondV` gives `p < o.num 0` [D1.3a], and `o.num 0 = x` [D1.2b item 5].
   `path_le`: `ReflTransGen` induction.
3. Item 6: for `k = 0`, `num - 1 < num`. For `k ≥ 1`, the entry `k - 1` exists, and its parent
   is `< c.num 0` [D1.3a].
4. Item 7: an edge from `x` reads only `c.resolve 0 x`. For paths, use head induction
   (`ReflTransGen.head_induction_on`) with the invariant "current vertex `< x₀`", maintained
   by `edge_lt`.
5. Item 8: `AAt` at `(c, i+1)` gives a path from `cutStart E c (i+1) = p_i` to `p_{i+1}`; then
   `path_le`.

**Uses:** D1.2b, D1.3a, D2.2.

**Lean:** `Scan.cutStart`, `Scan.AAt`, `Scan.condAK_iff`, `Scan.respEdge`, `Scan.edge_iff`,
`Scan.resp_eq_some`, `Scan.length_actualKeys`, `Scan.length_capKeys`,
`Scan.parents_getElem?`, `Scan.edge_lt`, `Scan.path_le`, `Scan.cutStart_lt`,
`Scan.edge_congr_stack`, `Scan.path_congr_stack`, `Scan.parents_antitone`. File
`Scan/Conditions.lean`.

**Difficulty:** S — short unfoldings and `ReflTransGen` inductions.

**Testable:** yes. `pathb` on L-forests (N1.1).

### D2.3 Owner return, condition S, class L   (paper: txt:201-204)

**Fidelity:** as in paper. P is not part of L (S-6).

**Statement.** Spine definitions `IsOwnerReturn`, `CondS` and `InL = V ∧ I ∧ H ∧ A ∧ S`.

**Proof.** Definitions.

**Uses:** D1.2a, D1.4.

**Lean:** spine names. File `Scan/Conditions.lean`.

**Difficulty:** S — spine definitions.

**Testable:** via N1.1.

### D2.3a Owner-return lemmas   (paper: new)

**Fidelity:** new.

**Statement.**
1. `isOwnerReturn_iff` (`Iff.rfl`, with `Contains`).
2. `isOwnerReturn_of_parent`: if `e₀.Contains c` and `E.entryAt ⟨c, k⟩ = some (e₀.col.num 0,
   J)`, then `IsOwnerReturn E e₀ ⟨c, k⟩`.

**Proof.**
1. Item 2: the containing column resolves under its own number [D1.2b `resolve_host`].

**Uses:** D1.2b.

**Lean:** `Scan.isOwnerReturn_iff`, `Scan.isOwnerReturn_of_parent`. File
`Scan/Conditions.lean`.

**Difficulty:** S — one application of D1.2b.

**Testable:** n/a.

---

## Part H — Path nesting, barrier, capping (G-006)

### L2.2a The path-nesting induction   (paper: new; G-006)

**Fidelity:** repaired (G-006). The predicate of codex-crosscheck-1 Q2 is written out.

**Statement.**
1. `NestPred E ks x :⇔ ∀ c W Z p, Noninc W → Noninc Z → W ≤ Z → Edge E ks c Z x p →
   Path E ks c W x p`. It quantifies over every stack owner `c`, so over all occurrences and
   scopes simultaneously.
2. `nestPred_step` (V, `CondAK E ks`): `(∀ y < x, NestPred E ks y) → NestPred E ks x`.
3. `nestPred_all`: `NestPred E ks x` for every `x`.

**Proof** of item 2. Fix `c, W, Z, p` with the hypotheses of item 1.
1. Unfold the edge [D2.2a item 3]: `o := c.resolve 0 x` and `resp E ks o Z = some p`.
   - `i := cursor (ks o) Z` indexes an entry of `o`; `o ∈ E.colAddrs` [D2.2a item 4,
     D1.2b item 10].
   - No length relation between `ks o` and the column is needed.
2. `j := cursor (ks o) W ≤ i` [L2.1 item 5].
3. If `j = i`, the `W`-response equals the `Z`-response, and `ReflTransGen.single` closes.
4. Otherwise `j < i`.
   - The `W`-edge is `x → p_j` (resp at `W`, entry `j` exists since `j < i`).
   - For each `k` with `j < k ≤ i`, `AAt E ks o k` (from `hA` via [D2.2a item 2]) gives
     `Path E ks o (cutQuery (ks o) k) p_{k-1} p_k`. Here `cutStart E o k = p_{k-1}`, since
     `k ≥ 1`.
5. `W ≤ cutQuery (ks o) k`. First `j < |ks o|`, because `j < i ≤ |ks o|` [L2.1a item 1]. Then
   `W < cutQuery (ks o) (j+1)` [L2.1 item 1] `≤ cutQuery (ks o) k` [D2.1 item 4]. Each
   `cutQuery` is `Noninc` [D2.1a item 10].
6. Transfer each A-path to `c`'s stack. Its start `p_{k-1}` is a parent of an entry of `o`, so
   `< o.num 0 = x` [D1.3a, D1.2b item 5]. The stacks of `o` and `c` agree below `x`
   [D1.2b item 7]. Apply [D2.2a item 7] with `x₀ = x`.
7. Replace each edge `y → y'` of a transferred path (query `Y_k := cutQuery (ks o) k`) by a
   `W`-path. Here `y ≤ p_{k-1} < x` [D2.2a item 5], so the hypothesis at `y` applies with
   `W ≤ Y_k` (step 5). Formally: `ReflTransGen` induction on the transferred path,
   concatenating with `ReflTransGen.trans`.
8. Concatenate `x → p_j ⇝ p_{j+1} ⇝ … ⇝ p_i = p`, by induction on `k` from `j + 1` to `i`.

Item 3 is `Nat.strong_induction_on` with item 2.

**Uses:** L2.1, L2.1a, D2.1, D2.1a, D2.2a, D1.2b, D1.3a.

**Lean:** `Scan.NestPred`, `Scan.nestPred_step`, `Scan.nestPred_all`. File `Scan/Paths.lean`.

**Difficulty:** M — a strong induction whose step chains several path concatenations (about 200 LOC).

<!-- U1-verify: changed -->
**Testable:** yes. The check: for every stack owner `c`, every `x < c.num`, every `Z` among
the forest's cut queries with an edge, and every cut query `W ≤ Z`, a `W`-path exists. There
were 0 failures in each of three runs:
- 200 standard L-forests: 50,421 instances;
- 3,000 raw V∧A forests, with I, H and S not imposed: 65,459 instances;
- capped key systems `ks = capKeys E sel` with V and decorated A on raw forests, with queries
  among the capped cut queries (which may contain `⊤`): 214,838 instances.

The lemma's hypotheses (V and `CondAK E ks` for an arbitrary key system) are therefore
exercised beyond actual keys.

### L2.2 Path nesting lemma   (paper: txt:194-200)

**Fidelity:** repaired (G-006, through L2.2a).

**Statement.** Spine `path_nesting`: assume `CondV E`, `CondAK E ks`, `Noninc W`, `Noninc Z`,
`W ≤ Z` and `Edge E ks c Z x p`. Then `Path E ks c W x p`.

**Proof.**
1. `nestPred_all E ks x` [L2.2a] applied to `c, W, Z, p`.

**Uses:** L2.2a.

**Lean:** spine `Scan.path_nesting`. File `Scan/Paths.lean`.

**Difficulty:** S — one application of L2.2a.

**Testable:** yes (L2.2a).

### L2.3a The barrier's joint predicates   (paper: new; G-006)

**Fidelity:** repaired (G-006). The predicates `C_e` and `R_e` of codex-crosscheck-1 Q2, the
localized pre-entry-cut barrier, and the joint lexicographic induction.

**Statement.** Fix a containing entry `e` with host `a = e.col.num 0` and index `u = e.idx`.
Put `D_e = boundary (actualKeys E e.col) u`.
1. `CutBound E e c k` (`C_e(c,k)`): if
   `Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) a`, then
   `cutQuery (actualKeys E c) k < D_e`.
2. `ReturnBound E e c k` (`R_e(c,k)`): if `(parents E c)[k]? = some a`, then
   `boundary (actualKeys E c) k < D_e`.
3. `cutBound_zero` (`e ∈ E.entryAddrs`): `CutBound E e c 0`.
4. `cutBound_of_returns` (localized barrier). Assume V, `e ∈ E.entryAddrs`, `c ∈ E.colAddrs`,
   `e.Contains c`, `k ≤ |parents E c|`, and:
   - `hlow`: `∀ o ∈ E.colAddrs, e.Contains o → o.num 0 < c.num 0 → ∀ v, ReturnBound E e o v`;
   - `hprev`: `∀ k' < k, ReturnBound E e c k'`.

   Then `CutBound E e c k`. No A at `(c, k)` is used.
5. `returnBound_of_cutBound`: S, `AAt E (actualKeys E) c k` and `CutBound E e c k` give
   `ReturnBound E e c k`.
6. `BarPred E e c k := CutBound E e c k ∧ ReturnBound E e c k`, and `barPred_step`: under V,
   A and S, `BarPred` at `(c, k)` follows from `BarPred` at every `(o, v)` with
   `o.num 0 < c.num 0` inside `H_e` (`v ≤ |parents E o|`), and at every `(c, k')` with
   `k' < k`.
7. `barrier_joint`: under V, A and S, `BarPred E e c k` for every column `c` inside `H_e` and
   every `k ≤ |parents E c|`.

**Proof.**
1. Item 3: `cutQuery _ 0 = []` [D2.1 item 1]. `D_e ≠ []`, because `u < |actualKeys E e.col|`
   [D2.1 item 5, D2.2a item 4]. And `[] < D_e` (`List.Lex.nil`).
2. Item 4. Put `W := cutQuery (actualKeys E c) k` (`Noninc`, D2.1a item 10) and
   `x := cutStart E c k`, and assume the path `x ⇝ a`.
   1. For `k = 0`, use item 3. Let `k > 0`.
   2. Split the path at its last step (`Relation.ReflTransGen.cases_tail`): either `x = a`, or
      `x ⇝ z` followed by an edge `z → a`.
   3. Case `x = a`: `x` is the parent of entry `k - 1`. `hprev` at `k - 1` gives
      `boundary (actualKeys E c) (k-1) < D_e`, and this boundary is `W`
      [D2.1 `boundary_eq_cutQuery`].
   4. Case of a last edge `z → a` with `o := c.resolve 0 z`:
      - `a < z` [D2.2a item 5]. Also `z ≤ x < c.num 0` [D2.2a items 5, 6], where
        `c.num 0 > a ≥ 0` because `e.col` is on `c`'s stack [D1.2b items 3, 9].
      - `e.Contains o` [D1.2b `contains_of_resolve`], `o ∈ E.colAddrs`, and
        `o.num 0 = z < c.num 0` [D1.2b item 5].
      - `v := cursor (actualKeys E o) W` is an entry of `o` with parent `a`
        [D2.2a item 4], so `v < |actualKeys E o|`.
      - `W < cutQuery (actualKeys E o) (v+1) = boundary (actualKeys E o) v` [L2.1 item 1].
      - `hlow` at `(o, v)` gives `boundary (actualKeys E o) v < D_e`, so `W < D_e`.
3. Item 5: assume `(parents E c)[k]? = some a`.
   1. `AAt` with `p = a` gives the path; `CutBound` gives `W := cutQuery (actualKeys E c) k
      < D_e`.
   2. The entry `⟨c, k⟩ = (a, J)` [D2.2a item 4] is an owner return of `e`
      [D2.3a item 2]. `CondS` gives `relKey (c.num 0) J < relKey a H_e`.
   3. These are `(actualKeys E c)[k]` and `(actualKeys E e.col)[u]` (definition,
      `List.getElem_map`), and the coercion preserves `<` (`WithTop.coe_lt_coe`).
   4. [L2.3b item 2] gives `boundary (actualKeys E c) k < D_e`.
4. Item 6:
   - The `CutBound` component is item 4, with `hlow` from the `ReturnBound` components at
     `(o, v)`. For `v > |parents E o|`, `ReturnBound` is vacuous, since `parents[v]? = none`.
     `hprev` comes from the `ReturnBound` components at `(c, k')`.
   - The `ReturnBound` component: for `k < |parents E c|`, item 5 with `AAt` from `CondA`
     [D2.2a item 2]; for `k = |parents E c|` it is vacuous.
5. Item 7 is a double strong induction: outer on `N = c.num 0` (`Nat.strong_induction_on`),
   inner on `k`. The predicate is: for all `c ∈ E.colAddrs` with `c.num 0 = N`,
   `e.Contains c → ∀ k ≤ |parents E c|, BarPred E e c k`. Each step applies item 6. This is
   the order of codex-crosscheck-1 Q2: the column number falls, or the same occurrence with a
   smaller entry index.

**Uses:** L2.1, L2.3b, D2.1, D2.1a, D2.2a, D2.3a, D1.2b.

**Lean:** `Scan.CutBound`, `Scan.ReturnBound`, `Scan.cutBound_zero`,
`Scan.cutBound_of_returns`, `Scan.returnBound_of_cutBound`, `Scan.BarPred`,
`Scan.barPred_step`, `Scan.barrier_joint`. File `Scan/Paths.lean`.

**Difficulty:** M. About 300 LOC.

**Testable:** yes, through L2.3.

### L2.3 Barrier lemma   (paper: txt:205-219)

**Fidelity:** repaired (G-006, through L2.3a).

**Statement.** Assume V, A and S.
1. `barrier`† (return form, txt:205-207): for an owner return of `e` to `e₀`,
   `boundary (actualKeys E e.col) e.idx < boundary (actualKeys E e₀.col) e₀.idx`
   (`B_c(v) < B_a(u)`).
2. `cut_barrier`† (txt:207-209): at any complete cut `k ≤ |parents E c|` of a column `c` inside
   `H_e`, including the cut after the last entry, if the cut's ancestor path reaches `a`, then
   `cutQuery (actualKeys E c) k < B_a(u)`.

**Proof.**
1. Item 1: `IsOwnerReturn` gives `e₀.Contains e.col`, and parent `q` with
   `e.col.resolve 0 q = some e₀.col`, so `q = e₀.col.num 0` [D1.2b item 5]. `e.col` is a
   column of `E`. Apply `barrier_joint` [L2.3a item 7] at `(e.col, e.idx)`, then the
   `ReturnBound` component with `parents_getElem?` [D2.2a item 4].
2. Item 2: the `CutBound` component of [L2.3a item 7], applied to `hpath`.

**Uses:** L2.3a, D1.2b, D2.2a.

**Lean:** `Scan.barrier`, `Scan.cut_barrier`. File `Scan/Paths.lean`.

**Difficulty:** S — projections of L2.3a.

<!-- U1-verify: changed -->
**Testable:** yes, with 0 failures:
- on 2,158 L-forests (standard and random): item 1 at every owner return, and item 2 at every
  cut `k ≤ m` of every column inside every entry;
- on 6,858 raw V∧A∧S forests, with I and H not imposed (578 of them fail I or H): 1,043 owner
  returns for item 1, and 2,806 cut paths reaching the host for item 2.

### L2.4b Capped responses, route visibility, forward paths   (paper: new)

**Fidelity:** new. Points 1 and 2 of codex-crosscheck-1 Q2, "Capping".

**Statement.** Let `sel` satisfy `∀ a ∈ sel, a ∈ routeCols E`.
1. `capKeys_of_not_mem`: `c ∉ sel → capKeys E sel c = actualKeys E c`.
2. `cutQuery_capKeys` (point 1, txt:222): if `i < |col c|`, then
   `cutQuery (capKeys E sel c) i = cutQuery (actualKeys E c) i`.
3. `resp_capKeys`: if `cursor (actualKeys E o) W < |actualKeys E o|`, then
   `resp E (capKeys E sel) o W = resp E (actualKeys E) o W`.
4. `routeCols_visible` (point 2): if `c ∈ E.colAddrs`, `a ∈ routeCols E` and
   `c.resolve 0 z = some a`, then some entry `⟨a, v⟩ ∈ E.entryAddrs` contains `c`.
5. `capped_path_of_actual`: assume V, `c ∈ E.colAddrs`, and
   `∀ e ∈ E.entryAddrs, e.Contains c → CutBound E e c k`. Then every actual path from
   `cutStart E c k` at query `cutQuery (actualKeys E c) k` is a capped path.

**Proof.**
1. Item 1: the `if` of `capKeys` is false.
2. Item 2: if `c ∈ sel`, `capKeys E sel c = ks.dropLast ++ [⊤]`, where `ks = actualKeys E c` is
   nonempty since `i < |ks|`. Then `take i` of it is `take i ks`, because
   `i ≤ |ks| - 1 = |dropLast|` (`List.take_append_of_le_length`, then `List.dropLast_eq_take`
   and `List.take_take`). If `c ∉ sel`, use item 1. <!-- U1-verify: changed -->
3. Item 3: if `o ∉ sel`, use item 1. If `o ∈ sel`: `ks` is nonempty, by `hnx`, and
   `capKeys E sel o = ks.dropLast ++ [⊤]`. [L2.5 (2)] gives equal traces, hence equal cursors
   [L2.5a item 2], hence equal responses (`resp` reads only the cursor and the column).
4. Item 4: `a` is on `c`'s stack [D1.2b item 2], and `a ∈ routeCols E` gives
   `a.col + 1 = |F|` for the forest `F` at `a.path` [D1.2d].
   - Own level (`a.path = c.path`, `a.col < c.col`): `c.col < |F|`, because `c` exists. So
     `c.col ≤ a.col`, a contradiction.
   - Containing level `k` (`a.path = c.path.take k`, `a.col ≤ ck`): `ck < |F|`, so
     `ck ≤ a.col`, and `a.col = ck`. Put `v := c.path[k].2`. Then
     `⟨a, v⟩.heightPath = c.path.take (k+1) <+: c.path`. The entry exists because
     `forestAt (c.path.take (k+1))` exists [D1.2b item 10].
5. Item 5: put `W = cutQuery (actualKeys E c) k` and `x = cutStart E c k`. Tail induction on the
   actual path (`Relation.ReflTransGen.rec`), with the induction hypothesis "capped path
   `x ⇝ z`". For an actual edge `z → y`, let `o := c.resolve 0 z`.
   - If `o ∉ sel`, the keys are equal (item 1), so the responses are equal.
   - If `o ∈ sel`: item 4 gives `⟨o, v⟩` containing `c`. Apply `hcut` at `⟨o, v⟩` to the
     actual path `x ⇝ z`, with `z = o.num 0` [D1.2b item 5]. This gives
     `W < boundary (actualKeys E o) v`, so `cursor (actualKeys E o) W ≤ v <
     |actualKeys E o|` [L2.1 item 3]. Item 3 gives equal responses.

**Uses:** L2.5, L2.5a, L2.1, L2.3a, D2.2a, D1.2b, D1.2d.

**Lean:** `Scan.capKeys_of_not_mem`, `Scan.cutQuery_capKeys`, `Scan.resp_capKeys`,
`Scan.routeCols_visible`, `Scan.capped_path_of_actual`. File `Scan/Capping.lean`.

**Difficulty:** M — two tail inductions on paths plus the route-visibility case analysis (about 200 LOC).

**Testable:** yes, through L2.4.

### L2.4a Reverse capping by first divergence   (paper: new; G-006)

**Fidelity:** repaired (G-006). The predicate "actual A together with actual return bounds" and
the first-divergence argument of codex-crosscheck-1 Q2.

**Statement.** Let `sel ⊆ routeCols E`.
1. `actual_path_of_capped`: under the hypotheses of [L2.4b item 5], every capped path from
   `cutStart E c k` at query `cutQuery (actualKeys E c) k` is an actual path.
2. `RevPred E c i :⇔ AAt E (actualKeys E) c i ∧ ∀ e ∈ E.entryAddrs, e.Contains c →
   ReturnBound E e c i`.
3. `revPred_step`: assume V, S and decorated A (`CondAK E (capKeys E sel)`). Then `RevPred` at
   `(c, i)` follows from `RevPred` at every `(o, v)` with `o.num 0 < c.num 0`, and at every
   `(c, i')` with `i' < i`.
4. `capping_reverse_joint`: `RevPred E c i` for every `c ∈ E.colAddrs` and every `i`.
5. `capping_reverse`: V, S and decorated A give `CondA E`.

**Proof.**
1. Item 1 (first divergence) is the tail induction of [L2.4b item 5], now on the capped path,
   with the induction hypothesis "actual path `x ⇝ z`". The edge argument repeats
   [L2.4b item 5, last step] verbatim: `CutBound` is applied to the actual prefix supplied by
   the induction hypothesis, never to a decorated one. This is exactly what codex Q2 requires:
   no actual bound is inferred from a decorated edge.
2. Item 3. If `i ≥ |parents E c|`, both components of `RevPred` are vacuous
   (`parents[i]? = none`), so assume `i < |parents E c|`.
   1. For each `e ∈ E.entryAddrs` containing `c`, `CutBound E e c i` holds by
      [L2.3a item 4]. Its `hlow` is the second component of the induction hypothesis at
      `(o, v)` (`e` contains `o`); its `hprev` is the second component at `(c, i')`.
   2. Actual A at `(c, i)`: for `(parents E c)[i]? = some p`, decorated A [D2.2a item 2]
      gives a capped path at query `cutQuery (capKeys E sel c) i`. That query equals
      `cutQuery (actualKeys E c) i` [L2.4b item 2], since `i < |col c|`. Item 1, with step
      2.1, makes the path actual.
   3. `ReturnBound E e c i` for each containing `e`: [L2.3a item 5], with steps 2.2, 2.1 and
      `hS`.
3. Item 4: double strong induction on `(c.num 0, i)`, as in [L2.3a item 7], applying item 3.
4. Item 5: the first component of item 4, through [D2.2a item 2].

**Uses:** L2.4b, L2.3a, D2.2a.

**Lean:** `Scan.actual_path_of_capped`, `Scan.RevPred`, `Scan.revPred_step`,
`Scan.capping_reverse_joint`, `Scan.capping_reverse`. File `Scan/Capping.lean`.

**Difficulty:** M — the double lexicographic induction and the first-divergence path induction (about 200 LOC).

**Testable:** yes, through L2.4.

### L2.4 Capping lemma   (paper: txt:220-231)

**Fidelity:** repaired (G-006, through L2.4a and L2.4b).

**Statement.** Assume V and S, and `sel ⊆ routeCols E`.
1. `capping_forward`: actual A gives decorated A.
2. `capping_iff`†: `CondA E ↔ CondAK E (capKeys E sel)`.

**Proof.**
1. Item 1: let `c ∈ E.colAddrs` and let `i` be an entry with parent `p`.
   - The decorated query equals the actual one [L2.4b item 2].
   - Actual A gives the actual path.
   - `barrier_joint` [L2.3a item 7] gives `CutBound E e c i` for every containing entry `e`.
   - [L2.4b item 5] turns the actual path into a capped one.
2. Item 2: (→) is item 1; (←) is [L2.4a item 5].

**Uses:** L2.4a, L2.4b, L2.3a.

**Lean:** `Scan.capping_forward`, spine-named `Scan.capping_iff`. File `Scan/Capping.lean`.

**Difficulty:** S — combination of L2.4a and L2.4b.

<!-- U1-verify: changed -->
**Testable:** yes. The check is, for every sublist `sel` of `routeCols E`,
`condAKb E (actualKeys E) = condAKb E (capKeys E sel)`. There were 0 failures on two pools:
- 2,935 forests with V and S (2,357 of them with A), drawn from standard and random V∧I forests.
  This pool never violates I.
- 8,685 raw V∧S forests, with I and H not imposed: 20,812 selections. Of these, 7,738 selections
  are on the 2,199 forests that fail I or H, and 1,827 forests fail actual A. The generator is
  `genRaw`/`genNear` in `scratch/blueprint/U1-verify/tests-raw.lean`.

So the hypotheses V and S alone are exercised.

### L2.4c Every operation is defined on V, I, A, S   (paper: txt:224, 232-236)

**Fidelity:** repaired. Following the task, "the operations are defined on V, I, A, S" becomes
`expand E n ≠ none` (`expand_ne_none`); the spine's `expand_isSome` is the same fact.

**Statement.**
1. `owner_root_nonexhaust`: assume V, A and S, `stopData E = some sd`,
   `rootData E = some rd` and `rd.owner`. Then `rd.cursor < |col rd.col|`.
2. `paperOp_isSome`: on nonempty V, I, A, S inputs, `paperOp E n` is `some`.
3. `expand_isSome` (spine) and `expand_ne_none`: on V, I, A, S inputs, `expand E n ≠ none`.
4. `inL_expand_ne_none`: `InL E → expand E n ≠ none`.

**Proof.**
1. Item 1, txt:232-236. Write `R = rd.col`.
   1. [D1.6b item 6] gives `u` with `⟨R, u⟩` containing `sd.col` and `u + 1 = |R|`.
   2. The closing slot `N = ⟨sd.col, |Q|⟩` has parent `r` and height `∅` [D1.6b item 1].
      `sd.col.resolve 0 r = some R` [D1.6b item 5]. So `N` is an owner return of `⟨R, u⟩`
      [D2.3a item 2].
   3. [L2.3 item 1]: `boundary (actualKeys E sd.col) |Q| < boundary (actualKeys E R) u`.
   4. Put `Z := cutQuery (actualKeys E sd.col) |Q|`. Then `Z <` the left side of step 3, by
      [D2.1 item 2] with `|actualKeys E sd.col| = |Q| + 1`. This is `Z < ν(Z ⌢ [∅])`
      (txt:235).
   5. So `Z < cutQuery (actualKeys E R) (u+1)`, and `cursor (actualKeys E R) Z ≤ u`
      [L2.1 item 3].
   6. `cursor (actualKeys E R) Z` equals each of the following in turn:
      - `cursor (actualKeys E R) ((actualKeys E sd.col).take |Q|)` [L2.1 item 6];
      - `cursor ((rootKeys E rd).map ↑) ((queryKeys sd).map ↑)` (definitions,
        `rd.col.num 0 = r`, `sd.t = sd.col.num 0`);
      - `cursor (rootKeys E rd) (queryKeys sd)` [L2.5 (1), the coercion is strictly
        monotone];
      - `rd.cursor` [D1.6b item 5].
   7. Hence `rd.cursor ≤ u < |R|`.
2. Item 2: `stepKind_isSome` [D1.6a] gives a branch.
   - Deletion: [D1.6b item 9].
   - Special: [D1.6b item 9], with `ownerEntry_of_special` [D1.6a] and [D1.6b item 8]
     supplying `hoe`, `hcol` and `hlast`.
   - Ordinary: [D1.6b item 9] is `none` only if `rd.owner ∧ n ≠ 0 ∧ R.drop rd.cursor = []`.
     Item 1 excludes this (`List.drop_eq_nil_iff`).
3. Item 3: if `E = ∅`, `expand_empty` [D1.6a]. Otherwise `expand_eq_paperOp` [D1.6a] and
   item 2. `≠ none` is `Option.isSome_iff_ne_none`.
4. Item 4: unpack `InL`.

**Uses:** L2.3, L2.1, L2.5, D2.1, D1.6a, D1.6b, D2.3a, D2.2a, D1.2b.
<!-- U1-verify: changed (D2.2a `length_actualKeys` in step 4; D1.2b `mem_entryAddrs_iff` for the
membership of `⟨R, u⟩` and `N` required by L2.3) -->

**Lean:** `Scan.owner_root_nonexhaust`, `Scan.paperOp_isSome`, spine `Scan.expand_isSome`,
`Scan.expand_ne_none`, `Scan.inL_expand_ne_none`. File `Scan/Capping.lean`.

**Difficulty:** S — a chain of existing lemmas (about 80 LOC).

<!-- U1-verify: changed -->
**Testable:** yes, with 0 failures:
- `owner_root_nonexhaust` on 2,158 L-forests, and on the raw V∧A∧S forests of L2.3 (only 9
  owner-root stops occur there);
- `(expand E n).isSome` for `n < 4` on the same L-forests, and on raw V∧I∧A∧S forests with H
  not imposed: 25,676 operations, also checking `paperOp`.

---

## Part I — Testing infrastructure

### N1.1 Decidable mirrors and test generators   (paper: new)

**Fidelity:** new. It is testing only; nothing in the main proof uses it.

**Statement.**
1. Bool mirrors with real bodies: `condVb`, `condIb`, `condHb`, `pathAux`/`pathb`, `condAKb`,
   `isOwnerReturnb`, `condSb` and `inLb`.
2. Correctness:
   - `condV_iff`, `condI_iff`, `condH_iff`, `condS_iff` and `inL_iff` are unconditional;
   - `path_iff_pathb` and `condAK_iff_b` assume `CondV`.
3. `stdUpTo m d p`: the expressions reachable from the seeds `0…m` in at most `d` operations
   with parameters `0…p` (frontier expansion). `isStd_of_mem_stdUpTo`.

**Proof.**
1. The `_iff` lemmas: `List.all_eq_true`, then unfold.
2. `path_iff_pathb`: edges are deterministic [D2.2a item 3] and decrease under V
   [D2.2a item 5]. So `Path x y` holds iff `y` lies on the strictly decreasing orbit of `x`,
   which has at most `x + 1` vertices; the fuel `x + 1` suffices.
3. `isStd_of_mem_stdUpTo`: induction on `d`, with the invariant that every element of both
   lists is standard (`IsStd.seed`, `IsStd.expand`, `List.mem_filterMap`).

**Uses:** D1.3, D2.2, D2.3, D2.2a.

**Lean:** `Scan.condVb`, `Scan.condIb`, `Scan.condHb`, `Scan.pathAux`, `Scan.pathb`,
`Scan.condAKb`, `Scan.isOwnerReturnb`, `Scan.condSb`, `Scan.inLb`, `Scan.condV_iff`,
`Scan.condI_iff`, `Scan.condH_iff`, `Scan.path_iff_pathb`, `Scan.condAK_iff_b`,
`Scan.condS_iff`, `Scan.inL_iff`, `Scan.stdUpTo`, `Scan.isStd_of_mem_stdUpTo`. File
`Scan/Dec.lean` (new).

**Difficulty:** M (optional) — eight Bool mirrors with their `_iff` lemmas (about 300 LOC).

**Testable:** this is the test infrastructure. As a sanity check, `inLb` holds on all 200
expressions of `stdUpTo 4 3 2`, consistent with U2's `std_inL`.

---

## Part J — Integration additions (T-016 integration)

These nodes were added when the five units were integrated. Each one states a fact that another
unit had stubbed in its Lean file or listed under Requires; the requester is named under
**Fidelity**, and the former stub's statement is kept verbatim (renamed only where a U1 name was
already taken). The Lean declarations are in `blueprint/lean/U1.lean`, section "Integration
additions". `Role.under` and `Packet.prefixRoles`, `Packet.rolesBefore`, `Packet.inQueryRegion`
and `Packet.rootLenOf` are spine definitions with real bodies (§c.2, §c.8 of `00-spine.md`).

### D1.2e Roles of an entry, and the stack before it   (paper: new; txt:923-924, 1022)

**Fidelity:** new (requested by U5 R12, R13, and by U3 D7.1b for U5 R19).

**Statement.** Let `E` be a forest, `e ∈ E.entryAddrs`, `h = (E.heightAt e).getD ∅` and
`π = e.heightPath`. Write `P(E,e) = prefixRoles E e = rolesBefore E U_e` (spine §c.8).
1. `roles_entry`: there is a list `post` with
   `E.roles = P(E,e) ++ U_e :: (h.roles.map (Role.under π) ++ post)`, and no `x ∈ post` has
   `x.inEntry e`.
2. `truncAfter_roles_under`: `(E.truncAfter e).roles = P(E,e) ++ U_e :: h.roles.map (Role.under π)`.
3. `stack_mem_prefix`: `A_{e.col} ∈ P(E,e)`; every `o` with `e.col.OnStack o` has `A_o ∈ P(E,e)`;
   every entry `e'` with `e'.Contains e.col` has `U_{e'} ∈ P(E,e)`.

**Proof.**
1. *Prefix lemma.* For every path `σ` and tree `H`, `rolesF σ H = (rolesF [] H).map (Role.under σ)`.
   This is a mutual structural induction through the spine bodies `rolesF`, `rolesCols`,
   `rolesCol`: each emitted role carries the path argument as a prefix, and `Role.under σ` prefixes
   `σ` (spine body). With `σ = π` it gives `rolesF π h = h.roles.map (Role.under π)`.
2. *Item 1.* Induction on `|e.col.path|`, unfolding `rolesF/rolesCols/rolesCol` along the address
   of `e`. At the level of `e`'s column `rolesCol` emits `U_e` immediately followed by
   `rolesF π h` (spine body), then the later entries of the column, then (through `rolesCols`) the
   later columns; at each containing level the same holds for the containing entry. So
   `E.roles = pre ++ U_e :: (rolesF π h ++ post)`. `U_e` occurs once (D1.2b `roles_nodup`), so
   `pre = takeWhile (· ≠ U_e) E.roles = P(E,e)`. Every role of `post` is a later entry of a column
   on the path of `e`, or lies in a later column or in the height of a later entry; none is `U_e`
   and none has a path with prefix `π`, so `inEntry e` is false (spine `Role.inEntry`).
3. *Item 2.* D1.2c `truncAfter_roles` gives `takeWhile (· ≠ U_e) E.roles` followed by the maximal
   run of roles in `e` starting at `U_e`. By item 1 the first part is `P(E,e)`; the run is
   `U_e :: h.roles.map (Role.under π)`, because every role of `h.roles.map (Role.under π)` has a
   path with prefix `π` and the first role of `post` (if any) does not satisfy `inEntry e`.
4. *Item 3.* By D1.2b item 1 (`OnStack`), `o` is either a column `⟨e.col.path.take k, j⟩` with
   `j ≤ c_k` at a containing level `k`, or a column `⟨e.col.path, j⟩` with `j < e.col.col`. In the
   first case `rolesCols` emits `A_o` before the entries of column `j`; if `j = c_k` these entries
   include the containing entry `i_k`, whose height holds `U_e`; if `j < c_k`, column `c_k` and
   everything in it comes later. In the second case column `e.col.col` comes later. `A_{e.col}`
   precedes the entries of `e.col`. For `e'` containing `e.col`, `rolesCol` emits `U_{e'}`
   immediately before the roles of its height, which include `U_e`. In every case the role precedes
   `U_e` in `E.roles`, hence lies in `takeWhile (· ≠ U_e) E.roles = P(E,e)` (D1.2b `roles_nodup`).

**Uses:** D1.2a, D1.2b, D1.2c.

**Lean:** `Tree.roles_entry`, `Tree.truncAfter_roles_under`, `Tree.stack_mem_prefix`; they use the
spine definition Role.under (§c.2). File `Scan/Occurrence.lean`.

**Difficulty:** M — the prefix lemma is a mutual induction with a path argument, as in D1.2c item
4; about 200 LOC.

**Testable:** yes. Item 1 (as U5 R12) was tested by U5's verifier on 34,794 entries
(`scratch/blueprint/U5-verify/test_misc.py`, 0 failures). Items 2 and 3 are decidable on bounded
inputs and were not run at integration.

### D1.2f Truncation and height replacement: basic laws   (paper: new)

**Fidelity:** new (requested by U3 R1, R2).

**Statement.** Let `t` be a forest and `e ∈ t.entryAddrs`.
1. `truncAfter_spec`: `(t.truncAfter e).truncAfter e = t.truncAfter e`;
   `e ∈ (t.truncAfter e).entryAddrs`; `(t.truncAfter e).heightAt e = t.heightAt e`;
   `(t.truncAfter e).entryAt e = t.entryAt e`; `prefixRoles (t.truncAfter e) e = prefixRoles t e`
   (and the inclusion form of the same).
2. `setHeight_basic`, for every `h`: `e ∈ (t.setHeight e h).entryAddrs`;
   `(t.setHeight e h).heightAt e = some h`; `(t.setHeight e h).setHeight e h' = t.setHeight e h'`;
   `t.heightAt e = some h → t.setHeight e h = t`; `t.truncAfter e = t → (t.setHeight e h).truncAfter e
   = t.setHeight e h`; and the label of `e` is unchanged.

**Proof.**
1. *Entry and height after truncation.* D1.2c `entryAt_truncAfter`; `heightAt` is its second
   component (spine body); membership by D1.2b `mem_entryAddrs_iff`.
2. *Prefix after truncation.* By D1.2e item 2, `(t.truncAfter e).roles = P(t,e) ++ U_e :: …`, and
   `U_e` occurs once (D1.2b `roles_nodup`), so the roles before `U_e` are `P(t,e)`.
3. *Idempotence.* Induction on `e.col.path` with the body `truncAux` (D1.2c; moved into the spine
   at integration). At a containing level `(c, i₀)` it keeps columns `0…c` and, in column `c`,
   entries `0…i₀`; the result has exactly `c + 1` columns and its column `c` has exactly `i₀ + 1`
   entries, so a second application keeps everything at this level and recurses into the same
   height. At the last level the same holds with `j` and `i`.
4. *`setHeight`.* The body `setAux` (D1.2c) rewrites, along the address of `e`, one entry per level
   with `List.modify`, and at the last level replaces the height of `e`. D1.2c `entryAt_setHeight`
   gives the new entry `(p, h)` with the old label `p`. Idempotence and the identity case follow, by
   induction on `e.col.path`, from the two `List.modify` laws: modifying an index twice applies the
   composite, and modifying with a function that fixes the current value is the identity.
5. *Truncation after `setHeight`.* `t.truncAfter e = t` holds iff, at every level, the column list
   has exactly `c_k + 1` columns and the containing column exactly `i_k + 1` entries (and `j + 1`,
   `i + 1` at the last level), by step 3's description of `truncAux`. `setAux` changes no column
   length, so the same equalities hold for `t.setHeight e h`, whose truncation after `e` is therefore
   the identity.

**Uses:** D1.2b, D1.2c, D1.2e.

**Lean:** `Tree.truncAfter_spec`, `Tree.setHeight_basic`. File `Scan/Occurrence.lean`.

**Difficulty:** M — about 150 LOC.

**Testable:** yes (decidable on bounded inputs; not run at integration).

### D1.3b First parents of nonempty heights   (paper: new; txt:72-73)

**Fidelity:** new (requested by U5 R8).

**Statement.** `firstParent_host`: under `CondV E` and `CondI E`, if `e ∈ E.entryAddrs`,
`E.heightAt e = some h` and `h ≠ ∅`, then the first column of `h` is `(e.col.num 0, H₀) :: rest`
for some `H₀`, `rest`.

**Proof.**
1. `h ≠ ∅ = .node []` means `h.cols ≠ []`. `CondI E` (spine body) at `e` gives that the first
   column of `h` is `(q, H₀) :: rest` with `e.col.num 0 ≤ q`.
2. That entry has address `e₀ = ⟨⟨e.heightPath, 0⟩, 0⟩` (D1.2b `forestAt_heightPath`), so
   `e₀ ∈ E.entryAddrs` (D1.2b `mem_entryAddrs_iff`), and D1.3a `condV_iff_lt` gives
   `q < e₀.col.num 0`.
3. By the spine body of `ColAddr.num`, `e₀.col.num 0 = e.col.num 0 + 1`: the path
   `e.col.path ++ [(e.col.col, e.idx)]` adds `e.col.col + 1` to the sum, and the column index is
   `0`. Hence `q = e.col.num 0`.

**Uses:** D1.2a, D1.2b, D1.3, D1.3a.

**Lean:** `Scan.firstParent_host`. File `Scan/Conditions.lean`.

**Difficulty:** S.

**Testable:** yes (not run at integration).

### D1.4b Shape of relative keys   (paper: new; txt:81-83)

**Fidelity:** new (requested by U5 R14; `Tree.roles_map` moved here from U3 L6.2a at integration,
since it is a pure tree fact and U1 precedes U3).

**Statement.**
1. `Tree.roles_map`: `(t.map f).roles = t.roles` for every `f : α → β`.
2. `relKey_roles`: `(relKey a B).roles = B.roles`.
3. `relKey_eq_empty`: `relKey a B = ∅ ↔ B = ∅`.

**Proof.**
1. Item 1: mutual structural induction through the locked `Tree.map/mapCols/mapCol` and the spine
   bodies `rolesF/rolesCols/rolesCol`; roles read only positions, which `map` preserves.
2. Item 2: D1.4 `relKey_eq_map` (`relKey a B = B.map (relLabel a)`, by `rfl`) and item 1.
3. Item 3: `Tree.map f (.node cols) = .node (mapCols f cols)` (locked body) and
   `mapCols f cols = [] ↔ cols = []` by cases on `cols`.

**Uses:** D1.4.

**Lean:** `Tree.roles_map`, `relKey_roles`, `relKey_eq_empty`. File `Scan/Order.lean`.

**Difficulty:** S.

**Testable:** yes (not run at integration).

### D1.5b Shifts commute with unshifted placement   (paper: new; txt:86-94)

**Fidelity:** new (requested by U2 REQ-U1-7, second form; used by U2 D3.3a–c and L3.5).

**Statement.** `shift_replaceAt`: `shift r a (replaceAt 0 0 Z δ G) = replaceAt r a (shift r a Z) δ G`
for all `r, a, δ, Z, G`.

**Proof.** Induction on `δ`, with the locked body of `replaceAt`.
1. `shiftVal 0 0 p = p` (D1.5a `shiftVal_zero`), so `replaceAt 0 0 Z` keeps every parent.
2. `δ = 0` and `G = .node []`: both sides are `.node []` (locked `replaceAt`; `shift` of
   `.node []` is `.node []`).
3. `δ = 0` and `G = .node cols` with `cols ≠ []`: the left side is
   `shift r a (.node (cols.dropLast ++ Z.cols))`, which by the locked `Tree.map` is
   `.node (cols.dropLast.map (Tree.mapCol (shiftVal r a)) ++ (shift r a Z).cols)`, the right side.
4. `δ = k + 1`: both sides apply `mapLast` to the columns and, in the last column, to the last
   entry (D1.5a `mapLast_eq`). Non-last columns and entries are shifted on both sides; on the last
   entry `(p, H)` the left side gives `(shiftVal r a p, shift r a (replaceAt 0 0 Z k H))` and the
   right side `(shiftVal r a p, replaceAt r a (shift r a Z) k H)`, equal by the induction
   hypothesis.

**Uses:** D1.5, D1.5a.

**Lean:** `Scan.shift_replaceAt`. File `Scan/Step.lean`.

**Difficulty:** S — about 60 LOC.

**Testable:** yes (decidable; not run at integration).

### D1.6d Branch data in the forms used by U3 and U5   (paper: new; txt:98-124)

**Fidelity:** new (requested by U3 R4, R5, R6, U5 R3, R4, R5, R7, and the converse half of U2
REQ-U1-3).

**Statement.** Let `stopData E = some sd` and, where named, `rootData E = some rd`. Write
`T = A_{sd.col}` and `N = U_{closingSlot sd}`.
1. `rootData_col` (U5 R3): `sd.col.resolve 0 sd.r = some rd.col`, `rd.col.num 0 = sd.r`,
   `closingSlot sd ∈ E.entryAddrs`, `E.entryAt (closingSlot sd) = some (sd.r, ∅)`.
2. `stopData_col_mem` (U5 R4): `T ∈ E.roles`.
3. `ownerEntry_mem` (U5 R5): if `stepKind E = some .special` and `sd.ownerEntry = some e`, then
   `e ∈ E.entryAddrs`, `T.inEntry e`, and the height of `e` ends with the column
   `[(e.col.num 0, ∅)]`.
4. `lastCol_of_ordinary` (U5 R7): `stepKind E = some .ordinary → E.cols.getLast? ≠ some []`.
5. `stopData_roles` (U3 R4): `sd.t = sd.col.num 0`, `sd.depth = |sd.col.path|`,
   `E.colAt sd.col = some (sd.Q ++ [(sd.r, ∅)])`, `E.entryAt (closingSlot sd) = some (sd.r, ∅)`,
   `E.truncAfter (closingSlot sd) = E`, and `E.roles = rolesBefore E T ++ T :: (qs ++ [N])` with
   `inQueryRegion sd x` for every `x ∈ qs`.
6. `rootData_path` (U3 R5): the first two clauses of item 1; `rd.layer = |rd.col.path|`;
   `rd.col.path <+: sd.col.path`; `rd.cursor = cursor (rootKeys E rd) (queryKeys sd)`;
   `rd.owner = true ↔ (rd.col.container sd.col).isSome`; and every container `e` of `sd.col` in the
   root column has `e.idx + 1 = rootLenOf E rd`.
7. `stepKind_ordinary_iff_unfold` (U3 R6): for `E ≠ ∅` with V and I, `stepKind E = some .ordinary`
   iff some `sd` has `stopData E = some sd`, `¬ (0 < sd.depth ∧ sd.Q = [] ∧ sd.r + (sd.col.col + 1) = sd.t)`
   and `(sd.col.resolve 0 sd.r).isSome`.
8. `stopData_of_route` (U2 REQ-U1-3, converse): if `(routeCols E).getLast? = some c` and
   `E.colAt c = some (Q ++ [(r, ∅)])`, then `stopData E = some ⟨|c.path|, c, c.num 0, r, Q⟩`. No
   condition on `E` is needed.

**Proof.**
1. *Item 1.* The first two clauses are D1.6b `rootData_spec`. D1.6b `stopData_spec` gives
   `E.colAt sd.col = some (sd.Q ++ [(sd.r, ∅)])`; `closingSlot sd = ⟨sd.col, |sd.Q|⟩` (spine), so the
   spine body of `entryAt` gives `some (sd.r, ∅)`; membership by D1.2b `mem_entryAddrs_iff`.
2. *Item 2.* `E.colAt sd.col` is `some` (step 1), so D1.2b `mem_roles_iff`.
3. *Item 3.* D1.6b `ownerEntry_spec` gives `e.Contains sd.col`, `e.heightPath = sd.col.path`,
   `e.col.num 0 = sd.r`, the column `col` of `e` with last entry `(p, Fl)`, `e.idx + 1 = |col|`, and
   `Fl.cols.getLast? = some [(sd.r, ∅)]`. The spine body of `entryAt` gives
   `E.entryAt e = some (p, Fl)`, hence `e ∈ E.entryAddrs` (D1.2b `mem_entryAddrs_iff`) and
   `E.heightAt e = some Fl`; rewrite `sd.r = e.col.num 0`. `T.inEntry e` holds because
   `e.heightPath = sd.col.path` is a prefix of `Role.path T = sd.col.path` (spine `Role.inEntry`).
4. *Item 4.* If `E.cols.getLast? = some []`, then `stepKind E = some .deletion` by D1.6b
   `stepKind_deletion_iff`, which differs from `some .ordinary`.
5. *Item 5.* The first three clauses are D1.6b `stopData_spec`; the fourth is step 1. The stopping
   column is the last route column (D1.6b `stopData_spec`; D1.2d `mem_routeCols_iff`): every
   containing entry is the last entry of a last column, and `N` is the last entry of its column. So
   `truncAux` (D1.2c body, now in the spine) keeps every column and entry, and
   `E.truncAfter (closingSlot sd) = E`. Then D1.2e item 2 at `N` (whose height is `∅`) gives
   `E.roles = P(E,N) ++ [N]`, and unfolding `rolesCols/rolesCol` at `sd.col` splits
   `P(E,N) = rolesBefore E T ++ T :: qs`, where `qs` are the slots and heights of the entries
   `0…|Q|−1` of `sd.col`; each satisfies `inQueryRegion sd` (spine body).
6. *Item 6.* Resolve, number, layer and cursor are D1.6b `rootData_spec`. By D1.2b `resolve_spec`
   `rd.col` is on the stack of `sd.col`, so `rd.col.path = sd.col.path.take k` for some `k` (D1.2b
   item 1), a prefix. Owner: D1.6b `rootData_owner_iff` gives `rd.owner ↔ ∃ u,
   ⟨rd.col,u⟩.Contains sd.col ∧ u + 1 = |root column|`; D1.2b `contains_iff_container` turns
   containment into `rd.col.container sd.col = some ⟨rd.col, u⟩`, and `container` is a function, so
   this is `isSome`. Last clause: a container of `sd.col` in the root column lies on the route path of
   `sd.col` (D1.2d `mem_routeCols_iff`), which takes the last entry of every column it passes, so
   `e.idx + 1` is the length of the root column, which is `rootLenOf E rd` (spine body).
7. *Item 7.* D1.6b `stepKind_ordinary_iff`, the spine body of `specialStop`
   (`decide (0 < depth) && Q.isEmpty && (r + col.col + 1 == t)` is `false` iff the conjunction
   fails), and `Option.isSome_iff_exists` for the root.
8. *Item 8.* Induction along the route (D1.2d `mem_routeCols_iff`, with `IsRoutePath`): every route
   column before `c` is the last column of its forest, is nonempty, and its last entry has a
   nonempty height (otherwise the route would end there); so the spine body `stopF/stopCols/stopCol`
   descends exactly along the route without returning `none`. At `c` the last entry is `(r, ∅)`, so
   `stopCol` returns depth `|c.path|`, column `c`, `t = c.num 0`, `r` and the entries before the
   last, `Q`.

**Uses:** D1.2b, D1.2c, D1.2d, D1.2e, D1.6, D1.6b.

**Lean:** `Scan.rootData_col`, `Scan.stopData_col_mem`, `Scan.ownerEntry_mem`,
`Scan.lastCol_of_ordinary`, `Scan.stopData_roles`, `Scan.rootData_path`,
`Scan.stepKind_ordinary_iff_unfold`, `Scan.stopData_of_route`. File `Scan/Agreement.lean`.

**Difficulty:** M — eight short derivations, about 300 LOC.

**Testable:** yes. Items 1–3 (as U5 R3–R5) were tested by U5's verifier on 3,073, 3,073 and 696
inputs (`scratch/blueprint/U5-verify/test_u5.py`); items 4–8 are decidable and were not run.

### D1.9b One-atom extensions of a word   (paper: new; used at txt:286-288, 497-498)

**Fidelity:** new (requested by U2 REQ-U1-14, the "one-atom decoding" of U2 N2.1 step 2).

**Statement.** `routeCols_of_word_snoc`: let `z = (2e, 1, p)` if `first`, else `(2e+1, 0, p)`, and
let `word E = word G ++ [z]`. Then there are `c` and `k` with:
- `|c.path| = e` and `k = 0 ↔ first`;
- `c` is the last element of `routeCols E`, `E.entryAt ⟨c, k⟩ = some (p, ∅)` and
  `|E.colAt c| = k + 1`;
- `G = safePrefix E (µ(E) − 1)`;
- `(routeCols G).take e = (routeCols E).take e`;
- if `k ≠ 0`: `(routeCols G)[e]? = some c` and `G.colAt c` is the first `k` entries of `E`'s
  column `c`.

**Proof.**
1. *The last atom of a word.* By mutual structural induction on the spine bodies `wordAt`,
   `wordCols`, `wordCol`, `wordLater`: the last atom of `wordAt d F` (for `F ≠ ∅`) is the
   empty-column atom of the last column if that column is empty; otherwise the last atom of the word
   of the last entry's height if that height is nonempty; otherwise the last entry's own atom,
   `(2d, 1, q)` for a first entry and `(2d+1, 0, q)` for a later one. Following last columns and
   last entries is the route (D1.2d `mem_routeCols_iff`), so the last atom of `word E` belongs to the
   last route column `c` of `E`, at depth `|c.path|`.
2. *The entry.* `z` is an entry atom, so `c` is nonempty, its last entry `⟨c, k⟩` has empty
   height, parent `p` and depth `e`, and its marker is `1` iff `k = 0`, i.e. iff `first`; also
   `|E.colAt c| = k + 1`.
3. *`G`.* `word G = (word E).take (µ(E) − 1)` by the hypothesis, and this is
   `word (safePrefix E (µ(E) − 1))` (spine `word_safePrefix`); conclude by spine `word_injective`.
4. *Route of `G`.* D1.9a `spF_spec` with budget `µ(E) − 1`: the walk keeps every atom but the last.
   So it keeps every column and entry of `E` except the entry `⟨c, k⟩`, and, if `k = 0`, drops
   column `c` too (a column is kept only if its first atom fits; spine body of `spCols`). The route
   columns of depth `< e` keep their addresses and remain last columns whose last entries are on the
   route, so the first `e` route columns agree (D1.2d `mem_routeCols_iff`). If `k ≠ 0`, column `c`
   survives with its first `k` entries (D1.9 `colAt_safePrefix`) and is still the last column of
   its forest, hence the route column of `G` at depth `e`.

**Uses:** C1.8, D1.2d, D1.9, D1.9a.

**Lean:** `Scan.routeCols_of_word_snoc`. File `Scan/CompactWord.lean`.

**Difficulty:** M — about 250 LOC; the budget bookkeeping of D1.9a carries most of it.

**Testable:** yes (decidable on bounded inputs; not run at integration).

### N1.4 Depth shift and relabelling of the compact word   (paper: new; txt:143-146, 331-336)

**Fidelity:** new (requested by U2 REQ-U1-18, for U2 D3.3b).

**Statement.**
1. `wordAt_add`: `wordAt (e + δ) X = (wordAt e X).map (A ↦ (A.1 + 2δ, A.2))`.
2. `WordAtom.relabel f A` (real body) is `A` if `A` has even depth coordinate and marker `0` (the
   empty-column atom), and otherwise `A` with its third coordinate `q` replaced by `f q`.
3. `wordAt_map`: `wordAt e (Tree.map f X) = (wordAt e X).map (WordAtom.relabel f)`.

**Proof.** Both items by mutual structural induction on the spine bodies `wordAt/wordCols/wordCol/
wordLater`, for all `e` at once.
1. Item 1: the atoms emitted at depth `e + δ` are `(2(e+δ), 0, 0)`, `(2(e+δ), 1, p)` and
   `(2(e+δ)+1, 0, p)`, the depth-`e` atoms with `2δ` added to the first coordinate; heights recurse
   at `(e + δ) + 1 = (e + 1) + δ`.
2. Item 3: `Tree.map f` keeps the shape and replaces each parent `p` by `f p` (locked
   `map/mapCols/mapCol`). Entry atoms have marker `1` at even depth, or odd depth, so `relabel f`
   applies `f` to them; the empty-column atom `(2e', 0, 0)` is the only atom with even depth and
   marker `0`, and it is emitted unchanged on both sides.

**Uses:** C1.8.

**Lean:** `Scan.wordAt_add`, `Scan.WordAtom.relabel`, `Scan.wordAt_map`. File
`Scan/CompactWord.lean`.

**Difficulty:** S — about 80 LOC.

**Testable:** yes (decidable; not run at integration).

### L2.1d Cursor below a boundary, with the key raised to `⊤`   (paper: new; txt:675-676, 680-681)

**Fidelity:** new (requested by U3 R7).

**Statement.** `cursor_cappedAt`: for keys `ks`, `u < |ks|`, and a reduced `⊤`-free query `W` with
`W < cutQuery ks (u + 1)`: `cursor ks W ≤ u` and `cursor ks W = cursor (ks.take u ++ [⊤]) W`.

**Proof.**
1. `cursor ks W ≤ u`: L2.1 `cursor_le_of_lt_cutQuery` with `v = u`.
2. Put `ks' = ks.take (u + 1)`. L2.1a `cursor_take` gives
   `cursor ks' W = min (u + 1) (cursor ks W) = cursor ks W < u + 1 = |ks'|` (step 1).
3. Since the run on `ks'` is not exhausted, L2.5 (2) `trace_cap_top` gives
   `trace (ks'.dropLast ++ [⊤]) W = trace ks' W`, so the final cursors agree (L2.5a
   `cursor_eq_of_trace_eq`); and `ks'.dropLast ++ [⊤] = ks.take u ++ [⊤]`.

**Uses:** L2.1, L2.1a, L2.5, L2.5a.

**Lean:** `Scan.cursor_cappedAt`. File `Scan/Words.lean`.

**Difficulty:** S.

**Testable:** yes. Tested exhaustively by U3's verifier as R7 (T2: alphabet `{0,1,2,3,⊤}`, lengths
`≤ 4`, 33,496 cases, 0 failures).

### L2.3c The cut barrier read at a containing column   (paper: txt:207-209, 675-681)

**Fidelity:** new (requested by U3 R8; the form of L2.3 used by U3 L4.2c and L4.2d).

**Statement.** `cut_barrier_read`: let `E ∈ L`, `c ∈ E.colAddrs`, `k ≤ |parents E c|`, and let `y`
be a vertex of the actual cut chain, `Path E (actualKeys E) c (cutQuery (actualKeys E c) k)
(cutStart E c k) y`, with `c.resolve 0 y = some o` and `o.container c = some e`. Then
`cutQuery (actualKeys E c) k < cutQuery (actualKeys E o) (e.idx + 1)`.

**Proof.**
1. D1.2b `container_spec`: `e.col = o` and `e.heightPath <+: c.path`, i.e. `e.Contains c`; `e` is an
   entry of `E`, since `c` is a column of `E` inside its height (D1.2b `mem_colAddrs_iff`,
   `forestAt_append`, `forestAt_heightPath`).
2. D1.2b `resolve_num`: `y = o.num 0 = e.col.num 0`.
3. L2.3 `cut_barrier` (V, A, S from `InL E`) gives
   `cutQuery (actualKeys E c) k < boundary (actualKeys E e.col) e.idx`, and D2.1a
   `boundary_eq_cutQuery` rewrites the right side as `cutQuery (actualKeys E o) (e.idx + 1)`.

**Uses:** D1.2b, D2.1a, L2.3.

**Lean:** `Scan.cut_barrier_read`. File `Scan/Paths.lean`.

**Difficulty:** S.

**Testable:** yes (through L2.3's tests; not rerun at integration).

### L2.5d Trace specification   (paper: new; txt:122-124)

**Fidelity:** new (requested by U5 R15).

**Statement.** `trace_spec`: the trace of `src` against `qry`
- starts at `(0, 0)`;
- moves between consecutive states `s, s'` by the three comparison rules on `x = src[s.1]`,
  `y = qry[s.2]`: `x < y ∧ s' = (s.1+1, s.2)`, `x = y ∧ s' = (s.1+1, s.2+1)`, or
  `y < x ∧ s' = (s.1, s.2+1)`;
- has `s.1 ≤ cursor src qry` and `s.2 ≤ |qry|` at every state;
- ends at `(cursor src qry, j)` for some `j`, with `j = |qry|` when `cursor src qry < |src|`.

**Proof.** Generalize to `traceFrom i j src qry` and induct on `|src| + |qry|`, the termination
measure of the spine body.
1. The first element of `traceFrom i j …` is `(i, j)` in every branch of the body.
2. In the branch `x :: xs, y :: ys` the list is `(i, j) :: traceFrom …` with the three cases of the
   body, whose heads are the stated successors.
3. First coordinates: L2.5a `trace_fst_le_cursor`. Second coordinates grow by at most one per step
   and only while the query is nonempty.
4. The last state is `(cursor src qry, qcursor src qry)` (L2.5a `trace_last`). The run stops when one
   list is exhausted; if the source is not exhausted (`cursor < |src|`), the query is, and the same
   induction shows that the final query cursor is then `|qry|`.

**Uses:** D2.1, L2.5a.

**Lean:** `Scan.trace_spec`. File `Scan/Words.lean`.

**Difficulty:** S — about 80 LOC.

**Testable:** yes. Tested exhaustively by U5's verifier as R15 on all 14,641 source/query pairs
over `{0,1,2}` of length `≤ 4` (`scratch/blueprint/U5-verify/test_misc.py`).

## Requires (from other units)

None. (At integration U1 gained the Part J nodes, which other units requested from U1.) Every proof above uses only the locked files, Mathlib/core, the spine's real-bodied
definitions, and U1 nodes. This matches spine §d, "U1 consumes only the locked files and
Mathlib". `section Stubs` is therefore absent from `U1.lean`.

## Spine change requests

**SCR-1 (vocabulary; not a correctness issue). Status: applied at integration** (spine §i.1). Register in spine §c the new U1 definitions
that other units will read, as FIRM types with U1 bodies. The names, grouped:
- addresses and the route: `EntryAddr.Contains`, `ColAddr.OnStack`, `Tree.lastStep?`,
  `Scan.IsRoutePath`;
- conditions and the barrier: `Scan.cutStart`, `Scan.AAt`, `Scan.CutBound`,
  `Scan.ReturnBound`;
- the operation: `Scan.specialStop`, `Scan.ordStep`, `Scan.ordLoop`, `Scan.ordZ`,
  `Scan.specialOut`, `Scan.ordinaryOut`, `Scan.Hole.put`;
- the word library: `Scan.Noninc`, `Scan.nuStep`, `Scan.qcursor`, `Scan.GAtom`, `Scan.gword`.

Why: U2's kernels and identity (1) unfold the ordinary output, which is now `ordZ`/`ordStep`
(`paperOp_ordinary`). U3's `qMap`/`fMap` follow the stage structure of `ordLoop`. U3's
`firstDiff_cap` (spine §c.10) writes the start of the complete-cut chain as the informal
"`x(c,k)`", which is `Scan.cutStart E c k`. U2/U3's uses of "complete-cut barriers" need
`CutBound` and `cut_barrier` with these names.
- *Proposed replacement:* add the listed names to §c.3–§c.5 with the signatures in `U1.lean`.
  In §c.10 replace `x(c,k)` by `Scan.cutStart E c k`.
<!-- U1-verify: changed -->
- *Also register these theorems as U1 provides* (§d). All are generic, with no extra
  hypotheses:
  - `Scan.nu_map`, `Scan.cutQuery_map`, `Scan.boundary_map` (D2.1a item 11). U2 needs "κ_j
    commute with ν" (txt:333), and U3 requests `nu_map`.
  - `Scan.trace_fst_le_cursor` (L2.5a item 3), which U3 requests.
  - `Forest.compare_eq_cmp`, `Key.compare_eq_keyCmp` (D1.1, D1.4) and
    `Scan.sign_of_agreement_compare` (L2.5c). Any consumer that verifies the sign hypothesis
    of `trace_agree` by txt:246-249 needs these.
- *Consumers affected:* U2 (D3.3 kernel, L3.5 (1), T3.2 ordinary case, L3.1 repair), U3
  (L4.2 `firstDiff_cap`, L6.2), U5 (L8.6 reads `rootData_spec` and `stopData_spec`).

**SCR-2 (delivery of owed bodies). Status: applied at integration** (spine §i.2). The spine's `sorry` bodies of `Tree.truncAfter`,
`Tree.setHeight`, `Scan.safePrefix`, `Scan.stepKind`, `Scan.stopData`, `Scan.rootData` and
`Scan.paperOp` cannot be filled from a unit file without redeclaring.
- *Problem:* until the bodies are moved, every `#eval` of those names fails. This blocks
  bounded testing by other drafters.
- *Proposed replacement:* the reconciler copies `U1.lean`'s `Tree.truncAux`,
  `Tree.truncAfterBody`, `Tree.setAux`, `Tree.setHeightBody`, the mutual
  `Scan.spF … spLater`, `Scan.safePrefixBody`, `Scan.stopF … stopCol`, `Scan.specialStop`,
  `Scan.stepKindBody`, `Scan.rootDataBody`, `Scan.ordStep`, `Scan.ordLoop`, `Scan.ordZ`,
  `Scan.specialOut`, `Scan.ordinaryOut` and `Scan.paperOpBody` into `Spine.lean`, and sets the
  seven spine bodies to them. Then U1's `…_eq_body` bridges become `rfl`.
- *Consumers affected:* none in statement. All units gain executable definitions.

**SCR-3 (minor: the instance proofs block `#eval`). Status: note only; nothing to apply.** The `sorry` proof fields of
`Forest.instLinearOrder` and `Key.instLinearOrder` force `#eval!` for any computation that uses
their `<` or `≤`. The computation is sound (proofs are erased).
- *Proposed replacement:* none needed. Recorded so that other drafters know to use `#eval!`
  until D1.1 and D1.4 are proved.
- *Consumers affected:* testing only.

No FIRM item was found wrong. In particular, the following agree with §1–§2 and with the
bounded tests:
- `CondV`, `CondI`, `CondH`, `CondAK`, `IsOwnerReturn`, `CondS`, `InL`;
- `resp`, `Edge`, `Path`, `capKeys`, `routeCols`;
- `cursor`, `traceFrom`, `ReachesGT`;
- `word`;
- the spine signatures of `path_nesting`, `cursor_spec`, `cursor_nu`, `cutQuery_lt_succ`,
  `expand_eq_paperOp`, `expand_isSome`, `stepKind_isSome` and the branch-data contracts.

## Proposed simplifications (flagged, not applied)

- **P-1 (V is numeric).** By `resolve_isSome_iff` [D1.2b], visibility of a parent is just
  `p < c.num 0` (`condV_iff_lt`, D1.3a). Consumers may use this form instead of `resolve`
  whenever only visibility, not the occurrence, is needed.
- **P-2 (paths are orbits).** Edges are deterministic (`edge_iff`, D2.2a). So `Path x y` holds
  iff `y` is on the orbit of `x` under the partial map `respEdge`, which is strictly
  decreasing under V. Path concatenation, first divergence (L2.4a) and `pathb` all become
  statements about iterates. This could shorten L2.2a, L2.4a and L2.4b.
- **P-3 (weaker agreement hypotheses).** D1.6c items 12–13 prove `expand = paperOp` wherever
  the paper's route stops and either the step is special or the root is visible, without V or
  I. The spine could expose `expand_eq_paperOp_special`/`_ordinary` as contracts, for
  consumers (U2's caps, U3's intermediate expressions) that know only these facts.
- **P-4 (one route function).** The spine's `routeCols` uses fuel `E.size + 1`, while
  `stopData` uses structural recursion. A structural `routeCols` (FIRM body) would remove the
  fuel-adequacy lemma of D1.2d.
- **P-5 (generic order instances).** `Forest.instLinearOrder` and `Key.instLinearOrder` could
  both be built by one generic `Tree.linearOrderOfCmp` for a lawful comparator (D1.1a), instead
  of two copies of five fields.
- **P-6 (`word` from `gword`).** `word` could be defined as `gword` composed with the forgetful
  atom map. C1.8 would then be C1.8a directly. Not applied, because `word` is FIRM.

## Open problems

- **OP-1 (minor).** `word_put` (D1.5a) and the hole laws are the U1 half of the S-6
  continuation-hole library: fill/shift, word of a fill, generic word of a shift. U2's kernel
  `F_H` (D3.3) and identity (1) may need composition of holes (filling a hole whose filler
  itself has a hole) and the word of `T_{r,d}`-shifted fillers. U2 should list any such need
  under Requires, and U1 will add it to D1.5a.
- **OP-2 (minor).** `mem_routeCols_iff` (D1.2d) needs the fuel-adequacy lemma for the spine's
  fuel-based `routeColsAux`. It is routine but must count column roles against `Tree.size`.
  P-4 would remove it.
- **OP-3 (minor).** `stopData` is `none` on deletion inputs (step 3 is not reached). The spine
  wording ("`stopData E` is `some` iff step 3 stops") agrees. A consumer that wants the
  stopping data of a deletion step must use `E.cols.dropLast` directly; no consumer listed in
  the spine does.
- **OP-4 (minor).** On `F = ∅` at depth 0, the locked `replaceAt` returns `∅` where txt:90
  would give `Z`. This is harmless on the route (D1.5 note). A consumer filling a hole outside
  the route (U2's kernels on raw forests) must check that the outer forest is nonempty.
