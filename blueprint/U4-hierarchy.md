# U4 — hierarchy (§5, §6.2 except the seed lemma)

**Task:** T-016, unit U4 (includes T-008, the proof-level library survey).
**Companion Lean file:** `blueprint/lean/U4.lean`. Check command (from the repository root):

```
mkdir -p scratch/blueprint/U4 && { grep -h '^import ' blueprint/lean/U4.lean; cat blueprint/lean/Spine.lean; \
  grep -v '^import ' blueprint/lean/U4.lean; } > scratch/blueprint/U4/check.lean && \
  (cd lean && PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake env lean ../scratch/blueprint/U4/check.lean)
```

Result: exit 0, only `declaration uses 'sorry'` warnings (180, spine included). <!-- V-U4-12 --> U4.lean adds no imports. No
definition body is `sorry`; every theorem proof is `sorry`; there is no axiom.

**Inputs read:**
- the paper, §5 (txt:733-921), §6.2 (txt:970-1016), §7.1 (txt:1017-1044) for (15)/(16); PDF
  pp. 16-19 for the basis B and (9);
- `blueprint/00-spine.md` and `blueprint/lean/Spine.lean`;
- the ledger (nodes F5.1-L6.7; G-004; S-1, S-4; R-1, R-4, R-5, R-6; D-1, D-2; T-008);
- `tracker/review/claude-review.md` (C-02, C-10, §6, §7), `codex-review.md` (X-05, §5, §6.2),
  `reuse-audit.md` (§2-§4);
- the locked `lean/BTBMS/Mahlo.lean` and `Statement.lean`;
- sources of the pinned Mathlib (`/home/dev/ggg/.deps/lean-4.33.1/mathlib`) and of CU
  (`/home/dev/ggg/.deps/lean-4.33.1/cu`), read only.

---

## 0. Overview

U4 delivers one value: an instance of the S-4 interface `Hier.Interface.{u}` (spine §c.7),
whose fields are all that U5 reads. This document gives two complete plans for it.

1. **Part B, the paper's route.** It builds the J-hierarchy of §5 in `ZFSet.{u}` and
   instantiates the interface as `Hier.jInst`. The route goes through:
   - the basis B and the levels J (D5.2);
   - truth tables and verifiers (C5.3), and heights and sizes (C5.4);
   - histories, the canonical order, Σ₁ Skolem functions and hulls (L5.5);
   - condensation for Σ₁ substructures (L5.6);
   - control edges (D5.7, with the G-004 repair in D5.7a);
   - certificates in ordinal form (L5.8), and capture and transport (L5.9);
   - (13) and (14) (L6.5, L6.6).

   Every paper claim is split into sub-lemmas, and each has a precise Lean statement. The
   route is library-scale: about 18k–37k LOC (R-1, R-4). Mathlib provides the set and ordinal
   substrate. CU provides only the collapse primitives and proof patterns: its condensation
   needs full elementarity (R-6).
2. **Part C, proposed simplification P-U4-1 (not applied).** It instantiates the same
   interface with the *reflection hierarchy*: ordinal structures `M(ν, Q)` in the language
   `{<, Elem, Edge}`. Here `Elem` and `Edge` are defined by well-founded recursion as exactly
   "every diagram reflects" and "every diagram transports". The structural laws, capture and
   transport then hold by definition. The only real content is (13) and (14). Both follow from
   Mathlib's Skolem hulls plus a short condensation argument, an induction on the top
   coordinate; no constructibility is involved. The estimate is about 2.5k–5k LOC. It removes
   R-1, R-4 and R-6, and needs no CU.

Part A holds what both routes share:
- (8) and the other limit facts;
- the Mahlo helper lemmas used by U5's seed lemma;
- the locality and congruence lemmas of the diagram grammar.

S-1 is applied throughout: (13) uses only uncountability and (14) only regularity. Strong
limitness never occurs. G-004 is repaired in D5.7a (J route). P-U4-1 has no step of the
form "the hull contains `J_b`", so G-004 does not arise there. U4 consumes nothing from other units.

**Recommendation:** adopt P-U4-1 (§8). Keep Part B as the fidelity reference for §5.

---

## 1. Conventions

- **Lean.** Everything lives in `BTBMS.Hier` (J route, shared lemmas) and in `BTBMS.Hier.Refl`
  (P-U4-1). The D6.4 helpers live in `BTBMS.IsWeaklyMahlo`, `BTBMS.StationaryIn` (dot notation
  works) and `BTBMS.IsClub` (call `BTBMS.IsClub.exists_gt_ord` by its full name, because
  `IsClub` is Mathlib's root-namespace predicate). The spine names `Hier.S` and `Hier.J` (spine §b, D5.2) are
  kept.
- **Coordinates.** `IsLim o` (spine) is `Lim(o)`: a successor limit `> ω`. In Part B,
  `Order.IsSuccLimit o` alone (a nonzero limit) is written "nonzero limit".
- **Sets.** `J o : ZFSet.{u}`. Lemmas about substructures use `(J o : Set ZFSet.{u})`. For a
  set `X : Set ZFSet.{u}`, `#X` is a `Cardinal.{u+1}`; `ZFSet.card` is a `Cardinal.{u}`.
  The two are related by `Cardinal.lift`. Every cardinal comparison in Part B states which one
  it uses.
- **Formulas (Part B).** `SetFml n` is a local stand-in for CU's `FOFormula`/`Delta0Formula`
  (§5 library plan). `Sat A φ s` is satisfaction in `(A, ∈)`, with quantifiers over `A`. `bex i`
  is the bounded quantifier `∃ y ∈ s_i`.
- **Formulas (Part C).** These are Mathlib first-order formulas
  `FirstOrder.Language.Formula` over `Refl.lang`.
- **Citations.** `[ID]` cites a node of this file or of the spine, and Mathlib or CU
  declarations are cited by full name and file. CU paths are relative to
  `/home/dev/ggg/.deps/lean-4.33.1/cu/ConstructibleUniverse/SetTheory/ZFC/Constructible/`.
  Mathlib paths are relative to `/home/dev/ggg/.deps/lean-4.33.1/mathlib/Mathlib/`.
- **Planned files.** These follow spine §e (`lean/BTBMS/Hier/…`). Part B adds
  `Hier/Formulas.lean`. Part C would add `Hier/Refl/{Language,Translation,Levels,Condensation,Reflection,Instance}.lean`.

---

## 2. Part A — shared nodes

### F5.1a Limit coordinates   (paper: txt:735-736 | new)
**Fidelity:** new (helper facts behind "all coordinates are limits > ω").
**Statement.** For ordinals of universe `u`:
1. `IsLim o → Order.IsSuccLimit o` and `IsLim o → ω < o` (projections);
2. `IsLim o → v < o → v + 1 < o`;
3. `ω ≤ o → IsLim (o + ω)`;
4. if every member of `s` is `IsLim`, `s` is nonempty, `IsLUB s a` and `a ∉ s`, then `IsLim a`;
5. if `f : ℕ → Ordinal` is strictly monotone and `ω ≤ f 0`, then `IsLim (⨆ n, f n)`;
6. `Order.IsSuccLimit w → v < w → v + ω ≤ w` ((8) for every nonzero limit, including
   `w = ω`). <!-- V-U4-7 -->

**Proof.**
1. Item 1: the projections `h.1` and `h.2`.
2. Item 2: `Order.IsSuccLimit.succ_lt h.1 hv` and `Order.succ_eq_add_one`.
3. Item 3:
   - `Ordinal.isSuccLimit_add o Ordinal.isSuccLimit_omega0` (`SetTheory/Ordinal/Arithmetic.lean:377, 943`) gives a successor limit.
   - `ω < ω + ω ≤ o + ω`: `add_le_add_right h ω` and `Ordinal.lt_add_of_pos_right` with `0 < ω`.
4. Item 4:
   - `a ≠ 0`: some `x ∈ s` has `ω < x ≤ a`.
   - `a` is not a successor. If `a = b + 1`, every `x ∈ s` has `x < a` (`a ∉ s`), so `x ≤ b`.
     Then `b` is an upper bound below `a`, which contradicts `IsLUB`.
   - Hence `Order.IsSuccLimit a`, and `ω < x ≤ a`.
5. Item 5. Let `a := ⨆ n, f n`; the range is bounded (`Ordinal.bddAbove_range`).
   - `a` is not attained: `a = f n` would give `f (n+1) ≤ f n`.
   - `a ≠ 0`, since `ω ≤ f 0 ≤ a`.
   - `a` is not a successor: if `a = b + 1`, then `b < a` gives some `f n > b`, so
     `f n ≥ a`; that is, `f n = a`, which contradicts non-attainment. Hence `Order.IsSuccLimit a`.
   - `ω ≤ f 0 < f 1 ≤ a`.
6. Item 6. <!-- V-U4-7 -->
   - For every `n : ℕ`, `v + n < w`, by induction on `n`: `n = 0` is the hypothesis; the step
     is `v + (n+1) = (v + n) + 1 < w` by `Order.IsSuccLimit.succ_lt hw` and
     `Order.succ_eq_add_one` (`Nat.cast_succ`, `add_assoc`).
   - `Ordinal.isNormal_add_right v : Order.IsNormal (v + ·)` (`Arithmetic.lean:373`).
     `Order.IsNormal.le_iff_forall_le` (`Order/IsNormal.lean:61`) at the limit `ω`
     (`Ordinal.isSuccLimit_omega0`) reduces the goal to `∀ b < ω, v + b ≤ w`.
   - `b < ω` gives `b = n` for some `n` (`Ordinal.lt_omega0`); conclude by the first step.

**Uses:** —
**Lean:** `Hier.IsLim.isSuccLimit`, `Hier.IsLim.omega0_lt`, `Hier.IsLim.add_one_lt`,
`Hier.isLim_add_omega0`, `Hier.isLim_of_isLUB`, `Hier.isLim_iSup_nat`,
`Hier.add_omega_le_of_isSuccLimit`; file `Hier/OrdinalFacts.lean`.
**Difficulty:** S (60–120 LOC). Ordinal bookkeeping only.
**Testable:** no (statements about arbitrary ordinals).

### F5.1 (8): `v < u`, `Lim(u)` ⇒ `v + ω ≤ u`   (paper: txt:735-737)
**Fidelity:** as in paper.
**Statement.** `IsLim w → v < w → v + ω ≤ w` (spine name `Hier.add_omega_le`).
**Proof.** [F5.1a] item 6 applied to `hw.1 : Order.IsSuccLimit w` ([F5.1a] item 1). <!-- V-U4-7 -->

**Uses:** F5.1a.
**Lean:** `Hier.add_omega_le` (spine); file `Hier/OrdinalFacts.lean`.
**Difficulty:** S (20–40 LOC). Two Mathlib lemmas.
**Testable:** no.

### D6.4 Finite Mahlo hierarchy and its helpers   (paper: txt:970-975)
**Fidelity:** simplified (S-1 via D-2).
- The locked definitions are `IsWeaklyMahlo` (uncountable regular base) and `IsMahlo` (the
  paper's, inaccessible base), with `IsMahlo.isWeaklyMahlo`.
- U4 proves the facts that U5's seed lemma needs, for `IsWeaklyMahlo`. Strong limitness is
  never needed.

**Statement.** For `κ : Cardinal.{u}`:
1. `isLim_ord`: `ℵ₀ < κ → IsLim κ.ord`;
2. `IsWeaklyMahlo.uncountable_regular`: `IsWeaklyMahlo n κ → ℵ₀ < κ ∧ κ.IsRegular`;
3. `IsWeaklyMahlo.stationary_pred`:
   `IsWeaklyMahlo (n+1) κ → StationaryIn κ {o | ∃ μ, IsWeaklyMahlo n μ ∧ μ.ord = o}`;
4. `StationaryIn.exists_mem_club`: `StationaryIn κ S → IsClub C → ∃ x ∈ C, x.1 ∈ S`, for
   `C : Set (Set.Iio κ.ord)`;
5. `IsClub.exists_gt_ord`: `ℵ₀ < κ → IsClub C → o < κ.ord → ∃ x ∈ C, o < x.1`.

**Proof.**
1. Item 1:
   - `Cardinal.isSuccLimit_ord h.le` (`Arithmetic.lean:1013`);
   - `Cardinal.omega0_lt_ord.2 h` (`SetTheory/Ordinal/Basic.lean:1236`).
2. Item 2: case on `n`. The defining equations of `IsWeaklyMahlo` give `h` for `n = 0` and `h.1` for `n+1`.
3. Item 3: `h.2`.
4. Item 4: unfold `StationaryIn` and `IsStationary` (`SetTheory/Cardinal/Cofinality/Club.lean`, `def IsStationary`).
   Then `hS hC : ({x | x.1 ∈ S} ∩ C).Nonempty`.
5. Item 5:
   - `o + 1 < κ.ord` by item 1 and [F5.1a] item 2.
   - `hC.isCofinal ⟨o+1, _⟩` gives `x ∈ C` with `⟨o+1,_⟩ ≤ x`, so `o < x.1`.

**Uses:** F5.1a.
**Lean:** `Hier.isLim_ord` (spine), `IsWeaklyMahlo.uncountable_regular`,
`IsWeaklyMahlo.stationary_pred`, `StationaryIn.exists_mem_club`, `IsClub.exists_gt_ord`; file
`Hier/OrdinalFacts.lean`.
**Difficulty:** S (40–80 LOC). Unfolding definitions.
**Testable:** no.

### N4.1 Diagram grammar and interface   (spine-defined; paper: txt:874-877)
**Fidelity:** new (S-4). The bodies are FIRM in `Spine.lean`. U4 adds the generic lemmas
N4.1b and N4.1a, which both instances use.
**Statement.** As in spine §c.7: `IsLim`, `Prims`, `BaseAtom`, `BlockAbove`, `Atom`, `Diagram`,
`RealizableBelow` and `Interface`.
**Proof.** Definitions.
**Uses:** —
**Lean:** spine declarations; file `Hier/Diagram.lean`, `Hier/Interface.lean`.
**Difficulty:** S (already written).
**Testable:** no.

### N4.1b Base-level congruence: values and frames   (new)
**Fidelity:** new.
**Statement.**
1. `baseHolds_congr`: if `a = a'` on `baseVars D`, then `BaseHolds P D a ↔ BaseHolds P D a'`.
2. `blockAbove_congr_frame`: if `fr = fr'` on `baseVars D`, then
   `BlockAbove P D fr L w ↔ BlockAbove P D fr' L w`.

**Proof.**
1. Item 1: by cases on each atom. `BaseAtom.Holds` reads `a` only at `BaseAtom.vars`.
2. Item 2. Given a witness `β` for `fr`, put `β' x := o` if `fr' x = some o`, and `β x`
   otherwise.
   - On `baseVars D`, `β' = β` because the frames agree there. So the bounds are unchanged,
     and `BaseHolds` is unchanged by item 1.
   - The frame clause holds by construction.

   The converse is this argument with `fr` and `fr'` exchanged, which is legitimate because the
   hypothesis `h` is symmetric in `fr`, `fr'`. <!-- V-U4-10 -->

**Uses:** N4.1.
**Lean:** `Hier.baseHolds_congr`, `Hier.blockAbove_congr_frame`; file `Hier/Diagram.lean`.
**Difficulty:** S (60–120 LOC).
**Testable:** no.

### N4.1a Congruence and locality of diagram truth   (new)
**Fidelity:** new.
**Statement.** Let `AgreeBelow Q Q' z` mean that `Q.Elem x y ↔ Q'.Elem x y` for all `x, y < z`,
and `Q.Edge c b a ↔ Q'.Edge c b a` for all `c, b, a < z`.
1. `Diagram.holds_congr`: if `a = a'` on `D.vars`, then `D.Holds P a ↔ D.Holds P a'`.
2. `Diagram.holds_congr_below`: if `AgreeBelow Q Q' z` and every `x ∈ D.vars` has `a x < z`,
   then `D.Holds Q a ↔ D.Holds Q' a`.
3. `Diagram.realizableBelow_mono`: `w ≤ w'` gives
   `RealizableBelow P D F σ w → RealizableBelow P D F σ w'`.
4. `Diagram.realizableBelow_congr_below`: if `AgreeBelow Q Q' z` and `w ≤ z`, then
   `RealizableBelow Q D F σ w ↔ RealizableBelow Q' D F σ w`.
5. `Diagram.realizableBelow_congr_fixed`: if `σ = σ'` on `{x ∈ D.vars | F x}`, then
   `RealizableBelow P D F σ w ↔ RealizableBelow P D F σ' w`.

**Proof.**
1. Item 1: by cases on each atom.
   - Base atoms: [N4.1b] item 1.
   - `noReal D' fr u L`: `Atom.vars = u :: L :: (baseVars D').filterMap fr`, so `a u = a' u`
     and `a L = a' L`.
   - The frames `fun x => (fr x).map a` and `fun x => (fr x).map a'` agree on `baseVars D'`,
     since `fr x = some y` puts `y ∈ D.vars`. Conclude by [N4.1b] item 2.
2. Item 2: by cases on each atom.
   - Base atoms read `Q.Elem` and `Q.Edge` at values of `D.vars`, which are `< z`.
   - `noReal D' fr u L`: a witness `β` of `BlockAbove` has every value on `baseVars D'` below
     `a u < z`. So `BaseHolds Q D' β ↔ BaseHolds Q' D' β` by the base case; the other clauses
     do not mention `Q`.
3. Item 3: the same witness works.
4. Item 4: the realization has every `D.vars`-value `< w ≤ z`; apply item 2.
5. Item 5. Given a realization `a` for `σ`, put `a' x := a x` for `x ∈ D.vars`, and otherwise
   `σ' x` if `F x` and `0` if not.
   - Fixedness: on `D.vars ∩ F`, `a x = σ x = σ' x`; off `D.vars`, by definition.
   - Bounds: unchanged on `D.vars`.
   - Truth: item 1.

   The converse is this argument with `σ` and `σ'` exchanged, which is legitimate because the
   hypothesis `h` is symmetric in `σ`, `σ'`. <!-- V-U4-10 -->

**Uses:** N4.1, N4.1b.
**Lean:** `Hier.AgreeBelow`, `Hier.Diagram.holds_congr`, `Hier.Diagram.holds_congr_below`,
`Hier.Diagram.realizableBelow_mono`, `Hier.Diagram.realizableBelow_congr_below`,
`Hier.Diagram.realizableBelow_congr_fixed`; file `Hier/Diagram.lean`.
**Difficulty:** M (150–300 LOC). Case analysis over the grammar, and the `noReal` frame.
**Testable:** no. It is generic over `Prims`; a `Nat`-valued mock could exercise the
bookkeeping, but this is not needed.

---

## 3. Part B — the paper's route (J-hierarchy)

### C5.3b Formulas of set theory, Δ₀ and Σ₁, absoluteness   (paper: txt:776-779)
**Fidelity:** as in paper. It makes explicit the "bounded formula" notions the paper uses.
**Statement.**
- **Definitions** (real bodies):
  - `SetFml n`, with atoms `mem i j` and `eq i j`, and the connectives `neg`, `and`, `ex`, `bex i`;
  - `SetFml.Sat A`;
  - `IsDelta0` (atoms, `neg`, `and`, `bex`);
  - `IsSigma1` (Δ₀, `ex`, `and`, `bex`);
  - `SigmaElem X Y` (`X ⊆ Y` and Σ₁ formulas with parameters in `X` agree);
  - `FullElem X Y` (the same for all formulas).
- **Lemmas:**
  1. `sat_delta0_iff`: `A ⊆ B`, `A` transitive, `φ` Δ₀, `s ∈ A` give `Sat A φ s ↔ Sat B φ s`;
  2. `sat_sigma1_up`: the same hypotheses with `φ` Σ₁ give `Sat A φ s → Sat B φ s`;
  3. `FullElem.sigmaElem`;
  4. `SigmaElem.trans`;
  5. `SigmaElem.mid`: `X ≺₁ Z`, `X ⊆ Y ⊆ Z`, with `X` and `Y` transitive, gives `X ≺₁ Y`.

**Proof.**
1. Lemma 1: induction on `IsDelta0`.
   - Atoms: same value.
   - `neg`, `and`: induction hypothesis.
   - `bex i φ`: `∃ y ∈ A, y ∈ s i ∧ …` versus `∃ y ∈ B, y ∈ s i ∧ …`. A `B`-witness `y ∈ s i ∈ A`
     lies in `A` by transitivity. Apply the induction hypothesis to `Fin.snoc s y`.
2. Lemma 2: induction on `IsSigma1`.
   - The Δ₀ case is lemma 1.
   - `ex`: the witness `y ∈ A ⊆ B`.
   - `and`, `bex`: induction hypothesis.
3. Lemma 3: restrict to Σ₁ formulas.
4. Lemma 4: chain the equivalences; parameters in `X ⊆ Y`.
5. Lemma 5. Let `φ` be Σ₁ with `s ∈ X`.
   - `Sat X → Sat Y` by lemma 2 (`X` transitive, `X ⊆ Y`).
   - `Sat Y → Sat Z` by lemma 2 (`Y` transitive), and then `Sat Z → Sat X` by hypothesis.

**Uses:** —
**Lean:** `Hier.SetFml`, `Hier.SetFml.Sat`, `Hier.SetFml.IsDelta0`, `Hier.SetFml.IsSigma1`,
`Hier.SetFml.sat_delta0_iff`, `Hier.SetFml.sat_sigma1_up`, `Hier.SigmaElem`, `Hier.FullElem`,
`Hier.FullElem.sigmaElem`, `Hier.SigmaElem.trans`, `Hier.SigmaElem.mid`; file `Hier/Formulas.lean`.
**Difficulty:** M (250–500 LOC). It drops to S if CU's `Delta0Formula` (`Delta0.lean:62`) and
`Delta0Formula.satisfies_absolute` (`Delta0.lean:302`) are vendored and only the Σ₁ layer is new.
**Testable:** no.

### D5.2 The basis B, `S(X)` and `J`   (paper: txt:739-766)
**Fidelity:** as in paper. These are the fifteen operations of txt:743-747, in order.
**Statement.** Real bodies:
- `triple x y z = ⟨x, ⟨y, z⟩⟩` (Kuratowski, right associated);
- `fibre r a = {z : ⟨a, z⟩ ∈ r}`;
- the enumeration `BOp` of the fifteen operations, with `BOp.arity` and `BOp.eval`:

  `{x,y}`, `x \ y`, `x × y`, `⋃x`, `dom x`, `x⁻¹`, `{⟨u,v⟩ ∈ x² : u ∈ v}`, `{⟨u,u⟩ : u ∈ x}`,
  `{⟨u,z,v⟩ : z ∈ x, ⟨u,v⟩ ∈ y}`, `{⟨u,v,z⟩ : z ∈ x, ⟨u,v⟩ ∈ y}`, `{x[z] : z ∈ y}`, `x[y]`,
  `⟨x,y⟩`, `⟨x,y,z⟩`, `{x, ⟨y,z⟩}`;
- `succSet X = X ∪ {X}`;
- `S X = X⁺ ∪ {G(x⃗) : G ∈ B, x⃗ ∈ (X⁺)^{arity G}}`;
- `J` by `Ordinal.limitRecOn`, with `J₀ = ∅`, `J_{ξ+1} = S(J_ξ)` and `J_λ = ⋃_{ξ<λ} J_ξ`;
- `BClosed X`.

Lemmas: `J_zero`, `J_add_one`, `J_limit`.
**Proof.**
1. The three unfolding lemmas are `Ordinal.limitRecOn_zero`, `Ordinal.limitRecOn_add_one` and
   `Ordinal.limitRecOn_limit` (`Arithmetic.lean:164-178`).
2. `ZFSet.iUnion` needs `Small.{u} (Set.Iio o)`, which is `Ordinal.small_Iio`
   (`Ordinal/Basic.lean:546`).

**Uses:** —
**Lean:** `Hier.triple`, `Hier.fld`, `Hier.fibre`, `Hier.BOp`, `Hier.BOp.arity`, `Hier.arg`,
`Hier.BOp.eval`, `Hier.succSet`, `Hier.S`, `Hier.J`, `Hier.J_zero`, `Hier.J_add_one`,
`Hier.J_limit`, `Hier.BClosed`; file `Hier/Basis.lean`.
**Difficulty:** M (150–300 LOC), mostly the membership characterizations of the fifteen operations.
**Testable:** yes, externally. Compute `J₀`, `J₁`, `J₂` as hereditarily finite sets (for
example in Python, with Kuratowski pairs). Check transitivity (C5.3a) and `X⁺ ⊆ S(X)`.
- By hand: `J₁ = {∅, {∅}, {{∅}}, ⟨∅,⟨∅,∅⟩⟩, {∅,{{∅}}}}`, and it is transitive.
- `J₃` is too large to enumerate naively: there are up to 15·|J₂⁺|³ generator values.

### D5.2a Bounded graphs of the basis operations and of `S`   (paper: txt:748-749, 760) <!-- V-U4-3 -->
**Fidelity:** as in paper (made explicit; L5.5a and L5.6 use it).
**Statement.**
1. `bOp_graph_delta0`: for each `G : BOp` there is a Δ₀ `γ_G : SetFml (G.arity + 1)` with
   `Sat univ γ_G (x⃗, z) ↔ z = G.eval x⃗` for all `x⃗`, `z`.
2. `S_graph_delta0`: there is a Δ₀ `γ_S : SetFml 2` with `Sat univ γ_S (X, Y) ↔ Y = S X`.

**Proof.**
1. Item 1, for each of the fifteen operations of [D5.2]: write `z = G(x⃗)` as "every member
   of `z` satisfies the defining condition of `G`, and every object that satisfies it is a member
   of `z`" (txt:748-749). Each defining condition is Δ₀ in `x⃗` and the candidate member:
   - pairs and triples: `p = ⟨u, v⟩` is `∀ q ∈ p (q = {u} ∨ q = {u,v}) ∧ ∃ q ∈ p (q = {u}) ∧ ∃ q ∈ p (q = {u,v})`,
     with `q = {u}` and `q = {u,v}` Δ₀;
   - the "every object" direction quantifies over the ingredients of the object, which are
     members of the arguments up to depth 3 (for `dom`, `conv`, `fibre`, `insMid`, `insLast`:
     the coordinates of a pair `p ∈ x` lie in `q ∈ p`), and asserts that the object built from
     them is a member of `z`, as `∃ p ∈ z (p = …)`. For example, for `dom x`:
     `∀ p ∈ x ∀ q ∈ p ∀ u ∈ q ((∃ v ∈ q, p = ⟨u, v⟩) → u ∈ z)`; for `x × y`:
     `∀ u ∈ x ∀ v ∈ y ∃ p ∈ z (p = ⟨u, v⟩)`.
2. Item 2. `Y = S X` iff
   - `X ⊆ Y` and `X ∈ Y` (so `X⁺ ⊆ Y`);
   - for each `G` and each `x⃗` with every `x_i ∈ X ∨ x_i = X` (bounded by `Y`, since `X⁺ ⊆ Y`):
     `∃ z ∈ Y, γ_G(x⃗, z)`;
   - every `z ∈ Y` satisfies `z ∈ X ∨ z = X ∨ ⋁_G ∃ x⃗ (x_i ∈ X ∨ x_i = X) γ_G(x⃗, z)`, again
     with all `x_i` bounded by `Y`.

   All quantifiers are bounded, so `γ_S` is Δ₀ ([C5.3b] `IsDelta0`). Correctness is [D5.2] `S`
   unfolded, with item 1.

**Uses:** C5.3b, D5.2.
**Lean:** `Hier.bOp_graph_delta0`, `Hier.S_graph_delta0`; file `Hier/Basis.lean`.
**Difficulty:** M (200–400 LOC). Fifteen explicit Δ₀ formulas.
**Testable:** no.

### C5.3a Transitivity and closure of the levels   (paper: txt:753-759)
**Fidelity:** as in paper.
**Statement.**
1. `S_isTransitive`: if `X` is transitive, then `S X` is transitive.
2. `succSet_subset_S`.
3. `J_isTransitive`.
4. `J_mono`: `o ≤ o' → J o ⊆ J o'`.
5. `J_mem_J`: `ξ < o → J ξ ∈ J o`.
6. `J_bClosed`: a nonzero limit `o` gives `BClosed (J o)`.

**Proof.**
1. Item 1, members of `X⁺`: they lie in `X⁺`, since `X⁺` is transitive.
2. Item 1, members of each generator value, by cases on the fifteen operations (txt:753-757).
   All arguments are in `X⁺`, so by transitivity all their members, and members of members,
   are in `X⁺`.
   - Set operations (`upair`, `diff`, `sUnion`, `dom`, `fibre`): members lie in `X⁺`.
   - Relation outputs (`prod`, `conv`, `memRel`, `diag`, `insMid`, `insLast`): members are
     `kpair`/`ktriple` values of members of `X⁺`, hence in `S X`.
   - `fibres x y`: members are `fibre x z` with `z ∈ y ⊆ X⁺`, hence `BOp.fibre` values.
   - `kpair x y = {{x},{x,y}}`: members are `upair x x` and `upair x y`.
   - `ktriple x y z = {{x},{x,⟨y,z⟩}}`: members are `upair x x` and `wrap x y z`.
   - `wrap x y z = {x,⟨y,z⟩}`: members are `x ∈ X⁺` and `kpair y z`.
3. Item 2: left summand of the union.
4. Items 3 and 4 by ordinal induction (`Ordinal.induction`):
   - zero: `∅`;
   - successor: item 1, and `J o ⊆ succSet (J o) ⊆ S (J o)` by item 2;
   - limit: a union of an increasing family of transitive sets ([D5.2] `J_limit`).
5. Item 5: `J ξ ∈ succSet (J ξ) ⊆ J (ξ+1) ⊆ J o`, by items 2 and 4.
6. Item 6. Finitely many arguments in `J o` lie in one `J ξ` with `ξ < o` ([D5.2] `J_limit`,
   item 4). Then `G(x⃗) ∈ S (J ξ) = J (ξ+1) ⊆ J o`.

**Uses:** D5.2.
**Lean:** `Hier.S_isTransitive`, `Hier.succSet_subset_S`, `Hier.J_isTransitive`, `Hier.J_mono`,
`Hier.J_mem_J`, `Hier.J_bClosed`; file `Hier/Basis.lean`.
**Difficulty:** M (300–600 LOC). Fifteen membership cases.
**Testable:** yes, on `J₀`–`J₂`, as in D5.2.

### C5.3c Truth tables of fixed formulas   (paper: txt:768-774)
**Fidelity:** as in paper, split into explicit closure steps.
**Statement.** Real bodies:
- `tup n s`, the right-nested tuple code with `∅` terminator;
- `tupSpace T n`, the coded `Tⁿ`;
- `table T φ = {tup n s : s ∈ Tⁿ, Sat T φ s}`.

`table_mem`: if `o` is a nonzero limit, `T ∈ J o` and `T` is transitive, then
`table T φ ∈ J o` for every `φ : SetFml n`.
**Proof.** Fix `o`. Write "available" for "∈ J o". All closure steps use [C5.3a] `J_bClosed`.
1. `tupSpace T n` is available, by induction on `n`:
   - `{∅} = upair ∅ ∅`;
   - `prod T (tupSpace T n)`.
2. Cylindrification (sub-lemma C5.3c-i). For `R ⊆ T^k` available and positions
   `i₁ … i_k < n`, the set `{t ∈ Tⁿ : (t_{i₁},…,t_{i_k}) ∈ R}` is available. Build it by
   induction on `n` from:
   - `insMid` and `insLast`, which insert a coordinate;
   - `conv`, which swaps;
   - `prod`.

   This is the analogue, for the basis B, of Gödel's normal-form theorem: "insertion places
   variables in their required tuple positions; converse and domain give projections",
   txt:771-772.
3. Atomic tables:
   - `mem i j` is the cylinder of `memRel T`;
   - `eq i j` is the cylinder of `diag T`.
4. `neg`: `tupSpace T n \ table T φ`. `and`: `R ∩ R' = R \ (R \ R')`.
5. `ex φ`: the table of `φ` lives in `T^{n+1}`. Re-associate the code so that the last
   coordinate is split off (C5.3c-i), then take `dom` (projection, txt:772-773).
6. `bex i φ`: `∃ y ∈ T (y ∈ s i ∧ φ)`, because `T` is transitive and `s i ∈ T`. Use steps 3-5.
7. Induction on `φ` combines steps 3-6.

**Uses:** D5.2, C5.3a, C5.3b.
**Lean:** `Hier.tup`, `Hier.tupSpace`, `Hier.table`, `Hier.table_mem`; file `Hier/TruthTables.lean`.
**Difficulty:** L (1,500–3,000 LOC). Step 2 is a normal-form theorem for a new basis. CU
proves the Gödel-operation version, which would need a bridge (§5). B contains the nine
operations of Jensen's basis of the rudimentary functions (pair, difference, product, the two
insertions `insMid`/`insLast`, union, domain, `memRel` and the fibre family `fibres`; Jensen
1972 §1, Devlin, *Constructibility*, Ch. VI §1), so step 2 can follow Jensen's proof once his
tuple convention is matched with the right-associated `triple` of [D5.2]. <!-- V-U4-13 -->
**Testable:** partially, externally: tables of small formulas over `T = J₁` inside a computed `J₂`/`J₃`
fragment. Not required.

### C5.3d The uniform bounded table verifier   (paper: txt:775-779)
**Fidelity:** as in paper.
**Statement.** `natSet` and `SetFml.code` (hereditarily finite codes) have real bodies.

`uniform_verifier`: there is a Δ₀ formula `TV(n, code, T, r, t)` such that, for every
nonzero limit `o`, every transitive `T ∈ J o`, every `φ : SetFml n` and every `s ∈ Tⁿ`:
`(∃ r ∈ J o, Sat (J o) TV [n, φ.code, T, r, tup n s]) ↔ Sat T φ s`.
**Proof.**
1. **Record format.** `r` is a finite function from the subformula positions of the parse
   tree of `code` to tables, together with `tupSpace T k` for the arities used (txt:776-777).
2. `TV` checks, with bounded quantifiers only:
   - `r` is a function on the subformula set;
   - each entry is obtained from its children by the local rule of [C5.3c] steps 3-6, with
     each table equality checked in both directions and every assignment quantifier bounded by
     the recorded `tupSpace`;
   - `t` lies in the root entry.

   Hence `TV` is Δ₀ (`IsDelta0`).
3. **Correctness**, by induction on the parse tree: if `TV` passes, every entry equals
   `table T ψ` for its subformula `ψ`. Uniqueness: equal children force an equal parent. So
   `t ∈ root ↔ Sat T φ s`.
4. **Existence**: the true record is available, by [C5.3c] (each table) and finite pairing.
5. `Sat (J o) TV ↔` true `TV`, by [C5.3b] `sat_delta0_iff`, since `J o` is transitive
   ([C5.3a]).

**Uses:** C5.3a, C5.3b, C5.3c.
**Lean:** `Hier.natSet`, `Hier.SetFml.code`, `Hier.uniform_verifier`; file `Hier/TruthTables.lean`.
**Difficulty:** L (1,000–2,500 LOC). Coded syntax and record checking. CU
`CodedSatisfaction.lean` (`boundedSatisfactionRelation`, `:39`;
`boundedSatisfactionRelation_mem_rudimentaryClosure`, `:45`) is a pattern for its own
rudimentary basis.
**Testable:** no.

### C5.3e `S(T)` inside closed levels   (paper: txt:780-797)
**Fidelity:** as in paper.
**Statement.** `S_mem`: if `o` is a nonzero limit, `T ∈ J o` and `T` is transitive, then
`S T ∈ J o`.
**Proof.** Everything below is built in `J o` via [C5.3c] and [C5.3a] `J_bClosed`.
1. `T⁺ = T ∪ {T}` is available (`upair`, `sUnion`). It is transitive.
2. Write `U = T⁺ ∪ (T⁺ × T⁺)` and
   `B_{T⁺} = T⁺ ∪ (T⁺ × T⁺) ∪ (T⁺ × (T⁺ × T⁺)) ∪ F_{T⁺} ∪ P_U`, where:
   - `P_X = {{x,y} : x,y ∈ X}`;
   - `F_X = {r[a] : r, a ∈ X}`;
   - both are fibre families of incidence tables (txt:782-786).

   Every member of every generator value on arguments from `T⁺` lies in `B_{T⁺}`. Check per
   operation, as in [C5.3a] step 2.
3. For each `G`, the relation `R_G = {⟨tup s, z⟩ : s ∈ (T⁺)^k, z ∈ B_{T⁺}, z ∈ G(s)}` is a table
   of a fixed Δ₀ formula over a transitive available set containing `T⁺` and `B_{T⁺}` ([C5.3c]).
4. `fibres R_G (tupSpace T⁺ k) = {G(s) : s ∈ (T⁺)^k}`, because each fibre equals `G(s) ⊆ B_{T⁺}`.
5. `S T` is the union of `T⁺` and the fifteen sets of step 4.

**Uses:** C5.3a, C5.3c.
**Lean:** `Hier.S_mem`; file `Hier/TruthTables.lean`.
**Difficulty:** L (600–1,200 LOC).
**Testable:** no.

### C5.3 Truth tables, bounded verifier, `S(T)` inside closed levels   (paper: txt:768-798)
**Fidelity:** as in paper (umbrella).
**Statement.** The conjunction of C5.3a–C5.3e.
**Proof.** [C5.3a], [C5.3b], [C5.3c], [C5.3d], [C5.3e].
**Uses:** C5.3a, C5.3b, C5.3c, C5.3d, C5.3e.
**Lean:** as listed in the sub-nodes.
**Difficulty:** L–XL (3,650–7,800 LOC in total).
**Testable:** see the sub-nodes.

### C5.4 (9) Heights and sizes   (paper: txt:799-807)
**Fidelity:** as in paper.
**Statement.** Let `o` be a nonzero limit.
1. `toZFSet_mem_J_iff`: `ξ.toZFSet ∈ J o ↔ ξ < o`. Together with
   `Ordinal.toZFSetIso` (`SetTheory/ZFC/Ordinal.lean:402`), this is `Ord ∩ J_o = o`.
2. `rank_J`: `(J o).rank = o`.
3. `card_J_le` (any `ξ`): `(J ξ).card ≤ max ℵ₀ ξ.card` (with `ZFSet.card`, `Cardinal.{u}`).

**Proof.**
1. **Size**, by induction on `ξ`:
   - `|S X| ≤ |X⁺| + Σ_G |X⁺|^{arity G} ≤ max ℵ₀ |X|`, because the arities are finite and
     `Cardinal.mk_range_le` applies;
   - at limits, `|⋃_{ξ<λ} J_ξ| ≤ |λ| · sup ≤ max ℵ₀ |λ|` (`Cardinal.mk_iUnion_le`).
2. **Rank upper bound.** Every argument of a generator lies in `X⁺`, whose rank is
   `rank X + 1`. Each operation adds at most 4 to the rank of its arguments; `ktriple` is the
   worst case. Hence `rank S(X) ≤ rank X + 5`, and `rank J_{η+n} ≤ η + 5n` for `η = 0` or a
   limit (Nat induction). So `rank J_λ ≤ λ` at limits (`ZFSet.rank`,
   `SetTheory/ZFC/Rank.lean:139`).
3. **Lower bound at `ω`.** `n ∈ J_{3n+1}`, by induction using
   `n+1 = ⋃{n, {n}}`, and `upair`, `sUnion`.
4. **Block step** for a limit `η` with `Ord ∩ J_η = η`:
   - `η = {x ∈ J_η : x is an ordinal}` is the projection of the table, over `T = J_η`, of
     the fixed Δ₀ formula "transitive and linearly ordered by ∈";
   - `J_η ∈ J_{η+1} ⊆ J_{η+ω}` [C5.3a], so [C5.3c] `table_mem` at the nonzero limit
     `o = η + ω`, followed by `dom` ([C5.3a] `J_bClosed`), gives `η ∈ J_{η+ω}`;
   - then `η + n ∈ J_{η+ω}` for every `n`, by induction on `n` with
     `η + (n+1) = ⋃{η+n, {η+n}}` and `J_bClosed` (`upair`, `sUnion`). <!-- V-U4-8 -->
5. **Limits of limits**: union (txt:806-807).
6. From steps 2-5: for limit `o`, every `ξ < o` is in `J o`, and every ordinal in `J o` has
   rank `< o`. This gives item 1. Item 2 follows from step 2 and `o ⊆ J o`.

**Uses:** D5.2, C5.3a, C5.3c.
**Lean:** `Hier.toZFSet_mem_J_iff`, `Hier.rank_J`, `Hier.card_J_le`; file `Hier/Height.lean`.
**Difficulty:** L (800–1,800 LOC). The rank and block induction is delicate. CU
`LStageZFCardinality.card_LStageZF_le_max` (`:56`) and `CondensationCore.ordinalHeight` (`:46`) are
the L-analogues (patterns only).
**Testable:** yes, for the finite part: `Ord ∩ J_n` for `n ≤ 2`, computed externally.

### L5.5a Histories: the bounded check and uniqueness   (paper: txt:813-815)
**Fidelity:** as in paper.
**Statement.** `history ξ = {⟨η, J_η⟩ : η ≤ ξ}` (real body). `histOK_exists`: there is a
Δ₀ formula `HistOK(h, ξ, x)` (a `SetFml 3`) such that, evaluated in `Set.univ`:
1. `HistOK(history ξ, ξ, J ξ)` holds;
2. `HistOK(h, ξ, x)` implies `h = history ξ` and `x = J ξ` (uniqueness);
3. `HistOK(h, z, x)` implies `z.IsOrdinal` for every set `z`; hence `z = ξ.toZFSet` with
   `ξ = z.rank` (`ZFSet.IsOrdinal.toZFSet_rank_eq`, `SetTheory/ZFC/Ordinal.lean`), and item 2
   applies. L5.5b step 2 and L5.6 steps 5-6 need this for a middle argument that is only known
   to be a set. <!-- V-U4-2 -->

L5.5b, L5.5c, L5.5g, L5.6 and L5.8a use this `HistOK`. Inside a transitive level it is
evaluated through [C5.3b] `sat_delta0_iff`.
**Proof.**
1. `HistOK(h, ξ, x)` says:
   - `ξ` is an ordinal (Δ₀: a transitive set of transitive sets,
     `ZFSet.isOrdinal_iff_forall_mem_isTransitive`); <!-- V-U4-2 -->
   - `h` is a function on `ξ+1` with `h(0) = ∅`;
   - `h(η+1) = S(h η)`, by the Δ₀ graph `γ_S` of [D5.2a] item 2 (txt:760); <!-- V-U4-3 -->
   - `h(λ) = ⋃_{η<λ} h η`;
   - `h(ξ) = x`.

   All quantifiers are bounded by `h`, `ξ` or the values of `h`.
2. Item 1: [D5.2] unfolding lemmas, and `ZFSet.isOrdinal_toZFSet`.
3. Item 2: by external induction on `η ≤ ξ`, `h(η) = J_η` ([D5.2] unfolding lemmas).
4. Item 3: the first conjunct.

**Uses:** D5.2, D5.2a, C5.3b.
**Lean:** `Hier.history`, `Hier.histOK_exists`; file `Hier/Hulls.lean`.
**Difficulty:** M (300–600 LOC). The Δ₀ graph of `S` is the bulk.
**Testable:** no.

### L5.5b The history budget   (paper: txt:809, 820-825)
**Fidelity:** as in paper.
**Statement.** `history_mem`: `history ξ ∈ J (ξ + ω)`.
**Proof.** Block induction over `η = 0` or `η` a limit, proving the claim for
`ξ ∈ [η, η+ω)`.
1. Every `ζ < η` has `history ζ ∈ J η`: the induction hypothesis gives
   `history ζ ∈ J (ζ + ω)`, and `ζ + ω ≤ η` by [F5.1a] item 6 (`η` is a nonzero limit,
   possibly `ω`, so [F5.1] does not apply), then [C5.3a] `J_mono`. <!-- V-U4-7 -->
2. `history↾η = {⟨ζ, J_ζ⟩ : ζ < η}` is the set of `p ∈ J_η` with
   `∃ ζ, x, h ∈ J_η (p = ⟨ζ,x⟩ ∧ HistOK(h,ζ,x))`. Indeed, by [L5.5a] item 3 every such `ζ` is
   an ordinal, hence `ζ < η` by [C5.4] (`ζ ∈ J η`), and [L5.5a] item 2 gives `x = J ζ`;
   conversely step 1, [L5.5a] item 1 and [C5.3b] `sat_delta0_iff` (`J η` transitive) supply
   the witnesses. This is a fixed formula over `T = J_η`. <!-- V-U4-2 -->
3. `J_η ∈ J_{η+1}` [C5.3a]. By [C5.3c] with `o = η+ω` and `T = J_η`, the table is in
   `J_{η+ω}`. Its domain (`dom`) gives `history↾η ∈ J_{η+ω}`.
4. `history (η+n)` adds the pairs `⟨η+i, J_{η+i}⟩`, `i ≤ n`. These are in `J_{η+ω}` by
   [C5.3a] `J_mem_J` and `kpair`; `upair` and `sUnion` finish.
5. Limits of blocks: every `ξ` lies in some block.

**Uses:** F5.1a, C5.3a, C5.3b, C5.3c, C5.4, L5.5a.
<!-- V-U4-7, V-U4-2: Uses changed -->
**Lean:** `Hier.history_mem`; file `Hier/Hulls.lean`.
**Difficulty:** L (1,000–2,500 LOC). CU `CanonicalBareHistoryGlobal.canonicalBareHistory_mem_LStageZF_add_omega`
(`:85`) is the same theorem for L; its proof architecture is reusable.
**Testable:** no.

### L5.5g `ξ ↦ J_ξ` is globally single-valued Σ₁   (paper: txt:808-815)
**Fidelity:** as in paper.
**Statement.** `J_sigma1`: there is a Σ₁ `φ(ξ, x)` such that, for every limit `o` (`IsLim`),
every `ξ < o` and every `x ∈ J o`: `Sat (J o) φ [ξ, x] ↔ x = J ξ`.
**Proof.**
1. `φ := ∃ h HistOK(h, ξ, x)`, with `HistOK` from [L5.5a]. It is Σ₁.
2. `Sat (J o) φ ↔ ∃ h ∈ J o, HistOK(h, ξ, x)`, by [C5.3b] `sat_delta0_iff` (`J o` is
   transitive, [C5.3a]).
3. (→) [L5.5a] item 2 gives `x = J ξ`.
4. (←) `history ξ ∈ J (ξ+ω)` [L5.5b], `ξ + ω ≤ o` [F5.1], and so `history ξ ∈ J o` by
   [C5.3a] `J_mono`. [L5.5a] item 1 gives `HistOK(history ξ, ξ, J ξ)`.

**Uses:** F5.1, C5.3a, C5.3b, L5.5a, L5.5b.
**Lean:** `Hier.J_sigma1`; file `Hier/Hulls.lean`.
**Difficulty:** M (150–300 LOC). CU `ValidStageHistoryFormula.lean` and
`StageHistoryFunctionality.lean` do the same for L (pattern).
**Testable:** no.

### L5.5c The canonical well-order `<_J`   (paper: txt:816-829)
**Fidelity:** as in paper.
**Statement.** `canonical_order`: there are a relation `lt` and a Σ₁ `φ(x, I)` such that:
- `lt` is well-founded;
- it is end-extending: `y ∈ J ξ` and `lt x y` give `x ∈ J ξ`;
- for every limit `o` and `x ∈ J o`:
  - `lt` is total on `J o`;
  - `I_x = {y : lt y x}` is a member of `J o`;
  - for `I ∈ J o`, `Sat (J o) φ [x, I] ↔ I = I_x`.

**Proof.**
1. Define `<_ξ` on `J_ξ` by recursion:
   - `<_0 = ∅`;
   - at `ξ+1`: the old elements in `<_ξ`, then `J_ξ` itself, then the new generator values,
     ordered by their least production code (generator index, then the argument tuple in the
     lexicographic order induced by `<_ξ` on `J_ξ⁺`);
   - at limits: the union.
2. Each `<_ξ` is a well-order: finite lexicographic products of well-orders are well-orders
   (`WellFounded.prod_lex`, `Prod.Lex`). Each `<_ξ` is end-extended by `<_{ξ'}` for
   `ξ ≤ ξ'` (external induction).
3. `lt := ⋃_ξ <_ξ` is well-founded and end-extending (step 2).
4. **Decorated histories** `(history ξ, ⟨<_η⟩_{η≤ξ})`: a Δ₀ check as in [L5.5a] step 1, with
   the order clauses. They are unique (external induction), and they have the budget
   `J_{ξ+ω}`, by the argument of [L5.5b] with the order added: at `η` the order is a
   fixed-formula relation over `J_η` (txt:821-825).
5. `I_x = {y ∈ J_ξ : y <_ξ x}` for any `ξ` with `x ∈ J_ξ`; by end-extension it does not
   depend on `ξ`. For `x ∈ J o`, `o` limit, choose `ξ < o`. Then `I_x ∈ J o`, by step 4 and
   [F5.1].
6. `φ(x, I) := ∃` a decorated history through some `ξ` with `x ∈ J_ξ` and
   `I = {y ∈ J_ξ : y <_ξ x}`. This is Σ₁, and it is correct over `J o` by steps 4-5.

**Uses:** F5.1, D5.2, C5.3a, C5.3b, C5.3c, L5.5a, L5.5b.
**Lean:** `Hier.canonical_order`; file `Hier/Hulls.lean`.
**Difficulty:** XL (2,000–4,000 LOC). A new decorated recursion, its uniqueness and its
budget. CU `CanonicalStageOrder.canonicalStageRel_isWellOrder` (`:115`), `InternalWellOrder.lean`
and `CoherentLimitOrder.lean` are the L analogues (pattern only).
**Testable:** no.

### L5.5f The canonical Σ₁ hull (definition)   (paper: txt:810-812, 860)
**Fidelity:** as in paper. The paper defines the hull as the closure under the canonical
Σ₁ Skolem functions. Here it is the set of elements Σ₁-definable over `J_C` from parameters
in `X`. The two agree by [L5.5d] step 5 and [L5.5e] item 3.
**Statement.** `hull C X := {x ∈ J C | ∃ Σ₁ φ, ∃ p ∈ X^n, J C ⊨ φ(p, x) ∧ ∀ y ∈ J C (J C ⊨ φ(p, y) → y = x)}`
(real body).
**Proof.** Definition.
**Uses:** C5.3b, D5.2.
**Lean:** `Hier.hull`; file `Hier/Hulls.lean`.
**Difficulty:** S (10 LOC; written).
**Testable:** no.

### L5.5d Compatible canonical Σ₁ Skolem functions   (paper: txt:830-838)
**Fidelity:** as in paper.
**Statement.** `skolem_compatible`: for every Σ₁ `φ(p, y)` there is a partial function
`h C p` such that:
- for limit `C` and `p ∈ J C`, `h C p` is defined iff `∃ y ∈ J C, Sat (J C) φ (p, y)`;
- if `h C p = some y`, then `y` is a witness and `y ∈ hull C {p_i}`;
- for limits `D ≤ C`, `p ∈ J D` and `h D p` defined, `h C p = h D p`.

**Proof.**
1. **Normal form** (sub-lemma L5.5d-i): over limit levels, every `IsSigma1` formula is
   equivalent to `∃ y ϑ` with `ϑ` Δ₀. Pair the witnesses (`kpair`, [C5.3a] closure), and move
   `bex` across `ex`.
2. `V(code, p, q)`: `q = ⟨y, T, r⟩` with:
   - `T` transitive and `p, y ∈ T`;
   - `TV(code ϑ, T, r, tup(p, y))` (Δ₀, [C5.3d]).

   `V` is Δ₀. If `V` passes, then `Sat T ϑ (p,y)`, hence `Sat (J C) ϑ (p,y)` by [C5.3b].
3. A witness `y ∈ J C` has a record in `J C`. Take `T = J_ξ`, `ξ < C`, containing `p, y`
   ([D5.2] `J_limit`, [C5.3a]). Then [C5.3d] gives the record in `J C` (txt:832-833).
4. `h C p :=` the `y`-component of the `lt`-least `q ∈ J C` with `V(code, p, q)`
   ([L5.5c]: `lt` is well-founded and total on `J C`).
5. **Σ₁ definition over `J C`**: `y = h(p) ↔ ∃ q, I (q = ⟨y,…⟩ ∧ V ∧ φ_{L5.5c}(q, I) ∧ ∀ q' ∈ I ¬V)`.
   This gives `h C p ∈ hull C {p_i}` (definition of `hull`).
6. **Compatibility.** Let `q` be least in `J D`.
   - `I_q ⊆ J D` by end-extension [L5.5c], so `q` is least in `J C`.
   - Hence `h C p = h D p` (txt:836-838).

**Uses:** C5.3a, C5.3b, C5.3d, D5.2, L5.5c, L5.5f.
**Lean:** `Hier.skolem_compatible`; file `Hier/Hulls.lean`.
**Difficulty:** L (1,500–3,000 LOC).
**Testable:** no.

### L5.5e Hulls: elementarity, monotonicity, continuity, size, compatibility   (paper: txt:808-812, 839-841, 867-871)
**Fidelity:** as in paper.
**Statement.** For `hull` as in [L5.5f] and `X ⊆ J C`:
1. `subset_hull`: `X ⊆ hull C X`.
2. `hull_mono`.
3. `hull_sigmaElem` (`IsLim C`): `SigmaElem (hull C X) (J C)`.
4. `hull_iUnion`: equality on directed unions.
5. `card_hull_le`: `#(hull C X) ≤ max ℵ₀ #X` (both `Cardinal.{u+1}`).
6. `hull_subset_of_le` (`D ≤ C` limits, `X ⊆ J D`): `hull D X ⊆ hull C X`.
7. `hull_eq_of_sigmaElem` (`J C ≺₁ J D`): `hull D X = hull C X`.

**Proof.**
1. Item 1: `x` is defined by `y = x`.
2. Item 2: parameters from `X ⊆ Y`.
3. Item 3. Induction on `IsSigma1` and `IsDelta0`, proving `Sat H ψ s ↔ Sat (J C) ψ s` for
   `s ∈ H`:
   - atoms: the same;
   - `neg`, `and`: induction hypothesis;
   - `bex i φ` and `ex φ`: a witness exists in `J C`; take `h C s` of [L5.5d] for `∃ y (y ∈ s_i ∧ φ)`
     (respectively `∃ y φ`).
   - `h C s ∈ H` by [L5.5d] and closure of `hull` under Σ₁-definable functions of its
     elements: compose the defining formulas of the `s_i` with that of `h`, giving
     `∃ p⃗ (⋀ φ_i ∧ y = h(p⃗))` (txt:839-840).
4. Item 4: a definition uses finitely many parameters, which lie in one `X_i` (directedness).
5. Item 5: `hull C X` is the image of the countable set of pairs (Σ₁ formula, finite tuple of
   `X`) under a partial map. Use `Cardinal.mk_le_of_surjective` and `Cardinal.mk_list_le_max`
   (`SetTheory/Cardinal/Arithmetic.lean:746`). <!-- V-U4-5 -->
6. Item 6. `x ∈ hull D X` is defined by `φ(p, ·)`. Then `h D p = x` (uniqueness), and
   [L5.5d] compatibility gives `h C p = x`, so `x ∈ hull C {p}` ⊆ `hull C X`.
7. Item 7.
   - (⊆) `J D ⊨ ∃ y φ(p,y)` reflects to `J C`. The witness `y'` satisfies `φ` in `J D`
     (upward, [C5.3b]), so `y' = x`. Uniqueness in `J C` again goes upward.
   - (⊇) Uniqueness in `J D`: a second witness gives the Σ₁ statement
     `∃ y (φ(p,y) ∧ ¬ y = x)` in `J D`. It reflects to `J C`, which is a contradiction.

**Uses:** C5.3a, C5.3b, D5.2, L5.5d, L5.5f.
**Lean:** `Hier.subset_hull`, `Hier.hull_mono`, `Hier.hull_sigmaElem`,
`Hier.hull_iUnion`, `Hier.card_hull_le`, `Hier.hull_subset_of_le`, `Hier.hull_eq_of_sigmaElem`;
file `Hier/Hulls.lean`.
**Difficulty:** L (600–1,200 LOC).
**Testable:** no.

### L5.5 History and hull lemma   (paper: txt:808-841)
**Fidelity:** as in paper (umbrella).
**Statement.** The conjunction of L5.5a–L5.5g.
**Proof.** [L5.5a], [L5.5b], [L5.5c], [L5.5d], [L5.5e], [L5.5f], [L5.5g].
**Uses:** L5.5a, L5.5b, L5.5c, L5.5d, L5.5e, L5.5f, L5.5g.
**Lean:** as in the sub-nodes.
**Difficulty:** XL (5,700–12,000 LOC in total).
**Testable:** no.

### L5.6a Collapse of a Σ₁ substructure   (paper: txt:844-845)
**Fidelity:** as in paper.
**Statement.** `collapse H` is the Mostowski collapse `π(x) = {π(y) : y ∈ x ∩ H}`, defined by
`WellFounded.fix` on `∈` (real body).
1. `collapse_injOn` (`IsLim C`, `SigmaElem H (J C)`): `π` is injective on `H`, and
   `π x ∈ π y ↔ x ∈ y` for `x, y ∈ H`.
2. `collapse_eq_self`: `π x = x` for `x ∈ T`, when `T` is transitive and `T ⊆ H`.
3. `collapse_image_transitive` (any `H`): `N := π[H]` is transitive. <!-- V-U4-1 -->
4. `collapse_sat_iff_image` (`IsLim C`, `SigmaElem H (J C)`): for every formula `φ` and
   `s ∈ H`, `Sat H φ s ↔ Sat N φ (π ∘ s)`. <!-- V-U4-1 -->

**Proof.**
1. **Extensionality of `H`.** For `x ≠ y` in `H`, the Σ₁ statement
   `∃ z (z ∈ x ∧ ¬ z ∈ y ∨ z ∈ y ∧ ¬ z ∈ x)` is true in `J C` (extensional, transitive). It
   reflects to `H`, giving a witness `z ∈ H` (txt:844).
2. Mostowski: ∈-induction on `H`. This is CU `MostowskiCollapse.collapse_injective_on`
   (`MostowskiCollapse.lean:117`) and `collapse_mem_collapse_iff` (`:171`), stated for a
   `ZFSet` domain with `IsExtensional` (`:75`). Convert `H` (small, since `H ⊆ J C`) by
   `ZFSet.sep`.
3. Item 2: ∈-induction (CU `collapse_eq_self_of_mem`, `:209`).
4. Item 3: a member of `π x` (`x ∈ H`) is `π y` with `y ∈ x ∩ H` (definition of `collapse`),
   hence in `π[H]` (CU `range_isTransitive`, `:65`). <!-- V-U4-1 -->
5. Item 4: induction on `φ`, using item 1. Atoms: `π x ∈ π y ↔ x ∈ y` and injectivity.
   `neg`, `and`: induction hypothesis. `ex`, `bex`: a witness `y ∈ H` maps to `π y ∈ N`, and
   every `y' ∈ N` is `π y` for some `y ∈ H`; for `bex i`, `π y ∈ π (s i) ↔ y ∈ s i` (item 1).
   This is CU `MostowskiElementarity.satisfies_equivRange_iff` (`:43`) for ZFSet domains.
   <!-- V-U4-1 -->

**Uses:** C5.3b, D5.2.
**Lean:** `Hier.collapse`, `Hier.collapse_injOn`, `Hier.collapse_eq_self`,
`Hier.collapse_image_transitive`, `Hier.collapse_sat_iff_image`; file `Hier/Condensation.lean`.
**Difficulty:** M (200–500 LOC). It drops to S with CU vendored.
**Testable:** no.

### L5.6 Condensation   (paper: txt:842-853)
**Fidelity:** as in paper.
**Statement.**
1. `condensation`: if `IsLim C` and `SigmaElem H (J C)`, there is `δ` with `IsLim δ`,
   `δ ≤ C` and `π[H] = J δ`. Moreover, if `ξ.toZFSet ∈ H` and `J ξ ∈ H`, then
   `π(ξ) = ξ'` and `π(J ξ) = J ξ'` for some `ξ'`.
2. `collapse_sat_iff`: `Sat H φ s ↔ Sat (J δ) φ (π ∘ s)` for `s ∈ H`, given `π[H] = J δ`.

**Proof.** Write `N := π[H]`. Steps 2-6 transfer formulas between `H` and `N` by [L5.6a]
`collapse_sat_iff_image`; they never use item 2, which presupposes `N = J δ`. <!-- V-U4-1 -->
1. `N` is transitive ([L5.6a] `collapse_image_transitive`), and `π : H ≅ N` is an
   ∈-isomorphism ([L5.6a] `collapse_injOn`). Item 2 is [L5.6a] `collapse_sat_iff_image`
   rewritten with `π[H] = J δ` (the first clause of item 1, proved in steps 4-6).
2. **`N` is B-closed.**
   - `J C` is B-closed [C5.3a], and each `G` has the Δ₀ graph `γ_G` of [D5.2a] item 1.
   - `∃ z γ_G(y⃗, z)` is Σ₁ and true in `J C` for `y⃗ ∈ H`, so it holds in `H` with `z ∈ H`
     (`SigmaElem H (J C)`; then `Sat H γ_G ↔ Sat (J C) γ_G` for these parameters, again by
     `SigmaElem`, and `Sat (J C) γ_G ↔ z = G(y⃗)` by [C5.3b] `sat_delta0_iff`).
   - Transfer by [L5.6a] `collapse_sat_iff_image`: `Sat N γ_G (π y⃗, π z)`, which means
     `π z = G(π y⃗)` by [C5.3b] `sat_delta0_iff` (`N` transitive, step 1) and [D5.2a].
3. **`ω ∈ H` and `π(ω) = ω`.** `ω` is the unique Δ₀-definable "least nonzero limit".
   Existence reflects (`SigmaElem H (J C)`), and `π` preserves the definition
   ([L5.6a] `collapse_sat_iff_image`, [C5.3b] `sat_delta0_iff`).
4. `δ := Ord ∩ N` is an ordinal (`N` transitive), `> ω` by step 3, and a limit by successor
   closure (step 2: `o+1 = ⋃{o, {o}}`).
5. **`J_δ ⊆ N`.** For `ν < δ`, let `ν' := π⁻¹ ν ∈ H`. It is an ordinal: ordinalhood is Δ₀,
   true of `ν` in `N`, hence true of `ν'` in `H` ([L5.6a] `collapse_sat_iff_image`) and in
   `J C` (`SigmaElem`), hence true ([C5.3b] `sat_delta0_iff`); so `ν' = ζ.toZFSet` with
   `ζ < C` ([C5.4], `ZFSet.IsOrdinal.toZFSet_rank_eq`).
   - `history ζ ∈ J C`, by [L5.5b], [F5.1] (`ζ + ω ≤ C`) and [C5.3a] `J_mono`.
   - `∃ h, x HistOK(h, ν', x)` is Σ₁ and true in `J C` ([L5.5a] item 1, [C5.3b]
     `sat_delta0_iff`), so it reflects to `H`: some `h, x ∈ H` satisfy it there.
   - Collapsing ([L5.6a] `collapse_sat_iff_image`) gives `HistOK(π h, ν, π x)` in `N`,
     which is true by [C5.3b] `sat_delta0_iff`. So `π x = J ν` ([L5.5a] item 2).
   - Hence `J ν ∈ N`, and `J_ν ⊆ N` by transitivity; `J_δ = ⋃_{ν<δ} J_ν ⊆ N` ([D5.2] `J_limit`).
6. **`N ⊆ J_δ`.** For `x = π x'` with `x' ∈ H ⊆ J C`, the statement
   `∃ ξ, h, y (HistOK(h, ξ, y) ∧ x' ∈ y)` is Σ₁, and true in `J C` ([D5.2] `J_limit`,
   [L5.5a] item 1, [L5.5b]).
   - Reflect it to `H`: witnesses `ξ'', h'', y'' ∈ H`. Collapse ([L5.6a]
     `collapse_sat_iff_image`) and use [C5.3b] `sat_delta0_iff`: `HistOK(π h'', π ξ'', π y'')`
     is true. By [L5.5a] item 3, `π ξ''` is an ordinal `ν ∈ N`, so `ν < δ`; by [L5.5a] item 2,
     `π y'' = J_ν`; and `x = π x' ∈ π y''` ([L5.6a] `collapse_injOn`). <!-- V-U4-2 -->
7. **`δ ≤ C`.** On ordinals of `H`, `π` is order-preserving and `π o ≤ o`, so
   `δ = otp(H ∩ Ord) ≤ C`.
8. **Final clause**: for `ξ.toZFSet, J ξ ∈ H`, the Σ₁ statement `∃ h HistOK(h, ξ, J ξ)` is
   true in `J C` (`history ξ ∈ J C` as in step 5) and reflects to `H`; collapsing as in step 5
   gives `HistOK(π h, π ξ, π (J ξ))` true, so `π ξ = ξ'.toZFSet` ([L5.5a] item 3) and
   `π (J ξ) = J ξ'` ([L5.5a] item 2).

**Uses:** F5.1, C5.3a, C5.3b, C5.4, D5.2, D5.2a, L5.5a, L5.5b, L5.6a.
<!-- V-U4-1, V-U4-3: Uses changed -->
**Lean:** `Hier.condensation`, `Hier.collapse_sat_iff`; file `Hier/Condensation.lean`.
**Difficulty:** XL (2,000–4,000 LOC). This is the largest single item (R-6). CU's
`StandardCondensation.condensation_of_elementary_isSuccLimit` (`:66`) needs full elementarity
(`FiniteFragmentSkolemHull.SatisfactionAbsolute`, `:57`) and the L-hierarchy, so it is not
usable.
**Testable:** no.

### D5.7 Control edges (10) and the J primitives   (paper: txt:859-861)
**Fidelity:** as in paper.
**Statement.** Real bodies:
- `JElem a b := IsLim a ∧ IsLim b ∧ a ≤ b ∧ SigmaElem (J a) (J b)`;
- `JEdge C b a := IsLim a ∧ IsLim b ∧ IsLim C ∧ a < b ∧ b < C ∧ hull C (J a ∪ {b}) ∩ J b = J a ∧ SigmaElem (J b) (J C)`;
- `jPrims := ⟨JElem, JEdge⟩`.

The basic properties of txt:862-873 are the sub-nodes D5.7a–D5.7d, which use this node.
**Proof.** Definitions.
**Uses:** C5.3b, D5.2, L5.5f.
**Lean:** `Hier.JElem`, `Hier.JEdge`, `Hier.jPrims`; file `Hier/ControlEdge.lean`.
**Difficulty:** S for the definitions (30 LOC); 600–1,200 LOC together with D5.7a–D5.7d.
**Testable:** no.

### D5.7a Edges give `J_a ≺ J_b`; repair of G-004   (paper: txt:864-866)
**Fidelity:** repaired (G-004). The paper says "the hull contains the whole `J_b`". That must
mean `J_b ∈ H`. The reading `J_b ⊆ H` would give `H ∩ J_b = J_b ≠ J_a`, since
`a ∈ J_b \ J_a` by [C5.4], contradicting (10). The repaired argument is membership followed by
relativized Tarski–Vaught.
**Statement.**
1. `J_mem_controlHull`: `JEdge C b a → J b ∈ hull C (J a ∪ {b})`.
2. `fullElem_inter_of_mem`: if `M` is transitive, `SigmaElem H M` and `T ∈ H`, then
   `FullElem (H ∩ T) T`.
3. `fullElem_of_edge`: `JEdge C b a → FullElem (J a) (J b)`.

**Proof.**
1. Item 1. `H := hull C (J a ∪ {b})`.
   - `b ∈ H` by [L5.5e] `subset_hull`.
   - The formula `φ(b, x)` of [L5.5g] `J_sigma1` holds in `J C` exactly at `x = J b`, for
     `x ∈ J C`. Here `b < C` (edge), and `J b ∈ J C` by [C5.3a] `J_mem_J`.
   - So `J b` is Σ₁-definable over `J C` from the parameter `b ∈ J a ∪ {b}`; that is
     `J b ∈ H` by the definition of `hull` (with `n = 1`, `p = [b]`).
2. Item 2.
   - **Relativization.** For each `φ`, `φ^T` (all quantifiers bounded by the parameter `T`) is
     Δ₀, and `Sat T φ s ↔ Sat M φ^T (s, T)` for `s ∈ T` (`M` transitive). CU has
     `Delta0Formula.relativize` (`Delta0.lean:96`) and `satisfies_relativize` (`:230`).
   - **Tarski–Vaught for `H ∩ T ⊆ T`**, by induction on `φ`, `s ∈ H ∩ T`. Case `ex`: a
     `T`-witness gives `Sat M (bex T φ^T)(s, T)`, which is Δ₀. Σ₁ elementarity puts a witness
     `y ∈ H` with `y ∈ T` and `Sat M φ^T(s, y, T)`, hence `Sat T φ (s, y)`; apply the
     induction hypothesis.
3. Item 3. `H ∩ J b = J a` (edge), `J b ∈ H` (item 1), and `H ≺₁ J C` ([L5.5e], `J C`
   transitive by [C5.3a]). Item 2 gives `J a = H ∩ J b ≺ J b`.

**Uses:** C5.3a, C5.3b, C5.4, D5.7, L5.5e, L5.5f, L5.5g.
**Lean:** `Hier.J_mem_controlHull`, `Hier.fullElem_inter_of_mem`, `Hier.fullElem_of_edge`;
file `Hier/ControlEdge.lean`.
**Difficulty:** M (300–600 LOC). The relativization syntax is the bulk.
**Testable:** no.

### D5.7b Environment restriction   (paper: txt:867-869)
**Fidelity:** as in paper.
**Statement.** `jEdge_restrict`: from `JEdge C b a`, `IsLim D`, `b < D` and `D ≤ C`, conclude
`JEdge D b a`.
**Proof.**
1. The coordinates and inequalities are immediate.
2. `hull D (J a ∪ {b}) ⊆ hull C (J a ∪ {b})`, by [L5.5e] `hull_subset_of_le`
   (`J a ∪ {b} ⊆ J D` by [C5.4] and [C5.3a]). So the intersection with `J b` is `⊆ J a`.
3. `⊇` holds because `J a ⊆ hull D …` ([L5.5e] `subset_hull`) and `J a ⊆ J b` ([C5.3a]).
4. `SigmaElem (J b) (J D)`, by [C5.3b] `SigmaElem.mid` with `J b ⊆ J D ⊆ J C` transitive ([C5.3a]).

**Uses:** C5.3a, C5.3b, C5.4, D5.7, L5.5e.
**Lean:** `Hier.jEdge_restrict`; file `Hier/ControlEdge.lean`.
**Difficulty:** S (80–150 LOC).
**Testable:** no.

### D5.7c Environment extension   (paper: txt:869-871)
**Fidelity:** as in paper.
**Statement.** `jEdge_extend`: from `JEdge C b a` and `JElem C D`, conclude `JEdge D b a`.
**Proof.**
1. `hull D (J a ∪ {b}) = hull C (J a ∪ {b})`, by [L5.5e] `hull_eq_of_sigmaElem`.
2. `SigmaElem (J b) (J D)`, by [C5.3b] `SigmaElem.trans`.
3. `b < C ≤ D`.

**Uses:** C5.3b, D5.7, L5.5e.
**Lean:** `Hier.jEdge_extend`; file `Hier/ControlEdge.lean`.
**Difficulty:** S (60–120 LOC).
**Testable:** no.

### D5.7d The control collapse   (paper: txt:872-873)
**Fidelity:** as in paper.
**Statement.** `control_collapse`: if `JEdge C b a` and `H := hull C (J a ∪ {b})`, there is
`δ` with:
- `IsLim δ` and `a < δ ≤ C`;
- `π[H] = J δ`;
- `π(b) = a`;
- `π` fixes `J a` pointwise.

**Proof.**
1. `H ≺₁ J C` [L5.5e]. [L5.6] gives `δ` with `IsLim δ`, `δ ≤ C` and `π[H] = J δ`.
2. `J a ⊆ H` [L5.5e] and `J a` is transitive [C5.3a]. So [L5.6a] `collapse_eq_self` makes
   `π` fix `J a` pointwise.
3. `b ∩ H = Ord ∩ (H ∩ J b) = Ord ∩ J a = a`, by the edge and [C5.4]. Hence
   `π(b) = {π y : y < a} = a`, by step 2.
4. `a = π(b) ∈ J δ`, so `a < δ` [C5.4].

**Uses:** C5.3a, C5.4, D5.7, L5.5e, L5.6a, L5.6.
**Lean:** `Hier.control_collapse`; file `Hier/ControlEdge.lean`.
**Difficulty:** M (150–300 LOC).
**Testable:** no.

### L5.8b `JElem`, `JEdge` are Δ₀ in a history parameter   (paper: txt:882-895)
**Fidelity:** as in paper, made explicit. The paper certifies `A ≺₁ B` and the hull trace
"by two fixed first-order formulas" over a level. Once the levels are parameters, both become
bounded, and the single parameter `history m` carries all levels `≤ m`.
**Statement.** `elem_edge_delta0`: there are Δ₀ `ε(x, y, h)` and `η(c, b, a, h)` such that,
for every nonzero limit `m` (`Order.IsSuccLimit m`, so `m = ω` is allowed):
- for `x, y ≤ m`: `Sat univ ε [x, y, history m] ↔ JElem x y`;
- for `c, b, a ≤ m`: `Sat univ η [c, b, a, history m] ↔ JEdge c b a`.

**Proof.**
1. From `h = history m`, the levels `J_x` (`x ≤ m`) are read off by bounded quantifiers
   (`h` is a function). `ω` and the set of Σ₁ codes are Δ₀-definable from `J_m` (`ω` is the
   least nonzero limit; codes are in `J_ω`). If `m = ω`, no coordinate `≤ m` is `IsLim`, so
   `ε` and `η` are false there; both formulas check `IsLim` first, so this case is trivial.
2. **Uniform Σ₁ satisfaction over a level `L = J_y`** (`y` limit):
   `Sat₁^L(i, p) ↔ ∃ q ∈ L, V(i, p, q)`, by [L5.5d] steps 2-3 (txt:883-885). This is Δ₀ in
   the parameter `L`.
3. **`JElem x y`.** It is `IsLim x ∧ IsLim y ∧ x ≤ y` (Δ₀) together with
   `∀ i ∀ p ∈ J_x (p a tuple; Sat₁^{J_y}(i,p) → Sat₁^{J_x}(i,p))`. The converse implication is
   automatic ([C5.3b] upward). "p a tuple of length n" is Δ₀ in `J_x`: the tail sequence of `p`
   lies in `J_x`, as `x` is a limit.
4. **`JEdge c b a`.** Hull membership:
   `z ∈ hull c X ↔ ∃ i ∃ p ∈ J_c (p a tuple over X ∧ Sat₁^{J_c}(i,(p,z)) ∧ ∀ y ∈ J_c (Sat₁^{J_c}(i,(p,y)) → y = z))`.
   This is Δ₀ in `J_c`, `J_a` and `b`. So the trace equation `∀ z ∈ J_b (z ∈ hull ↔ z ∈ J_a)`,
   the inequalities and `J_b ≺₁ J_c` (step 3) are Δ₀ in `history m`.
5. **Correctness**: by [C5.3b] `sat_delta0_iff` between transitive `J`-levels and `univ`, and
   by [L5.5d]/[L5.5e] for the meaning of `hull`.

**Uses:** C5.3b, C5.3d, D5.7, L5.5a, L5.5d, L5.5e.
**Lean:** `Hier.elem_edge_delta0`; file `Hier/Certificates.lean`.
**Difficulty:** L (1,500–3,000 LOC). Coded tuples and formula codes inside Δ₀ formulas.
**Testable:** no.

### L5.8c Block problems are Δ₀ in their parameters   (paper: txt:1033-1040, 874-881)
**Fidelity:** as in paper. This is the bounded checker `Cert_B` and the budget "a positive
realization with maximum `v < u` has a complete certificate in `J_{v+ω} ⊆ J_u`".
**Statement.** `blockAbove_delta0`. For a base diagram `D` over `W` and a frame pattern
`isFr`, there are:
- an enumeration `ι` of the framed variables of `D`;
- a Δ₀ `θ(frame, L, u, h)`.

For every nonzero limit `m` and all `u ≤ m + ω`, `L` and frames `fr` of pattern `isFr`:
`Sat univ θ [frame values, L, u, history m] ↔ BlockAbove jPrims D fr L u`.
**Proof.**
1. `θ := ∃ β⃗ ∈ u` (one bounded quantifier per new variable of `D`), together with:
   - floor conditions `L ∈ β` for new variables;
   - `frame value ∈ u` for framed variables;
   - the atoms of `D`: `lim` (Δ₀: limit, `> ω`), `lt`, `le`, `eq` (Δ₀), and `elem`/`edge`
     via [L5.8b] at `m`.
2. **Applicability of [L5.8b].** Every coordinate of an `elem`/`edge` atom that holds is a
   limit `< u ≤ m + ω`, hence `≤ m`. If a coordinate is not a limit, the atom is false, and
   `θ` checks limitness first.
3. **Correctness**: `BlockAbove` (spine) unfolds to exactly step 1, given [N4.1b]
   `blockAbove_congr_frame` (only frame values on `baseVars D` matter) and [C5.4] (ordinals as
   sets).

**Uses:** C5.3b, C5.4, N4.1b, L5.8b.
**Lean:** `Hier.blockAbove_delta0`; file `Hier/Certificates.lean`.
**Difficulty:** L (1,000–2,000 LOC). It compiles a `List (BaseAtom W)` into `SetFml`.
**Testable:** no.

### L5.8d (16) The negative label is Δ₀   (paper: txt:1041-1044)
**Fidelity:** as in paper (`No_B(U; …) ⇔ ∀ z ∈ U ¬Cert_B`). It is stated with the history
parameter of L5.8c.
**Statement.** `noReal_delta0`: as in L5.8c, with `¬ BlockAbove`.
**Proof.** `θ' := neg θ` of [L5.8c]. Δ₀ is closed under `neg`.
**Uses:** L5.8c.
**Lean:** `Hier.noReal_delta0`; file `Hier/Certificates.lean`.
**Difficulty:** S (30–60 LOC).
**Testable:** no.

### L5.8a Certificate lemma, ordinal form   (paper: txt:874-905; spine L5.8a)
**Fidelity:** simplified (S-4). The paper's "complete certificate in `J_w`" becomes
`RealizableBelow … w` (spine §c.7). This node proves that the two agree, as one Σ₁ formula.
The paper's last sentence of the certificate lemma (txt:879-881: additional set parameters and
auxiliary records with their own budget) has no counterpart: the grammar of spine §c.7 has no
set parameters, and its only auxiliary record is the label `noReal`, whose budget is handled
by [L5.8c] and [L5.8d] (all its variables are below the level). <!-- V-U4-9 -->
**Statement.** `cert_sigma1`. For each diagram `D` and fixed set `F`, there are:
- an enumeration `ι` of the fixed variables occurring in `D`;
- a Σ₁ `Φ_D`.

For every limit `v` and every `σ` with `σ(ι i) < v`:
`Sat (J v) Φ_D (σ ∘ ι) ↔ RealizableBelow jPrims D F σ v`.
**Proof.**
1. **The history parameter.** For values `r⃗`, let `μ := max (ω, r⃗)` and let `m` be the
   largest nonzero limit `≤ μ`. This is `m = ω · (μ / ω)` (`Ordinal.div_add_mod`), and
   `μ < m + ω`. Every limit `≤ μ` is `≤ m`, and `m ≤ μ < v`.
2. `Φ_D := ∃ r⃗ (ordinals, one per free variable of `D`) ∃ m ∃ h`, with:
   - `HistOK(h, m, ·)` ([L5.5a]), `m` a nonzero limit, and every limit
     `z ≤ r_i` satisfies `z ≤ m` (all Δ₀);
   - each `noReal D' fr u L` atom: `θ'` of [L5.8d] at `(frame, L, u, h)`, legitimate because
     `u ≤ μ < m + ω`;
   - each base atom: as in [L5.8c] step 1, with [L5.8b] for `elem`/`edge` at `m`;
   - the fixed variables are the free variables of `Φ_D`, through `ι`.

   The bound `r_i < v` is automatic, since the witnesses lie in `J v`.
3. **Witnesses exist in `J v`.** `r⃗ < v`, `m < v`, and
   `history m ∈ J (m+ω) ⊆ J v`, by [L5.5b], [F5.1] (`m < v`, `IsLim v`) and [C5.3a].
4. **Correctness.**
   - [L5.8b], [L5.8c] and [L5.8d] identify each conjunct with the corresponding atom of
     `Diagram.Holds jPrims`.
   - [C5.3b] gives `Sat (J v) ↔` true for the Δ₀ part.
   - [C5.4] identifies `r ∈ J v` with `r < v`.
   - [N4.1a] `realizableBelow_congr_fixed` reduces `F` to the fixed variables in `D.vars`,
     which are the range of `ι`.
5. **Budget reading** (spine §c.7 translation table): "`w_low ∈ J_β`" is "`< β`" by [C5.4].
   "Genuine `J_u` with history in `J_{u+ω} ⊆ J_W`" is "`u < W`" by step 3.

**Uses:** F5.1, C5.3a, C5.3b, C5.4, N4.1a, L5.5a, L5.5b, L5.5g, L5.8b, L5.8c, L5.8d.
**Lean:** `Hier.cert_sigma1`; file `Hier/Certificates.lean`.
**Difficulty:** L (1,000–2,500 LOC). It compiles the full grammar (R-4).
**Testable:** no.

### L5.8 Certificate lemma   (paper: txt:874-905)
**Fidelity:** simplified (S-4), umbrella.
**Statement.** The conjunction of L5.8a–L5.8d.
**Proof.** [L5.8a], [L5.8b], [L5.8c], [L5.8d].
**Uses:** L5.8a, L5.8b, L5.8c, L5.8d.
**Lean:** as in the sub-nodes.
**Difficulty:** XL (3,500–7,500 LOC in total).
**Testable:** no.

### L5.9a Capture   (paper: txt:909-911)
**Fidelity:** simplified (S-4: ordinal form).
**Statement.** `jCapture`: from `JElem a b`, `σ x < a` for fixed `x ∈ D.vars`, and
`RealizableBelow jPrims D F σ b`, conclude `RealizableBelow jPrims D F σ a`.
**Proof.**
1. [L5.8a] for `D` and `F` gives `ι` and `Φ_D`. The values `σ (ι i)` are `< a ≤ b`, since
   `ι i ∈ D.vars ∧ F (ι i)`.
2. The realization below `b` gives `Sat (J b) Φ_D (σ ∘ ι)` ([L5.8a] at `v = b`, `IsLim b`).
3. `(σ (ι i)).toZFSet ∈ J a`, by [C5.4]. `SigmaElem (J a) (J b)` gives
   `Sat (J a) Φ_D (σ ∘ ι)`.
4. [L5.8a] at `v = a` gives the realization below `a`.

**Uses:** C5.4, D5.7, L5.8a.
**Lean:** `Hier.jCapture`; file `Hier/Capture.lean`.
**Difficulty:** S (50–100 LOC).
**Testable:** no.

### L5.9b Control transport   (paper: txt:912-918)
**Fidelity:** simplified (S-4: ordinal form). This is the single "existentially chosen joint
record" of txt:917-918.
**Statement.** `jTransport`: given `JEdge c b a`, `¬ F t`, fixed values `< a`, and
`RealizableBelow jPrims D (F ∨ · = t) (σ[t ↦ b]) c`, conclude
`RealizableBelow jPrims D (F ∨ · = t) (σ[t ↦ a]) b`.
**Proof.**
1. Let `F' := F ∨ (· = t)`. [L5.8a] for `D` and `F'` gives `ι` and `Φ`.
2. `Sat (J c) Φ (σ[t↦b] ∘ ι)`, by [L5.8a] at `v = c`. Its values are `< c`: `σ < a < c` and
   `b < c`.
3. `H := hull c (J a ∪ {b})` satisfies `H ≺₁ J c` [L5.5e], and the parameters lie in `H`:
   - `σ`-values are `< a`, hence in `J a ⊆ H`;
   - `b ∈ H`.

   So `Sat H Φ`.
4. [D5.7d] gives `δ`: `π[H] = J δ`, `π b = a`, and `π` fixes `J a`. [L5.6] `collapse_sat_iff`
   gives `Sat (J δ) Φ (σ[t↦a] ∘ ι)`.
5. [L5.8a] at `v = δ` (`IsLim δ`; values `< a < δ`) gives a realization below `δ`. Then
   [N4.1a] `realizableBelow_mono` (`δ ≤ c`) gives one below `c`.
6. [L5.9a] along `JElem b c` (edge, last conjunct, with lims and `b ≤ c`): the fixed values of
   `F'` are `< b` (`σ < a < b`, `a < b`). This gives a realization below `b`.

**Uses:** N4.1a, D5.7, D5.7d, L5.5e, L5.6, L5.8a, L5.9a.
**Lean:** `Hier.jTransport`; file `Hier/Capture.lean`.
**Difficulty:** M (150–300 LOC).
**Testable:** no.

### L5.9 Capture and transport   (paper: txt:909-918)
**Fidelity:** simplified (S-4), umbrella.
**Statement.** [L5.9a] ∧ [L5.9b].
**Proof.** [L5.9a], [L5.9b].
**Uses:** L5.9a, L5.9b.
**Lean:** no declaration of its own (umbrella): the declarations are those of L5.9a and L5.9b; file
`Hier/Capture.lean`.
**Difficulty:** S once L5.9a and L5.9b are done (the 200–400 LOC are counted there).
**Testable:** no.

### L6.5 (13) `J_κ ≺₁ J_w`   (paper: txt:976-983)
**Fidelity:** simplified (S-1). The paper's `λ` is any uncountable cardinal. Only
`ℵ₀ < κ` is used, never strong limitness.
**Statement.** `jCard_elem`: from `ℵ₀ < κ`, `IsLim w` and `κ.ord < w`, conclude
`JElem κ.ord w`.
**Proof.**
1. `IsLim κ.ord` [D6.4]; `κ.ord ≤ w`.
2. (←, from `J κ` to `J w`) Upward absoluteness: [C5.3b] `sat_sigma1_up`, with `J κ ⊆ J w`
   transitive ([C5.3a]).
3. (→) Let `φ` be Σ₁ with `s ∈ J κ` and `Sat (J w) φ s`.
   - Some `ξ < κ.ord` has all `s_i ∈ J ξ` ([D5.2] `J_limit`, [C5.3a] `J_mono`; finitely many `i`).
4. `X := J ξ` and `H := hull w X`. `H ≺₁ J w` [L5.5e], so `Sat H φ s`.
5. Size: `#H ≤ max ℵ₀ #X` [L5.5e], and `#X = lift (J ξ).card ≤ lift (max ℵ₀ ξ.card)` [C5.4].
   Moreover `ξ.card < κ` (`Cardinal.lt_ord`, `SetTheory/Ordinal/Basic.lean:1093`) and
   `ℵ₀ < κ`. Hence `#H < lift κ`.
6. [L5.6]: `π[H] = J δ`. Since `δ ⊆ J δ` [C5.4], `δ.card ≤ #(J δ) = #H < κ`, so
   `δ < κ.ord` (`Cardinal.lt_ord`).
7. `π` fixes `s` ([L5.6a] `collapse_eq_self`, with `X` transitive and `⊆ H` by [L5.5e]).
   [L5.6] `collapse_sat_iff` gives `Sat (J δ) φ s`.
8. Upward from `J δ` to `J κ` ([C5.3b], [C5.3a], `δ < κ.ord`).

**Uses:** C5.3a, C5.3b, C5.4, D5.2, D6.4, L5.5e, L5.6a, L5.6.
**Lean:** `Hier.jCard_elem`; file `Hier/Reflection.lean`.
**Difficulty:** M (150–300 LOC). Universe lifting of cardinals.
**Testable:** no.

### L6.6a Hulls meet `J_κ` boundedly   (paper: txt:988-990)
**Fidelity:** simplified (S-1: regularity only).
**Statement.** `hull_bounded`: from `ℵ₀ < κ`, `κ.IsRegular`, `κ.ord < w` and `r < κ.ord`,
there is `f` with `r < f < κ.ord` and `hull w (J r ∪ {κ}) ∩ J κ ⊆ J f`.
**Proof.**
1. `#H_r ≤ max ℵ₀ #(J r ∪ {κ}) ≤ max ℵ₀ (lift (J r).card + 1)` ([L5.5e] `card_hull_le`), and
   `(J r).card ≤ max ℵ₀ r.card` ([C5.4] `card_J_le`). Since `r < κ.ord`, `r.card < κ`
   (`Cardinal.lt_ord`); with `ℵ₀ < κ` this gives `#H_r < lift κ` (all in `Cardinal.{u+1}`).
   <!-- V-U4-6 -->
2. Each `y ∈ H_r ∩ J κ` has a least `ζ_y < κ.ord` with `y ∈ J (ζ_y)` ([D5.2] `J_limit`).
3. `κ` is regular, so `sup_y (ζ_y + 1) < κ.ord`, by `Ordinal.lift_iSup_lt_of_lt_cof`
   (`SetTheory/Cardinal/Cofinality/Ordinal.lean:292`; the index type `H_r ∩ J κ` lives in
   `Type (u+1)`, so the lifted form is needed) and `Cardinal.IsRegular.cof_ord`
   (`Regular.lean:47`). `Cardinal.iSup_lt_ord_of_isRegular` is deprecated (2026-03-22) and
   needs the index in universe `u`. <!-- V-U4-5 -->
4. `f := max (r+1) (sup + 1) < κ.ord`, by [D6.4] and [F5.1a]. Conclude with [C5.3a] `J_mono`.

**Uses:** C5.3a, C5.4, D5.2, D6.4, F5.1a, L5.5e.
**Lean:** `Hier.hull_bounded`; file `Hier/Reflection.lean`.
**Difficulty:** M (100–250 LOC).
**Testable:** no.

### L6.6 (14) The club of reflection points   (paper: txt:984-999)
**Fidelity:** simplified (S-1: regularity only).
**Statement.** `jClub_edge`: from `ℵ₀ < κ`, `κ.IsRegular`, `IsLim w` and `κ.ord < w`, there
is a club `C` of `Set.Iio κ.ord` (Mathlib `IsClub`) with `JEdge w κ.ord x` for all `x ∈ C`.
**Proof.**
1. Choose `f(r)` by [L6.6a] (`Classical.choose`). Put
   `C := {x : IsLim x.1 ∧ ∀ r < x.1, f r ≤ x.1}`.
2. **Closed** (`DirSupClosed`, `dirSupClosed_iff_of_linearOrder`, `Order/DirSupClosed.lean:287`).
   Let `d ⊆ C` be nonempty with `IsLUB d a`.
   - If `a ∈ d`, done.
   - Otherwise `IsLim a` [F5.1a] item 4, applied to `s := Subtype.val '' d ⊆ Ordinal`: since
     `Set.Iio κ.ord` is downward closed, `a.1` is the least upper bound of `s` in `Ordinal`
     (an upper bound `b ≥ κ.ord` of `s` is above `a.1`, and one below `κ.ord` is a point of the
     subtype), and `a.1 ∉ s`. Every `r < a` lies below some `x ∈ d`, so `f r ≤ x ≤ a`.
     <!-- V-U4-6 -->
3. **Cofinal.** Given `y < κ.ord`, put:
   - `g 0 := max y ω + 1`;
   - `g (n+1) := max (g n + 1) (sup_{r < g n + 1} f r)`. This is `< κ.ord` by regularity
     (`Ordinal.lift_iSup_lt_of_lt_cof` with `Cardinal.IsRegular.cof_ord`; the index
     `Set.Iio (g n + 1) : Type (u+1)` has `#(Iio (g n + 1)) = lift (g n + 1).card < lift κ` by
     `Cardinal.mk_Iio_ordinal` and `Cardinal.lt_ord`). <!-- V-U4-5 -->
   - `a := ⨆ n, g n < κ.ord`, by `Ordinal.lift_iSup_lt_of_lt_cof` with index `ℕ`
     (`lift ℵ₀ < κ = cof κ.ord`, `IsRegular.cof_ord`, `Regular.lean:47`). <!-- V-U4-5 -->
   - `IsLim a` [F5.1a] item 5. For `r < a`, `r < g n` for some `n`, so `f r ≤ g(n+1) ≤ a`.
4. **Edge at `x ∈ C`.**
   - The coordinates and `x < κ.ord < w` are given.
   - `SigmaElem (J κ) (J w)` by [L6.5].
   - Trace. `J x ∪ {κ} = ⋃_{r<x} (J r ∪ {κ})`, a directed union ([D5.2] `J_limit`, [C5.3a]).
     [L5.5e] `hull_iUnion` gives `hull w (J x ∪ {κ}) ∩ J κ = ⋃_{r<x} (H_r ∩ J κ)`, which is
     `⊆ ⋃_{r<x} J (f r) ⊆ J x`, by [L6.6a], `f r ≤ x` and `J_mono`.
   - `⊇`: [L5.5e] `subset_hull` and `J x ⊆ J κ`.

**Uses:** C5.3a, D5.2, D6.4, F5.1a, L5.5e, L6.5, L6.6a.
**Lean:** `Hier.jClub_edge`; file `Hier/Reflection.lean`.
**Difficulty:** M (300–600 LOC).
**Testable:** no.

### N4.2 The J instance of the interface   (spine N4.2)
**Fidelity:** new (S-4). This is the paper route's instance.
**Statement.** `jInst : Interface.{u}`, with `toPrims := jPrims` and every field given by the
named theorems below (real body).
**Proof.** The field theorems:
1. `jElem_le`, `jElem_lim`: definition.
2. `jElem_refl`: `SigmaElem X X` is trivial.
3. `jElem_trans`: [C5.3b] `SigmaElem.trans`.
4. `jElem_mid`: [C5.3b] `SigmaElem.mid`, with `J a ⊆ J b ⊆ J c` transitive ([C5.3a]).
5. `jEdge_lt`, `jEdge_lim`, `jEdge_elem_high`: definition.
6. `jEdge_elem_low`: [D5.7a] `fullElem_of_edge`, then [C5.3b] `FullElem.sigmaElem`.
7. `edge_restrict` is [D5.7b], `edge_extend` is [D5.7c].
8. `capture` is [L5.9a], `transport` is [L5.9b].
9. `card_elem` is [L6.5], `club_edge` is [L6.6].

At T-018 the spine's `jInterface` gets the body `jInst`, unless P-U4-1 is adopted (SCR-U4-1).
**Uses:** C5.3a, C5.3b, D5.7, D5.7a, D5.7b, D5.7c, L5.9a, L5.9b, L6.5, L6.6.
**Lean:** `Hier.jElem_le` … `Hier.jEdge_elem_high`, `Hier.jInst`; file `Hier/Instance.lean`.
**Difficulty:** S (60–150 LOC).
**Testable:** no.

---

## 4. Part C — proposed simplification P-U4-1: the reflection hierarchy (not applied)

**Idea.** The interface (spine §c.7) talks about ordinals only. Every hierarchy fact that U5
uses is a field of it. So we may define:
- `Elem a b` to be exactly "every diagram realizable below `b`, with fixed values below `a`,
  is realizable below `a`";
- `Edge c b a` to be exactly "every such diagram transports along `(c, b, a)`".

Both are defined by recursion on the top coordinate, because realizability below `b` reads the
primitives only below `b` ([N4.1a]). Capture, transport and all the structural laws then hold
by definition. Only (13) and (14) need work.
- **Mathlib supplies Skolem hulls of the ordinal structure `M_w = (w, <, Elem, Edge)`.** These
  are elementary, monotone, continuous and small.
- **Condensation is the one real lemma.** The order collapse of an elementary substructure is
  an isomorphism onto the genuine `M_ν`. It holds because `Elem` and `Edge` at top `y` are
  conjunctions of first-order formulas (`θ`, `τ`) over the structure below `y`. So an
  induction on the collapsed top coordinate identifies the pushed-forward relations with the
  true ones ([N4.7]).

### N4.3 The language `{<, Elem, Edge}` and the structures `M(ν, Q)`   (new)
**Fidelity:** new (P-U4-1).
**Statement.** Real bodies:
- `Refl.Rel`, with symbols `lt`, `elem` (binary) and `edge` (ternary);
- `Refl.lang : Language.{0,0}`, with no function symbols;
- `Refl.Carrier ν Q`, the ordinals `< ν`;
- `Refl.relMap`, and the instance `lang.Structure (Carrier ν Q)`, with the true order and `Q`
  restricted to `ν`.

**Proof.** Definitions.
**Uses:** N4.1.
**Lean:** `Hier.Refl.Rel`, `Hier.Refl.lang`, `Hier.Refl.Carrier`, `Hier.Refl.relMap`,
`Hier.Refl.instStructure`; file `Hier/Refl/Language.lean`.
**Difficulty:** S (40–80 LOC; written).
**Testable:** no.

### N4.4 Translation of the grammar into first-order formulas   (new)
**Fidelity:** new (P-U4-1).
**Statement.** Real bodies:
- `limFml`, `baseFml`;
- `NewVars`, `blockVar`, `boundFml`, `blockFml`, `atomFml`, `diagramFml`;
- `FixT`, `FreeT`, `splitVar`, `fixBelowFml`, `realFml`, `realTopFml`, `fixAsg`;
- `reflFml` (θ) and `transFml` (τ);
- `ReflectsD`, `TransportsD`.

Lemmas, in every `M(ν, Q)`:
1. `realize_limFml`: `limFml` holds at `x` iff `IsLim x.val`.
2. `realize_blockFml`: `blockFml D fr u L` holds at `v` iff
   `BlockAbove Q D (fr ↦ v) (v L) (v u)`.
3. `realize_diagramFml`: `diagramFml D` holds at `v` iff `D.Holds Q (val ∘ v)`.
4. `realize_realFml`: holds at `(c, v)` iff `RealizableBelow Q D F (fixAsg v) (c bd)`.
   - 4'. `realize_realFml_some` (`¬ F t`, `(c tgt).val < (c bd).val`): `realFml D F (some t) tgt bd`
     holds at `(c, v)` iff
     `RealizableBelow Q D (F ∨ · = t) (Function.update (fixAsg v) t (c tgt).val) (c bd)`.
     <!-- V-U4-4 -->
5. `realize_realTopFml`: `realTopFml D F` holds at `(c, v)` iff
   `RealizableBelow Q D F (fixAsg v) ν` (the bound is the height `ν` of the structure).
6. `realize_reflFml` (`a ≤ b`): `θ` holds at `(a, b)` iff `ReflectsD Q D F a b`.
7. `realize_transFml` (`¬ F t`, `a < b < c`): `τ` holds at `(c, b, a)` iff
   `TransportsD Q D F t c b a`. When `F t` holds, `TransportsD` is vacuously true, and that
   case is never transferred: in [N4.7] step 4c the conjunct for such `t` is true on both
   sides.

**Proof.**
1. Item 1. Points are the ordinals `< ν`, and every witness used is `< x.val < ν`.
   - "`∃ z < x`" is `x ≠ 0`.
   - "`∀ z < x ∃ t (z < t < x)`" is "not a successor", which gives `Order.IsSuccLimit`.
   - "`∃ y < x` with `y` a nonzero non-successor" is `ω < x`
     (`Ordinal.omega0_le_of_isSuccLimit`, `Ordinal.isSuccLimit_omega0`).
   - Use `BoundedFormula.realize_inf`, `realize_ex`, `realize_all`, `realize_imp` and
     `realize_rel₂` (`ModelTheory/Semantics.lean`).
2. Item 3, for base atoms: case analysis with `Formula.realize_relabel`,
   `Formula.realize_rel₂`, `Formula.realize_equal` and `Formula.realize_not`. The instance's
   `RelMap` is `relMap` by `rfl`.
3. Item 2. `Formula.realize_iExs` (`Semantics.lean:866`) yields `β' : NewVars → Carrier`.
   - Glue `β x :=` `β' x` on new variables, and the frame value on framed `x`. These are the
     only constrained cases ([N4.1b] `blockAbove_congr_frame`).
   - `BoundedFormula.realize_foldr_inf` (`Semantics.lean:280`) splits the conjunctions. The
     bounds give floor and ceiling, and the atoms give `BaseHolds` (step 2 with
     `BaseAtom.map`).
   - Conversely, every value on `baseVars D` is `< v u < ν`, so `β` restricts to `β'`.
4. Item 3: induction on the list. `noReal` is step 3 with `Formula.realize_not`.
5. Items 4 and 5. `realize_iExs` and `realize_iInf` (`:907`) give the free values below the
   bound. `splitVar` glues fixed, free and dummy variables. [N4.1a] `holds_congr` moves between
   the glued and the given assignment, and [N4.1a] `realizableBelow_congr_fixed` reduces to
   the fixed variables in `D.vars`.
5'. Item 4'. <!-- V-U4-4 --> `splitVar D F (some t) tgt` sends `t` to the coordinate `tgt`, the
   other fixed variables of `D` to `FixT D F` (`t ∉ FixT` since `¬ F t`), and the remaining
   variables of `D` to `FreeT D F (some t)`.
   - (→) The glued assignment `g` (`t ↦ c tgt`, fixed `↦ v`, free `↦` the `iExs` witnesses,
     others `↦ c 0`) satisfies `D` (item 3). Put `a x := g x` for `x ∈ D.vars` and
     `a x := Function.update (fixAsg v) t (c tgt).val x` otherwise. Fixedness: at `t` both are
     `c tgt`; at a fixed `x ≠ t` both are `v ⟨x, _⟩` or `fixAsg v x`. Bounds on `D.vars`: `t`
     by `htb`, fixed variables by `fixBelowFml`, free ones by the `iInf` conjunct. Truth:
     [N4.1a] `holds_congr`.
   - (←) A realization `a` has `a t = (c tgt).val` and `a x = (v ⟨x,_⟩).val` on `FixT`; its values
     on `D.vars` are `< (c bd).val < ν`, so the free values are points of `Carrier ν Q`, and the
     glued assignment equals `a` on `D.vars`. `fixBelowFml` holds because each fixed `x` is in
     `D.vars`.
6. Items 6 and 7.
   - `realize_iAlls` (`:842`) gives the fixed values. They range over the points
     `< ν`, but in `ReflectsD`/`TransportsD` they are `< a < ν`, which covers every case.
   - For `reflFml`, item 4 applies to both `realFml` conjuncts, and `a ≤ b` makes the bound
     conjuncts redundant.
   - For `transFml`, item 4' applies: to the premise with `tgt = 1` (`b`), `bd = 0` (`c`),
     `htb : b < c`; to the conclusion with `tgt = 2` (`a`), `bd = 1` (`b`), `htb : a < b`.
     This matches `Function.update σ t b` and `… t a`, after [N4.1a]
     `realizableBelow_congr_fixed` replaces `fixAsg v` by `σ` on the fixed variables of `D`
     (`t` excluded, since `¬ F t`). <!-- V-U4-4 -->

**Uses:** N4.1, N4.1a, N4.1b, N4.3.
**Lean:** the definitions above, `Hier.Refl.realize_limFml`, `realize_blockFml`,
`realize_diagramFml`, `realize_realFml`, `realize_realFml_some`, `realize_realTopFml`,
`realize_reflFml`, `realize_transFml`; file `Hier/Refl/Translation.lean`. <!-- V-U4-4 -->
**Difficulty:** L (600–1,200 LOC). Variable gluing and the finite quantifier blocks of Mathlib.
**Testable:** no.

### N4.5 The recursive definition of `Elem` and `Edge`   (new)
**Fidelity:** new (P-U4-1).
**Statement.** Real bodies:
- `Reflects Q a b`: `ReflectsD` for all `V`, `D`, `F`;
- `Transports Q c b a`, in exactly the shape of the `transport` field;
- `LevData`, `below`, `step`;
- `lev := Ordinal.lt_wf.fix (fun z IH => step z (below IH))`;
- `prims := ⟨(lev b).1 a, (lev c).2 b a⟩`.

Lemmas:
1. `elem_iff`: `prims.Elem a b ↔ IsLim a ∧ IsLim b ∧ a ≤ b ∧ Reflects prims a b`.
2. `edge_iff`: `prims.Edge c b a ↔ IsLim a ∧ IsLim b ∧ IsLim c ∧ a < b ∧ b < c ∧ prims.Elem a b ∧ prims.Elem b c ∧ Transports prims c b a`.

**Proof.**
1. `WellFounded.fix_eq` gives `lev z = step z (below (fun y _ => lev y))`.
2. `AgreeBelow (below …) prims z`. For `x, y < z`, `(below …).Elem x y = ∃ h : y < z, (lev y).1 x`
   equals `prims.Elem x y`; the same holds for `Edge` with `c < z`.
3. `elem_iff`: under `a ≤ b`, `Reflects (below_b) a b ↔ Reflects prims a b`. Every
   realizability bound involved (`b` and `a`) is `≤ b`, so [N4.1a]
   `realizableBelow_congr_below` applies. Without `a ≤ b` both sides are false.
4. `edge_iff`:
   - `(below_c).Elem a b ↔ prims.Elem a b`, since `b < c` (step 2).
   - The level-`c` clause for `b` is `prims.Elem b c`, by step 3.
   - `Transports (below_c) c b a ↔ Transports prims c b a`, by [N4.1a], with bounds
     `b ≤ c` and `c`.

**Uses:** N4.1a, N4.4 (definitions `ReflectsD`/`TransportsD`).
**Lean:** `Hier.Refl.Reflects`, `Transports`, `LevData`, `below`, `step`, `lev`, `prims`,
`elem_iff`, `edge_iff`; file `Hier/Refl/Levels.lean`.
**Difficulty:** M (120–250 LOC).
**Testable:** no.

### N4.6 The structural laws, capture and transport   (new)
**Fidelity:** new (P-U4-1).
**Statement.** The theorems `Refl.elem_le`, `elem_lim`, `elem_refl`, `elem_trans`, `elem_mid`,
`edge_lt`, `edge_lim`, `edge_elem_low`, `edge_elem_high`, `edge_restrict`, `edge_extend`,
`capture` and `transport`, with exactly the shapes of the interface fields.
**Proof.** Throughout, [N4.5] `elem_iff`/`edge_iff`, plus:
1. `elem_le`, `elem_lim`, `edge_lt`, `edge_lim`, `edge_elem_low`, `edge_elem_high`:
   conjuncts.
2. `elem_refl`: `ReflectsD Q D F a a` is the identity.
3. `elem_trans`: fixed `< a ≤ b`. Below `c`, then below `b` (`Elem b c`), then below `a`
   (`Elem a b`).
4. `elem_mid`: below `b`, then below `c` ([N4.1a] `realizableBelow_mono`), then below `a`.
5. `edge_restrict`:
   - `Elem b d` comes from `Elem b c` by step 4.
   - Transport: below `d`, then below `c` (mono), then the `Transports c b a` clause.
6. `edge_extend`:
   - `IsLim d` and `c ≤ d` come from `Elem c d`.
   - `Elem b d` comes from step 3.
   - Transport: below `d`, then below `c` (capture along `Elem c d`; the fixed values are
     `σ < a < c` and `t ↦ b < c`), then `Transports c b a`.
7. `capture`: the `Reflects` clause. `transport`: the `Transports` clause.

**Uses:** N4.1a, N4.5.
**Lean:** the theorems listed; file `Hier/Refl/Levels.lean`.
**Difficulty:** M (120–250 LOC).
**Testable:** no.

### N4.7 Hulls and condensation in `M_w`   (new)
**Fidelity:** new (P-U4-1). This replaces L5.5 and L5.6.
**Statement.** `M w := Carrier w prims`.
- `hull w hw s := Substructure.elementarySkolem₁Reduct (closure (lang.sum lang.skolem₁) s)` (real body).

Lemmas:
1. `subset_hull`, `hull_mono`, `hull_iUnion` (directed unions over any index type) and
   `card_hull_le` (`#hull ≤ max ℵ₀ #s`).
2. `condensation`: for every `S : lang.ElementarySubstructure (M w)` there are `ν ≤ w` and an
   isomorphism `π : S ≃[lang] M ν` such that:
   - `π` is order-preserving;
   - `π` fixes every point below which `S` is full;
   - `lift ν.card = #S`.
3. `collapse_eq_of_cut`: if the points of `S` below `k` are exactly the ordinals `< x`, all
   present, then `(π k).val = x`.

**Proof.**
1. Item 1, using `Substructure.subset_closure`, `closure_mono`, `closure_iUnion` and
   `mem_iSup_of_directed` (`ModelTheory/Substructures.lean:242, 262, 374, 389`).
   - The carrier of `elementarySkolem₁Reduct` is that of the closure
     (`coeSort_elementarySkolem₁Reduct`, `ModelTheory/Skolem.lean:98`).
   - Size: `Substructure.lift_card_closure_le` (`:293`) and `card_functions_sum_skolem₁_le`
     (`Skolem.lean:64`). `lang` is countable, so `lang.card ≤ ℵ₀`
     (`Language.card_eq_card_functions_add_card_relations`).
   - Elementarity: `skolem₁_reduct_isElementary` (`Skolem.lean:82`).
2. **Order collapse.** Let `X := {x.val | x ∈ S} ⊆ Iio w`. Use
   `Ordinal.enumOrdOrderIso (X ∪ Ici w)` (`SetTheory/Ordinal/Enum.lean:153`; the union is
   unbounded), with `ν :=` its preimage of `w`. This gives an order isomorphism
   `e : Iio ν ≃o X`, and `ν ≤ w`. Points fully present below `x` are fixed (induction).
   `#S = #Iio ν = lift ν.card` (`Cardinal.mk_Iio_ordinal`, `Ordinal/Basic.lean:785`).
3. **The pushed-forward primitives.** Let `Q_N.Elem x' y' :⇔ ∃ x y ∈ S, π x = x', π y = y',
   prims.Elem x y`, and
   `Q_N.Edge c' b' a' :⇔ ∃ c b a ∈ S, π c = c', π b = b', π a = a', prims.Edge c b a`.
   <!-- V-U4-10 --> By construction `π : S ≃[lang] Carrier ν Q_N` (relations transported, using
   injectivity of `π`; order by step 2).
4. **Claim** (strong induction on `o < ν`): `Q_N` and `prims` agree on all tuples with top
   coordinate `o`. That is, `Q_N.Elem x' o ↔ prims.Elem x' o` for all `x'`, and
   `Q_N.Edge o b' a' ↔ prims.Edge o b' a'` for all `b', a'`.
   - **4a.** The induction hypothesis gives `AgreeBelow Q_N prims o`. Points `≥ ν` are false
     on both sides: `Q_N` by definition, and `prims` by `elem_le` and `edge_lt` ([N4.6]).
   - **4b. Elem at `o`.** Let `o = π y` and `x' = π x`. By [N4.5] `elem_iff`, compare the
     conjuncts:
     - `IsLim x.val ↔ IsLim (π x).val`: [N4.4] `realize_limFml` in `M_w`, then elementarity
       of `S`, then invariance under `π`, then `realize_limFml` in `Carrier ν Q_N`.
       Elementarity is `ElementaryEmbedding.map_formula` (`ModelTheory/ElementaryMaps.lean:92`,
       any variable type) applied to `ElementarySubstructure.subtype`
       (`ElementarySubstructures.lean:76`). Invariance is `StrongHomClass.realize_formula`
       (`Semantics.lean:1010`);
     - order: step 2;
     - for each `V`, `D`, `F`, `ReflectsD prims D F x y`: [N4.4] `realize_reflFml` in `M_w`,
       then elementarity and `π`, then `realize_reflFml` in `Carrier ν Q_N`. This gives
       `ReflectsD Q_N D F (π x) o`, which equals `ReflectsD prims D F (π x) o` by [N4.1a]
       `realizableBelow_congr_below` (4a, bounds `≤ o`).

     Hence `prims.Elem x y ↔ prims.Elem (π x) o`, and the left side is `Q_N.Elem (π x) o`
     by definition.
   - **4c. Edge at `o`.** By [N4.5] `edge_iff`, compare:
     - the limits and order, as in 4b;
     - `prims.Elem a b` with `π b < o`: induction hypothesis;
     - `prims.Elem b y`: 4b;
     - `Transports`: decompose it as `∀ V D F t, TransportsD …`. Instances with `F t` are
       vacuous on both sides. For `¬ F t`, use `realize_transFml` ([N4.4], with `a < b < y`
       from the order conjuncts), elementarity, `π`, and [N4.1a].
5. By the claim, `Q_N = prims` on `ν`. So `Carrier ν Q_N` and `M ν` have the same relations,
   and `π : S ≃[lang] M ν`.
6. Item 3: `π` is an order isomorphism onto `Iio ν`, the points below `k` are fixed, and so
   `π k` is the least ordinal not of the form `π y` with `y < k`, which is `x`.

**Uses:** N4.1a, N4.3, N4.4, N4.5, N4.6.
**Lean:** `Hier.Refl.M`, `hull`, `subset_hull`, `hull_mono`, `hull_iUnion`, `card_hull_le`,
`condensation`, `collapse_eq_of_cut`; file `Hier/Refl/Condensation.lean`.
**Difficulty:** L (700–1,400 LOC). Steps 2 and 4, and universe lifts between `Cardinal.{u}`
and `Cardinal.{u+1}`.
**Testable:** no.

### N4.8 Transfer through a collapsed hull   (new)
**Fidelity:** new (P-U4-1). It plays the role of L5.8 and L5.9 for this route.
**Statement.**
1. `transfer`. Let `S` be an elementary substructure, `π : S ≃[lang] M ν`, and `p : V → S`
   with `(p x).val = σ x` and `(π (p x)).val = σ' x` for the fixed `x ∈ D.vars`. Then, for
   any point `bd` of `S`, `RealizableBelow prims D F σ bd.val` gives
   `RealizableBelow prims D F σ' (π bd).val`.
2. `transfer_top`: the same with the bounds `w ↦ ν`.

**Proof.**
1. [N4.4] `realize_realFml` in `M_w`, at coordinates `bd` and the fixed points `p`, gives
   `realFml.Realize`. Remap the fixed variables with [N4.1a] `realizableBelow_congr_fixed`
   (`fixAsg` versus `σ`).
2. Elementarity of `S` (`ElementaryEmbedding.map_formula` on `S.subtype`; the formula has
   variables `Fin 1 ⊕ FixT D F`, which that lemma allows), then invariance under `π`
   (`StrongHomClass.realize_formula`).
3. `realize_realFml` in `M ν = Carrier ν prims` ([N4.7] item 2), followed by [N4.1a]
   `realizableBelow_congr_fixed`.
4. `transfer_top`: steps 1-3 with `realTopFml`/`realize_realTopFml` in place of
   `realFml`/`realize_realFml`, the bounds `w` (in `M_w`) and `ν` (in `M ν`), and `c := fun _ => s₀`
   for any point `s₀ ∈ S` (only the dummy coordinate). If `S` is empty then `w = 0` (an
   elementary substructure satisfies `∃ x, x = x` whenever `M_w` is nonempty), so
   `RealizableBelow … 0` forces `D.vars = []`, hence `D = []` (every atom has a variable), and
   the conclusion holds with `a := σ'`. <!-- V-U4-10 -->

**Uses:** N4.1a, N4.4, N4.7.
**Lean:** `Hier.Refl.transfer`, `Hier.Refl.transfer_top`; file `Hier/Refl/Condensation.lean`.
**Difficulty:** M (100–250 LOC).
**Testable:** no.

### N4.9a (13) for the reflection hierarchy   (new; paper analogue txt:976-983)
**Fidelity:** new (P-U4-1); S-1 (uncountability only).
**Statement.** `Refl.card_elem`: from `ℵ₀ < κ`, `IsLim w` and `κ.ord < w`, conclude
`prims.Elem κ.ord w`.
**Proof.**
1. By [N4.5] `elem_iff`: `IsLim κ.ord` [D6.4], `IsLim w` and `κ.ord ≤ w`. It remains to show
   `ReflectsD prims D F κ.ord w`.
2. Let `σ` have fixed values `< κ.ord`. Let `m := (max of those values) + 1 < κ.ord`, by
   [F5.1a] and [D6.4]; `m ≥ 1`.
3. `s := {x : M w | x.val < m}`, and `S := hull w s`. `#S ≤ max ℵ₀ (lift m.card) < lift κ`, by
   [N4.7] `card_hull_le` and `Cardinal.lt_ord`.
4. [N4.7] `condensation` gives `π : S ≃ M ν` with `ν.card < κ`, so `ν < κ.ord`. The points
   `< m` are in `S` ([N4.7] `subset_hull`) and are fixed.
5. [N4.8] `transfer_top`, with `σ' := σ` and the total map `p : V → S` given by
   `p x :=` the point `σ x` (in `S`, since `σ x < m`) if `x ∈ D.vars ∧ F x`, and the point `0`
   (in `S`, since `0 < m`) otherwise, gives a realization below `ν`: the hypothesis `hp` holds
   by step 4. Then [N4.1a] `realizableBelow_mono` gives one below `κ.ord`. <!-- V-U4-11 -->

**Uses:** D6.4, F5.1a, N4.1a, N4.5, N4.7, N4.8.
**Lean:** `Hier.Refl.card_elem`; file `Hier/Refl/Reflection.lean`.
**Difficulty:** M (100–200 LOC).
**Testable:** no.

### N4.9b (14) for the reflection hierarchy   (new; paper analogue txt:984-999)
**Fidelity:** new (P-U4-1); S-1 (regularity only).
**Statement.** Real bodies:
- `hullAt κ w hw r := hull w {x | x.val < r ∨ x.val = κ.ord}`;
- `reflPoints κ w hw := {x : Iio κ.ord | IsLim x ∧ every point of hullAt x below κ is below x}`.

Lemmas:
1. `hullAt_bounded`: for `r < κ.ord`, the points of `hullAt r` below `κ` are below some `f`
   with `r < f < κ.ord`.
2. `isClub_reflPoints`.
3. `edge_of_reflPoint`: `prims.Edge w κ.ord x`.
4. `Refl.club_edge`.

**Proof.**
1. `hullAt_bounded`. <!-- V-U4-6 -->
   - Size: the generator set `s_r := {y : M w | y.val < r ∨ y.val = κ.ord}` has
     `#s_r ≤ lift r.card + 1` (`Cardinal.mk_Iio_ordinal`), so
     `#(hullAt r) ≤ max ℵ₀ #s_r < lift κ` by [N4.7] `card_hull_le`, `r.card < κ`
     (`Cardinal.lt_ord`, `r < κ.ord`) and `ℵ₀ < κ`.
   - Bound: the values `y.val` for points `y` of `hullAt r` with `y.val < κ.ord` form a family
     indexed by a type of cardinality `< lift κ`, all `< κ.ord`. Regularity gives
     `σ_r := sup (y.val + 1) < κ.ord` (`Ordinal.lift_iSup_lt_of_lt_cof`,
     `Cardinal.IsRegular.cof_ord`).
   - `f := max (r + 1) σ_r` satisfies `r < f` and `f < κ.ord` ([D6.4] item 1 and [F5.1a]
     item 2 for `r + 1 < κ.ord`), and every such `y.val < σ_r ≤ f`.
2. `isClub_reflPoints`.
   - **Closed** (`DirSupClosed`, `dirSupClosed_iff_of_linearOrder`,
     `Order/DirSupClosed.lean:287`). Let `d ⊆ reflPoints` be nonempty with `IsLUB d a` in
     `Set.Iio κ.ord`. If `a ∈ d`, done. Otherwise `IsLim a.1` by [F5.1a] item 4, applied to
     `Subtype.val '' d` (its least upper bound in `Ordinal` is `a.1`, because `Set.Iio κ.ord` is
     downward closed, and `a.1` is not attained). <!-- V-U4-6 --> Then
     `hullAt a = ⋃_{x ∈ d} hullAt x`, by [N4.7]
     `hull_iUnion` (index `↥d`, a chain): the generators satisfy
     `{y | y.val < a ∨ y.val = κ} = ⋃_{x∈d} {y | y.val < x ∨ y.val = κ}`, since `a` is a
     sup that is not attained. A point of `hullAt a` below `κ` therefore lies in some
     `hullAt x` and is `< x < a`.
   - **Cofinal:** given `y < κ.ord`, put `g 0 := max y ω + 1` and
     `g (n+1) := max (g n + 1) (f (g n))`, with `f r` chosen by item 1 (`Classical.choose`)
     for `r < κ.ord`. Each `g n < κ.ord` by induction. Let `a := ⨆ g n`; `a < κ.ord` by
     `Ordinal.lift_iSup_lt_of_lt_cof` (index `ℕ`, `ℵ₀ < κ = cof κ.ord`), and `IsLim a` by
     [F5.1a] item 5. <!-- V-U4-6 --> Continuity over the index
     `ℕ` gives `hullAt a = ⋃ hullAt (g n)`. A point of `hullAt (g n)` below `κ` is
     `< f (g n) ≤ g (n+1) < a`. Monotonicity of `hullAt` in `r` ([N4.7] `hull_mono`) makes
     the single bound `f (g n)` enough.
3. `edge_of_reflPoint`, by [N4.5] `edge_iff`:
   - **3a.** Coordinates, and `x < κ.ord < w`.
   - **3b.** `Elem κ.ord w`: [N4.9a].
   - **3c.** Let `S := hullAt x`, `π : S ≃ M ν` ([N4.7]), and `k` the point `κ.ord ∈ S`
     ([N4.7] `subset_hull`). Points `< x` are in `S` ([N4.7] `subset_hull`) and fixed by `π`
     ([N4.7] `condensation`, fixing clause: every ordinal below such a point is a point of `S`).
     <!-- V-U4-11 --> `S` is cut at `k` exactly at
     `x` (definition of `reflPoints`), so `(π k).val = x` ([N4.7] `collapse_eq_of_cut`). Also
     `ν < κ.ord`, since `#S < lift κ` as in [N4.9a] step 3.
   - **3d.** `Elem x κ.ord`, by [N4.5] `elem_iff`: `IsLim x`, `IsLim κ.ord`, `x ≤ κ.ord`, and
     `ReflectsD prims D F x κ.ord` for all `V, D, F`. Take `σ` with fixed values `< x`.
     [N4.8] `transfer` with `bd := k`, `σ' := σ`, and the total map `p y :=` the point `σ y` if
     `y ∈ D.vars ∧ F y` (in `S` and fixed by `π`, since `σ y < x`; step 3c), and `p y := k`
     otherwise, sends a realization below `κ.ord = k.val` to one below `(π k).val = x`.
     <!-- V-U4-11 -->
   - **3e.** `Transports w κ.ord x`. Given `V, D, F, σ, t` with `¬ F t` and fixed values `< x`,
     apply [N4.8] `transfer_top` with fixed set `F ∨ (· = t)`, its source assignment
     `Function.update σ t κ.ord`, its target assignment `Function.update σ t x`, and the total
     map `p t := k`,
     `p y :=` the point `σ y` if `y ≠ t ∧ y ∈ D.vars ∧ F y`, and `p y := k` otherwise. The
     hypothesis `hp` holds: at `t`, `(p t).val = κ.ord` and `(π k).val = x` (step 3c); at the
     other fixed variables by step 3c. This sends `σ[t↦κ]` below `w` to `σ[t↦x]` below `ν`,
     and then below `κ.ord` by [N4.1a] `realizableBelow_mono`, since `ν < κ.ord`.
     <!-- V-U4-11 -->
4. `club_edge`: `C := reflPoints` with `hw := ` positivity of `w`; items 2-3.

**Uses:** D6.4, F5.1a, N4.1a, N4.5, N4.7, N4.8, N4.9a.
**Lean:** `Hier.Refl.hullAt`, `hullAt_bounded`, `reflPoints`, `isClub_reflPoints`,
`edge_of_reflPoint`, `club_edge`; file `Hier/Refl/Reflection.lean`.
**Difficulty:** M (300–600 LOC).
**Testable:** no.

### N4.10 The reflection instance   (new; alternative body of spine N4.2)
**Fidelity:** new (P-U4-1).
**Statement.** `Refl.interface : Interface.{u}`, with `toPrims := prims` and fields from
[N4.6], [N4.9a] and [N4.9b] (real body).
**Proof.** Field by field: [N4.6], [N4.9a], [N4.9b].
**Uses:** N4.6, N4.9a, N4.9b.
**Lean:** `Hier.Refl.interface`; file `Hier/Refl/Instance.lean`.
**Difficulty:** S (20 LOC; written).
**Testable:** no.

---

## 5. Library plan (T-008, proof level)

Mathlib is the pinned copy at `/home/dev/ggg/.deps/lean-4.33.1/mathlib`; it builds with the
project. CU is Apache-2.0 at `/home/dev/ggg/.deps/lean-4.33.1/cu`. It is not a project
dependency. It shares the same Mathlib directory (its `lakefile.lean` requires
`../mathlib`), uses Lean's `module` system, and declares toolchain `v4.33.0-rc1`. Vendoring it
(R-5) would need a 4.33.1 build check. Nothing from the unlicensed reference is used.

| Node | Mathlib provides | CU provides | New | LOC |
|---|---|---|---|---|
| F5.1, F5.1a | `Ordinal.isNormal_add_right`, `Order.IsNormal.le_iff_forall_le`, `Ordinal.isSuccLimit_omega0`, `Ordinal.isSuccLimit_add`, `Order.IsSuccLimit.succ_lt` | — | wrappers | 80–160 |
| D6.4 | `Cardinal.isSuccLimit_ord`, `Cardinal.omega0_lt_ord`, `IsClub`, `IsStationary`, `IsCofinal` (`Cofinality/Club.lean`, `Order/Cofinal.lean`) | — | 4 helpers | 40–80 |
| N4.1a/b | — | — | all | 210–420 |
| C5.3b | `ZFSet` membership | `FOFormula`, `Satisfies` (`Def.lean:79`), `Delta0Formula` (`Delta0.lean:62`), `satisfies_absolute` (`:302`), `relativize` (`:96`) | Σ₁ layer; a bridge if CU is used | 250–500 (S with CU) |
| D5.2 | `ZFSet.pair/prod/sep/sUnion/range/iUnion` (`ZFC/Basic.lean:375-680`), `Ordinal.limitRecOn` | `LStageZF` is the L analogue only | B, S, J | 150–300 |
| D5.2a <!-- V-U4-3 --> | — | — | fifteen Δ₀ graphs, graph of `S` | 200–400 |
| C5.3a | `ZFSet.IsTransitive` | — | 15 membership cases | 300–600 |
| C5.3c, C5.3d | — | Gödel-operation definability `DefZF_eq_godelDef`, `Godel.godelDef`, `RudimentaryTerm` (`Rudimentary.lean:25`), `CodedSatisfaction.boundedSatisfactionRelation` (`:39`), `FormulaSyntaxCode.RawFormula` (`:51`) — all for CU's basis | normal form for B, verifier | 2,500–5,500 |
| C5.3e | — | — | all | 600–1,200 |
| C5.4 | `ZFSet.rank` (`Rank.lean:139`), `ZFSet.card` (`ZFC/Cardinal.lean:30`), `Ordinal.toZFSet` (`ZFC/Ordinal.lean:307`), `Cardinal.mk_iUnion_le` | pattern: `card_LStageZF_le_max` (`LStageZFCardinality.lean:56`), `ordinalHeight` (`CondensationCore.lean:46`) | height and size for J | 800–1,800 |
| L5.5a, L5.5b | — | pattern: `canonicalBareHistory_mem_LStageZF_add_omega` (`CanonicalBareHistoryGlobal.lean:85`), `ValidStageHistoryFormula`, `StageHistoryFunctionality` | J histories and budget | 1,600–3,700 |
| L5.5c, L5.5d | `WellFounded.prod_lex`, `Prod.Lex` | pattern: `CanonicalStageOrder.canonicalStageRel_isWellOrder` (`:115`), `CanonicalSkolemSelection`, `FullSkolemHull.canonicalWitnessSelection` (`:218`) | decorated order, compatible Σ₁ functions | 3,500–7,000 |
| L5.5e | `Cardinal.mk_le_of_surjective`, `Cardinal.mk_list_le_max` <!-- V-U4-5 --> | — | hull lemmas | 600–1,200 |
| L5.6a | — | **direct**: `MostowskiCollapse.collapse` (`:26`), `IsExtensional` (`:75`), `collapse_injective_on` (`:117`), `collapse_mem_collapse_iff` (`:171`), `collapse_eq_self_of_mem` (`:209`), `range_isTransitive` (`:65`) | adapter `Set ZFSet` to `ZFSet` | 200–500 (S with CU) |
| L5.6 | — | **direct**: `MostowskiElementarity.satisfies_equivRange_iff` (`:43`). **Not usable** (R-6): `StandardCondensation.condensation_of_elementary_isSuccLimit` (`:66`), which needs `SatisfactionAbsolute` (full) and `LStageZF` | Σ₁-J condensation | 2,000–4,000 |
| D5.7 | — | relativization (`Delta0.lean:96, 230`) | edges, G-004 | 600–1,200 |
| L5.8 | — | — | the whole compiler (R-4) | 3,500–7,500 |
| L5.9, L6.5, L6.6 | `Cardinal.lt_ord`, `Ordinal.lift_iSup_lt_of_lt_cof` (`Cofinality/Ordinal.lean:292`), `Cardinal.IsRegular.cof_ord` (`:47`), `Cardinal.mk_Iio_ordinal`, `dirSupClosed_iff_of_linearOrder` <!-- V-U4-5 --> | — | proofs | 750–1,550 |
| N4.2 | — | — | assembly | 60–150 |
| **Part B total** (with Part A) | | | | **≈ 18k–37k** |
| N4.3 | `FirstOrder.Language`, `Language.Structure` | — | language and structure (written) | 40–80 |
| N4.4 | `Formula.iExs/iAlls/iInf` (`Syntax.lean:769-809`), `realize_iExs/iAlls/iInf` (`Semantics.lean:842-907`), `realize_foldr_inf` (`:280`), `Relations.formula₂`, `Term.equal` | — | translation lemmas | 600–1,200 |
| N4.5, N4.6 | `WellFounded.fix_eq`, `Ordinal.lt_wf` | — | recursion and laws | 240–500 |
| N4.7 | **direct**: `Substructure.elementarySkolem₁Reduct` (`Skolem.lean:94`), `skolem₁_reduct_isElementary` (`:82`), `card_functions_sum_skolem₁_le` (`:64`), `Substructure.closure_iUnion` (`Substructures.lean:374`), `mem_iSup_of_directed` (`:389`), `lift_card_closure_le` (`:293`), `ElementarySubstructure.isElementary`, `StrongHomClass.realize_formula`, `Ordinal.enumOrdOrderIso` (`Enum.lean:153`), `Cardinal.mk_Iio_ordinal` | — | collapse and condensation induction | 700–1,400 |
| N4.8, N4.9 | as above, plus `Ordinal.lift_iSup_lt_of_lt_cof`, `Cardinal.IsRegular.cof_ord` <!-- V-U4-5 --> | — | transfer, (13), (14) | 500–1,050 |
| **Part C total** (with Part A) | | | | **≈ 2.5k–5k** |

**Simpler hierarchy, the CU L-hierarchy (evaluated; P-U4-2).** Put
`Elem a b := L_a ≺₁ L_b`, with the CU stages `LStageZF` (`Def.lean:883`), and keep the
remaining structure of Part B.
- **Saved:**
  - D5.2, most of C5.3a and C5.4 (`card_LStageZF_le_max`, `ordinalHeight`);
  - the history budget L5.5b (`canonicalBareHistory_mem_LStageZF_add_omega`);
  - parts of C5.3c/d (CU's own Gödel/rudimentary definability);
  - the collapse primitives.
- **Still new:**
  - compatible Σ₁ Skolem functions on all `L_λ` (CU's hulls are full-elementary and E-enumeration based);
  - Σ₁ condensation for `L_λ` (R-6; CU's `StageCondensationInterfaces` carries
    `satisfactionAbsolute` as a field, so the proof must be re-audited);
  - the certificate compiler L5.8.
- **Rule-out:** full elementarity cannot be used instead of Σ₁. `elem_mid` (an interface
  field, used at txt:1230) fails for full elementarity: `L_a ≺ L_c` with
  `L_a ⊆ L_b ⊆ L_c` does not give `L_a ≺ L_b`.
- **Estimate:** 12k–25k LOC. It is better than J by about 35%, and far worse than P-U4-1.

---

## 6. Requires

None. U4 consumes nothing from other units. Its other provisions, for U5's seed lemma (L6.7),
are the D6.4 helpers and F5.1a, beyond the spine contracts `isLim_ord`, `add_omega_le`,
`card_elem` and `club_edge`.

---

## 7. Spine change requests

**SCR-U4-1 (conditional on P-U4-1). Status at integration: deferred to root** (a fidelity
decision; see `blueprint/INTEGRATION.md`, "Spine change requests deferred").
- **Items:**
  - spine §c.7 "Why the laws are sound for J";
  - §b row N4.2 ("J-hierarchy instance");
  - the docstring of `Hier.jInterface` ("the J-hierarchy instance");
  - §d U4 "Instance";
  - §e `Hier/` module list;
  - §g rows R-1, R-4, R-6.
- **Missing case:** none is wrong. They describe an instance that P-U4-1 replaces.
- **Proposed replacement:**
  - the body `jInterface := Hier.Refl.interface`, with the name kept so `Main.lean` is unchanged;
  - the docstring "the reflection-hierarchy instance (P-U4-1)";
  - §c.7's soundness paragraph replaced by the one-paragraph idea of §4;
  - `Hier/Refl/*.lean` replacing `Basis`, `TruthTables`, `Height`, `Hulls`, `Condensation`,
    `ControlEdge` and `Certificates`;
  - R-1, R-4 and R-6 closed.
- **Consumers affected:** none. U3 uses only the grammar. U5 uses only `Interface` fields and
  `isLim_ord`. `Main.lean` uses the name `jInterface`.

**No unconditional spine change is needed.** Every FIRM item in U4's scope checked out
against both instances:
- the `Interface` field shapes, in particular `capture` (fixed `< a` only on `D.vars`) and
  `transport` (the `Function.update` form);
- `club_edge` on `Set (Set.Iio κ.ord)`, which is compatible with `StationaryIn`.

Both `jInst` and `Refl.interface` typecheck against the spine's `Interface`.

---

## 8. Proposed simplifications (flagged, not applied)

**P-U4-1 — reflection hierarchy instead of J (recommended).** Part C.
- **Effect:**
  - it replaces Part B, about 18k–37k LOC, by about 2.5k–5k LOC;
  - it removes R-1, R-4 and R-6;
  - it needs no CU and no `ZFSet` (R-5 disappears for U4).
- **Fidelity:** `MainTheorem` is unchanged. The paper's §5 becomes one admissible
  instantiation rather than the instantiation, so the formal proof no longer certifies §5
  itself. Part B remains in this blueprint as the reference for §5.
- **Soundness argument:**
  - The interface laws, capture and transport hold by definition ([N4.6]).
  - (13) and (14) use only Mathlib's Skolem hulls and [N4.7]'s condensation induction.
  - The condensation induction is sound because the defining properties of `Elem`/`Edge` at
    top `y` are conjunctions, over all diagrams, of first-order formulas `θ`, `τ` whose
    quantifiers are bounded by `y` ([N4.4]). An elementary substructure therefore preserves
    each conjunct, and the induction on the collapsed top coordinate identifies the
    transported relations with the true ones.
  - For J the corresponding identification is Σ₁ condensation (L5.6). There it needs
    histories, their budgets and canonical Skolem functions (L5.5), which is exactly what §5
    builds.
- **Risk to check** (verifier): that U5 never needs a hierarchy fact outside `Interface`.
  This is already a spine rule (§d, U5 consumes only the interface fields). If a field is
  added later, it must be proved for `prims`; laws that are closure properties of
  reflection or transport are immediate.

**P-U4-2 — CU's L-hierarchy as the substrate for Part B (fallback only).** See §5, last
paragraph.
- **Effect:** about 12k–25k LOC.
- **Use:** only if the reconciler requires a constructibility-based instance.

---

## 9. Open problems

| ID | Node | Issue | Severity |
|---|---|---|---|
| OP-U4-1 | L5.5c, L5.5d, L5.8 | Part B's canonical order, compatible Σ₁ Skolem functions and certificate compiler are paper sketches. The blueprint fixes exact statements and proof steps, but each step is itself a fine-structure development. No library supplies Σ₁-J condensation (R-6). If Part B is chosen, these dominate the project's risk. | major |
| OP-U4-2 | N4.7 | P-U4-1 is new mathematics relative to the paper, although elementary. It must pass the adversarial verifier: the condensation induction (step 4), and the claim that `θ`/`τ` express `ReflectsD`/`TransportsD` exactly (N4.4 items 6-7, including variables of `F` outside `D.vars` and a distinguished `t ∉ D.vars`). | major (until verified) |
| OP-U4-3 | N4.7, N4.9 | Universe bookkeeping: `Carrier w prims : Type (u+1)`, `#S : Cardinal.{u+1}`, `κ : Cardinal.{u}`. Every comparison goes through `Cardinal.lift`; `condensation` states `lift.{u+1} ν.card = #S`. Expect friction, not failure. | minor |
| OP-U4-4 | C5.3c | Part B's basis B differs from CU's Gödel operations. Reusing CU's definability requires a bridge in both directions (each Gödel operation as a B-composition and conversely) that is not in any library. | minor |
| OP-U4-5 | — | CU declares toolchain `v4.33.0-rc1` and uses `module`/`public import`. A 4.33.1 build of the needed CU files was not attempted (no `lake build` allowed). It is relevant only to Part B or P-U4-2. | minor |

---

## Appendix: node → Lean declarations

| Node | Declarations (`blueprint/lean/U4.lean`) |
|---|---|
| F5.1 | `Hier.add_omega_le` (spine) |
| F5.1a | `Hier.IsLim.isSuccLimit`, `.omega0_lt`, `.add_one_lt`, `Hier.isLim_add_omega0`, `Hier.isLim_of_isLUB`, `Hier.isLim_iSup_nat`, `Hier.add_omega_le_of_isSuccLimit` <!-- V-U4-7 --> |
| D6.4 | `Hier.isLim_ord` (spine), `IsWeaklyMahlo.uncountable_regular`, `IsWeaklyMahlo.stationary_pred`, `StationaryIn.exists_mem_club`, `IsClub.exists_gt_ord` |
| N4.1b | `Hier.baseHolds_congr`, `Hier.blockAbove_congr_frame` |
| N4.1a | `Hier.AgreeBelow`, `Hier.Diagram.holds_congr`, `.holds_congr_below`, `.realizableBelow_mono`, `.realizableBelow_congr_below`, `.realizableBelow_congr_fixed` |
| C5.3b | `Hier.SetFml`, `.Sat`, `.IsDelta0`, `.IsSigma1`, `.sat_delta0_iff`, `.sat_sigma1_up`, `Hier.SigmaElem`, `Hier.FullElem`, `.sigmaElem`, `SigmaElem.trans`, `SigmaElem.mid` |
| D5.2 | `Hier.triple`, `fld`, `fibre`, `BOp`, `BOp.arity`, `arg`, `BOp.eval`, `succSet`, `S`, `J`, `J_zero`, `J_add_one`, `J_limit`, `BClosed` |
| D5.2a | `Hier.bOp_graph_delta0`, `S_graph_delta0` <!-- V-U4-3 --> |
| C5.3a | `Hier.S_isTransitive`, `succSet_subset_S`, `J_isTransitive`, `J_mono`, `J_mem_J`, `J_bClosed` |
| C5.3c | `Hier.tup`, `tupSpace`, `table`, `table_mem` |
| C5.3d | `Hier.natSet`, `SetFml.code`, `uniform_verifier` |
| C5.3e | `Hier.S_mem` |
| C5.4 | `Hier.toZFSet_mem_J_iff`, `rank_J`, `card_J_le` |
| L5.5a, L5.5b, L5.5g | `Hier.history`, `histOK_exists`, `history_mem`, `J_sigma1` |
| L5.5c/d | `Hier.canonical_order`, `skolem_compatible` |
| L5.5f | `Hier.hull` |
| L5.5e | `Hier.subset_hull`, `hull_mono`, `hull_sigmaElem`, `hull_iUnion`, `card_hull_le`, `hull_subset_of_le`, `hull_eq_of_sigmaElem` |
| L5.6a/L5.6 | `Hier.collapse`, `collapse_injOn`, `collapse_eq_self`, `collapse_image_transitive`, `collapse_sat_iff_image`, `condensation`, `collapse_sat_iff` <!-- V-U4-1 --> |
| D5.7, a–d | `Hier.JElem`, `JEdge`, `jPrims`, `J_mem_controlHull`, `fullElem_inter_of_mem`, `fullElem_of_edge`, `jEdge_restrict`, `jEdge_extend`, `control_collapse` |
| L5.8a–d | `Hier.cert_sigma1`, `elem_edge_delta0`, `blockAbove_delta0`, `noReal_delta0` |
| L5.9a/b | `Hier.jCapture`, `jTransport` |
| L6.5, L6.6a, L6.6 | `Hier.jCard_elem`, `hull_bounded`, `jClub_edge` |
| N4.2 | `Hier.jElem_le` … `jEdge_elem_high`, `Hier.jInst` |
| N4.3 | `Hier.Refl.Rel`, `lang`, `Carrier`, `relMap`, `instStructure` |
| N4.4 | `Hier.Refl.ltB`, `fv`, `limFml`, `baseFml`, `NewVars`, `blockVar`, `boundFml`, `blockFml`, `atomFml`, `diagramFml`, `FixT`, `FreeT`, `splitVar`, `fixBelowFml`, `realFml`, `realTopFml`, `fixAsg`, `reflFml`, `transFml`, `ReflectsD`, `TransportsD`, `realize_*` (including `realize_realFml_some` <!-- V-U4-4 -->) |
| N4.5, N4.6 | `Hier.Refl.Reflects`, `Transports`, `LevData`, `below`, `step`, `lev`, `prims`, `elem_iff`, `edge_iff`, `elem_le` … `transport` |
| N4.7, N4.8 | `Hier.Refl.M`, `hull`, `subset_hull`, `hull_mono`, `hull_iUnion`, `card_hull_le`, `condensation`, `collapse_eq_of_cut`, `transfer`, `transfer_top` |
| N4.9a/b, N4.10 | `Hier.Refl.card_elem`, `hullAt`, `hullAt_bounded`, `reflPoints`, `isClub_reflPoints`, `edge_of_reflPoint`, `club_edge`, `interface` |
