/-!
# BTBMS blueprint — unit U4 (hierarchy): §5 and §6.2 except the seed lemma

Companion of `blueprint/U4-hierarchy.md`. This file is appended after `Spine.lean`; it adds no
imports. Every declaration's docstring starts with its node ID.

Layout:
* `BTBMS.Hier` — F5.1a limit facts, D6.4 Mahlo helpers, N4.1b/N4.1a generic diagram lemmas
  (owner U4, grammar of §c.7).
* `BTBMS.Hier` (J part) — the paper's route: D5.2 … L6.6 for the J-hierarchy, and the instance
  `Hier.jInst` (N4.2 as in the paper).
* `BTBMS.Hier.Refl` — PROPOSED SIMPLIFICATION P-U4-1 (not applied): the reflection-structure
  instance `Hier.Refl.interface` (nodes N4.3 … N4.10).

All proofs are `sorry`. No definition body is `sorry`.
-/

namespace BTBMS

universe u

open Cardinal

namespace Hier

/-! ## F5.1a: limit coordinates -/

/-- F5.1a: a coordinate is a successor limit. -/
theorem IsLim.isSuccLimit {o : Ordinal.{u}} (h : IsLim o) : Order.IsSuccLimit o := by sorry

/-- F5.1a: a coordinate is above `ω`. -/
theorem IsLim.omega0_lt {o : Ordinal.{u}} (h : IsLim o) : Ordinal.omega0 < o := by sorry

/-- F5.1a: a coordinate is closed under successor. -/
theorem IsLim.add_one_lt {o v : Ordinal.{u}} (h : IsLim o) (hv : v < o) : v + 1 < o := by sorry

/-- F5.1a: `o + ω` is a coordinate when `ω ≤ o` (used for `u_m = a_m + ω` in L6.7). -/
theorem isLim_add_omega0 {o : Ordinal.{u}} (h : Ordinal.omega0 ≤ o) :
    IsLim (o + Ordinal.omega0) := by sorry

/-- F5.1a: a least upper bound, not attained, of a nonempty set of coordinates is a coordinate
(closedness half of L6.6 and N4.9). -/
theorem isLim_of_isLUB {s : Set Ordinal.{u}} {a : Ordinal.{u}} (hs : ∀ x ∈ s, IsLim x)
    (hne : s.Nonempty) (hlub : IsLUB s a) (hna : a ∉ s) : IsLim a := by sorry

/-- F5.1a: the supremum of a strictly increasing `ω`-sequence starting at or above `ω` is a
coordinate (unboundedness half of L6.6 and N4.9). -/
theorem isLim_iSup_nat {f : ℕ → Ordinal.{u}} (hf : StrictMono f) (h0 : Ordinal.omega0 ≤ f 0) :
    IsLim (⨆ n, f n) := by sorry

-- V-U4-7
/-- F5.1a: (8) for every nonzero limit `w`, including `w = ω` (used by L5.5b at the block
`[ω, ω + ω)`; the spine's `add_omega_le` is the case `IsLim w`). -/
theorem add_omega_le_of_isSuccLimit {v w : Ordinal.{u}} (hw : Order.IsSuccLimit w) (h : v < w) :
    v + Ordinal.omega0 ≤ w := by sorry

/-! ## D6.4: helper lemmas on the locked Mahlo predicates -/

end Hier

/-- D6.4: every weakly `n`-Mahlo cardinal is uncountable and regular. -/
theorem IsWeaklyMahlo.uncountable_regular {n : Nat} {κ : Cardinal.{u}} (h : IsWeaklyMahlo n κ) :
    ℵ₀ < κ ∧ κ.IsRegular := by sorry

/-- D6.4: below a weakly `(n+1)`-Mahlo cardinal the weakly `n`-Mahlo cardinals are stationary. -/
theorem IsWeaklyMahlo.stationary_pred {n : Nat} {κ : Cardinal.{u}}
    (h : IsWeaklyMahlo (n + 1) κ) :
    StationaryIn κ {o | ∃ μ : Cardinal.{u}, IsWeaklyMahlo n μ ∧ μ.ord = o} := by sorry

/-- D6.4: a stationary set meets every club (unfolding `StationaryIn`). -/
theorem StationaryIn.exists_mem_club {κ : Cardinal.{u}} {S : Set Ordinal.{u}}
    (hS : StationaryIn κ S) {C : Set (Set.Iio κ.ord)} (hC : IsClub C) :
    ∃ x ∈ C, x.1 ∈ S := by sorry

/-- D6.4: a club of `κ` (uncountable) is unbounded below `κ`. -/
theorem IsClub.exists_gt_ord {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) {C : Set (Set.Iio κ.ord)}
    (hC : IsClub C) {o : Ordinal.{u}} (ho : o < κ.ord) : ∃ x ∈ C, o < x.1 := by sorry

namespace Hier

/-! ## N4.1b, N4.1a: generic facts about the diagram grammar (owner U4) -/

/-- N4.1a: two primitive structures agree on all tuples of coordinates below `z`. -/
def AgreeBelow (Q Q' : Prims.{u}) (z : Ordinal.{u}) : Prop :=
  (∀ x y, x < z → y < z → (Q.Elem x y ↔ Q'.Elem x y)) ∧
    (∀ c b a, c < z → b < z → a < z → (Q.Edge c b a ↔ Q'.Edge c b a))

/-- N4.1b: truth of a base diagram depends only on the values of its variables. -/
theorem baseHolds_congr {W : Type} (P : Prims.{u}) (D : List (BaseAtom W))
    (a a' : W → Ordinal.{u}) (h : ∀ x ∈ baseVars D, a x = a' x) :
    BaseHolds P D a ↔ BaseHolds P D a' := by sorry

/-- N4.1a: truth of a diagram depends only on the values of its variables. -/
theorem Diagram.holds_congr {V : Type} (P : Prims.{u}) (D : Diagram V) (a a' : V → Ordinal.{u})
    (h : ∀ x ∈ D.vars, a x = a' x) : D.Holds P a ↔ D.Holds P a' := by sorry

/-- N4.1a (locality): a diagram whose variables are all below `z` reads the primitives only
below `z`. -/
theorem Diagram.holds_congr_below {V : Type} {Q Q' : Prims.{u}} {z : Ordinal.{u}}
    (hQ : AgreeBelow Q Q' z) (D : Diagram V) (a : V → Ordinal.{u}) (ha : ∀ x ∈ D.vars, a x < z) :
    D.Holds Q a ↔ D.Holds Q' a := by sorry

/-- N4.1a: realizability below `w` is monotone in `w`. -/
theorem Diagram.realizableBelow_mono {V : Type} (P : Prims.{u}) (D : Diagram V) (F : V → Prop)
    (σ : V → Ordinal.{u}) {w w' : Ordinal.{u}} (hw : w ≤ w') :
    D.RealizableBelow P F σ w → D.RealizableBelow P F σ w' := by sorry

/-- N4.1a (locality of realizability). -/
theorem Diagram.realizableBelow_congr_below {V : Type} {Q Q' : Prims.{u}} {z w : Ordinal.{u}}
    (hQ : AgreeBelow Q Q' z) (hw : w ≤ z) (D : Diagram V) (F : V → Prop) (σ : V → Ordinal.{u}) :
    D.RealizableBelow Q F σ w ↔ D.RealizableBelow Q' F σ w := by sorry

/-- N4.1a: only fixed variables that occur in `D` matter. -/
theorem Diagram.realizableBelow_congr_fixed {V : Type} (P : Prims.{u}) (D : Diagram V)
    (F : V → Prop) (σ σ' : V → Ordinal.{u}) (w : Ordinal.{u})
    (h : ∀ x ∈ D.vars, F x → σ x = σ' x) :
    D.RealizableBelow P F σ w ↔ D.RealizableBelow P F σ' w := by sorry

/-- N4.1b: `BlockAbove` only reads the frame on the base variables (used by the translation
N4.4 and by L5.8c). -/
theorem blockAbove_congr_frame {W : Type} (P : Prims.{u}) (D : List (BaseAtom W))
    (fr fr' : W → Option Ordinal.{u}) (L w : Ordinal.{u})
    (h : ∀ x ∈ baseVars D, fr x = fr' x) :
    BlockAbove P D fr L w ↔ BlockAbove P D fr' L w := by sorry

/-! ## J route (paper §5): C5.3b formulas of set theory -/

/-- C5.3b: formulas of set theory with `n` free variables. `ex φ` and `bex i φ` bind a new last
variable; `bex i φ` is `∃ y ∈ v_i, φ`. (Stand-in for CU's `FOFormula`/`Delta0Formula`.) -/
inductive SetFml : Nat → Type
  | mem {n : Nat} (i j : Fin n) : SetFml n
  | eq {n : Nat} (i j : Fin n) : SetFml n
  | neg {n : Nat} (φ : SetFml n) : SetFml n
  | and {n : Nat} (φ ψ : SetFml n) : SetFml n
  | ex {n : Nat} (φ : SetFml (n + 1)) : SetFml n
  | bex {n : Nat} (i : Fin n) (φ : SetFml (n + 1)) : SetFml n

namespace SetFml

/-- C5.3b: satisfaction in `(A, ∈)`; quantifiers range over `A`. -/
def Sat (A : Set ZFSet.{u}) : {n : Nat} → SetFml n → (Fin n → ZFSet.{u}) → Prop
  | _, mem i j, s => s i ∈ s j
  | _, eq i j, s => s i = s j
  | _, neg φ, s => ¬ Sat A φ s
  | _, and φ ψ, s => Sat A φ s ∧ Sat A ψ s
  | _, ex φ, s => ∃ y ∈ A, Sat A φ (Fin.snoc (α := fun _ => ZFSet.{u}) s y)
  | _, bex i φ, s => ∃ y ∈ A, y ∈ s i ∧ Sat A φ (Fin.snoc (α := fun _ => ZFSet.{u}) s y)

/-- C5.3b: bounded (`Δ₀`) formulas. -/
inductive IsDelta0 : {n : Nat} → SetFml n → Prop
  | mem {n : Nat} (i j : Fin n) : IsDelta0 (mem i j)
  | eq {n : Nat} (i j : Fin n) : IsDelta0 (eq i j)
  | neg {n : Nat} {φ : SetFml n} : IsDelta0 φ → IsDelta0 (neg φ)
  | and {n : Nat} {φ ψ : SetFml n} : IsDelta0 φ → IsDelta0 ψ → IsDelta0 (and φ ψ)
  | bex {n : Nat} (i : Fin n) {φ : SetFml (n + 1)} : IsDelta0 φ → IsDelta0 (bex i φ)

/-- C5.3b: generalized `Σ₁` formulas (closed under `∧`, `∃`, bounded `∃`). -/
inductive IsSigma1 : {n : Nat} → SetFml n → Prop
  | ofDelta0 {n : Nat} {φ : SetFml n} : IsDelta0 φ → IsSigma1 φ
  | ex {n : Nat} {φ : SetFml (n + 1)} : IsSigma1 φ → IsSigma1 (ex φ)
  | and {n : Nat} {φ ψ : SetFml n} : IsSigma1 φ → IsSigma1 ψ → IsSigma1 (and φ ψ)
  | bex {n : Nat} (i : Fin n) {φ : SetFml (n + 1)} : IsSigma1 φ → IsSigma1 (bex i φ)

/-- C5.3b: `Δ₀` absoluteness: for transitive `A ⊆ B` and parameters in `A`. -/
theorem sat_delta0_iff {A B : Set ZFSet.{u}} (hAB : A ⊆ B) (hA : ∀ x ∈ A, ∀ y ∈ x, y ∈ A)
    {n : Nat} {φ : SetFml n} (hφ : φ.IsDelta0) {s : Fin n → ZFSet.{u}} (hs : ∀ i, s i ∈ A) :
    φ.Sat A s ↔ φ.Sat B s := by sorry

/-- C5.3b: `Σ₁` upward absoluteness for transitive `A ⊆ B`. -/
theorem sat_sigma1_up {A B : Set ZFSet.{u}} (hAB : A ⊆ B) (hA : ∀ x ∈ A, ∀ y ∈ x, y ∈ A)
    {n : Nat} {φ : SetFml n} (hφ : φ.IsSigma1) {s : Fin n → ZFSet.{u}} (hs : ∀ i, s i ∈ A) :
    φ.Sat A s → φ.Sat B s := by sorry

end SetFml

open SetFml

/-- C5.3b: `X ≺_{Σ₁} Y`. -/
def SigmaElem (X Y : Set ZFSet.{u}) : Prop :=
  X ⊆ Y ∧ ∀ {n : Nat} (φ : SetFml n) (s : Fin n → ZFSet.{u}), φ.IsSigma1 → (∀ i, s i ∈ X) →
    (φ.Sat X s ↔ φ.Sat Y s)

/-- C5.3b: `X ≺ Y` (full elementarity). -/
def FullElem (X Y : Set ZFSet.{u}) : Prop :=
  X ⊆ Y ∧ ∀ {n : Nat} (φ : SetFml n) (s : Fin n → ZFSet.{u}), (∀ i, s i ∈ X) →
    (φ.Sat X s ↔ φ.Sat Y s)

/-- C5.3b: full elementarity implies `Σ₁` elementarity. -/
theorem FullElem.sigmaElem {X Y : Set ZFSet.{u}} (h : FullElem X Y) : SigmaElem X Y := by sorry

/-- C5.3b: transitivity of `Σ₁` elementarity. -/
theorem SigmaElem.trans {X Y Z : Set ZFSet.{u}} (h₁ : SigmaElem X Y) (h₂ : SigmaElem Y Z) :
    SigmaElem X Z := by sorry

/-- C5.3b: intermediate `Σ₁` elementarity between transitive sets
(`X ≺₁ Z`, `X ⊆ Y ⊆ Z`, `Y` transitive ⇒ `X ≺₁ Y`), by upward absoluteness. -/
theorem SigmaElem.mid {X Y Z : Set ZFSet.{u}} (h : SigmaElem X Z) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z)
    (hY : ∀ x ∈ Y, ∀ y ∈ x, y ∈ Y) (hX : ∀ x ∈ X, ∀ y ∈ x, y ∈ X) : SigmaElem X Y := by sorry

/-! ## D5.2: the basis `B`, `S(X)` and `J` -/

/-- D5.2: right-associated triple `⟨x, y, z⟩ = ⟨x, ⟨y, z⟩⟩` (Kuratowski pairs). -/
def triple (x y z : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair x (ZFSet.pair y z)

/-- D5.2: `⋃⋃r`, which contains both coordinates of every pair in `r`. -/
noncomputable def fld (r : ZFSet.{u}) : ZFSet.{u} := ZFSet.sUnion (ZFSet.sUnion r)

/-- D5.2: the fibre `r[a] = {z : ⟨a, z⟩ ∈ r}`. -/
noncomputable def fibre (r a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ZFSet.pair a z ∈ r) (fld r)

/-- D5.2: the fifteen basis operations of txt:743-747, in the paper's order. -/
inductive BOp
  | upair | diff | prod | sUnion | dom | conv | memRel | diag
  | insMid | insLast | fibres | fibre | kpair | ktriple | wrap
  deriving DecidableEq

/-- D5.2: arities. -/
def BOp.arity : BOp → Nat
  | .upair => 2 | .diff => 2 | .prod => 2 | .sUnion => 1 | .dom => 1 | .conv => 1
  | .memRel => 1 | .diag => 1 | .insMid => 2 | .insLast => 2 | .fibres => 2 | .fibre => 2
  | .kpair => 2 | .ktriple => 3 | .wrap => 3

/-- D5.2: total argument access (out-of-range arguments read `∅`; never used in range). -/
noncomputable def arg {k : Nat} (s : Fin k → ZFSet.{u}) (i : Nat) : ZFSet.{u} :=
  if h : i < k then s ⟨i, h⟩ else ∅

/-- D5.2: the evaluation of a basis operation (txt:743-747). -/
noncomputable def BOp.eval : (G : BOp) → (Fin G.arity → ZFSet.{u}) → ZFSet.{u}
  | .upair, s => insert (arg s 0) {arg s 1}
  | .diff, s => arg s 0 \ arg s 1
  | .prod, s => ZFSet.prod (arg s 0) (arg s 1)
  | .sUnion, s => ZFSet.sUnion (arg s 0)
  | .dom, s => ZFSet.sep (fun x => ∃ y, ZFSet.pair x y ∈ arg s 0) (fld (arg s 0))
  | .conv, s =>
      ZFSet.sep (fun p => ∃ x y, p = ZFSet.pair y x ∧ ZFSet.pair x y ∈ arg s 0)
        (ZFSet.prod (fld (arg s 0)) (fld (arg s 0)))
  | .memRel, s =>
      ZFSet.sep (fun p => ∃ x y, p = ZFSet.pair x y ∧ x ∈ y) (ZFSet.prod (arg s 0) (arg s 0))
  | .diag, s =>
      ZFSet.sep (fun p => ∃ x, p = ZFSet.pair x x) (ZFSet.prod (arg s 0) (arg s 0))
  | .insMid, s =>
      ZFSet.sep (fun t => ∃ x z y, t = triple x z y ∧ z ∈ arg s 0 ∧ ZFSet.pair x y ∈ arg s 1)
        (ZFSet.prod (fld (arg s 1)) (ZFSet.prod (arg s 0) (fld (arg s 1))))
  | .insLast, s =>
      ZFSet.sep (fun t => ∃ x y z, t = triple x y z ∧ z ∈ arg s 0 ∧ ZFSet.pair x y ∈ arg s 1)
        (ZFSet.prod (fld (arg s 1)) (ZFSet.prod (fld (arg s 1)) (arg s 0)))
  | .fibres, s => ZFSet.range (fun z : (arg s 1 : ZFSet.{u}) => Hier.fibre (arg s 0) z.1)
  | .fibre, s => Hier.fibre (arg s 0) (arg s 1)
  | .kpair, s => ZFSet.pair (arg s 0) (arg s 1)
  | .ktriple, s => triple (arg s 0) (arg s 1) (arg s 2)
  | .wrap, s => insert (arg s 0) {ZFSet.pair (arg s 1) (arg s 2)}

/-- D5.2: `X⁺ = X ∪ {X}`. -/
noncomputable def succSet (X : ZFSet.{u}) : ZFSet.{u} := insert X X

/-- D5.2: one generator step `S(X) = X⁺ ∪ {G(x⃗) : G ∈ B, x⃗ ∈ (X⁺)^{arity G}}` (txt:751-752). -/
noncomputable def S (X : ZFSet.{u}) : ZFSet.{u} :=
  succSet X ∪ ZFSet.range (fun p : (Σ G : BOp, Fin G.arity → (succSet X : ZFSet.{u})) =>
    p.1.eval (fun i => (p.2 i).1))

/-- D5.2: `J₀ = ∅`, `J_{ξ+1} = S(J_ξ)`, `J_λ = ⋃_{ξ<λ} J_ξ` (txt:757-758). -/
noncomputable def J (o : Ordinal.{u}) : ZFSet.{u} :=
  Ordinal.limitRecOn (motive := fun _ => ZFSet.{u}) o ∅ (fun _ X => S X)
    (fun o _ IH => ZFSet.iUnion (fun ξ : Set.Iio o => IH ξ.1 ξ.2))

/-- D5.2: unfolding at `0`. -/
theorem J_zero : J (0 : Ordinal.{u}) = ∅ := by sorry
/-- D5.2: unfolding at successors. -/
theorem J_add_one (o : Ordinal.{u}) : J (o + 1) = S (J o) := by sorry
/-- D5.2: unfolding at limits. -/
theorem J_limit {o : Ordinal.{u}} (h : Order.IsSuccLimit o) :
    J o = ZFSet.iUnion (fun ξ : Set.Iio o => J ξ.1) := by sorry

/-- D5.2: closure of a set under the basis. -/
def BClosed (X : ZFSet.{u}) : Prop :=
  ∀ (G : BOp) (s : Fin G.arity → ZFSet.{u}), (∀ i, s i ∈ X) → G.eval s ∈ X

-- V-U4-3
/-- D5.2a: every basis operation has a `Δ₀` graph (txt:748-749): one bounded formula
`γ_G(x⃗, z)` that holds (in `Set.univ`) exactly when `z = G(x⃗)`. -/
theorem bOp_graph_delta0 (G : BOp) : ∃ γ : SetFml (G.arity + 1), γ.IsDelta0 ∧
    ∀ (s : Fin G.arity → ZFSet.{u}) (z : ZFSet.{u}),
      (γ.Sat Set.univ (Fin.snoc (α := fun _ => ZFSet.{u}) s z) ↔ z = G.eval s) := by sorry

/-- D5.2a: the graph of `S` is `Δ₀` (txt:760). -/
theorem S_graph_delta0 : ∃ γ : SetFml 2, γ.IsDelta0 ∧
    ∀ X Y : ZFSet.{u}, (γ.Sat Set.univ ![X, Y] ↔ Y = S X) := by sorry

/-! ## C5.3: transitivity, closure, truth tables, verifier, `S(T)` inside closed levels -/

/-- C5.3a: `S` preserves transitivity (txt:753-757). -/
theorem S_isTransitive {X : ZFSet.{u}} (hX : X.IsTransitive) : (S X).IsTransitive := by sorry

/-- C5.3a: `X⁺ ⊆ S(X)`. -/
theorem succSet_subset_S (X : ZFSet.{u}) : succSet X ⊆ S X := by sorry

/-- C5.3a: every level is transitive. -/
theorem J_isTransitive (o : Ordinal.{u}) : (J o).IsTransitive := by sorry

/-- C5.3a: levels increase. -/
theorem J_mono {o o' : Ordinal.{u}} (h : o ≤ o') : J o ⊆ J o' := by sorry

/-- C5.3a: earlier levels are elements of later ones. -/
theorem J_mem_J {ξ o : Ordinal.{u}} (h : ξ < o) : J ξ ∈ J o := by sorry

/-- C5.3a: nonzero limit levels are `B`-closed (txt:759). -/
theorem J_bClosed {o : Ordinal.{u}} (h : Order.IsSuccLimit o) : BClosed (J o) := by sorry

/-- C5.3c: right-nested tuple code `⟨s₀, ⟨s₁, … ⟨s_{n-1}, ∅⟩⟩⟩`. -/
noncomputable def tup : (n : Nat) → (Fin n → ZFSet.{u}) → ZFSet.{u}
  | 0, _ => ∅
  | n + 1, s => ZFSet.pair (s 0) (tup n (fun i => s i.succ))

/-- C5.3c: the coded tuple space `Tⁿ`. -/
noncomputable def tupSpace (T : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => {∅}
  | n + 1 => ZFSet.prod T (tupSpace T n)

/-- C5.3c: the truth table of `φ` over `(T, ∈)`. -/
noncomputable def table (T : ZFSet.{u}) {n : Nat} (φ : SetFml n) : ZFSet.{u} :=
  ZFSet.sep (fun t => ∃ s : Fin n → ZFSet.{u}, t = tup n s ∧ (∀ i, s i ∈ T) ∧ φ.Sat T s)
    (tupSpace T n)

/-- C5.3c: truth tables of fixed formulas over transitive members of a nonzero limit level lie
in that level (txt:768-774). -/
theorem table_mem {o : Ordinal.{u}} (ho : Order.IsSuccLimit o) {T : ZFSet.{u}} (hT : T ∈ J o)
    (hTt : T.IsTransitive) {n : Nat} (φ : SetFml n) : table T φ ∈ J o := by sorry

/-- C5.3d: von Neumann natural numbers as sets. -/
noncomputable def natSet (k : Nat) : ZFSet.{u} := (k : Ordinal.{u}).toZFSet

/-- C5.3d: hereditarily finite code of a formula. -/
noncomputable def SetFml.code : {n : Nat} → SetFml n → ZFSet.{u}
  | _, .mem i j => triple (natSet 0) (natSet i) (natSet j)
  | _, .eq i j => triple (natSet 1) (natSet i) (natSet j)
  | _, .neg φ => ZFSet.pair (natSet 2) φ.code
  | _, .and φ ψ => triple (natSet 3) φ.code ψ.code
  | _, .ex φ => ZFSet.pair (natSet 4) φ.code
  | _, .bex i φ => triple (natSet 5) (natSet i) φ.code

/-- C5.3d: the uniform bounded table verifier (txt:775-779). There is one `Δ₀` formula
`TV(n, code, T, record, tuple)` such that, for every transitive `T` in a nonzero limit level, some
record in that level passes `TV` exactly when the coded formula holds in `(T, ∈)` at the tuple.
The record carries the parse tree, the powers of `T` and every subformula table. -/
theorem uniform_verifier : ∃ TV : SetFml 5, TV.IsDelta0 ∧
    ∀ {o : Ordinal.{u}}, Order.IsSuccLimit o → ∀ {T : ZFSet.{u}}, T ∈ J o → T.IsTransitive →
    ∀ {n : Nat} (φ : SetFml n) (s : Fin n → ZFSet.{u}), (∀ i, s i ∈ T) →
      ((∃ r ∈ J o, TV.Sat (J o) ![natSet n, φ.code, T, r, tup n s]) ↔ φ.Sat T s) := by sorry

/-- C5.3e: `S(T)` is constructed inside every nonzero limit level containing the transitive `T`
(txt:781-797). -/
theorem S_mem {o : Ordinal.{u}} (ho : Order.IsSuccLimit o) {T : ZFSet.{u}} (hT : T ∈ J o)
    (hTt : T.IsTransitive) : S T ∈ J o := by sorry

/-! ## C5.4: (9) heights and sizes -/

/-- C5.4 (9): `Ord ∩ J_λ = λ` for a nonzero limit `λ`. -/
theorem toZFSet_mem_J_iff {o ξ : Ordinal.{u}} (ho : Order.IsSuccLimit o) :
    ξ.toZFSet ∈ J o ↔ ξ < o := by sorry

/-- C5.4 (9): `rk(J_λ) = λ` for a nonzero limit `λ`. -/
theorem rank_J {o : Ordinal.{u}} (ho : Order.IsSuccLimit o) : (J o).rank = o := by sorry

/-- C5.4 (9): `|J_ξ| ≤ max(ℵ₀, |ξ|)`. -/
theorem card_J_le (ξ : Ordinal.{u}) : (J ξ).card ≤ max ℵ₀ ξ.card := by sorry

/-! ## L5.5: histories and canonical hulls -/

/-- L5.5a: the genuine history through `ξ`: the set of pairs `⟨η, J_η⟩`, `η ≤ ξ`. -/
noncomputable def history (ξ : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.range (fun η : Set.Iio (ξ + 1) => ZFSet.pair η.1.toZFSet (J η.1))

-- V-U4-2
/-- L5.5a: the bounded history check `HistOK(h, ξ, x)` (txt:813-815): it holds of the genuine
history, its middle argument is always an ordinal, and it holds only of the genuine history
(uniqueness by external induction). -/
theorem histOK_exists : ∃ H : SetFml 3, H.IsDelta0 ∧
    (∀ ξ : Ordinal.{u}, H.Sat Set.univ ![history ξ, ξ.toZFSet, J ξ]) ∧
    (∀ h z x : ZFSet.{u}, H.Sat Set.univ ![h, z, x] → z.IsOrdinal) ∧
    ∀ (h x : ZFSet.{u}) (ξ : Ordinal.{u}), H.Sat Set.univ ![h, ξ.toZFSet, x] →
      h = history ξ ∧ x = J ξ := by sorry

/-- L5.5g: `ξ ↦ J_ξ` is globally single-valued `Σ₁`, uniformly over limit levels
(txt:808-815). -/
theorem J_sigma1 : ∃ φ : SetFml 2, φ.IsSigma1 ∧
    ∀ {o : Ordinal.{u}}, IsLim o → ∀ {ξ : Ordinal.{u}} {x : ZFSet.{u}}, ξ < o → x ∈ J o →
      (φ.Sat (J o) ![ξ.toZFSet, x] ↔ x = J ξ) := by sorry

/-- L5.5b: the history budget `history ξ ∈ J_{ξ+ω}` (txt:809, 820-825). -/
theorem history_mem (ξ : Ordinal.{u}) : history ξ ∈ J (ξ + Ordinal.omega0) := by sorry

/-- L5.5c: the decorated canonical well-order `<_J` (txt:816-829): a well-founded relation on
sets, end-extending along the levels, total on every limit level, whose predecessor sets
`I_x = {y : y <_J x}` belong to every limit level containing `x` and are given there by one
`Σ₁` formula `φ(x, I)`. -/
theorem canonical_order : ∃ (lt : ZFSet.{u} → ZFSet.{u} → Prop) (φ : SetFml 2),
    IsWellFounded ZFSet.{u} lt ∧ φ.IsSigma1 ∧
    (∀ {ξ : Ordinal.{u}} {x y : ZFSet.{u}}, y ∈ J ξ → lt x y → x ∈ J ξ) ∧
    (∀ {o : Ordinal.{u}}, IsLim o → ∀ {x : ZFSet.{u}}, x ∈ J o →
      (∀ y ∈ J o, lt x y ∨ x = y ∨ lt y x) ∧ (∃ I ∈ J o, ∀ y, y ∈ I ↔ lt y x) ∧
      ∀ I ∈ J o, (φ.Sat (J o) ![x, I] ↔ ∀ y, y ∈ I ↔ lt y x)) := by sorry

/-- L5.5f: the canonical `Σ₁` hull `Hull^{J_C}_{Σ₁}(X)`: the members of `J_C` that are
`Σ₁`-definable over `J_C` from finitely many parameters of `X`. -/
def hull (C : Ordinal.{u}) (X : Set ZFSet.{u}) : Set ZFSet.{u} :=
  {x | x ∈ J C ∧ ∃ (n : Nat) (φ : SetFml (n + 1)) (p : Fin n → ZFSet.{u}), φ.IsSigma1 ∧
    (∀ i, p i ∈ X) ∧ φ.Sat (J C) (Fin.snoc (α := fun _ => ZFSet.{u}) p x) ∧
    ∀ y ∈ J C, φ.Sat (J C) (Fin.snoc (α := fun _ => ZFSet.{u}) p y) → y = x}

/-- L5.5d: canonical partial `Σ₁` Skolem functions, compatible across limit levels
(txt:830-838): for each `Σ₁` formula `∃ y φ` there is a partial function, `Σ₁`-definable over
every limit level by one formula, picking a witness from the `<_J`-least valid record; its value
on parameters in `J_D` is the same in every limit `J_C ⊇ J_D` where it is defined in `J_D`. -/
theorem skolem_compatible : ∀ {n : Nat} (φ : SetFml (n + 1)), φ.IsSigma1 →
    ∃ h : Ordinal.{u} → (Fin n → ZFSet.{u}) → Option ZFSet.{u},
      (∀ {C : Ordinal.{u}}, IsLim C → ∀ p : Fin n → ZFSet.{u}, (∀ i, p i ∈ J C) →
        ((∃ y ∈ J C, φ.Sat (J C) (Fin.snoc (α := fun _ => ZFSet.{u}) p y)) ↔ (h C p).isSome) ∧
        (∀ y, h C p = some y → y ∈ hull C {x | ∃ i, p i = x} ∧
          φ.Sat (J C) (Fin.snoc (α := fun _ => ZFSet.{u}) p y))) ∧
      (∀ {D C : Ordinal.{u}}, IsLim D → IsLim C → D ≤ C → ∀ p : Fin n → ZFSet.{u},
        (∀ i, p i ∈ J D) → (h D p).isSome → h C p = h D p) := by sorry

/-- L5.5e: the hull is `Σ₁` elementary (txt:839-840). -/
theorem hull_sigmaElem {C : Ordinal.{u}} (hC : IsLim C) {X : Set ZFSet.{u}}
    (hX : X ⊆ (J C : Set ZFSet.{u})) : SigmaElem (hull C X) (J C) := by sorry

/-- L5.5e: generators lie in the hull. -/
theorem subset_hull {C : Ordinal.{u}} {X : Set ZFSet.{u}} (hX : X ⊆ (J C : Set ZFSet.{u})) :
    X ⊆ hull C X := by sorry

/-- L5.5e: monotonicity. -/
theorem hull_mono {C : Ordinal.{u}} {X Y : Set ZFSet.{u}} (h : X ⊆ Y) : hull C X ⊆ hull C Y := by
  sorry

/-- L5.5e: continuity on directed unions. -/
theorem hull_iUnion {C : Ordinal.{u}} {ι : Type*} [Nonempty ι] {X : ι → Set ZFSet.{u}}
    (hX : Directed (· ⊆ ·) X) : hull C (⋃ i, X i) = ⋃ i, hull C (X i) := by sorry

/-- L5.5e: the size bound `|Hull(X)| ≤ max(ℵ₀, |X|)`. -/
theorem card_hull_le (C : Ordinal.{u}) (X : Set ZFSet.{u}) :
    Cardinal.mk (hull C X) ≤ max ℵ₀ (Cardinal.mk X) := by sorry

/-- L5.5e: compatibility: a smaller limit environment gives a subhull (txt:867-868). -/
theorem hull_subset_of_le {D C : Ordinal.{u}} (hD : IsLim D) (hC : IsLim C) (hDC : D ≤ C)
    {X : Set ZFSet.{u}} (hX : X ⊆ (J D : Set ZFSet.{u})) : hull D X ⊆ hull C X := by sorry

/-- L5.5e: invariance under a `Σ₁` elementary end-extension (txt:869-871). -/
theorem hull_eq_of_sigmaElem {C D : Ordinal.{u}} (hC : IsLim C) (hD : IsLim D)
    (hCD : SigmaElem (J C : Set ZFSet.{u}) (J D : Set ZFSet.{u})) {X : Set ZFSet.{u}}
    (hX : X ⊆ (J C : Set ZFSet.{u})) : hull D X = hull C X := by sorry

/-! ## L5.6: condensation -/

/-- L5.6: the Mostowski collapse of `H`: `π(x) = {π(y) : y ∈ x ∩ H}`. -/
noncomputable def collapse (H : Set ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  (IsWellFounded.wf : WellFounded (α := ZFSet.{u}) (· ∈ ·)).fix fun x IH =>
    ZFSet.range (fun y : {y : (x : ZFSet.{u}) // y.1 ∈ H} => IH y.1.1 y.1.2)

/-- L5.6a: a `Σ₁` elementary substructure of a limit level is extensional, so the collapse is
injective on it and an `∈`-isomorphism onto its transitive image (txt:844-845). -/
theorem collapse_injOn {C : Ordinal.{u}} (hC : IsLim C) {H : Set ZFSet.{u}}
    (hH : SigmaElem H (J C : Set ZFSet.{u})) :
    Set.InjOn (collapse H) H ∧ ∀ x ∈ H, ∀ y ∈ H, (collapse H x ∈ collapse H y ↔ x ∈ y) := by
  sorry

/-- L5.6a: the collapse is the identity on transitive subsets of `H`. -/
theorem collapse_eq_self {H : Set ZFSet.{u}} {T : ZFSet.{u}} (hT : T.IsTransitive)
    (hTH : (T : Set ZFSet.{u}) ⊆ H) {x : ZFSet.{u}} (hx : x ∈ T) : collapse H x = x := by sorry

-- V-U4-1
/-- L5.6a: the image of the collapse is transitive (no hypothesis on `H`). -/
theorem collapse_image_transitive (H : Set ZFSet.{u}) :
    ∀ x ∈ collapse H '' H, ∀ y ∈ x, y ∈ collapse H '' H := by sorry

/-- L5.6a: the collapse is an `∈`-isomorphism of `H` onto its image, so it preserves
satisfaction of every formula. This is the form used inside the proof of L5.6, before the image
is known to be a level. -/
theorem collapse_sat_iff_image {C : Ordinal.{u}} (hC : IsLim C) {H : Set ZFSet.{u}}
    (hH : SigmaElem H (J C : Set ZFSet.{u})) {n : Nat} (φ : SetFml n)
    (s : Fin n → ZFSet.{u}) (hs : ∀ i, s i ∈ H) :
    φ.Sat H s ↔ φ.Sat (collapse H '' H) (fun i => collapse H (s i)) := by sorry

/-- L5.6 (condensation): the collapse of `H ≺_{Σ₁} J_C` is `J_δ` for a limit `ω < δ ≤ C`, and
whole levels in `H` go to whole levels (txt:842-853). -/
theorem condensation {C : Ordinal.{u}} (hC : IsLim C) {H : Set ZFSet.{u}}
    (hH : SigmaElem H (J C : Set ZFSet.{u})) :
    ∃ δ : Ordinal.{u}, IsLim δ ∧ δ ≤ C ∧ collapse H '' H = (J δ : Set ZFSet.{u}) ∧
      ∀ ξ : Ordinal.{u}, ξ.toZFSet ∈ H → J ξ ∈ H →
        ∃ ξ' : Ordinal.{u}, collapse H ξ.toZFSet = ξ'.toZFSet ∧ collapse H (J ξ) = J ξ' := by
  sorry

/-- L5.6 (transfer): the collapse preserves satisfaction of all formulas from `H` to `J_δ`
(`collapse_sat_iff_image` rewritten with `hδ`). -/
theorem collapse_sat_iff {C : Ordinal.{u}} (hC : IsLim C) {H : Set ZFSet.{u}}
    (hH : SigmaElem H (J C : Set ZFSet.{u})) {δ : Ordinal.{u}}
    (hδ : collapse H '' H = (J δ : Set ZFSet.{u})) {n : Nat} (φ : SetFml n)
    (s : Fin n → ZFSet.{u}) (hs : ∀ i, s i ∈ H) :
    φ.Sat H s ↔ φ.Sat (J δ) (fun i => collapse H (s i)) := by sorry

/-! ## D5.7: control edges (10) and the J primitives -/

/-- D5.7: `J_a ≺_{Σ₁} J_b` between coordinates. -/
def JElem (a b : Ordinal.{u}) : Prop :=
  IsLim a ∧ IsLim b ∧ a ≤ b ∧ SigmaElem (J a : Set ZFSet.{u}) (J b : Set ZFSet.{u})

/-- D5.7 (10): `R(C, b, a)`: `Hull^{J_C}_{Σ₁}(J_a ∪ {b}) ∩ J_b = J_a` and `J_b ≺_{Σ₁} J_C`. -/
def JEdge (C b a : Ordinal.{u}) : Prop :=
  IsLim a ∧ IsLim b ∧ IsLim C ∧ a < b ∧ b < C ∧
    hull C ((J a : Set ZFSet.{u}) ∪ {b.toZFSet}) ∩ (J b : Set ZFSet.{u}) = (J a : Set ZFSet.{u}) ∧
    SigmaElem (J b : Set ZFSet.{u}) (J C : Set ZFSet.{u})

/-- D5.7: the J primitives. -/
def jPrims : Prims.{u} := ⟨JElem, JEdge⟩

/-- D5.7a (G-004): an edge puts the whole level `J_b` into the control hull as an *element*:
`J_b ∈ Hull^{J_C}(J_a ∪ {b})` (not `J_b ⊆ Hull`). -/
theorem J_mem_controlHull {C b a : Ordinal.{u}} (h : JEdge C b a) :
    J b ∈ hull C ((J a : Set ZFSet.{u}) ∪ {b.toZFSet}) := by sorry

/-- D5.7a: relativization: if `T ∈ H ≺_{Σ₁} M` with `M` transitive, then `H ∩ T ≺ T`. -/
theorem fullElem_inter_of_mem {H M : Set ZFSet.{u}} (hM : ∀ x ∈ M, ∀ y ∈ x, y ∈ M)
    (hH : SigmaElem H M) {T : ZFSet.{u}} (hT : T ∈ H) :
    FullElem (H ∩ (T : Set ZFSet.{u})) (T : Set ZFSet.{u}) := by sorry

/-- D5.7a: an edge gives `J_a ≺ J_b` (full elementarity), hence `JElem a b`. -/
theorem fullElem_of_edge {C b a : Ordinal.{u}} (h : JEdge C b a) :
    FullElem (J a : Set ZFSet.{u}) (J b : Set ZFSet.{u}) := by sorry

/-- D5.7b: environment restriction (txt:867-869). -/
theorem jEdge_restrict {C b a D : Ordinal.{u}} (h : JEdge C b a) (hD : IsLim D) (hbD : b < D)
    (hDC : D ≤ C) : JEdge D b a := by sorry

/-- D5.7c: environment extension along `J_C ≺_{Σ₁} J_D` (txt:869-871). -/
theorem jEdge_extend {C b a D : Ordinal.{u}} (h : JEdge C b a) (hCD : JElem C D) :
    JEdge D b a := by sorry

/-- D5.7d: the control collapse fixes `J_a`, sends `b ↦ a`, and has height `a < δ ≤ C`
(txt:872-873). -/
theorem control_collapse {C b a : Ordinal.{u}} (h : JEdge C b a) :
    ∃ δ : Ordinal.{u}, IsLim δ ∧ a < δ ∧ δ ≤ C ∧
      collapse (hull C ((J a : Set ZFSet.{u}) ∪ {b.toZFSet}))
          '' hull C ((J a : Set ZFSet.{u}) ∪ {b.toZFSet}) = (J δ : Set ZFSet.{u}) ∧
      collapse (hull C ((J a : Set ZFSet.{u}) ∪ {b.toZFSet})) b.toZFSet = a.toZFSet ∧
      ∀ x ∈ J a, collapse (hull C ((J a : Set ZFSet.{u}) ∪ {b.toZFSet})) x = x := by sorry

/-! ## L5.8: certificates (ordinal form) -/

/-- L5.8b: below a nonzero limit `m`, `JElem` and `JEdge` are `Δ₀` in the single parameter
`history m` (txt:883-895: `J_c` and its history are available; `A ≺_{Σ₁} B` and the hull trace
equation become bounded once the levels are parameters). -/
theorem elem_edge_delta0 : ∃ (ε : SetFml 3) (η : SetFml 4), ε.IsDelta0 ∧ η.IsDelta0 ∧
    ∀ {m : Ordinal.{u}}, Order.IsSuccLimit m →
      (∀ {x y : Ordinal.{u}}, x ≤ m → y ≤ m →
        (ε.Sat Set.univ ![x.toZFSet, y.toZFSet, history m] ↔ JElem x y)) ∧
      (∀ {c b a : Ordinal.{u}}, c ≤ m → b ≤ m → a ≤ m →
        (η.Sat Set.univ ![c.toZFSet, b.toZFSet, a.toZFSet, history m] ↔ JEdge c b a)) := by
  sorry

/-- L5.8c: a positive block problem (base diagram, frame, floor `L`, bound `u`) is `Δ₀` in its
ordinal parameters and `history m`, for any nonzero limit `m` with `u ≤ m + ω` (txt:1033-1040: the
complete certificate of a realization lies in `J_{v+ω}`). -/
theorem blockAbove_delta0 {W : Type} (D : List (BaseAtom W)) (isFr : W → Prop) :
    ∃ (n : Nat) (ι : Fin n → W) (θ : SetFml (n + 3)), θ.IsDelta0 ∧
      (∀ i, ι i ∈ baseVars D ∧ isFr (ι i)) ∧ (∀ x ∈ baseVars D, isFr x → x ∈ Set.range ι) ∧
      ∀ {u L m : Ordinal.{u}} (fr : W → Option Ordinal.{u}), Order.IsSuccLimit m →
        u ≤ m + Ordinal.omega0 → (∀ x ∈ baseVars D, (fr x).isSome ↔ isFr x) →
        (θ.Sat Set.univ (Fin.snoc (α := fun _ => ZFSet.{u}) (Fin.snoc (α := fun _ => ZFSet.{u})
            (Fin.snoc (α := fun _ => ZFSet.{u}) (fun i => ((fr (ι i)).getD 0).toZFSet)
              L.toZFSet) u.toZFSet) (history m)) ↔
          BlockAbove jPrims D fr L u) := by sorry

/-- L5.8d (16): the negative label is `Δ₀` in the same parameters (negation of L5.8c). -/
theorem noReal_delta0 {W : Type} (D : List (BaseAtom W)) (isFr : W → Prop) :
    ∃ (n : Nat) (ι : Fin n → W) (θ : SetFml (n + 3)), θ.IsDelta0 ∧
      (∀ i, ι i ∈ baseVars D ∧ isFr (ι i)) ∧ (∀ x ∈ baseVars D, isFr x → x ∈ Set.range ι) ∧
      ∀ {u L m : Ordinal.{u}} (fr : W → Option Ordinal.{u}), Order.IsSuccLimit m →
        u ≤ m + Ordinal.omega0 → (∀ x ∈ baseVars D, (fr x).isSome ↔ isFr x) →
        (θ.Sat Set.univ (Fin.snoc (α := fun _ => ZFSet.{u}) (Fin.snoc (α := fun _ => ZFSet.{u})
            (Fin.snoc (α := fun _ => ZFSet.{u}) (fun i => ((fr (ι i)).getD 0).toZFSet)
              L.toZFSet) u.toZFSet) (history m)) ↔
          ¬ BlockAbove jPrims D fr L u) := by sorry

/-- L5.8a (certificate lemma, ordinal form; spine L5.8a): for each diagram and set of fixed
variables there is one `Σ₁` formula `Φ_D` in the fixed variables of `D` such that, at every
limit `v` with fixed values below `v`, `J_v ⊨ Φ_D` iff `D` is realizable below `v`
(txt:874-905; the translation table of spine §c.7). -/
theorem cert_sigma1 {V : Type} (D : Diagram V) (F : V → Prop) :
    ∃ (n : Nat) (ι : Fin n → V) (φ : SetFml n), φ.IsSigma1 ∧ (∀ i, ι i ∈ D.vars ∧ F (ι i)) ∧
      (∀ x ∈ D.vars, F x → x ∈ Set.range ι) ∧
      ∀ {v : Ordinal.{u}} (σ : V → Ordinal.{u}), IsLim v → (∀ i, σ (ι i) < v) →
        (φ.Sat (J v) (fun i => (σ (ι i)).toZFSet) ↔ D.RealizableBelow jPrims F σ v) := by sorry

/-! ## L5.9: capture and transport -/

/-- L5.9a: capture along `J_a ≺_{Σ₁} J_b` (txt:909-911). -/
theorem jCapture {V : Type} (D : Diagram V) (F : V → Prop) (σ : V → Ordinal.{u})
    {a b : Ordinal.{u}} (hab : JElem a b) (hσ : ∀ x ∈ D.vars, F x → σ x < a) :
    D.RealizableBelow jPrims F σ b → D.RealizableBelow jPrims F σ a := by sorry

/-- L5.9b: control transport, then capture into `J_b` (txt:912-918). -/
theorem jTransport {V : Type} [DecidableEq V] (D : Diagram V) (F : V → Prop)
    (σ : V → Ordinal.{u}) (t : V) {c b a : Ordinal.{u}} (h : JEdge c b a) (ht : ¬ F t)
    (hσ : ∀ x ∈ D.vars, F x → σ x < a) :
    D.RealizableBelow jPrims (fun x => F x ∨ x = t) (Function.update σ t b) c →
      D.RealizableBelow jPrims (fun x => F x ∨ x = t) (Function.update σ t a) b := by sorry

/-! ## L6.5, L6.6: (13) and (14) for J -/

/-- L6.5 (13): `J_κ ≺_{Σ₁} J_w` for an uncountable cardinal `κ` and a limit `w > κ`
(txt:976-983; S-1: only uncountability). -/
theorem jCard_elem (κ : Cardinal.{u}) (w : Ordinal.{u}) (hκ : ℵ₀ < κ) (hw : IsLim w)
    (hκw : κ.ord < w) : JElem κ.ord w := by sorry

/-- L6.6a: hulls `H_r = Hull^{J_w}(J_r ∪ {κ})`, `r < κ`, meet `J_κ` boundedly (regularity). -/
theorem hull_bounded (κ : Cardinal.{u}) (w : Ordinal.{u}) (hκ : ℵ₀ < κ) (hreg : κ.IsRegular)
    (hκw : κ.ord < w) {r : Ordinal.{u}} (hr : r < κ.ord) :
    ∃ f : Ordinal.{u}, r < f ∧ f < κ.ord ∧
      hull w ((J r : Set ZFSet.{u}) ∪ {κ.ord.toZFSet}) ∩ (J κ.ord : Set ZFSet.{u}) ⊆
        (J f : Set ZFSet.{u}) := by sorry

/-- L6.6 (14): the reflection points form a club (txt:984-999; S-1: only regularity). -/
theorem jClub_edge (κ : Cardinal.{u}) (w : Ordinal.{u}) (hκ : ℵ₀ < κ) (hreg : κ.IsRegular)
    (hw : IsLim w) (hκw : κ.ord < w) :
    ∃ C : Set (Set.Iio κ.ord), IsClub C ∧ ∀ x ∈ C, JEdge w κ.ord x.1 := by sorry

/-! ## The J laws and the J instance (N4.2 as in the paper) -/

/-- N4.2: field `elem_le` of `jInst`. -/
theorem jElem_le {a b : Ordinal.{u}} (h : JElem a b) : a ≤ b := by sorry
/-- N4.2: field `elem_lim`. -/
theorem jElem_lim {a b : Ordinal.{u}} (h : JElem a b) : IsLim a ∧ IsLim b := by sorry
/-- N4.2: field `elem_refl`. -/
theorem jElem_refl {a : Ordinal.{u}} (h : IsLim a) : JElem a a := by sorry
/-- N4.2: field `elem_trans` (C5.3b `SigmaElem.trans`). -/
theorem jElem_trans {a b c : Ordinal.{u}} (h₁ : JElem a b) (h₂ : JElem b c) : JElem a c := by
  sorry
/-- N4.2: field `elem_mid` (C5.3b `SigmaElem.mid`). -/
theorem jElem_mid {a b c : Ordinal.{u}} (h : JElem a c) (hab : a ≤ b) (hbc : b ≤ c)
    (hb : IsLim b) : JElem a b := by sorry
/-- N4.2: field `edge_lt`. -/
theorem jEdge_lt {c b a : Ordinal.{u}} (h : JEdge c b a) : a < b ∧ b < c := by sorry
/-- N4.2: field `edge_lim`. -/
theorem jEdge_lim {c b a : Ordinal.{u}} (h : JEdge c b a) : IsLim a ∧ IsLim b ∧ IsLim c := by
  sorry
/-- N4.2: field `edge_elem_low` (D5.7a, G-004). -/
theorem jEdge_elem_low {c b a : Ordinal.{u}} (h : JEdge c b a) : JElem a b := by sorry
/-- N4.2: field `edge_elem_high`. -/
theorem jEdge_elem_high {c b a : Ordinal.{u}} (h : JEdge c b a) : JElem b c := by sorry

/-- N4.2 (paper route): the J-hierarchy instance. At T-018 the spine's `jInterface` gets this
body unless P-U4-1 is accepted. -/
noncomputable def jInst : Interface.{u} where
  toPrims := jPrims
  elem_le := jElem_le
  elem_lim := jElem_lim
  elem_refl := jElem_refl
  elem_trans := jElem_trans
  elem_mid := jElem_mid
  edge_lt := jEdge_lt
  edge_lim := jEdge_lim
  edge_elem_low := jEdge_elem_low
  edge_elem_high := jEdge_elem_high
  edge_restrict := jEdge_restrict
  edge_extend := jEdge_extend
  capture := fun D F σ _ _ hab hσ => jCapture D F σ hab hσ
  transport := fun D F σ t _ _ _ h ht hσ => jTransport D F σ t h ht hσ
  card_elem := jCard_elem
  club_edge := jClub_edge

end Hier

end BTBMS

/-! # PROPOSED SIMPLIFICATION P-U4-1 (not applied): the reflection-structure instance

Everything below is a proposal. It replaces the instance `jInst` (all of §5) by a hierarchy of
ordinal structures defined by recursion, whose only non-formal input is Mathlib's downward
Löwenheim–Skolem machinery. The spine's `jInterface` is not touched; at T-018 the reconciler
decides whether its body is `Hier.jInst` or `Hier.Refl.interface`. -/

namespace BTBMS

universe u

open Cardinal

namespace Hier

namespace Refl

open FirstOrder FirstOrder.Language

/-! ## N4.3: the language `{<, Elem, Edge}` and the structures `M(ν, Q)` -/

/-- N4.3: relation symbols. -/
inductive Rel : Nat → Type
  | lt : Rel 2
  | elem : Rel 2
  | edge : Rel 3

/-- N4.3: the relational language of ordinal structures. -/
def lang : Language.{0, 0} := ⟨fun _ => Empty, Rel⟩

/-- N4.3: points of `M(ν, Q)`: the ordinals below `ν`. -/
@[ext] structure Carrier (ν : Ordinal.{u}) (Q : Prims.{u}) : Type (u + 1) where
  val : Ordinal.{u}
  lt : val < ν

/-- N4.3: the relations of `M(ν, Q)`: the true order, and `Q` restricted to `ν`. -/
def relMap {ν : Ordinal.{u}} {Q : Prims.{u}} : {n : Nat} → Rel n → (Fin n → Carrier ν Q) → Prop
  | _, .lt, xs => (xs 0).val < (xs 1).val
  | _, .elem, xs => Q.Elem (xs 0).val (xs 1).val
  | _, .edge, xs => Q.Edge (xs 0).val (xs 1).val (xs 2).val

/-- N4.3: `M(ν, Q)` as a first-order structure. -/
instance instStructure (ν : Ordinal.{u}) (Q : Prims.{u}) : lang.Structure (Carrier ν Q) where
  funMap := fun f => Empty.elim f
  RelMap := fun r xs => relMap r xs

/-! ## N4.4: translation of the diagram grammar into first-order formulas -/

/-- N4.4: `t₁ < t₂`. -/
def ltB {α : Type} {n : Nat} (t₁ t₂ : lang.Term (α ⊕ Fin n)) : lang.BoundedFormula α n :=
  Relations.boundedFormula₂ (Rel.lt : lang.Relations 2) t₁ t₂

/-- N4.4: a free variable as a term. -/
def fv {α : Type} {n : Nat} (a : α) : lang.Term (α ⊕ Fin n) := Term.var (Sum.inl a)

/-- N4.4: "`x₀` is a limit ordinal greater than `ω`", read in an initial segment of the
ordinals: `x₀ ≠ 0`, `x₀` is not a successor, and some `y < x₀` is a nonzero non-successor. -/
def limFml : lang.Formula (Fin 1) :=
  (∃' ltB (&0) (fv 0)) ⊓
    (∀' (ltB (&0) (fv 0) ⟹ ∃' (ltB (&0) (&1) ⊓ ltB (&1) (fv 0)))) ⊓
    (∃' (ltB (&0) (fv 0) ⊓ (∃' ltB (&1) (&0)) ⊓
      (∀' (ltB (&1) (&0) ⟹ ∃' (ltB (&1) (&2) ⊓ ltB (&2) (&0))))))

/-- N4.4: translation of a base atom. -/
def baseFml {V : Type} : BaseAtom V → lang.Formula V
  | .lim x => limFml.relabel (fun _ => x)
  | .lt x y => Relations.formula₂ (Rel.lt : lang.Relations 2) (Term.var x) (Term.var y)
  | .le x y => (Relations.formula₂ (Rel.lt : lang.Relations 2) (Term.var y) (Term.var x)).not
  | .eq x y => Term.equal (Term.var x) (Term.var y)
  | .elem x y => Relations.formula₂ (Rel.elem : lang.Relations 2) (Term.var x) (Term.var y)
  | .edge c b a =>
      Relations.formula (Rel.edge : lang.Relations 3) ![Term.var c, Term.var b, Term.var a]

/-- N4.4: the new (unframed) variables of a block problem. -/
abbrev NewVars {W V : Type} (D : List (BaseAtom W)) (fr : W → Option V) : Type :=
  {x : W // x ∈ baseVars D ∧ fr x = none}

/-- N4.4: finitely many new variables. -/
instance {W V : Type} (D : List (BaseAtom W)) (fr : W → Option V) : Finite (NewVars D fr) := by
  classical
  exact Finite.of_injective (fun x : NewVars D fr => (⟨x.1, x.2.1⟩ : {y // y ∈ baseVars D}))
    (fun a b h => Subtype.ext (congrArg (fun z : {y // y ∈ baseVars D} => z.1) h))

open Classical in
/-- N4.4: variables of a block problem: new variables are bound, framed ones read the frame
(the default `d` is never used on base variables). -/
noncomputable def blockVar {W V : Type} (D : List (BaseAtom W)) (fr : W → Option V) (d : V)
    (x : W) : V ⊕ NewVars D fr :=
  if h : x ∈ baseVars D ∧ fr x = none then Sum.inr ⟨x, h⟩ else Sum.inl ((fr x).getD d)

open Classical in
/-- N4.4: the bounds of a block: new variables in `(L, u)`, framed ones below `u`. -/
noncomputable def boundFml {W V : Type} (D : List (BaseAtom W)) (fr : W → Option V) (u L : V)
    (x : W) : lang.Formula (V ⊕ NewVars D fr) :=
  if x ∈ baseVars D ∧ fr x = none then
    Relations.formula₂ (Rel.lt : lang.Relations 2) (Term.var (Sum.inl L))
        (Term.var (blockVar D fr u x)) ⊓
      Relations.formula₂ (Rel.lt : lang.Relations 2) (Term.var (blockVar D fr u x))
        (Term.var (Sum.inl u))
  else
    Relations.formula₂ (Rel.lt : lang.Relations 2) (Term.var (blockVar D fr u x))
      (Term.var (Sum.inl u))

/-- N4.4: `BlockAbove` as a formula: some values of the new variables satisfy the bounds and
the block. -/
noncomputable def blockFml {W V : Type} (D : List (BaseAtom W)) (fr : W → Option V) (u L : V) :
    lang.Formula V :=
  Formula.iExs (NewVars D fr)
    ((((baseVars D).map (boundFml D fr u L)).foldr (· ⊓ ·) ⊤) ⊓
      ((D.map (fun b => baseFml (b.map (blockVar D fr u)))).foldr (· ⊓ ·) ⊤))

/-- N4.4: translation of an atom of the full grammar. -/
noncomputable def atomFml {V : Type} : Atom V → lang.Formula V
  | .base b => baseFml b
  | .noReal D fr u L => (blockFml D fr u L).not

/-- N4.4: translation of a diagram (conjunction of its atoms). -/
noncomputable def diagramFml {V : Type} (D : Diagram V) : lang.Formula V :=
  (List.map atomFml D).foldr (· ⊓ ·) ⊤

/-- N4.4: correctness of `limFml` in every `M(ν, Q)`. -/
theorem realize_limFml {ν : Ordinal.{u}} {Q : Prims.{u}} (x : Carrier ν Q) :
    limFml.Realize (fun _ => x) ↔ IsLim x.val := by sorry

/-- N4.4: correctness of the block translation. -/
theorem realize_blockFml {ν : Ordinal.{u}} {Q : Prims.{u}} {W V : Type}
    (D : List (BaseAtom W)) (fr : W → Option V) (u L : V) (v : V → Carrier ν Q) :
    (blockFml D fr u L).Realize v ↔
      BlockAbove Q D (fun x => (fr x).map (fun y => (v y).val)) (v L).val (v u).val := by sorry

/-- N4.4 (translation lemma): in every `M(ν, Q)`, the translation of a diagram holds exactly
when the diagram holds for `Q`. -/
theorem realize_diagramFml {ν : Ordinal.{u}} {Q : Prims.{u}} {V : Type} (D : Diagram V)
    (v : V → Carrier ν Q) : (diagramFml D).Realize v ↔ D.Holds Q (fun x => (v x).val) := by
  sorry

/-! ## N4.4: the reflection and transport properties, semantically and as formulas -/

/-- N4.4: fixed variables occurring in `D`. -/
abbrev FixT {V : Type} (D : Diagram V) (F : V → Prop) : Type := {x : V // x ∈ D.vars ∧ F x}

/-- N4.4: free variables occurring in `D`, other than `t`. -/
abbrev FreeT {V : Type} (D : Diagram V) (F : V → Prop) (t : Option V) : Type :=
  {x : V // x ∈ D.vars ∧ ¬ F x ∧ some x ≠ t}

/-- N4.4: finitely many fixed variables. -/
instance {V : Type} (D : Diagram V) (F : V → Prop) : Finite (FixT D F) := by
  classical
  exact Finite.of_injective (fun x : FixT D F => (⟨x.1, x.2.1⟩ : {y // y ∈ D.vars}))
    (fun a b h => Subtype.ext (congrArg (fun z : {y // y ∈ D.vars} => z.1) h))

/-- N4.4: finitely many free variables. -/
instance {V : Type} (D : Diagram V) (F : V → Prop) (t : Option V) : Finite (FreeT D F t) := by
  classical
  exact Finite.of_injective (fun x : FreeT D F t => (⟨x.1, x.2.1⟩ : {y // y ∈ D.vars}))
    (fun a b h => Subtype.ext (congrArg (fun z : {y // y ∈ D.vars} => z.1) h))

open Classical in
/-- N4.4: sorting the variables of `D`: the distinguished `t` goes to the coordinate `tgt`,
fixed ones to `FixT`, free ones to `FreeT`, others to the dummy coordinate `0`. -/
noncomputable def splitVar {V : Type} (D : Diagram V) (F : V → Prop) (t : Option V) {k : Nat}
    (tgt : Fin (k + 1)) (x : V) : (Fin (k + 1) ⊕ FixT D F) ⊕ FreeT D F t :=
  if some x = t then Sum.inl (Sum.inl tgt)
  else if h : x ∈ D.vars ∧ F x then Sum.inl (Sum.inr ⟨x, h⟩)
  else if h' : x ∈ D.vars ∧ ¬ F x ∧ some x ≠ t then Sum.inr ⟨x, h'⟩
  else Sum.inl (Sum.inl 0)

/-- N4.4: "every fixed value is below the coordinate `bd`". -/
noncomputable def fixBelowFml {V : Type} (D : Diagram V) (F : V → Prop) {k : Nat}
    (bd : Fin (k + 1)) : lang.Formula (Fin (k + 1) ⊕ FixT D F) :=
  Formula.iInf (fun f : FixT D F =>
    Relations.formula₂ (Rel.lt : lang.Relations 2) (Term.var (Sum.inr f))
      (Term.var (Sum.inl bd)))

/-- N4.4: "`D` is realizable below the coordinate `bd`", with the fixed variables read from
`FixT` and the distinguished variable `t` (if any) at the coordinate `tgt`. -/
noncomputable def realFml {V : Type} (D : Diagram V) (F : V → Prop) (t : Option V) {k : Nat}
    (tgt bd : Fin (k + 1)) : lang.Formula (Fin (k + 1) ⊕ FixT D F) :=
  fixBelowFml D F bd ⊓
    Formula.iExs (FreeT D F t)
      (Formula.iInf (fun r : FreeT D F t =>
          Relations.formula₂ (Rel.lt : lang.Relations 2) (Term.var (Sum.inr r))
            (Term.var (Sum.inl (Sum.inl bd)))) ⊓
        (diagramFml D).relabel (splitVar D F t tgt))

/-- N4.4: "`D` is realizable" in the whole structure (no explicit bound; used with bound `w`). -/
noncomputable def realTopFml {V : Type} (D : Diagram V) (F : V → Prop) :
    lang.Formula (Fin 1 ⊕ FixT D F) :=
  Formula.iExs (FreeT D F none) ((diagramFml D).relabel (splitVar D F none 0))

open Classical in
/-- N4.4: the fixed assignment read from a valuation of `FixT` (`0` off the fixed variables). -/
noncomputable def fixAsg {ν : Ordinal.{u}} {Q : Prims.{u}} {V : Type} (D : Diagram V)
    (F : V → Prop) (v : FixT D F → Carrier ν Q) (x : V) : Ordinal.{u} :=
  if h : x ∈ D.vars ∧ F x then (v ⟨x, h⟩).val else 0

/-- N4.4: correctness of `realFml` (no distinguished variable). -/
theorem realize_realFml {ν : Ordinal.{u}} {Q : Prims.{u}} {V : Type} (D : Diagram V)
    (F : V → Prop) {k : Nat} (tgt bd : Fin (k + 1)) (c : Fin (k + 1) → Carrier ν Q)
    (v : FixT D F → Carrier ν Q) :
    (realFml D F none tgt bd).Realize (Sum.elim c v) ↔
      D.RealizableBelow Q F (fixAsg D F v) (c bd).val := by sorry

-- V-U4-4
/-- N4.4: correctness of `realFml` with a distinguished variable `t ∉ F`, which is read at the
coordinate `tgt` and whose value lies below the bound `bd` (used by `realize_transFml`). -/
theorem realize_realFml_some {ν : Ordinal.{u}} {Q : Prims.{u}} {V : Type} [DecidableEq V]
    (D : Diagram V) (F : V → Prop) (t : V) (ht : ¬ F t) {k : Nat} (tgt bd : Fin (k + 1))
    (c : Fin (k + 1) → Carrier ν Q) (v : FixT D F → Carrier ν Q)
    (htb : (c tgt).val < (c bd).val) :
    (realFml D F (some t) tgt bd).Realize (Sum.elim c v) ↔
      D.RealizableBelow Q (fun x => F x ∨ x = t)
        (Function.update (fixAsg D F v) t (c tgt).val) (c bd).val := by sorry

/-- N4.4: correctness of `realTopFml`: realizable below the height `ν` of the structure. -/
theorem realize_realTopFml {ν : Ordinal.{u}} {Q : Prims.{u}} {V : Type} (D : Diagram V)
    (F : V → Prop) (c : Fin 1 → Carrier ν Q) (v : FixT D F → Carrier ν Q) :
    (realTopFml D F).Realize (Sum.elim c v) ↔ D.RealizableBelow Q F (fixAsg D F v) ν := by
  sorry

/-- N4.4: `θ_{D,F}(a, b)` (coordinates `0 = a`, `1 = b`): fixed values below `a` and a
realization below `b` give a realization below `a`. -/
noncomputable def reflFml {V : Type} (D : Diagram V) (F : V → Prop) : lang.Formula (Fin 2) :=
  Formula.iAlls (FixT D F)
    (fixBelowFml D F 0 ⟹ (realFml D F none 0 1 ⟹ realFml D F none 0 0))

/-- N4.4: `τ_{D,F,t}(c, b, a)` (coordinates `0 = c`, `1 = b`, `2 = a`): fixed values below `a`
and a realization below `c` with `t ↦ b` give a realization below `b` with `t ↦ a`. -/
noncomputable def transFml {V : Type} (D : Diagram V) (F : V → Prop) (t : V) :
    lang.Formula (Fin 3) :=
  Formula.iAlls (FixT D F)
    (fixBelowFml D F 2 ⟹ (realFml D F (some t) 1 0 ⟹ realFml D F (some t) 2 1))

/-- N4.4: the reflection property of one diagram. -/
def ReflectsD (Q : Prims.{u}) {V : Type} (D : Diagram V) (F : V → Prop) (a b : Ordinal.{u}) :
    Prop :=
  ∀ σ : V → Ordinal.{u}, (∀ x ∈ D.vars, F x → σ x < a) →
    D.RealizableBelow Q F σ b → D.RealizableBelow Q F σ a

/-- N4.4: the transport property of one diagram and distinguished variable. -/
def TransportsD (Q : Prims.{u}) {V : Type} [DecidableEq V] (D : Diagram V) (F : V → Prop)
    (t : V) (c b a : Ordinal.{u}) : Prop :=
  ¬ F t → ∀ σ : V → Ordinal.{u}, (∀ x ∈ D.vars, F x → σ x < a) →
    D.RealizableBelow Q (fun x => F x ∨ x = t) (Function.update σ t b) c →
    D.RealizableBelow Q (fun x => F x ∨ x = t) (Function.update σ t a) b

/-- N4.4: `θ` expresses `ReflectsD` (for `a ≤ b`). -/
theorem realize_reflFml {ν : Ordinal.{u}} {Q : Prims.{u}} {V : Type} (D : Diagram V)
    (F : V → Prop) (a b : Carrier ν Q) (hab : a.val ≤ b.val) :
    (reflFml D F).Realize ![a, b] ↔ ReflectsD Q D F a.val b.val := by sorry

/-- N4.4: `τ` expresses `TransportsD` (for `t ∉ F` and `a < b < c`; for `t ∈ F` the property
`TransportsD` is vacuous and is not needed). -/
theorem realize_transFml {ν : Ordinal.{u}} {Q : Prims.{u}} {V : Type} [DecidableEq V]
    (D : Diagram V) (F : V → Prop) (t : V) (ht : ¬ F t) (c b a : Carrier ν Q)
    (hab : a.val < b.val) (hbc : b.val < c.val) :
    (transFml D F t).Realize ![c, b, a] ↔ TransportsD Q D F t c.val b.val a.val := by sorry

/-! ## N4.5: the recursive definition of `Elem` and `Edge` -/

/-- N4.5: all diagrams reflect from below `b` to below `a`. -/
def Reflects (Q : Prims.{u}) (a b : Ordinal.{u}) : Prop :=
  ∀ {V : Type} (D : Diagram V) (F : V → Prop), ReflectsD Q D F a b

/-- N4.5: all diagrams transport along `(c, b, a)`; this is the shape of the `transport`
field of `Interface`. -/
def Transports (Q : Prims.{u}) (c b a : Ordinal.{u}) : Prop :=
  ∀ {V : Type} [DecidableEq V] (D : Diagram V) (F : V → Prop) (σ : V → Ordinal.{u}) (t : V),
    ¬ F t → (∀ x ∈ D.vars, F x → σ x < a) →
    D.RealizableBelow Q (fun x => F x ∨ x = t) (Function.update σ t b) c →
    D.RealizableBelow Q (fun x => F x ∨ x = t) (Function.update σ t a) b

/-- N4.5: the data of one level `z`: `Elem (·) z` and `Edge z (·) (·)`. -/
abbrev LevData : Type (u + 1) := (Ordinal.{u} → Prop) × (Ordinal.{u} → Ordinal.{u} → Prop)

/-- N4.5: the primitives below `z`, read from the levels below `z`. -/
def below {z : Ordinal.{u}} (lv : ∀ y : Ordinal.{u}, y < z → LevData.{u}) : Prims.{u} where
  Elem x y := ∃ h : y < z, (lv y h).1 x
  Edge c b a := ∃ h : c < z, (lv c h).2 b a

/-- N4.5: one level, from the primitives below it. -/
def step (z : Ordinal.{u}) (Q : Prims.{u}) : LevData.{u} :=
  (fun a => IsLim a ∧ IsLim z ∧ a ≤ z ∧ Reflects Q a z,
   fun b a => IsLim a ∧ IsLim b ∧ IsLim z ∧ a < b ∧ b < z ∧ Q.Elem a b ∧
     (IsLim b ∧ IsLim z ∧ b ≤ z ∧ Reflects Q b z) ∧ Transports Q z b a)

/-- N4.5: the levels, by well-founded recursion on the top coordinate. -/
noncomputable def lev : Ordinal.{u} → LevData.{u} :=
  Ordinal.lt_wf.fix (fun z IH => step z (below IH))

/-- N4.5: the primitives of the reflection hierarchy. -/
noncomputable def prims : Prims.{u} := ⟨fun a b => (lev b).1 a, fun c b a => (lev c).2 b a⟩

/-- N4.5: unfolding `Elem`. -/
theorem elem_iff {a b : Ordinal.{u}} :
    prims.Elem a b ↔ IsLim a ∧ IsLim b ∧ a ≤ b ∧ Reflects prims a b := by sorry

/-- N4.5: unfolding `Edge`. -/
theorem edge_iff {c b a : Ordinal.{u}} :
    prims.Edge c b a ↔ IsLim a ∧ IsLim b ∧ IsLim c ∧ a < b ∧ b < c ∧ prims.Elem a b ∧
      prims.Elem b c ∧ Transports prims c b a := by sorry

/-! ## N4.6: the structural laws -/

/-- N4.6: field `elem_le`. -/
theorem elem_le {a b : Ordinal.{u}} (h : prims.Elem a b) : a ≤ b := by sorry
/-- N4.6: field `elem_lim`. -/
theorem elem_lim {a b : Ordinal.{u}} (h : prims.Elem a b) : IsLim a ∧ IsLim b := by sorry
/-- N4.6: field `elem_refl`. -/
theorem elem_refl {a : Ordinal.{u}} (h : IsLim a) : prims.Elem a a := by sorry
/-- N4.6: field `elem_trans`. -/
theorem elem_trans {a b c : Ordinal.{u}} (h₁ : prims.Elem a b) (h₂ : prims.Elem b c) :
    prims.Elem a c := by sorry
/-- N4.6: field `elem_mid`. -/
theorem elem_mid {a b c : Ordinal.{u}} (h : prims.Elem a c) (hab : a ≤ b) (hbc : b ≤ c)
    (hb : IsLim b) : prims.Elem a b := by sorry
/-- N4.6: field `edge_lt`. -/
theorem edge_lt {c b a : Ordinal.{u}} (h : prims.Edge c b a) : a < b ∧ b < c := by sorry
/-- N4.6: field `edge_lim`. -/
theorem edge_lim {c b a : Ordinal.{u}} (h : prims.Edge c b a) : IsLim a ∧ IsLim b ∧ IsLim c := by
  sorry
/-- N4.6: field `edge_elem_low`. -/
theorem edge_elem_low {c b a : Ordinal.{u}} (h : prims.Edge c b a) : prims.Elem a b := by sorry
/-- N4.6: field `edge_elem_high`. -/
theorem edge_elem_high {c b a : Ordinal.{u}} (h : prims.Edge c b a) : prims.Elem b c := by sorry
/-- N4.6: field `edge_restrict`. -/
theorem edge_restrict {c b a d : Ordinal.{u}} (h : prims.Edge c b a) (hd : IsLim d) (hbd : b < d)
    (hdc : d ≤ c) : prims.Edge d b a := by sorry
/-- N4.6: field `edge_extend`. -/
theorem edge_extend {c b a d : Ordinal.{u}} (h : prims.Edge c b a) (hcd : prims.Elem c d) :
    prims.Edge d b a := by sorry
/-- N4.6: field `capture` (by definition of `Elem`). -/
theorem capture {V : Type} (D : Diagram V) (F : V → Prop) (σ : V → Ordinal.{u})
    {a b : Ordinal.{u}} (hab : prims.Elem a b) (hσ : ∀ x ∈ D.vars, F x → σ x < a) :
    D.RealizableBelow prims F σ b → D.RealizableBelow prims F σ a := by sorry
/-- N4.6: field `transport` (by definition of `Edge`). -/
theorem transport {V : Type} [DecidableEq V] (D : Diagram V) (F : V → Prop)
    (σ : V → Ordinal.{u}) (t : V) {c b a : Ordinal.{u}} (h : prims.Edge c b a) (ht : ¬ F t)
    (hσ : ∀ x ∈ D.vars, F x → σ x < a) :
    D.RealizableBelow prims (fun x => F x ∨ x = t) (Function.update σ t b) c →
      D.RealizableBelow prims (fun x => F x ∨ x = t) (Function.update σ t a) b := by sorry

/-! ## N4.7: hulls in `M_w`, collapse and condensation -/

/-- N4.7: the ambient structure `M_w = M(w, prims)`. -/
abbrev M (w : Ordinal.{u}) : Type (u + 1) := Carrier w prims

/-- N4.7: the Skolem hull of `s` in `M_w`: the closure under Mathlib's Skolem functions, an
elementary substructure (`Substructure.elementarySkolem₁Reduct`). -/
noncomputable def hull (w : Ordinal.{u}) (hw : 0 < w) (s : Set (M w)) :
    lang.ElementarySubstructure (M w) :=
  haveI : Nonempty (M w) := ⟨⟨0, hw⟩⟩
  Substructure.elementarySkolem₁Reduct (Substructure.closure (lang.sum lang.skolem₁) s)

/-- N4.7: generators lie in the hull. -/
theorem subset_hull (w : Ordinal.{u}) (hw : 0 < w) (s : Set (M w)) :
    s ⊆ (hull w hw s : Set (M w)) := by sorry

/-- N4.7: monotonicity. -/
theorem hull_mono (w : Ordinal.{u}) (hw : 0 < w) {s t : Set (M w)} (h : s ⊆ t) :
    (hull w hw s : Set (M w)) ⊆ hull w hw t := by sorry

/-- N4.7: continuity on directed unions. -/
theorem hull_iUnion (w : Ordinal.{u}) (hw : 0 < w) {ι : Type*} [Nonempty ι]
    {s : ι → Set (M w)} (hs : Directed (· ⊆ ·) s) :
    (hull w hw (⋃ i, s i) : Set (M w)) = ⋃ i, (hull w hw (s i) : Set (M w)) := by sorry

/-- N4.7: the size bound `|hull s| ≤ max(ℵ₀, |s|)`. -/
theorem card_hull_le (w : Ordinal.{u}) (hw : 0 < w) (s : Set (M w)) :
    Cardinal.mk (hull w hw s) ≤ max ℵ₀ (Cardinal.mk s) := by sorry

/-- N4.7 (condensation for reflection structures): the order collapse of an elementary
substructure of `M_w` is an isomorphism onto the *genuine* `M_ν`, for some `ν ≤ w`; it fixes
every point below which the substructure is full, and `|ν| = |S|`. -/
theorem condensation {w : Ordinal.{u}} (S : lang.ElementarySubstructure (M w)) :
    ∃ (ν : Ordinal.{u}) (π : S ≃[lang] M ν), ν ≤ w ∧
      (∀ x y : S, ((x : M w).val < (y : M w).val ↔ (π x).val < (π y).val)) ∧
      (∀ x : S, (∀ o < (x : M w).val, ∃ y : S, (y : M w).val = o) →
        (π x).val = (x : M w).val) ∧
      Cardinal.lift.{u + 1} ν.card = Cardinal.mk S := by sorry

/-- N4.7: the collapse of a point is the order type of the substructure below it: if exactly
the ordinals below `x` lie (as points of `S`) below `k`, then `π k = x`. -/
theorem collapse_eq_of_cut {w ν : Ordinal.{u}} (S : lang.ElementarySubstructure (M w))
    (π : S ≃[lang] M ν)
    (hπ : ∀ x y : S, ((x : M w).val < (y : M w).val ↔ (π x).val < (π y).val)) (k : S)
    {x : Ordinal.{u}} (hcut : ∀ y : S, (y : M w).val < (k : M w).val ↔ (y : M w).val < x)
    (hfull : ∀ o < x, ∃ y : S, (y : M w).val = o) : (π k).val = x := by sorry

/-! ## N4.8: transfer of realizations through a collapsed hull -/

/-- N4.8: a realization below a point `bd` of `S` with fixed values at points of `S`
transfers to a realization below `π bd` with the collapsed fixed values. -/
theorem transfer {w ν : Ordinal.{u}} (S : lang.ElementarySubstructure (M w))
    (π : S ≃[lang] M ν) {V : Type} (D : Diagram V) (F : V → Prop) (σ σ' : V → Ordinal.{u})
    (p : V → S) (hp : ∀ x ∈ D.vars, F x → (p x : M w).val = σ x ∧ (π (p x)).val = σ' x)
    (bd : S) :
    D.RealizableBelow prims F σ (bd : M w).val → D.RealizableBelow prims F σ' (π bd).val := by
  sorry

/-- N4.8: the same with the top bound `w ↦ ν`. -/
theorem transfer_top {w ν : Ordinal.{u}} (S : lang.ElementarySubstructure (M w))
    (π : S ≃[lang] M ν) {V : Type} (D : Diagram V) (F : V → Prop) (σ σ' : V → Ordinal.{u})
    (p : V → S) (hp : ∀ x ∈ D.vars, F x → (p x : M w).val = σ x ∧ (π (p x)).val = σ' x) :
    D.RealizableBelow prims F σ w → D.RealizableBelow prims F σ' ν := by sorry

/-! ## N4.9: (13) and (14) for the reflection hierarchy -/

/-- N4.9a (13): `Elem κ w` for an uncountable cardinal `κ` and a limit `w > κ` (S-1). -/
theorem card_elem (κ : Cardinal.{u}) (w : Ordinal.{u}) (hκ : ℵ₀ < κ) (hw : IsLim w)
    (hκw : κ.ord < w) : prims.Elem κ.ord w := by sorry

/-- N4.9b: the hulls `H_r = hull(Iio r ∪ {κ})` in `M_w`. -/
noncomputable def hullAt (κ : Cardinal.{u}) (w : Ordinal.{u}) (hw : 0 < w) (r : Ordinal.{u}) :
    lang.ElementarySubstructure (M w) :=
  hull w hw {x | x.val < r ∨ x.val = κ.ord}

/-- N4.9b: for regular uncountable `κ`, `H_r ∩ κ` is bounded below `κ` when `r < κ`. -/
theorem hullAt_bounded (κ : Cardinal.{u}) (w : Ordinal.{u}) (hw : 0 < w) (hκ : ℵ₀ < κ)
    (hreg : κ.IsRegular) (hκw : κ.ord < w) {r : Ordinal.{u}} (hr : r < κ.ord) :
    ∃ f : Ordinal.{u}, r < f ∧ f < κ.ord ∧
      ∀ y : hullAt κ w hw r, (y : M w).val < κ.ord → (y : M w).val < f := by sorry

/-- N4.9b: the club of reflection points: limits `x < κ` whose hull meets `κ` exactly in `x`. -/
def reflPoints (κ : Cardinal.{u}) (w : Ordinal.{u}) (hw : 0 < w) : Set (Set.Iio κ.ord) :=
  {x | IsLim x.1 ∧ ∀ y : hullAt κ w hw x.1, (y : M w).val < κ.ord → (y : M w).val < x.1}

/-- N4.9b: `reflPoints` is a club. -/
theorem isClub_reflPoints (κ : Cardinal.{u}) (w : Ordinal.{u}) (hw : 0 < w) (hκ : ℵ₀ < κ)
    (hreg : κ.IsRegular) (hκw : κ.ord < w) : IsClub (reflPoints κ w hw) := by sorry

/-- N4.9b: every reflection point carries an edge `Edge w κ x`. -/
theorem edge_of_reflPoint (κ : Cardinal.{u}) (w : Ordinal.{u}) (hw : 0 < w) (hκ : ℵ₀ < κ)
    (hreg : κ.IsRegular) (hwl : IsLim w) (hκw : κ.ord < w) {x : Set.Iio κ.ord}
    (hx : x ∈ reflPoints κ w hw) : prims.Edge w κ.ord x.1 := by sorry

/-- N4.9b (14). -/
theorem club_edge (κ : Cardinal.{u}) (w : Ordinal.{u}) (hκ : ℵ₀ < κ) (hreg : κ.IsRegular)
    (hw : IsLim w) (hκw : κ.ord < w) :
    ∃ C : Set (Set.Iio κ.ord), IsClub C ∧ ∀ x ∈ C, prims.Edge w κ.ord x.1 := by sorry

/-- N4.10 (P-U4-1): the reflection-structure instance of the S-4 interface. -/
noncomputable def interface : Interface.{u} where
  toPrims := prims
  elem_le := elem_le
  elem_lim := elem_lim
  elem_refl := elem_refl
  elem_trans := elem_trans
  elem_mid := elem_mid
  edge_lt := edge_lt
  edge_lim := edge_lim
  edge_elem_low := edge_elem_low
  edge_elem_high := edge_elem_high
  edge_restrict := edge_restrict
  edge_extend := edge_extend
  capture := fun D F σ _ _ hab hσ => capture D F σ hab hσ
  transport := fun D F σ t _ _ _ h ht hσ => transport D F σ t h ht hσ
  card_elem := card_elem
  club_edge := club_edge

end Refl

end Hier

end BTBMS
