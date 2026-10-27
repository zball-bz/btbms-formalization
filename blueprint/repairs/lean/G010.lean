/-!
# G-010 repair — the decorated head path (U2: T3.2q, T3.8li, T3.8lb, T3.8lo)

Companion of `blueprint/repairs/G-010.md`. Appended after the integrated blueprint
(`Spine.lean`, then `U1.lean` … `U5.lean` without their imports). Owner U2, namespace
`BTBMS.Closure`. Every definition has a real body; every proof is `sorry`. Node IDs `D-G010.k`,
`L-G010.k` refer to the repair document.

The decorated system that the projection T3.8li really reads is not `capKeys B (routeCols B)` but
the system of the cap `K = litCap B c k ρ`, `capKeys K (routeCols K)`: there exactly the active
containers of the cap column are capped. Read back in `B` this is `activeKeys B c` (D-G010.1,
L-G010.1). In these systems the head path holds for every reduced `⊤`-free query (L-G010.10),
in particular for every cut query of `a` (L-G010.11).
-/

namespace BTBMS

open Scan

namespace Closure

/-! ## D-G010 — definitions -/

/-- D-G010.1 (txt:531-541, "cap all strict active ancestors"): the key system of `E` capped at the
active containers of `c`. In a column `o` with an entry `e` whose height contains `c`
(`o.container c = some e`), key `e.idx` becomes `⊤` and the later keys are dropped; every other
column keeps its actual keys. -/
def activeKeys (E : Forest) (c : ColAddr) : KeySys := fun o =>
  match o.container c with
  | some e => (actualKeys E o).take e.idx ++ [⊤]
  | none => actualKeys E o

/-- D-G010.2: `κ_φ` on reduced queries (`⊤` is fixed). -/
def kappaQ (r d φ : Nat) (W : List (WithTop Key)) : List (WithTop Key) :=
  W.map (WithTop.map (kappa r d φ))

/-- D-G010.2: the complete terminal query `Z = ν(y_0, …, y_{m−1})` (txt:380, 383). -/
def complQuery (sd : StopData) : List (WithTop Key) :=
  nu ((queryKeys sd).map fun k => (k : WithTop Key))

/-- D-G010.2: the projection of a vertex of a phase-`φ` stack (txt:521-524): `x − φd` above
`s_φ = r + φd`, `r` at `s_φ`, unchanged below. -/
def phaseProj (r d φ x : Nat) : Nat :=
  if r + φ * d < x then x - φ * d else if x = r + φ * d then r else x

/-- D-G010.3: `(a, c, φ)` is a phase pair of layer `j`: a template column `a` with its phase copy
`c = phaseCol j a` (phase `φ = phaseOff j a`; `φ = j − 1` for Q-material), or the stopping column
with the head of layer `j` (the old terminal in phase `j − 1`, txt:536-537, 607-608). -/
def PhasePair (A : Forest) (sd : StopData) (rd : RootData) (j : Nat) (a c : ColAddr) (φ : Nat) :
    Prop :=
  (IsTmplCol A sd rd a ∧ phaseCol sd rd j a = some c ∧ φ = phaseOff sd j a) ∨
    (a = sd.col ∧ phaseCol sd rd j rd.col = some c ∧ φ = j - 1)

/-- D-G010.4 (txt:532-533): an admissible key list of the root column `R`: its actual keys, or `R`
capped (key `u` raised to `⊤`, later keys dropped) at an entry `u ≥ c_A`. -/
def RootCap (A : Forest) (rd : RootData) (ks : List (WithTop Key)) : Prop :=
  ks = actualKeys A rd.col ∨
    ∃ u, rd.cursor ≤ u ∧ u < (parents A rd.col).length ∧
      ks = (actualKeys A rd.col).take u ++ [⊤]

/-- D-G010.5 (T3.2i): the image, on the stack of the copy `c`, of a column `o` of the stack of `a`
above `r`. The stopping column goes to the head of layer `j`; for Q-material and for the head pair
the columns of the stopping column's stack go to layer `j − 1` (to themselves when `j = 1`: phase
`0` is `A`'s own material, kept as context); every other template column goes to layer `j`. -/
def phaseImg (sd : StopData) (rd : RootData) (j : Nat) (a o : ColAddr) : Option ColAddr :=
  if o = sd.col then phaseCol sd rd j rd.col
  else if (isQMat sd a && !isQMat sd o) || a == sd.col then
    (if j = 1 then some o else phaseCol sd rd (j - 1) o)
  else phaseCol sd rd j o

/-- D-G010.2: `OrdStep.proj` is `phaseProj` (holds by `rfl`). -/
theorem OrdStep.proj_eq_phaseProj (S : OrdStep) (φ ρ : Nat) :
    S.proj φ ρ = phaseProj S.sd.r S.d φ ρ := by sorry

/-! ## L-G010.21 — generic helpers (word and address level) -/

/-- L-G010.21a: a `⊤`-free query never passes a source key `⊤`. -/
theorem cursor_append_top (l : List (WithTop Key)) {W : List (WithTop Key)} (hT : ∀ w ∈ W, w ≠ ⊤) :
    cursor (l ++ [⊤]) W ≤ l.length := by sorry

/-- L-G010.21b: cut queries of actual keys are `⊤`-free (letters of `ν(l)` are letters of `l`). -/
theorem ne_top_of_mem_cutQuery (E : Forest) (o : ColAddr) (k : Nat) :
    ∀ w ∈ cutQuery (actualKeys E o) k, w ≠ ⊤ := by sorry

/-- L-G010.21c (T3.2i fill law, address level): the stack of a placed address is the stack of the
hole below the hole's number and the placed stack above it. -/
theorem resolve_underCol (h a : ColAddr) (q : Nat) :
    (underCol h a).resolve 0 q =
      if q < h.num 0 then h.resolve 0 q else (a.resolve 0 (q - h.num 0)).map (underCol h) := by
  sorry

/-- L-G010.21e (T3.2i fill law, template level): `kerCol` carries the stack of a root-tail template
column, and of the stopping column, from `r` on to the stack of its kernel image, numbers shifted
by `−r` (the root goes to the head, column `0`). -/
theorem resolve_kerCol {A : Forest} {sd : StopData} {rd : RootData} (hL : InL A)
    (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd) (hrd : rootData A = some rd)
    {a a' : ColAddr} (ha : (IsTmplCol A sd rd a ∧ isQMat sd a = false) ∨ a = sd.col)
    (ha' : kerCol sd rd a = some a') {x : Nat} (hx : sd.r ≤ x) {o : ColAddr}
    (ho : a.resolve 0 x = some o) : a'.resolve 0 (x - sd.r) = kerCol sd rd o := by sorry

/-- L-G010.21e (Q-material form): from `t` on, numbers shift by `−t` and the stopping column goes to
the head. -/
theorem resolve_kerCol_qmat {A : Forest} {sd : StopData} {rd : RootData} (hL : InL A)
    (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd) (hrd : rootData A = some rd)
    {a a' : ColAddr} (ha : IsTmplCol A sd rd a) (hq : isQMat sd a = true)
    (ha' : kerCol sd rd a = some a') {x : Nat} (hx : sd.t ≤ x) {o : ColAddr}
    (ho : a.resolve 0 x = some o) :
    a'.resolve 0 (x - sd.t) = if o = sd.col then some ⟨[], 0⟩ else kerCol sd rd o := by sorry

/-- L-G010.21f (T3.2i proof step 2, context fill law): a column of `A` other than the stopping
column and outside its heights is a column of `B` with the same parents, and the same heights
except the one containing the stopping column (a continuation). -/
theorem colAt_context {A B : Forest} {sd : StopData} {rd : RootData} {n : Nat} (hL : InL A)
    (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd) (hrd : rootData A = some rd)
    (hB : expand A n = some B) {o : ColAddr} (ho : o ∈ A.colAddrs) (hne : o ≠ sd.col)
    (hout : ∀ v, ¬ (⟨sd.col, v⟩ : EntryAddr).Contains o) :
    ∃ colA colB, A.colAt o = some colA ∧ B.colAt o = some colB ∧ colB.length = colA.length ∧
      ∀ v x, colA[v]? = some x → ∃ y, colB[v]? = some y ∧ y.1 = x.1 ∧
        (¬ (⟨o, v⟩ : EntryAddr).Contains sd.col → y.2 = x.2) := by sorry

/-- L-G010.21d (D3.1c, L3.1c): the full cut of a nonempty route column is at the end of the word
(an empty route column's marker atom is replaced instead: `capPos = µ − 1`). -/
theorem capPos_route {E : Forest} {c : ColAddr} (hc : c ∈ routeCols E) (hne : parents E c ≠ []) :
    capPos E c (parents E c).length = mu E := by sorry

/-! ## L-G010.1–3 — the capped systems of a literal cap, of a stack, of the stopping column -/

/-- L-G010.1 (bridge): on the stack of the cap column, the decorated system of a literal cap is
`activeKeys` of the capped expression (edge level, every `⊤`-free query; with `⊤` in `W` the
scan can pass the capped key, and `E` has entries that the cap deleted). -/
theorem respEdge_litCap_activeKeys {E : Forest} {c : ColAddr} {k p : Nat} (hc : c ∈ E.colAddrs)
    (hk : k ≤ (parents E c).length) {W : List (WithTop Key)} (hT : ∀ w ∈ W, w ≠ ⊤) (x : Nat) :
    respEdge (litCap E c k p) (capKeys (litCap E c k p) (routeCols (litCap E c k p))) c W x =
      respEdge E (activeKeys E c) c W x := by sorry

/-- L-G010.1 (bridge, path form). -/
theorem path_litCap_activeKeys {E : Forest} {c : ColAddr} {k p : Nat} (hc : c ∈ E.colAddrs)
    (hk : k ≤ (parents E c).length) {W : List (WithTop Key)} (hT : ∀ w ∈ W, w ≠ ⊤) (x y : Nat) :
    Path (litCap E c k p) (capKeys (litCap E c k p) (routeCols (litCap E c k p))) c W x y ↔
      Path E (activeKeys E c) c W x y := by sorry

/-- L-G010.2: below a stack column `c'` of `c`, the systems capped at `c` and at `c'` give the
same responses. -/
theorem respEdge_activeKeys_onStack (E : Forest) {c c' : ColAddr} {z : Nat}
    (hc' : c.resolve 0 z = some c') (W : List (WithTop Key)) {x : Nat} (hx : x < z) :
    respEdge E (activeKeys E c) c W x = respEdge E (activeKeys E c') c' W x := by sorry

/-- L-G010.3: on the stack of the stopping column, `activeKeys` is the route-capped system of
`A` (the containers of `sd.col` are the route columns above it, active at their last entries). -/
theorem activeKeys_stopCol {A : Forest} {sd : StopData} (hsd : stopData A = some sd) {o : ColAddr}
    {z : Nat} (ho : sd.col.resolve 0 z = some o) :
    activeKeys A sd.col o = capKeys A (routeCols A) o := by sorry

/-! ## L-G010.4–9 — phase copies, heads, roots -/

/-- L-G010.4a (T3.2i.4 for hole-route columns): a template column on the hole route is copied with
parents shifted; only an entry containing the stopping column (necessarily the last) carries a
changed (continuation) height, and then the copy is a route column of `B`. -/
theorem colAt_phaseCol_route {A B : Forest} {sd : StopData} {rd : RootData} {n i : Nat}
    {a c : ColAddr} (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hi : 1 ≤ i ∧ i ≤ n)
    (ha : IsTmplCol A sd rd a) (hroute : OnHoleRoute sd a) (hc : phaseCol sd rd i a = some c) :
    ∃ colA colB, A.colAt a = some colA ∧ B.colAt c = some colB ∧ colB.length = colA.length ∧
      (∀ v x, colA[v]? = some x → ∃ y, colB[v]? = some y ∧
        y.1 = shiftVal sd.r (i * period sd) x.1 ∧
        (¬ (⟨a, v⟩ : EntryAddr).Contains sd.col → y.2 = shift sd.r (i * period sd) x.2)) ∧
      (∀ v, (⟨a, v⟩ : EntryAddr).Contains sd.col → c ∈ routeCols B) := by sorry

/-- L-G010.4b (stack correspondence above `r`): the stack of `c` at `x + φd` is the image of the
stack of `a` at `x`, with the same active container entries, capped keys `κ_φ`-related and parents
`τ_φ`-related up to the active entry. -/
theorem phaseImg_spec {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) {x : Nat} (hx : sd.r < x) {o : ColAddr}
    (ho : a.resolve 0 x = some o) :
    ∃ o', phaseImg sd rd j a o = some o' ∧ c.resolve 0 (x + φ * period sd) = some o' ∧
      (o'.container c).map EntryAddr.idx = (o.container a).map EntryAddr.idx ∧
      activeKeys B c o' = kappaQ sd.r (period sd) φ (activeKeys A a o) ∧
      ∀ v, v < (activeKeys A a o).length →
        (parents B o')[v]? = ((parents A o)[v]?).map (shiftVal sd.r (φ * period sd)) := by sorry

/-- L-G010.4c (the fixed region below `r`): the stacks agree below `r`, and so do the capped keys,
which are `κ`-fixed, and the parents up to the active entry. -/
theorem fixed_spec {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) {x : Nat} (hx : x < sd.r) {o : ColAddr}
    (ho : a.resolve 0 x = some o) :
    c.resolve 0 x = some o ∧ activeKeys B c o = activeKeys A a o ∧
      kappaQ sd.r (period sd) φ (activeKeys A a o) = activeKeys A a o ∧
      ∀ v, v < (activeKeys A a o).length → (parents B o)[v]? = (parents A o)[v]? := by sorry

/-- L-G010.4 (edge copy; T3.2q step 1, txt:524-530): phase-`φ` material is copied edge by edge, and
the fixed region below `r` is shared, for every `⊤`-free query (a `⊤` in `W` could pass an active
key, beyond which `a`'s and `c`'s columns differ: the old terminal against the restored suffix). -/
theorem respEdge_phase_active {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) {W : List (WithTop Key)}
    (hT : ∀ w ∈ W, w ≠ ⊤) (x : Nat) :
    (sd.r < x → respEdge B (activeKeys B c) c (kappaQ sd.r (period sd) φ W) (x + φ * period sd) =
      (respEdge A (activeKeys A a) a W x).map (shiftVal sd.r (φ * period sd))) ∧
    (x < sd.r → respEdge B (activeKeys B c) c (kappaQ sd.r (period sd) φ W) x =
      respEdge A (activeKeys A a) a W x) := by sorry

/-- L-G010.5 (head keys; T3.2i.5 with T3.2h.1, T3.2h.5): every head `s_h`, `1 ≤ h ≤ φ`, lies on the
stack of `c`; in `activeKeys B c` its keys are `κ_{h−1}(y)` followed by an admissible root list from
`c_A` on, which at `h = φ` is the root list of `activeKeys A a`; its parents are `τ_{h−1}(Q)`'s
followed by the root parents from `c_A` on. -/
theorem activeKeys_head {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) {h : Nat} (hh1 : 1 ≤ h) (hh : h ≤ φ) :
    ∃ hd ks, phaseCol sd rd h rd.col = some hd ∧
      c.resolve 0 (sd.r + h * period sd) = some hd ∧ RootCap A rd ks ∧
      (h = φ → ks = activeKeys A a rd.col) ∧
      activeKeys B c hd =
        (queryKeys sd).map (fun y => ((kappa sd.r (period sd) (h - 1) y : Key) : WithTop Key)) ++
          ks.drop rd.cursor ∧
      parents B hd = sd.Q.map (fun x => shiftVal sd.r ((h - 1) * period sd) x.1) ++
        (parents A rd.col).drop rd.cursor := by sorry

/-- L-G010.6 (the old root on both stacks): `R` is the column `r` of both stacks, keeps its parents,
and both capped systems read it through an admissible root list. -/
theorem activeKeys_root {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) (hφ : 1 ≤ φ) :
    a.resolve 0 sd.r = some rd.col ∧ c.resolve 0 sd.r = some rd.col ∧
      parents B rd.col = parents A rd.col ∧
      RootCap A rd (activeKeys A a rd.col) ∧ RootCap A rd (activeKeys B c rd.col) := by sorry

/-- L-G010.7 (T3.2p.2 hypotheses for an admissible root list, spine L2.1). -/
theorem rootCap_headHyp {A : Forest} {sd : StopData} {rd : RootData} (hL : InL A)
    (hsd : stopData A = some sd) (hrd : rootData A = some rd) {ks : List (WithTop Key)}
    (hks : RootCap A rd ks) :
    rd.cursor ≤ ks.length ∧ cutQuery ks rd.cursor ≤ complQuery sd ∧
      (rd.cursor < ks.length → complQuery sd < cutQuery ks (rd.cursor + 1)) := by sorry

/-- L-G010.8 (txt:532-534, "at low queries both … have cursor at most c and the same
response"): below the complete query every admissible root list scans like `R`, and stops at or
before `c_A`. -/
theorem rootCap_low {A : Forest} {sd : StopData} {rd : RootData} (hL : InL A)
    (hsd : stopData A = some sd) (hrd : rootData A = some rd) {ks : List (WithTop Key)}
    (hks : RootCap A rd ks) {W : List (WithTop Key)} (hW : W.Pairwise fun x y => y ≤ x)
    (hT : ∀ w ∈ W, w ≠ ⊤) (hlow : W < complQuery sd) :
    cursor ks W = cursor (actualKeys A rd.col) W ∧ cursor (actualKeys A rd.col) W ≤ rd.cursor := by
  sorry

/-- L-G010.9 (txt:396-397, 535-537; OP-U2-5): Q-material is phase `j − 1` uniformly: the head of
layer `j` sits on the stack of the copy at `t + (j−1)d`, contains it through the same entry
`q < m` through which the stopping column contains `a`, and is the phase-`(j−1)` copy of the old
terminal up to that entry. -/
theorem qmat_head {A B : Forest} {sd : StopData} {rd : RootData} {n j : Nat} (hL : InL A)
    (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd) (hrd : rootData A = some rd)
    (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n) {a c : ColAddr}
    (ha : IsTmplCol A sd rd a) (hq : isQMat sd a = true) (hc : phaseCol sd rd j a = some c) :
    ∃ q hd, sd.col.container a = some ⟨sd.col, q⟩ ∧ q < sd.Q.length ∧
      a.resolve 0 sd.t = some sd.col ∧ phaseCol sd rd j rd.col = some hd ∧
      c.resolve 0 (sd.t + (j - 1) * period sd) = some hd ∧ hd.container c = some ⟨hd, q⟩ ∧
      activeKeys B c hd = kappaQ sd.r (period sd) (j - 1) (activeKeys A a sd.col) ∧
      (parents B hd).take (q + 1) =
        ((parents A sd.col).take (q + 1)).map (shiftVal sd.r ((j - 1) * period sd)) := by sorry

/-! ## L-G010.10–14 — the decorated head path -/

/-- L-G010.12 (generic): paths of a deterministic decreasing system are orbits. -/
theorem path_det {E : Forest} (hV : CondV E) {ks : KeySys} {c : ColAddr} {W : List (WithTop Key)}
    {x y z : Nat} (hy : Path E ks c W x y) (hz : Path E ks c W x z) (hyz : y ≤ z) :
    Path E ks c W z y := by sorry

/-- L-G010.13 (T3.2h): `κ_j` is inflationary on reduced queries. -/
theorem le_kappaQ (r d j : Nat) (W : List (WithTop Key)) : W ≤ kappaQ r d j W := by sorry

/-- L-G010.14 (T3.2q step 2, high case, txt:390-391): a high scan at the head `s_φ` returns the old
root response at `W`. -/
theorem respEdge_head_high {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) (hφ : 1 ≤ φ)
    {W : List (WithTop Key)} (hW : W.Pairwise fun x y => y ≤ x) (hT : ∀ w ∈ W, w ≠ ⊤)
    (hhigh : complQuery sd ≤ kappaQ sd.r (period sd) 1 W) :
    respEdge B (activeKeys B c) c (kappaQ sd.r (period sd) φ W) (sd.r + φ * period sd) =
      respEdge A (activeKeys A a) a W sd.r := by sorry

/-- L-G010.14 corollary (T3.8lo step 1): a high exit at `s_φ` lands below `r`. -/
theorem head_high_exit {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) (hφ : 1 ≤ φ)
    {W : List (WithTop Key)} (hW : W.Pairwise fun x y => y ≤ x) (hT : ∀ w ∈ W, w ≠ ⊤)
    (hhigh : complQuery sd ≤ kappaQ sd.r (period sd) 1 W) {p : Nat}
    (he : respEdge B (activeKeys B c) c (kappaQ sd.r (period sd) φ W) (sd.r + φ * period sd) = some p) :
    p < sd.r := by sorry

/-- L-G010.15 (T3.2q steps 2–3, low case, txt:391-394, 527-530): below the complete query the
detours through the heads are deleted: a path from `s_φ` to an endpoint below `r` is an old path
from `r`. -/
theorem path_head_low {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) (hφ : 1 ≤ φ)
    {W : List (WithTop Key)} (hW : W.Pairwise fun x y => y ≤ x) (hT : ∀ w ∈ W, w ≠ ⊤)
    (hlow : kappaQ sd.r (period sd) 1 W < complQuery sd) {y : Nat} (hy : y < sd.r)
    (hpath : Path B (activeKeys B c) c (kappaQ sd.r (period sd) φ W) (sd.r + φ * period sd) y) :
    Path A (activeKeys A a) a W sd.r y := by sorry

/-- L-G010.15' (with T3.8lm): a low path from `s_φ` passes through `r` itself. -/
theorem path_head_low_root {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) (hφ : 1 ≤ φ)
    {W : List Key} (hW : W.Pairwise fun x y => y ≤ x)
    (hlow : kappaQ sd.r (period sd) 1 (W.map fun k => (k : WithTop Key)) < complQuery sd) :
    Path B (activeKeys B c) c (kappaQ sd.r (period sd) φ (W.map fun k => (k : WithTop Key)))
      (sd.r + φ * period sd) sd.r := by sorry

/-- L-G010.10 (G-010: the decorated head path). Paths in the system capped at the active
containers of the copy `c` project to paths in the system capped at the active containers of `a`,
for every reduced `⊤`-free query, from every start outside `[r, s_φ)` to every end outside
`(r, s_φ)`. -/
theorem head_path_active {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) (hφ : 1 ≤ φ)
    {W : List (WithTop Key)} (hW : W.Pairwise fun x y => y ≤ x) (hT : ∀ w ∈ W, w ≠ ⊤)
    {x y : Nat} (hx : x < sd.r ∨ sd.r + φ * period sd ≤ x)
    (hy : y ≤ sd.r ∨ sd.r + φ * period sd ≤ y)
    (hpath : Path B (activeKeys B c) c (kappaQ sd.r (period sd) φ W) x y) :
    Path A (activeKeys A a) a W (phaseProj sd.r (period sd) φ x)
      (phaseProj sd.r (period sd) φ y) := by sorry

/-- L-G010.11 (the decorated `head_path` for cut queries of `a`, the form T3.8li uses). -/
theorem head_path_cut {A B : Forest} {sd : StopData} {rd : RootData} {n j φ : Nat}
    (hL : InL A) (hk : stepKind A = some .ordinary) (hsd : stopData A = some sd)
    (hrd : rootData A = some rd) (hB : expand A n = some B) (hj : 1 ≤ j ∧ j ≤ n)
    {a c : ColAddr} (hp : PhasePair A sd rd j a c φ) (hφ : 1 ≤ φ) (k : Nat)
    {x y : Nat} (hx : x < sd.r ∨ sd.r + φ * period sd ≤ x)
    (hy : y ≤ sd.r ∨ sd.r + φ * period sd ≤ y)
    (hpath : Path B (activeKeys B c) c
      (kappaQ sd.r (period sd) φ (cutQuery (actualKeys A a) k)) x y) :
    Path A (activeKeys A a) a (cutQuery (actualKeys A a) k) (phaseProj sd.r (period sd) φ x)
      (phaseProj sd.r (period sd) φ y) := by sorry

/-! ## L-G010.16–20 — the final tests of T3.8li and T3.8lb -/

/-- L-G010.16 (T3.8li step 1, made explicit): a cut of a template copy before `µ(B)` is pure: its
first `k` entries are the phase copies of `a`'s, so its cut query is `κ_φ` of `a`'s. -/
theorem cutPrefix_phaseCol (S : OrdStep) {i : Nat} {a c : ColAddr} {k : Nat}
    (hi : 1 ≤ i ∧ i ≤ S.n) (ha : IsTmplCol S.A S.sd S.rd a) (hc : phaseCol S.sd S.rd i a = some c)
    (hk : k ≤ (parents S.B c).length) (hend : capPos S.B c k < mu S.B) :
    k ≤ (parents S.A a).length ∧
      (parents S.B c).take k =
        ((parents S.A a).take k).map (shiftVal S.sd.r (phaseOff S.sd i a * S.d)) ∧
      cutQuery (actualKeys S.B c) k =
        kappaQ S.sd.r S.d (phaseOff S.sd i a) (cutQuery (actualKeys S.A a) k) := by sorry

/-- L-G010.17 (T3.8lb step 1, made explicit): the query part of a head is the phase-`(i−1)` copy of
the old terminal's query part. -/
theorem cutPrefix_head (S : OrdStep) {i : Nat} {c : ColAddr} {k : Nat} (hi : 1 ≤ i ∧ i ≤ S.n)
    (hc : phaseCol S.sd S.rd i S.rd.col = some c) (hk : k ≤ S.m) :
    (parents S.B c).take k =
        ((parents S.A S.sd.col).take k).map (shiftVal S.sd.r ((i - 1) * S.d)) ∧
      cutQuery (actualKeys S.B c) k =
        kappaQ S.sd.r S.d (i - 1) (cutQuery (actualKeys S.A S.sd.col) k) := by sorry

/-- L-G010.18 (cut starts, T3.8ln): the start of a pure phase-`φ` cut lies outside `[r, s_φ)` and
projects to the old start. -/
theorem cutStart_phase {A B : Forest} {r d φ : Nat} (hφ : 1 ≤ φ) {a c : ColAddr} {k : Nat}
    (ha : r < a.num 0) (hnum : c.num 0 = a.num 0 + φ * d) (hk : k ≤ (parents A a).length)
    (hpre : (parents B c).take k = ((parents A a).take k).map (shiftVal r (φ * d))) :
    (cutStart B c k < r ∨ r + φ * d ≤ cutStart B c k) ∧
      phaseProj r d φ (cutStart B c k) = cutStart A a k := by sorry

/-- L-G010.19 (T3.8li step 5, the final test of the projected cap). -/
theorem projection_finalTest (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat}
    (hi : 1 ≤ i ∧ i ≤ S.n) (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ)
    (hKL : InL (litCap S.B c k ρ)) (hend : capPos S.B c k < mu S.B)
    (hρ : ρ ≤ S.sd.r ∨ S.s (phaseOff S.sd i a) ≤ ρ) :
    let K' := litCap S.A a k (S.proj (phaseOff S.sd i a) ρ)
    AAt K' (capKeys K' (routeCols K')) a k := by sorry

/-- L-G010.20 (T3.8lb step 4, the final test of the old terminal cap). -/
theorem headQuery_finalTest (S : OrdStep) {i : Nat} {c : ColAddr} {k ρ : Nat}
    (hi : 2 ≤ i ∧ i ≤ S.n) (hc : phaseCol S.sd S.rd i S.rd.col = some c)
    (hk : k < S.m ∨ (k = S.m ∧ S.s (i - 1) < ρ)) (hup : IsUpward S.B c k ρ)
    (hKL : InL (litCap S.B c k ρ)) (hρ : S.s (i - 1) < ρ) :
    let K' := litCap S.A S.sd.col k (ρ - (i - 1) * S.d)
    AAt K' (capKeys K' (routeCols K')) S.sd.col k := by sorry

end Closure

end BTBMS
