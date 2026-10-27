/-!
# G-009 — the low-head detour invariant behind T3.8lo (U2, paper txt:553-560)

Repair of OP-U2-1 (`blueprint/repairs/G-009.md`). Appended after `blueprint/lean/U5.lean` in the
integrated check; no imports beyond those of the unit files. Owner unit U2, namespace
`BTBMS.Closure`. Every declaration's comment starts with its repair node ID (`G9.k`). All proofs
are `sorry`; the proof plans are in the repair document.

Notation (as in U2): `S : OrdStep`, `r = S.sd.r`, `t = S.sd.t`, `d = S.d`, `m = S.m`,
`s_h = S.s h`, `φ = phaseOff S.sd i a`, `K = litCap S.B c k ρ`, `V = S.capQ c k ρ` (the cut query
of `K` at `(c, k)`), `Z = S.termZ` (the old terminal's complete query).
-/

namespace BTBMS

open Scan

namespace Closure

/-! ## G9.0 — definitions -/

/-- G9.0: `κ_j` on a query of actual keys (a list of `WithTop Key`), exactly the map applied to
queries in `head_path` (T3.2q). -/
def kappaQry (r d j : Nat) (W : List (WithTop Key)) : List (WithTop Key) :=
  W.map (WithTop.map (kappa r d j))

namespace OrdStep

variable (S : OrdStep)

/-- G9.0: the old terminal's complete query `Z = B_t(m−1) = ν(y_0,…,y_{m−1})` (txt:381), read in
the actual key system of `A` at the stopping column. -/
def termZ : List (WithTop Key) := cutQuery (actualKeys S.A S.sd.col) S.m

/-- G9.0: the address in `B` of the head `s_h` of layer `h ≥ 1` (`phaseCol h rd.col`). -/
def headCol (h : Nat) : ColAddr := (phaseCol S.sd S.rd h S.rd.col).getD S.rd.col

/-- G9.0: the phase-`h` copy in `B` of a column `o` of `A` on the stopping column's stack: `o`
itself at phase `0` (retained context), `phaseCol h o` at phase `h ≥ 1`. -/
def copyCol (h : Nat) (o : ColAddr) : ColAddr :=
  if h = 0 then o else (phaseCol S.sd S.rd h o).getD o

/-- G9.0: the cut query `V = B_c(k−1)` of the literal cap `K = litCap B c k ρ` at its stopping
column `c` (the query of `K`'s closing A test and of its root scan). -/
def capQ (c : ColAddr) (k ρ : Nat) : List (WithTop Key) :=
  cutQuery (actualKeys (litCap S.B c k ρ) c) k

end OrdStep

/-! ## G9.1, G9.2 — generic scan and path facts -/

section G9Words

variable {α : Type} [LinearOrder α]

-- G9.1: two sources that agree before `u`, scanned by runs that both stop at or before `u`,
-- have the same final cursor
theorem cursor_eq_of_take_eq {s₁ s₂ W : List α} {u : Nat} (htake : s₁.take u = s₂.take u)
    (h₁ : cursor s₁ W ≤ u) (h₂ : cursor s₂ W ≤ u) : cursor s₁ W = cursor s₂ W := by sorry

-- G9.2a: a query strictly below the full boundary of the first `m` keys stops before `m`
theorem cursor_lt_of_lt_cutQuery {ks W : List α} (hW : Noninc W) {m : Nat} (hm : m ≤ ks.length)
    (h : W < cutQuery ks m) : cursor ks W < m := by sorry

-- G9.2b: conversely, a run that stops before `m` has its query strictly below that boundary
theorem lt_cutQuery_of_cursor_lt {ks W : List α} (hW : Noninc W) {m : Nat} (hm : m ≤ ks.length)
    (h : cursor ks W < m) : W < cutQuery ks m := by sorry

-- G9.2c: `ν(l)` is a sublist of `l`
theorem nu_sublist (l : List α) : (nu l).Sublist l := by sorry

end G9Words

-- G9.2d: `κ_j` on `WithTop Key` is strictly increasing
theorem kappaQry_strictMono (r d j : Nat) : StrictMono (WithTop.map (kappa r d j)) := by sorry

-- G9.2e: path nesting for whole paths (U1 L2.2 edgewise)
theorem path_nesting_path {E : Forest} {ks : KeySys} (hV : CondV E) (hA : CondAK E ks)
    (c : ColAddr) {W Z : List (WithTop Key)} (hW : Noninc W) (hZ : Noninc Z) (hWZ : W ≤ Z)
    {x y : Nat} (h : Path E ks c Z x y) : Path E ks c W x y := by sorry

-- G9.2f: paths are orbits of the partial response function: a path through `y` and a path to a
-- lower `z` from the same start meet, so `z` is reached from `y`
theorem path_functional {E : Forest} (hV : CondV E) {ks : KeySys} {c : ColAddr}
    {W : List (WithTop Key)} {x y z : Nat} (hy : Path E ks c W x y) (hz : Path E ks c W x z)
    (hzy : z ≤ y) : Path E ks c W y z := by sorry

/-! ## G9.3 — the old terminal-to-root path at a low query -/

-- G9.3 (txt:391-392, "path nesting supplies the terminal-to-root path"): at a reduced query
-- `W' < Z` the old terminal answers with a query parent `q_j`, `j = cursor y W' < m`, and `q_j`
-- reaches `r` by a `g_{W'}` path on the stopping column's stack
theorem term_detour (S : OrdStep) {W : List (WithTop Key)} (hW : Noninc W) (hlow : W < S.termZ) :
    cursor (actualKeys S.A S.sd.col) W < S.m ∧
      ∃ q, (parents S.A S.sd.col)[cursor (actualKeys S.A S.sd.col) W]? = some q ∧
        S.sd.r ≤ q ∧ q < S.sd.t ∧ Path S.A (actualKeys S.A) S.sd.col W q S.sd.r := by sorry

/-! ## G9.4 — the stack of a phase copy (address algebra, T3.2i) -/

-- G9.4s1: the stack of `underCol h b` is the stack of `h` together with the `underCol h`-image of
-- the stack of `b`
theorem onStack_underCol (h b o : ColAddr) :
    (underCol h b).OnStack o ↔ h.OnStack o ∨ ∃ o', b.OnStack o' ∧ o = underCol h o' := by sorry

-- G9.4s2: printed numbers add under `underCol`
theorem num_underCol (h b : ColAddr) : (underCol h b).num 0 = h.num 0 + b.num 0 := by sorry

-- G9.4s3: containment is carried by `underCol`
theorem container_underCol (h b o : ColAddr) :
    (underCol h o).container (underCol h b) = (o.container b).map fun e => ⟨underCol h o, e.idx⟩ := by
  sorry

-- G9.4s3b: a column strictly on the stack of `h` contains `underCol h b` exactly when it contains
-- `h`, through the same entry
theorem container_underCol_of_onStack {h o : ColAddr} (ho : h.OnStack o) (b : ColAddr) :
    o.container (underCol h b) = o.container h := by sorry

-- G9.4s4: on root-tail material `kerCol` is a stack isomorphism onto the kernel output, with
-- `num (kerCol o) = num o − r`, and it carries containment
theorem onStack_kerCol_tail (S : OrdStep) {x x' : ColAddr} (hx : kerCol S.sd S.rd x = some x')
    (hxq : isQMat S.sd x = false) (o' : ColAddr) :
    x'.OnStack o' ↔ ∃ o, x.OnStack o ∧ S.sd.r ≤ o.num 0 ∧ isQMat S.sd o = false ∧
      kerCol S.sd S.rd o = some o' := by sorry

-- G9.4s4b: every stack column with number `≥ r` of root-tail material is root-tail material
theorem kerCol_of_onStack_tail (S : OrdStep) {x x' : ColAddr} (hx : kerCol S.sd S.rd x = some x')
    (hxq : isQMat S.sd x = false) {o : ColAddr} (ho : x.OnStack o) (hr : S.sd.r ≤ o.num 0) :
    (kerCol S.sd S.rd o).isSome ∧ isQMat S.sd o = false := by sorry

theorem num_kerCol_tail (S : OrdStep) {x x' : ColAddr} (hx : kerCol S.sd S.rd x = some x')
    (hxq : isQMat S.sd x = false) : x'.num 0 + S.sd.r = x.num 0 := by sorry

theorem container_kerCol (S : OrdStep) {x x' o o' : ColAddr} (hx : kerCol S.sd S.rd x = some x')
    (ho : kerCol S.sd S.rd o = some o') (hxq : isQMat S.sd x = false) :
    o'.container x' = (o.container x).map fun e =>
      ⟨o', if o = S.rd.col then S.m + (e.idx - S.rd.cursor) else e.idx⟩ := by sorry

-- G9.4s5: the stack of Q-material images: the head and Q-material images only
theorem onStack_kerCol_qmat (S : OrdStep) {x x' : ColAddr} (hx : kerCol S.sd S.rd x = some x')
    (hxq : isQMat S.sd x = true) (o' : ColAddr) :
    x'.OnStack o' ↔ o' = ⟨[], 0⟩ ∨ ∃ o, x.OnStack o ∧ isQMat S.sd o = true ∧
      kerCol S.sd S.rd o = some o' := by sorry

-- G9.4l: a literal cap keeps every stack column of its cap column: a container through its
-- active entry `u` (same parents up to `u`, same keys before `u`), any other stack column whole
theorem colAt_litCap_onStack {B : Forest} {c o : ColAddr} {k p : Nat} (hc : c ∈ B.colAddrs)
    (ho : c.OnStack o) :
    (∀ e, o.container c = some e →
        parents (litCap B c k p) o = (parents B o).take (e.idx + 1) ∧
        (actualKeys (litCap B c k p) o).take e.idx = (actualKeys B o).take e.idx) ∧
      (o.container c = none → (litCap B c k p).colAt o = B.colAt o) := by sorry

-- G9.4m: a context `C_A(Z)` keeps every stack column of the stopping column: same parents, and
-- the same entries except the height of the active entry of a container
theorem colAt_context_onStack {A : Forest} {sd : StopData} (hsd : stopData A = some sd)
    (Z : Forest) {o : ColAddr} (ho : sd.col.OnStack o) :
    parents (context A sd Z) o = parents A o ∧
      (∀ e, o.container sd.col = some e →
        ((context A sd Z).colAt o).map (·.take e.idx) = (A.colAt o).map (·.take e.idx)) ∧
      (o.container sd.col = none → (context A sd Z).colAt o = A.colAt o) := by sorry

-- G9.4m' (added by the G-009 verification, used by G9.6 for template columns off the stopping
-- column's stack): a context `C_A(Z)` keeps every column of `A` that is not the stopping column,
-- not inside one of its heights and not a container of it
theorem colAt_context_of_not_route {A : Forest} {sd : StopData} (hsd : stopData A = some sd)
    (Z : Forest) {o : ColAddr} (ho : o ∈ A.colAddrs) (hne : o ≠ sd.col)
    (hin : sd.col.container o = none) (hnc : o.container sd.col = none) :
    (context A sd Z).colAt o = A.colAt o := by sorry

-- G9.4n: the column of a root-tail phase copy is the shifted column of the shorter output
-- `A' = A[n−h]` (the first column of `localSuffix_phase`, T3.2i.6)
theorem colAt_phaseCol_tail (S : OrdStep) {h : Nat} (hh : 1 ≤ h ∧ h ≤ S.n) {o : ColAddr}
    (ho : IsTmplCol S.A S.sd S.rd o) (hoq : isQMat S.sd o = false) {A' : Forest}
    (hA' : expand S.A (S.n - h) = some A') :
    S.B.colAt ((phaseCol S.sd S.rd h o).getD o) =
      (A'.colAt o).map (Tree.mapCol (shiftVal S.sd.r (h * S.d))) := by sorry

-- G9.4a: the heads `s_1, …, s_φ` are on the stack of `c`; a head containing `c` does so through
-- an entry of index `≥ m` (a restored entry)
theorem resolve_headCol (S : OrdStep) {i : Nat} {a c : ColAddr} (hi : 1 ≤ i ∧ i ≤ S.n)
    (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) {h : Nat} (hh : 1 ≤ h ∧ h ≤ phaseOff S.sd i a) :
    c.resolve 0 (S.s h) = some (S.headCol h) ∧
      ∀ e, (S.headCol h).container c = some e → S.m ≤ e.idx := by sorry

-- G9.4b: for `h < φ`, the phase-`h` copies of the stopping column's stack columns between `r` and
-- `t` are on the stack of `c` at numbers `x + h d`, and they contain `c` exactly when the old
-- columns contain the stopping column, through the same (last) entry
theorem resolve_copyCol (S : OrdStep) {i : Nat} {a c : ColAddr} (hi : 1 ≤ i ∧ i ≤ S.n)
    (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) {h : Nat} (hh : h < phaseOff S.sd i a)
    {x : Nat} {o : ColAddr} (hx : S.sd.r < x) (hxt : x < S.sd.t)
    (ho : S.sd.col.resolve 0 x = some o) :
    c.resolve 0 (x + h * S.d) = some (S.copyCol h o) ∧
      (S.copyCol h o).container c = (o.container S.sd.col).map (fun e => ⟨S.copyCol h o, e.idx⟩) ∧
      ∀ e, o.container S.sd.col = some e → e.idx + 1 = (parents S.A o).length := by sorry

-- G9.4c: contents in `K` of a copy: parents shifted by `τ_h`, keys `κ_h`-related before the
-- active index `u` (all keys when the copy does not contain `c`)
theorem copyCol_litCap (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat} (hi : 1 ≤ i ∧ i ≤ S.n)
    (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ) {h : Nat}
    (hh : h < phaseOff S.sd i a) {x : Nat} {o : ColAddr} (hx : S.sd.r < x) (hxt : x < S.sd.t)
    (ho : S.sd.col.resolve 0 x = some o) :
    parents (litCap S.B c k ρ) (S.copyCol h o) = (parents S.A o).map (shiftVal S.sd.r (h * S.d)) ∧
      (actualKeys (litCap S.B c k ρ) (S.copyCol h o)).take
          (((o.container S.sd.col).map (·.idx)).getD (parents S.A o).length) =
        kappaQry S.sd.r S.d h ((actualKeys S.A o).take
          (((o.container S.sd.col).map (·.idx)).getD (parents S.A o).length)) := by sorry

-- G9.4d: contents in `K` of the head `s_h` (`1 ≤ h ≤ φ`): the query part `τ_{h−1}(Q)` with keys
-- `κ_{h−1}(y)`, then restored entries with parents `< r`
theorem headCol_litCap (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat} (hi : 1 ≤ i ∧ i ≤ S.n)
    (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ) {h : Nat}
    (hh : 1 ≤ h ∧ h ≤ phaseOff S.sd i a) :
    (parents (litCap S.B c k ρ) (S.headCol h)).take S.m =
        ((parents S.A S.sd.col).take S.m).map (shiftVal S.sd.r ((h - 1) * S.d)) ∧
      (∀ v p, S.m ≤ v → (parents (litCap S.B c k ρ) (S.headCol h))[v]? = some p → p < S.sd.r) ∧
      (actualKeys (litCap S.B c k ρ) (S.headCol h)).take S.m =
        kappaQry S.sd.r S.d (h - 1) ((actualKeys S.A S.sd.col).take S.m) ∧
      S.m ≤ (actualKeys (litCap S.B c k ρ) (S.headCol h)).length := by sorry

-- G9.4e: every column on the stack of `c` above `s_φ` has parents `< r` or `≥ s_φ` in `K`
-- (generalizes T3.8ln from `c` to its stack)
theorem stack_parent_dichotomy (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat}
    (hi : 1 ≤ i ∧ i ≤ S.n) (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ) {x : Nat} {o : ColAddr}
    (hx : S.s (phaseOff S.sd i a) < x) (ho : c.resolve 0 x = some o) :
    ∀ p ∈ parents (litCap S.B c k ρ) o, p < S.sd.r ∨ S.s (phaseOff S.sd i a) ≤ p := by sorry

/-! ## G9.5 — the invariant: low heads detour along copies of the old terminal-to-root path -/

-- G9.5a (txt:391-393, 553-560): at a head `s_h`, `1 ≤ h ≤ φ`, whose query `V = κ_{h−1}(W')` is low
-- (`W' < Z`): (i) the response of `s_h` is `τ_{h−1}(q_j)`, `j = cursor y W'`; (ii) every edge
-- `x → y` of the old `g_{W'}` orbit at a column `x ∈ (r, t)` of the stopping column's stack is
-- copied to the edge `x + (h−1)d → τ_{h−1}(y)` of `K`, provided `K`'s cut path reaches
-- `x + (h−1)d` (the cut barrier of `K` then protects a copy that contains `c`)
theorem detour_copy (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat} (hi : 1 ≤ i ∧ i ≤ S.n)
    (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ)
    (hKL : InL (litCap S.B c k ρ)) {h : Nat} (hh : 1 ≤ h ∧ h ≤ phaseOff S.sd i a)
    {W' : List (WithTop Key)} (hW' : Noninc W') (hV : S.capQ c k ρ = kappaQry S.sd.r S.d (h - 1) W')
    (hlow : W' < S.termZ) :
    (∃ q, (parents S.A S.sd.col)[cursor (actualKeys S.A S.sd.col) W']? = some q ∧
      Edge (litCap S.B c k ρ) (actualKeys (litCap S.B c k ρ)) c (S.capQ c k ρ) (S.s h)
        (q + (h - 1) * S.d)) ∧
    ∀ x y, S.sd.r < x → x < S.sd.t → Edge S.A (actualKeys S.A) S.sd.col W' x y →
      Path (litCap S.B c k ρ) (actualKeys (litCap S.B c k ρ)) c (S.capQ c k ρ)
        (cutStart (litCap S.B c k ρ) c k) (x + (h - 1) * S.d) →
      Edge (litCap S.B c k ρ) (actualKeys (litCap S.B c k ρ)) c (S.capQ c k ρ) (x + (h - 1) * S.d)
        (shiftVal S.sd.r ((h - 1) * S.d) y) := by sorry

-- G9.5 (the invariant, `low_head_detour`): if `K`'s cut path reaches a low head `s_h`,
-- `1 ≤ h ≤ φ`, it continues to `s_{h−1}` (`s_0 = r`) along the `τ_{h−1}`-copy of the old
-- terminal-to-root path at `W'`
theorem low_head_detour (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat} (hi : 1 ≤ i ∧ i ≤ S.n)
    (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ)
    (hKL : InL (litCap S.B c k ρ)) {h : Nat} (hh : 1 ≤ h ∧ h ≤ phaseOff S.sd i a)
    {W' : List (WithTop Key)} (hW' : Noninc W') (hV : S.capQ c k ρ = kappaQry S.sd.r S.d (h - 1) W')
    (hlow : W' < S.termZ)
    (hreach : Path (litCap S.B c k ρ) (actualKeys (litCap S.B c k ρ)) c (S.capQ c k ρ)
      (cutStart (litCap S.B c k ρ) c k) (S.s h)) :
    Path (litCap S.B c k ρ) (actualKeys (litCap S.B c k ρ)) c (S.capQ c k ρ) (S.s h)
      (S.s (h - 1)) := by sorry

/-! ## G9.6, G9.7 — the cut query is `κ_φ W`; lowness is the same at every head -/

-- G9.6: off the full cut, the first `k` entries of `c` are pure `τ_φ`-copies of those of `a`, so
-- `V = κ_φ(W)` with `W = B_a(k−1)` the old cut query (T3.2h.1)
theorem capQ_eq_kappaQ (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat} (hi : 1 ≤ i ∧ i ≤ S.n)
    (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ)
    (hend : capPos S.B c k < mu S.B) :
    S.capQ c k ρ = kappaQry S.sd.r S.d (phaseOff S.sd i a) (cutQuery (actualKeys S.A a) k) := by sorry

-- G9.7 (T3.8lm, list form): a query `κ_φ W` that is low at `s_φ` is low at every head
-- `s_1, …, s_φ`
theorem low_all_heads (S : OrdStep) {φ : Nat} (hφ : 1 ≤ φ) (W : List Key)
    (hlow : kappaQry S.sd.r S.d φ (W.map (↑)) < kappaQry S.sd.r S.d (φ - 1) S.termZ) {h : Nat}
    (hh : 1 ≤ h ∧ h ≤ φ) :
    kappaQry S.sd.r S.d φ (W.map (↑)) < kappaQry S.sd.r S.d (h - 1) S.termZ := by sorry

/-! ## G9.8 — the derivation of T3.8lo -/

-- G9.8a: the cut path of `K` starts at or above `s_φ` and passes through `s_φ` on its way to a
-- previous-phase root
theorem phase_exit (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat} (hi : 1 ≤ i ∧ i ≤ S.n)
    (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ)
    (hKL : InL (litCap S.B c k ρ)) (hρ1 : S.sd.r < ρ) (hρ2 : ρ < S.s (phaseOff S.sd i a)) :
    S.s (phaseOff S.sd i a) ≤ cutStart (litCap S.B c k ρ) c k ∧
      Path (litCap S.B c k ρ) (actualKeys (litCap S.B c k ρ)) c (S.capQ c k ρ)
        (cutStart (litCap S.B c k ρ) c k) (S.s (phaseOff S.sd i a)) ∧
      Path (litCap S.B c k ρ) (actualKeys (litCap S.B c k ρ)) c (S.capQ c k ρ)
        (S.s (phaseOff S.sd i a)) ρ := by sorry

-- G9.8b: a head `s_h` whose response is a parent `≥ r` is low
theorem low_of_head_edge (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat}
    (hi : 1 ≤ i ∧ i ≤ S.n) (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ) {h : Nat}
    (hh : 1 ≤ h ∧ h ≤ phaseOff S.sd i a) {w : Nat}
    (he : Edge (litCap S.B c k ρ) (actualKeys (litCap S.B c k ρ)) c (S.capQ c k ρ) (S.s h) w)
    (hw : S.sd.r ≤ w) : S.capQ c k ρ < kappaQry S.sd.r S.d (h - 1) S.termZ := by sorry

-- G9.8c: the first unconsumed root entry of a literal cap is the response of its root column at
-- the cap's cut query
theorem unconsumed_litCap {B : Forest} {c : ColAddr} {k ρ : Nat} (hup : IsUpward B c k ρ)
    {rd : RootData} (hrd : rootData (litCap B c k ρ) = some rd) :
    c.resolve 0 ρ = some rd.col ∧
      (unconsumed (litCap B c k ρ) rd).head?.map Prod.fst =
        resp (litCap B c k ρ) (actualKeys (litCap B c k ρ)) rd.col
          (cutQuery (actualKeys (litCap B c k ρ) c) k) := by sorry

-- G9.8 (T3.8lo, corrected: `hend` added): at a previous-phase root the actual response is a
-- parent `≥ r`. Replaces the statement of `prev_root_response` at merge.
theorem prev_root_response_pure (S : OrdStep) {i : Nat} {a c : ColAddr} {k ρ : Nat}
    (hi : 1 ≤ i ∧ i ≤ S.n) (ha : IsTmplCol S.A S.sd S.rd a) (hq : isQMat S.sd a = true → 2 ≤ i)
    (hc : phaseCol S.sd S.rd i a = some c) (hup : IsUpward S.B c k ρ)
    (hKL : InL (litCap S.B c k ρ)) (hend : capPos S.B c k < mu S.B) (hρ1 : S.sd.r < ρ)
    (hρ2 : ρ < S.s (phaseOff S.sd i a))
    {rdN : RootData} (hN : rootData (litCap S.B c k ρ) = some rdN) :
    ∃ u us, unconsumed (litCap S.B c k ρ) rdN = u :: us ∧ S.sd.r ≤ u.1 := by sorry

end Closure

end BTBMS
