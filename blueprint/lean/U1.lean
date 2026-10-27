import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot

/-!
# Blueprint unit U1 — syntax, occurrences, scans (paper §1–§2)

Companion of `blueprint/U1-syntax-scans.md`. Every declaration's docstring begins with its node
ID. This file is appended after `blueprint/lean/Spine.lean`; it never redeclares a spine name.

**Bodies owed to the spine.** The spine declares `Tree.truncAfter`, `Tree.setHeight`,
`Scan.safePrefix`, `Scan.stepKind`, `Scan.stopData`, `Scan.rootData` and `Scan.paperOp` with
`sorry` bodies owed by U1. At integration (SCR-2, `00-spine.md` §i.2) the real bodies `…Body` and
their helpers moved verbatim into `Spine.lean`, the spine names are defined by them, and the
theorems `…_eq_body` below hold by `rfl` (proofs left `sorry`, as for every blueprint proof). Every
lemma about these operations is stated with the spine name, so no consumer statement changes.

All proofs are `sorry` (blueprint). No axioms.
-/

namespace BTBMS

/-! ## D1.1a, D1.4a — lawful comparators, the order on forests and keys -/

namespace Tree

variable {α β : Type}

/-- D1.1a: `Tree.cmp c` is oriented when `c` is (proved by mutual structural induction through
`cmp`/`cmpCols`/`cmpCol`). -/
theorem cmp_eq_swap (c : α → α → Ordering) [Std.OrientedCmp c] (s t : Tree α) :
    cmp c s t = (cmp c t s).swap := by sorry

/-- D1.1a: `Tree.cmp c` is reflexive when `c` is. -/
theorem cmp_self (c : α → α → Ordering) [Std.ReflCmp c] (s : Tree α) : cmp c s s = .eq := by
  sorry

/-- D1.1a: `Tree.cmp c` decides equality when `c` does. -/
theorem eq_of_cmp_eq (c : α → α → Ordering) [Std.LawfulEqCmp c] {s t : Tree α}
    (h : cmp c s t = .eq) : s = t := by sorry

-- U1-verify: changed
/-- D1.1a: `Tree.cmp c` is transitive when `c` is. Proved together with the two strict variants
(`lt` then `isLE` gives `lt`; `isLE` then `lt` gives `lt`) in one mutual structural induction on
`s`; transitivity of `isLE` alone is not inductive (U1 doc, D1.1a item 4). -/
theorem cmp_isLE_trans (c : α → α → Ordering) [Std.TransCmp c] {s t w : Tree α}
    (h₁ : (cmp c s t).isLE = true) (h₂ : (cmp c t w).isLE = true) : (cmp c s w).isLE = true := by
  sorry

instance instOrientedCmp (c : α → α → Ordering) [Std.OrientedCmp c] :
    Std.OrientedCmp (cmp c) := ⟨fun {a b} => cmp_eq_swap c a b⟩

instance instTransCmp (c : α → α → Ordering) [Std.TransCmp c] : Std.TransCmp (cmp c) :=
  { isLE_trans := fun h₁ h₂ => cmp_isLE_trans c h₁ h₂ }

instance instReflCmp (c : α → α → Ordering) [Std.ReflCmp c] : Std.ReflCmp (cmp c) :=
  ⟨fun {a} => cmp_self c a⟩

instance instLawfulEqCmp (c : α → α → Ordering) [Std.LawfulEqCmp c] :
    Std.LawfulEqCmp (cmp c) := { eq_of_compare := fun h => eq_of_cmp_eq c h }

/-- D1.4a: relabelling by a comparison-preserving map preserves the comparison. This is the tree
form of trace fact (1) and gives `relKey_lt_iff`. -/
theorem cmp_map {c : α → α → Ordering} {c' : β → β → Ordering} {f : α → β}
    (hf : ∀ x y, c' (f x) (f y) = c x y) (s t : Tree α) :
    cmp c' (map f s) (map f t) = cmp c s t := by sorry

/-- D1.4a: relabelling by an injective map is injective. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (map f : Tree α → Tree β) := by sorry

end Tree

/-- D1.4a: `keyLabelCmp` is the lexicographic comparison of `Bool ×ₗ Nat` (false before true). -/
theorem keyLabelCmp_eq (x y : Bool × Nat) : keyLabelCmp x y = compare (toLex x) (toLex y) := rfl

/-- D1.4a: `keyCmp` is `Tree.cmp compare` on `Tree (Bool ×ₗ Nat)` (definitional). -/
theorem keyCmp_eq_cmp_lex (x y : Key) : keyCmp x y = @Tree.cmp (Lex (Bool × Nat)) compare x y := rfl

/-- D1.1: the spine's `≤` on forests (definitional). -/
theorem Forest.le_iff_cmp (a b : Forest) : a ≤ b ↔ Tree.cmp compare a b ≠ .gt := Iff.rfl

-- U1-verify: changed (new declaration)
/-- D1.1: the `compare` of the spine's linear order (its default `compareOfLessAndEq`) is the
locked comparison `Tree.cmp compare`. -/
theorem Forest.compare_eq_cmp (a b : Forest) : compare a b = Tree.cmp compare a b := by sorry

/-- D1.4: the spine's `<` on keys (definitional). -/
theorem Key.lt_iff_keyCmp (x y : Key) : x < y ↔ keyCmp x y = .lt := Iff.rfl

instance keyLabelCmp_transCmp : Std.TransCmp keyLabelCmp := by sorry
instance keyLabelCmp_lawfulEqCmp : Std.LawfulEqCmp keyLabelCmp := by sorry

/-- D1.4: the label map of `h_a` (txt:82-83). -/
def relLabel (a p : Nat) : Bool × Nat := if p < a then (false, p) else (true, p - a)

/-- D1.4: `relKey a` is relabelling by `relLabel a` (definitional). -/
theorem relKey_eq_map (a : Nat) (H : Forest) : relKey a H = H.map (relLabel a) := rfl

/-- D1.4: `relLabel a` is strictly increasing: it turns `compare` into `keyLabelCmp`
(txt:84-85). -/
theorem keyLabelCmp_relLabel (a p q : Nat) :
    keyLabelCmp (relLabel a p) (relLabel a q) = compare p q := by sorry

/-- D1.4: `h_a` preserves and reflects the comparison. -/
theorem keyCmp_relKey (a : Nat) (H H' : Forest) :
    keyCmp (relKey a H) (relKey a H') = Tree.cmp compare H H' := by sorry

/-- D1.4: `h_a` is injective. -/
theorem relKey_injective (a : Nat) : Function.Injective (relKey a) := by sorry

-- U1-verify: changed (new declaration)
/-- D1.4: the `compare` of the spine's linear order on keys (its default `compareOfLessAndEq`)
is the locked `keyCmp`. Needed to feed `sign_of_agreement` (stated with `keyCmp`) into
`trace_agree` (stated with `compare`). -/
theorem Key.compare_eq_keyCmp (x y : Key) : compare x y = keyCmp x y := by sorry

/-! ## D1.2b — occurrences: stacks, containment, accessors, roles -/

namespace ColAddr

/-- D1.2b: `o` lies on the visible stack of `c` (txt:66-69): at a containing level `k` it is one
of the columns `0…c_k` of that forest, or at `c`'s own level one of the columns `0…c.col-1`. -/
def OnStack (c o : ColAddr) : Prop :=
  (∃ k ck ik, c.path[k]? = some (ck, ik) ∧ o.path = c.path.take k ∧ o.col ≤ ck) ∨
    (o.path = c.path ∧ o.col < c.col)

/-- D1.2b: `resolve` returns exactly the stack occurrence with the given printed number. -/
theorem resolve_spec (base : Nat) (c o : ColAddr) (q : Nat) :
    c.resolve base q = some o ↔ c.OnStack o ∧ o.num base = q := by sorry

/-- D1.2b: stack occurrences have smaller printed numbers. -/
theorem num_lt_of_onStack (base : Nat) {c o : ColAddr} (h : c.OnStack o) :
    o.num base < c.num base := by sorry

/-- D1.2b: numbers on a stack are unique (txt:69). -/
theorem onStack_inj (base : Nat) {c o o' : ColAddr} (h : c.OnStack o) (h' : c.OnStack o')
    (hn : o.num base = o'.num base) : o = o' := by sorry

theorem resolve_num {base : Nat} {c o : ColAddr} {q : Nat} (h : c.resolve base q = some o) :
    o.num base = q := by sorry

/-- D1.2b: only numbers below `c`'s own number resolve (V makes edges decrease). -/
theorem resolve_lt {base : Nat} {c o : ColAddr} {q : Nat} (h : c.resolve base q = some o) :
    q < c.num base := by sorry

/-- D1.2b: the visible stack of `c` carries exactly the numbers `base, …, c.num base - 1`. -/
theorem resolve_isSome_iff (base : Nat) (c : ColAddr) (q : Nat) :
    (c.resolve base q).isSome ↔ base ≤ q ∧ q < c.num base := by sorry

/-- D1.2b (stack nesting, codex-crosscheck-1 Q2 "restricting σ"): below a stack occurrence `o`
of `c`, the stacks of `o` and `c` resolve every number identically. -/
theorem resolve_of_resolve_lt {base : Nat} {c o : ColAddr} {x q : Nat}
    (h : c.resolve base x = some o) (hq : q < x) : o.resolve base q = c.resolve base q := by sorry

/-- D1.2b: the container of `c` in column `q`. -/
theorem container_spec (q c : ColAddr) (e : EntryAddr) :
    q.container c = some e ↔ e.col = q ∧ e.heightPath <+: c.path := by sorry

end ColAddr

/-- D1.2b: column occurrence `c` lies inside the height of entry `e`. -/
def EntryAddr.Contains (e : EntryAddr) (c : ColAddr) : Prop := e.heightPath <+: c.path

namespace EntryAddr

/-- D1.2b: a containing column is visible from inside, under its own number. -/
theorem resolve_host {e : EntryAddr} {c : ColAddr} (h : e.Contains c) :
    c.resolve 0 (e.col.num 0) = some e.col := by sorry

/-- D1.2b (txt:216-217, "every visible z > a on this path is still inside H_e"): a stack
occurrence with a number above the host of a containing entry lies inside that entry's height. -/
theorem contains_of_resolve {e : EntryAddr} {c o : ColAddr} {z : Nat} (h : e.Contains c)
    (hz : c.resolve 0 z = some o) (hlt : e.col.num 0 < z) : e.Contains o := by sorry

/-- D1.2b: `e` contains `c` iff `e.col.container c = some e`. -/
theorem contains_iff_container (e : EntryAddr) (c : ColAddr) :
    e.Contains c ↔ e.col.container c = some e := by sorry

end EntryAddr

namespace Tree

variable {α : Type}

/-- D1.2b: column addresses are exactly the addresses at which `colAt` succeeds. -/
theorem mem_colAddrs_iff (t : Tree α) (c : ColAddr) : c ∈ t.colAddrs ↔ (t.colAt c).isSome := by
  sorry

/-- D1.2b: entry addresses are exactly the addresses at which `entryAt` succeeds. -/
theorem mem_entryAddrs_iff (t : Tree α) (e : EntryAddr) :
    e ∈ t.entryAddrs ↔ (t.entryAt e).isSome := by sorry

/-- D1.2b: the roles of a tree are its column and entry occurrences. -/
theorem mem_roles_iff (t : Tree α) (x : Role) :
    x ∈ t.roles ↔ match x with
      | .ord c => (t.colAt c).isSome
      | .slot e => (t.entryAt e).isSome := by sorry

/-- D1.2b (`roles_nodup`†): every role occurs once in reading order. -/
theorem roles_nodup (t : Tree α) : t.roles.Nodup := by sorry

/-- D1.2b: forests at concatenated paths. -/
theorem forestAt_append (t : Tree α) (π π' : List (Nat × Nat)) :
    t.forestAt (π ++ π') = (t.forestAt π).bind fun f => f.forestAt π' := by sorry

/-- D1.2b: the height of an entry is the forest at its height path. -/
theorem forestAt_heightPath (t : Tree α) (e : EntryAddr) :
    t.forestAt e.heightPath = t.heightAt e := by sorry

/-- D1.2b: an entry of `t` has its column in `t`. -/
theorem colAt_of_entryAt {t : Tree α} {e : EntryAddr} {x : α × Tree α} (h : t.entryAt e = some x) :
    ∃ col, t.colAt e.col = some col ∧ col[e.idx]? = some x := by sorry

-- bridge: holds by `rfl` (SCR-2 applied; checked in scratch/blueprint/all/rfl_check.lean)
theorem truncAfter_eq_body (t : Tree α) (e : EntryAddr) : t.truncAfter e = t.truncAfterBody e := by
  sorry
-- bridge: holds by `rfl` (SCR-2 applied)
theorem setHeight_eq_body (t : Tree α) (e : EntryAddr) (h : Tree α) :
    t.setHeight e h = t.setHeightBody e h := by sorry

/-- D1.2c (`truncAfter_roles`†): the roles of `truncAfter t e` are the roles of `t` strictly before
`U_e`, followed by the maximal run of roles inside `e` starting with `U_e`. -/
theorem truncAfter_roles {t : Tree α} {e : EntryAddr} (he : e ∈ t.entryAddrs) :
    (t.truncAfter e).roles =
      t.roles.takeWhile (· != .slot e) ++
        (t.roles.dropWhile (· != .slot e)).takeWhile (fun x => x.inEntry e) := by sorry

/-- D1.2c: `truncAfter` keeps `e` and its height. -/
theorem entryAt_truncAfter {t : Tree α} {e : EntryAddr} (he : e ∈ t.entryAddrs) :
    (t.truncAfter e).entryAt e = t.entryAt e := by sorry

/-- D1.2c: `setHeight` changes only the height of `e`. -/
theorem entryAt_setHeight {t : Tree α} {e : EntryAddr} {p : α} {H : Tree α}
    (he : t.entryAt e = some (p, H)) (h : Tree α) : (t.setHeight e h).entryAt e = some (p, h) := by
  sorry

/-- D1.2d: the last step of the last-column, last-entry route in `F`: `(|F| - 1, |col| - 1)` for
the last column `col`, if it is nonempty. -/
def lastStep? (F : Tree α) : Option (Nat × Nat) :=
  F.cols.getLast?.bind fun col => if col.isEmpty then none else some (F.cols.length - 1, col.length - 1)

end Tree

/-! ## D1.2d — the terminal last-column, last-entry route -/

/-- D1.2d: the route path: at every level `d` the step taken is the last-column, last-entry step
of the forest there. -/
def Scan.IsRoutePath (E : Forest) (π : List (Nat × Nat)) : Prop :=
  ∀ d < π.length, ∃ F, E.forestAt (π.take d) = some F ∧ F.lastStep? = π[d]?

/-- D1.2d: membership in the spine's `routeCols` (whose fuel `E.size + 1` suffices). -/
theorem Scan.mem_routeCols_iff (E : Forest) (c : ColAddr) :
    c ∈ Scan.routeCols E ↔ Scan.IsRoutePath E c.path ∧
      ∃ F, E.forestAt c.path = some F ∧ F.cols.length = c.col + 1 := by sorry

/-- D1.2d: route columns are columns of `E`. -/
theorem Scan.mem_colAddrs_of_mem_routeCols {E : Forest} {c : ColAddr} (h : c ∈ Scan.routeCols E) :
    c ∈ E.colAddrs := by sorry

/-! ## D2.1, D2.1a, L2.1, L2.1a–c, L2.3b, L2.5 — the generic word library (S-6, U1 half) -/

namespace Scan

section Words

variable {α : Type} [LinearOrder α]

/-- D2.1a: a nonincreasing word (the reduced words of txt:159). -/
abbrev Noninc (l : List α) : Prop := l.Pairwise fun x y => y ≤ x

/-- D2.1a: one reduction step: delete terminal letters strictly smaller than `x`, append `x`. -/
def nuStep (acc : List α) (x : α) : List α :=
  (acc.reverse.dropWhile fun y => decide (y < x)).reverse ++ [x]

theorem nu_eq_foldl (l : List α) : nu l = l.foldl nuStep [] := rfl

/-- D2.1a. -/
theorem nu_append_singleton (l : List α) (x : α) : nu (l ++ [x]) = nuStep (nu l) x := by sorry

/-- D2.1a: `ν(W)` is nonincreasing (txt:159). -/
theorem nu_noninc (l : List α) : Noninc (nu l) := by sorry

/-- D2.1a: a nonincreasing word is reduced. -/
theorem nu_of_noninc {l : List α} (h : Noninc l) : nu l = l := by sorry

/-- D2.1a. -/
theorem nu_append_nu (l m : List α) : nu (nu l ++ m) = nu (l ++ m) := by sorry

/-- D2.1a: on a nonincreasing word, a step keeps the letters `≥ x` and appends `x`. -/
theorem nuStep_eq_takeWhile {acc : List α} (h : Noninc acc) (x : α) :
    nuStep acc x = acc.takeWhile (fun y => decide (x ≤ y)) ++ [x] := by sorry

/-- D2.1a (txt:163-164): an append strictly increases a reduced word. -/
theorem lt_nuStep {acc : List α} (h : Noninc acc) (x : α) : acc < nuStep acc x := by sorry

/-- D2.1a: every letter of `nuStep acc x` is at least `x`. -/
theorem le_of_mem_nuStep {acc : List α} (h : Noninc acc) {x y : α} (hy : y ∈ nuStep acc x) :
    x ≤ y := by sorry

theorem cutQuery_zero (ks : List α) : cutQuery ks 0 = [] := rfl

theorem boundary_eq_cutQuery (ks : List α) (i : Nat) : boundary ks i = cutQuery ks (i + 1) := rfl

/-- D2.1a. -/
theorem cutQuery_succ {ks : List α} {k : Nat} (hk : k < ks.length) :
    cutQuery ks (k + 1) = nuStep (cutQuery ks k) ks[k] := by sorry

theorem cutQuery_noninc (ks : List α) (k : Nat) : Noninc (cutQuery ks k) := nu_noninc _

/-- D2.1 (with `cutQuery_lt_succ`): boundaries strictly increase up to the full cut. -/
theorem cutQuery_strictMono {ks : List α} {j k : Nat} (hjk : j < k) (hk : k ≤ ks.length) :
    cutQuery ks j < cutQuery ks k := by sorry

/-- D2.1: boundaries are monotone (constant beyond the full cut). -/
theorem cutQuery_mono (ks : List α) {j k : Nat} (hjk : j ≤ k) : cutQuery ks j ≤ cutQuery ks k := by
  sorry

theorem boundary_ne_nil {ks : List α} {i : Nat} (hi : i < ks.length) : boundary ks i ≠ [] := by
  sorry

-- U1-verify: changed (new declarations)
/-- D2.1a: `ν` commutes with a strictly increasing map (used for the maps `κ_j` of txt:331-333
and for the coercion `Key → WithTop Key`). -/
theorem nu_map {β : Type} [LinearOrder β] {f : α → β} (hf : StrictMono f) (l : List α) :
    nu (l.map f) = (nu l).map f := by sorry

/-- D2.1a: cut queries commute with a strictly increasing map. -/
theorem cutQuery_map {β : Type} [LinearOrder β] {f : α → β} (hf : StrictMono f) (ks : List α)
    (k : Nat) : cutQuery (ks.map f) k = (cutQuery ks k).map f := by sorry

/-- D2.1a: boundaries commute with a strictly increasing map. -/
theorem boundary_map {β : Type} [LinearOrder β] {f : α → β} (hf : StrictMono f) (ks : List α)
    (i : Nat) : boundary (ks.map f) i = (boundary ks i).map f := by sorry

/-- L2.3b (word observation, txt:211-213): if `D = ν(P ⌢ [K])`, `W` is nonincreasing, `W < D`
and `J < K`, then `ν(W ⌢ [J]) < D`. -/
theorem nu_append_lt {P W : List α} {K J : α} (hW : Noninc W) (hWD : W < nu (P ++ [K]))
    (hJK : J < K) : nu (W ++ [J]) < nu (P ++ [K]) := by sorry

/-- L2.3b, boundary form: `W(c,k) < B_a(u)` and `K_k < K_u` give `B_c(k) < B_a(u)`. -/
theorem boundary_lt_of_cut {ksc ksa : List α} {k u : Nat} (hk : k < ksc.length)
    (hu : u < ksa.length) (hW : cutQuery ksc k < boundary ksa u) (hK : ksc[k] < ksa[u]) :
    boundary ksc k < boundary ksa u := by sorry

/-- L2.1a: the source cursor never exceeds the source length. -/
theorem cursor_le_length (src qry : List α) : cursor src qry ≤ src.length := by sorry

/-- L2.1a: the run on a source prefix is the run on the whole source, stopped at its end. -/
theorem cursor_take (src qry : List α) (k : Nat) :
    cursor (src.take k) qry = min k (cursor src qry) := by sorry

/-- L2.1a: the final query cursor of the raw scan (same recursion as `cursor`). -/
def qcursor : List α → List α → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys =>
    if x < y then qcursor xs (y :: ys)
    else if x = y then qcursor xs ys + 1
    else qcursor (x :: xs) ys + 1
termination_by xs ys => xs.length + ys.length

theorem qcursor_le_length (src qry : List α) : qcursor src qry ≤ qry.length := by sorry

/-- L2.1a: a run that exhausts `src` continues on `src'` from the query position it reached. -/
theorem cursor_append_of_exhausted {src qry : List α} (src' : List α)
    (h : cursor src qry = src.length) :
    cursor (src ++ src') qry = src.length + cursor src' (qry.drop (qcursor src qry)) ∧
      qcursor (src ++ src') qry = qcursor src qry + qcursor src' (qry.drop (qcursor src qry)) := by
  sorry

/-- L2.1a: a run that stops inside `src` (its query is exhausted) ignores what follows. -/
theorem cursor_append_of_lt {src qry : List α} (src' : List α) (h : cursor src qry < src.length) :
    cursor (src ++ src') qry = cursor src qry := by sorry

/-- L2.1a: a one-letter source against a nonincreasing query `y :: V`. -/
theorem cursor_singleton_cons (x y : α) (V : List α) (hV : Noninc (y :: V)) :
    (x < y → cursor [x] (y :: V) = 1 ∧ qcursor [x] (y :: V) = 0) ∧
      (x = y → cursor [x] (y :: V) = 1 ∧ qcursor [x] (y :: V) = 1) ∧
      (y < x → cursor [x] (y :: V) = 0) := by sorry

theorem cursor_nil_right (src : List α) : cursor src [] = 0 := by sorry

/-- L2.1b (txt:170-173): against a nonincreasing query, exhaustion is lexicographic comparison
of the reduced source. -/
theorem cursor_eq_length_iff (src : List α) {W : List α} (hW : Noninc W) :
    cursor src W = src.length ↔ nu src ≤ W := by sorry

/-- L2.1 ("the unique i", txt:165-167). -/
theorem cursor_unique {ks W : List α} (hW : Noninc W) {i : Nat} (hi : i ≤ ks.length)
    (hlo : cutQuery ks i ≤ W) (hhi : i < ks.length → W < cutQuery ks (i + 1)) :
    cursor ks W = i := by sorry

/-- L2.1: a query strictly below `B(v)` stops the scan at or before `v`. -/
theorem cursor_le_of_lt_cutQuery {ks W : List α} (hW : Noninc W) {v : Nat} (hv : v < ks.length)
    (h : W < cutQuery ks (v + 1)) : cursor ks W ≤ v := by sorry

/-- L2.1: a query at least `B(v-1)` reaches `v`. -/
theorem le_cursor_of_cutQuery_le {ks W : List α} (hW : Noninc W) {v : Nat} (hv : v ≤ ks.length)
    (h : cutQuery ks v ≤ W) : v ≤ cursor ks W := by sorry

/-- L2.1: the final source cursor is monotone in reduced queries (used by L2.2). -/
theorem cursor_mono (ks : List α) {W Z : List α} (hW : Noninc W) (hZ : Noninc Z) (h : W ≤ Z) :
    cursor ks W ≤ cursor ks Z := by sorry

/-- L2.1c (txt:174-176): deleting a query letter immediately followed by a larger one does not
change the final source cursor. -/
theorem cursor_delete (src A B : List α) {x y : α} (hxy : x < y) :
    cursor src (A ++ x :: y :: B) = cursor src (A ++ y :: B) := by sorry

/-- L2.5a: the final state of the trace is `(cursor, qcursor)`. -/
theorem trace_last (src qry : List α) :
    (trace src qry).getLast? = some (cursor src qry, qcursor src qry) := by sorry

/-- L2.5a: equal traces have equal final source cursors. -/
theorem cursor_eq_of_trace_eq {src₁ src₂ qry₁ qry₂ : List α}
    (h : trace src₁ qry₁ = trace src₂ qry₂) : cursor src₁ qry₁ = cursor src₂ qry₂ := by sorry

-- U1-verify: changed (new declaration)
/-- L2.5a: no state of a run has a source cursor beyond the final one (used in the proof of
`trace_agree`). -/
theorem trace_fst_le_cursor (src qry : List α) {i j : Nat} (h : (i, j) ∈ trace src qry) :
    i ≤ cursor src qry := by sorry

/-- L2.5 (1) (`trace_map`†, txt:238): a common strictly increasing map preserves every cursor
pair. -/
theorem trace_map {β : Type} [LinearOrder β] {f : α → β} (hf : StrictMono f) (src qry : List α) :
    trace (src.map f) (qry.map f) = trace src qry := by sorry

/-- L2.5 (1), cursor form. -/
theorem cursor_map {β : Type} [LinearOrder β] {f : α → β} (hf : StrictMono f) (src qry : List α) :
    cursor (src.map f) (qry.map f) = cursor src qry := by sorry

/-- L2.5 (2) (`trace_cap_top`†, txt:239, 242-244): if a nonempty source is not exhausted,
replacing its last key by `⊤` preserves every cursor pair. -/
theorem trace_cap_top {β : Type} [LinearOrder β] [OrderTop β] {src qry : List β} (hne : src ≠ [])
    (hnx : cursor src qry < src.length) : trace (src.dropLast ++ [⊤]) qry = trace src qry := by
  sorry

/-- L2.5 (3) (`trace_agree`†, txt:240-241, 244-245): sources agreeing before `u`, with keys at `u`
of identical signs against every query key, have the same trace for a run ending at or before
`u`. -/
theorem trace_agree {src₁ src₂ qry : List α} {u : Nat} (hpre : src₁.take u = src₂.take u)
    (hu₁ : u < src₁.length) (hu₂ : u < src₂.length)
    (hsign : ∀ y ∈ qry, compare src₁[u] y = compare src₂[u] y) (hrun : cursor src₁ qry ≤ u) :
    trace src₁ qry = trace src₂ qry := by sorry

end Words

/-- L2.5b (`cursor_eq_scanCount`†): the generic cursor at `Key` is the locked `scanCount`. -/
theorem cursor_eq_scanCount (xs ys : List Key) : scanCount xs ys = cursor xs ys := by sorry

/-! ## N1.2, C1.8a, C1.8, D1.9 — compact words and safe prefixes -/

/-- N1.2: atoms of the generic compact word over labels `α`: `(depth coordinate, marker, label)`,
the label `⊥` marking an empty column. -/
abbrev GAtom (α : Type) := Nat ×ₗ Nat ×ₗ WithBot α

mutual
/-- N1.2: the generic compact word at depth `e` (txt:143-146), with `⊥` in the empty-column
atom so that relabelling commutes with the word. -/
def gwordAt {α : Type} (e : Nat) : Tree α → List (GAtom α)
  | .node cols => gwordCols e cols

def gwordCols {α : Type} (e : Nat) : List (List (α × Tree α)) → List (GAtom α)
  | [] => []
  | col :: rest => gwordCol e col ++ gwordCols e rest

def gwordCol {α : Type} (e : Nat) : List (α × Tree α) → List (GAtom α)
  | [] => [toLex (2 * e, toLex (0, (⊥ : WithBot α)))]
  | (p, h) :: rest =>
    toLex (2 * e, toLex (1, (p : WithBot α))) :: (gwordAt (e + 1) h ++ gwordLater e rest)

def gwordLater {α : Type} (e : Nat) : List (α × Tree α) → List (GAtom α)
  | [] => []
  | (p, h) :: rest =>
    toLex (2 * e + 1, toLex (0, (p : WithBot α))) :: (gwordAt (e + 1) h ++ gwordLater e rest)
end

/-- N1.2. -/
def gword {α : Type} (t : Tree α) : List (GAtom α) := gwordAt 0 t

/-- N1.2: relabelling of an atom. -/
def GAtom.map {α β : Type} (f : α → β) (A : GAtom α) : GAtom β :=
  toLex ((ofLex A).1, toLex ((ofLex (ofLex A).2).1, (ofLex (ofLex A).2).2.map f))

/-- N1.2: the spine's word atoms, read as generic atoms (`⊥` exactly at even depth coordinate and
marker `0`, which only the empty-column atom has). -/
def toGAtom (A : WordAtom) : GAtom Nat :=
  toLex ((ofLex A).1, toLex ((ofLex (ofLex A).2).1,
    if (ofLex A).1 % 2 = 0 ∧ (ofLex (ofLex A).2).1 = 0 then (⊥ : WithBot Nat)
    else ((ofLex (ofLex A).2).2 : WithBot Nat)))

/-- N1.2: relabelling commutes with the generic word (positions and length are unchanged). -/
theorem gword_map {α β : Type} (f : α → β) (t : Tree α) :
    gword (t.map f) = (gword t).map (GAtom.map f) := by sorry

/-- N1.2: the spine's word is the generic word with the label decoration forgotten. -/
theorem gword_eq_map_word (E : Forest) : gword E = (word E).map toGAtom := by sorry

theorem mu_eq_length_gword (E : Forest) : mu E = (gword E).length := by sorry

/-- C1.8a: every atom of `gwordAt e t` has depth coordinate at least `2e`. -/
theorem gwordAt_fst_ge {α : Type} (e : Nat) (t : Tree α) :
    ∀ A ∈ gwordAt e t, 2 * e ≤ (ofLex A).1 := by sorry

/-- C1.8a (txt:147-151): with continuations whose first atoms have depth coordinate below `2e`,
comparison of words followed by continuations is comparison of the trees, then of the
continuations. -/
theorem gwordAt_append_lt_iff {α : Type} [LinearOrder α] (e : Nat) (s t : Tree α)
    {xs ys : List (GAtom α)} (hxs : ∀ A ∈ xs.head?, (ofLex A).1 < 2 * e)
    (hys : ∀ A ∈ ys.head?, (ofLex A).1 < 2 * e) :
    gwordAt e s ++ xs < gwordAt e t ++ ys ↔
      Tree.cmp compare s t = .lt ∨ (s = t ∧ xs < ys) := by sorry

/-- C1.8a: injectivity with continuations. -/
theorem gwordAt_append_inj {α : Type} (e : Nat) {s t : Tree α} {xs ys : List (GAtom α)}
    (hxs : ∀ A ∈ xs.head?, (ofLex A).1 < 2 * e) (hys : ∀ A ∈ ys.head?, (ofLex A).1 < 2 * e)
    (h : gwordAt e s ++ xs = gwordAt e t ++ ys) : s = t ∧ xs = ys := by sorry

/-- C1.8a: the generic word is an order embedding. -/
theorem gword_lt_iff {α : Type} [LinearOrder α] (s t : Tree α) :
    gword s < gword t ↔ Tree.cmp compare s t = .lt := by sorry

theorem gword_injective {α : Type} : Function.Injective (gword : Tree α → List (GAtom α)) := by
  sorry

/-- N1.3: a map strictly increasing on the letters that occur preserves list order. -/
theorem list_map_lt_iff {γ δ : Type} [LinearOrder γ] [LinearOrder δ] {f : γ → δ} {S : Set γ}
    (hf : StrictMonoOn f S) {l₁ l₂ : List γ} (h₁ : ∀ x ∈ l₁, x ∈ S) (h₂ : ∀ x ∈ l₂, x ∈ S) :
    l₁.map f < l₂.map f ↔ l₁ < l₂ := by sorry

/-- N1.3: a comparison with `Y` is decided within the first `|Y| + 1` letters. -/
theorem list_lt_of_take_eq {γ : Type} [LinearOrder γ] {X₁ X₂ Y : List γ}
    (hlen : Y.length < X₁.length) (h : X₁.take (Y.length + 1) = X₂.take (Y.length + 1)) :
    (X₁ < Y ↔ X₂ < Y) ∧ X₁ ≠ Y ∧ X₂ ≠ Y := by sorry

/-- N1.2: the shapes of atoms that occur in words: `(2e, 0, 0)`, `(2e, 1, p)`, `(2e+1, 0, p)`. -/
def WordAtom.WF (A : WordAtom) : Prop :=
  ((ofLex A).1 % 2 = 0 ∧ (((ofLex (ofLex A).2).1 = 0 ∧ (ofLex (ofLex A).2).2 = 0) ∨
      (ofLex (ofLex A).2).1 = 1)) ∨
    ((ofLex A).1 % 2 = 1 ∧ (ofLex (ofLex A).2).1 = 0)

/-- N1.2: every atom of a word is well formed. -/
theorem word_wf (E : Forest) : ∀ A ∈ word E, A.WF := by sorry

/-- N1.2: `toGAtom` is strictly increasing on well-formed atoms. -/
theorem toGAtom_strictMonoOn : StrictMonoOn toGAtom {A : WordAtom | A.WF} := by sorry

-- bridge: holds by `rfl` (SCR-2 applied)
theorem safePrefix_eq_body (E : Forest) (k : Nat) : safePrefix E k = safePrefixBody E k := by sorry

/-- D1.9a: the budget bookkeeping of `spF` (the invariant behind `word_safePrefix`):
`word (spF k E).1 = (word E).take k` and the unused budget is `k - µ(E)`. -/
theorem spF_spec (e k : Nat) (E : Forest) :
    wordAt e (spF k E).1 = (wordAt e E).take k ∧ (spF k E).2 = k - (wordAt e E).length := by sorry

/-- D1.9: a safe prefix of full length is the whole forest. -/
theorem safePrefix_of_le {E : Forest} {k : Nat} (hk : mu E ≤ k) : safePrefix E k = E := by sorry

/-- D1.9: a safe prefix is `≤` the forest (by `word_safePrefix` and `word_lt_iff`). -/
theorem safePrefix_le (E : Forest) (k : Nat) : safePrefix E k ≤ E := by sorry

/-- D1.9 (txt:152-153): every column of a safe prefix is a prefix of the corresponding column,
nonempty if the original column is nonempty; every kept entry keeps its parent and its height is
a safe prefix of the original height. -/
theorem colAt_safePrefix {E : Forest} {k : Nat} {c : ColAddr} {col' : Column}
    (h : (safePrefix E k).colAt c = some col') :
    ∃ col, E.colAt c = some col ∧ col'.length ≤ col.length ∧ (col' = [] → col = []) ∧
      ∀ (i p' : Nat) (H' : Forest), col'[i]? = some (p', H') →
        ∃ (H : Forest) (j : Nat), col[i]? = some (p', H) ∧ H' = safePrefix H j := by sorry

/-- D1.9a: the word of a truncation after an entry is a prefix of the word. -/
theorem word_truncAfter_prefix (E : Forest) (e : EntryAddr) : word (E.truncAfter e) <+: word E := by
  sorry

/-- L2.5c (`sign_of_agreement`†, txt:246-249): if two height words agree for more atoms than the
length of a query height, their normalized comparisons with it have the same strict sign; the
thresholds are arbitrary. -/
theorem sign_of_agreement (r t : Nat) {A₁ A₂ J : Forest} (hlen : mu J < mu A₁)
    (hagree : (word A₁).take (mu J + 1) = (word A₂).take (mu J + 1)) :
    keyCmp (relKey r A₁) (relKey t J) = keyCmp (relKey r A₂) (relKey t J) ∧
      keyCmp (relKey r A₁) (relKey t J) ≠ .eq := by sorry

-- U1-verify: changed (new declaration)
/-- L2.5c, key-system form: the sign hypothesis `hsign` of `trace_agree` at `α = WithTop Key`,
for one query key. -/
theorem sign_of_agreement_compare (r t : Nat) {A₁ A₂ J : Forest} (hlen : mu J < mu A₁)
    (hagree : (word A₁).take (mu J + 1) = (word A₂).take (mu J + 1)) :
    compare ((relKey r A₁ : Key) : WithTop Key) ((relKey t J : Key) : WithTop Key) =
      compare ((relKey r A₂ : Key) : WithTop Key) ((relKey t J : Key) : WithTop Key) := by sorry

/-! ## D1.5a — shifts and the continuation hole (S-6) -/

theorem shiftVal_zero (r p : Nat) : shiftVal r 0 p = p := by sorry

/-- D1.5a. -/
theorem shift_zero (r : Nat) (F : Forest) : shift r 0 F = F := by sorry

/-- D1.5a: shifts at one threshold compose additively. -/
theorem shift_add (r d d' : Nat) (F : Forest) : shift r d (shift r d' F) = shift r (d + d') F := by
  sorry

/-- D1.5a: `mapLast` (locked) in list form. -/
theorem mapLast_eq {γ δ : Type} (f g : γ → δ) (l : List γ) :
    mapLast f g l = l.dropLast.map f ++ (l.getLast?.map g).toList := by sorry

/-- D1.5a: the unshifted placement of `Z` into the hole (`A_{0,0,depth,Z}`). -/
def Hole.put (h : Hole) (Z : Forest) : Forest := replaceAt 0 0 Z h.depth h.outer

/-- D1.5a (fill/shift law): `A_{r,d,ℓ,Z}(F)` is `T_{r,d}(F)` with `Z` placed unshifted. -/
theorem Hole.fill_eq_put (h : Hole) (r d : Nat) (Z : Forest) :
    h.fill r d Z = (⟨shift r d h.outer, h.depth⟩ : Hole).put Z := by sorry

theorem Hole.fill_zero (h : Hole) (Z : Forest) : h.fill 0 0 Z = h.put Z := by sorry

/-- D1.5a: the word of a filled hole is the word with the hole emptied, followed by the word of
`Z` at the hole's depth (the hole column is the last thing in reading order). -/
theorem word_put (h : Hole) (Z : Forest) (hd : h.depth < (routeCols h.outer).length) :
    word (h.put Z) = word (h.put Tree.empty) ++ wordAt h.depth Z := by sorry

/-- D1.5a: the generic word of a shift relabels the generic word. -/
theorem gword_shift (r d : Nat) (F : Forest) :
    gword (shift r d F) = (gword F).map (GAtom.map (shiftVal r d)) := gword_map _ _

/-! ## D1.6, D1.6b — the paper's operation written from §1.2 (G-001) -/

-- bridges: hold by `rfl` (SCR-2 applied)
theorem stopData_eq_body (E : Forest) : stopData E = stopDataBody E := by sorry
theorem stepKind_eq_body (E : Forest) : stepKind E = stepKindBody E := by sorry
theorem rootData_eq_body (E : Forest) : rootData E = rootDataBody E := by sorry
theorem paperOp_eq_body (E : Forest) (n : Nat) : paperOp E n = paperOpBody E n := by sorry

/-! ### D1.6b — branch data specifications -/

/-- D1.6b (`stopData_spec`†): the stopping column `Q ⌢ [(r, ∅)]` is the last route column. -/
theorem stopData_spec {E : Forest} {sd : StopData} (h : stopData E = some sd) :
    E.colAt sd.col = some (sd.Q ++ [(sd.r, Tree.empty)]) ∧ sd.depth = sd.col.path.length ∧
      sd.t = sd.col.num 0 ∧ sd.col ∈ routeCols E ∧ (routeCols E).getLast? = some sd.col ∧
      (routeCols E).length = sd.depth + 1 := by sorry

/-- D1.6b: under I the route is never stuck (X-02 cannot happen). -/
theorem stopData_isSome {E : Forest} (hI : CondI E) {col : Column}
    (hlast : E.cols.getLast? = some col) (hne : col ≠ []) : (stopData E).isSome := by sorry

/-- D1.6b: `stopData` is `none` on `∅` and on a last outer column that is empty. -/
theorem stopData_eq_none_of_lastCol {E : Forest} (h : E.cols.getLast? = none ∨ E.cols.getLast? = some []) :
    stopData E = none := by sorry

/-- D1.6b: the deletion branch is exactly an empty last outer column. -/
theorem stepKind_deletion_iff (E : Forest) : stepKind E = some .deletion ↔ E.cols.getLast? = some [] := by
  sorry

/-- D1.6b: the special branch is exactly `specialStop`. -/
theorem stepKind_special_iff (E : Forest) :
    stepKind E = some .special ↔ ∃ sd, stopData E = some sd ∧ specialStop sd = true := by sorry

/-- D1.6b: the ordinary branch: a stop that is not special with a visible root. -/
theorem stepKind_ordinary_iff (E : Forest) :
    stepKind E = some .ordinary ↔ ∃ sd o, stopData E = some sd ∧ specialStop sd = false ∧
      sd.col.resolve 0 sd.r = some o := by sorry

/-- D1.6b (`rootData_spec`†). -/
theorem rootData_spec {E : Forest} {sd : StopData} {rd : RootData} (hsd : stopData E = some sd)
    (hrd : rootData E = some rd) :
    sd.col.resolve 0 sd.r = some rd.col ∧ rd.layer = rd.col.path.length ∧ rd.idx = rd.col.col ∧
      rd.col.num 0 = sd.r ∧ sd.r < sd.t ∧ rd.col ∈ E.colAddrs ∧
      rd.cursor = cursor (rootKeys E rd) (queryKeys sd) ∧
      (rd.owner = true ↔ ∃ F, E.forestAt rd.col.path = some F ∧ rd.col.col + 1 = F.cols.length) := by
  sorry

/-- D1.6b: the root is an owner iff it contains the stopping column; then the containing entry is
its last entry (the active root entry `u`). -/
theorem rootData_owner_iff {E : Forest} {sd : StopData} {rd : RootData} (hsd : stopData E = some sd)
    (hrd : rootData E = some rd) :
    rd.owner = true ↔ ∃ u, (⟨rd.col, u⟩ : EntryAddr).Contains sd.col ∧
      u + 1 = ((E.colAt rd.col).getD []).length := by sorry

/-- D1.6b: in the owner case the root layer is strictly above the stopping depth. -/
theorem rootData_layer_lt {E : Forest} {sd : StopData} {rd : RootData} (hsd : stopData E = some sd)
    (hrd : rootData E = some rd) (ho : rd.owner = true) : rd.layer < sd.depth := by sorry

theorem rootData_layer_le {E : Forest} {sd : StopData} {rd : RootData} (hsd : stopData E = some sd)
    (hrd : rootData E = some rd) : rd.layer ≤ sd.depth := by sorry

/-- D1.6b: the special owner entry is the last entry of the owner column, its height is the
stopping forest, which ends in the single-entry column `[(r, ∅)]`. -/
theorem ownerEntry_spec {E : Forest} {sd : StopData} {oe : EntryAddr}
    (hk : stepKind E = some .special) (hsd : stopData E = some sd) (hoe : sd.ownerEntry = some oe) :
    oe.Contains sd.col ∧ oe.heightPath = sd.col.path ∧ oe.col.num 0 = sd.r ∧
      ∃ col p Fl, E.colAt oe.col = some col ∧ col.getLast? = some (p, Fl) ∧
        oe.idx + 1 = col.length ∧ Fl.cols.getLast? = some [(sd.r, Tree.empty)] := by sorry

/-- D1.6b (`paperOp_deletion`). -/
theorem paperOp_deletion {E : Forest} (h : stepKind E = some .deletion) (n : Nat) :
    paperOp E n = some (.node E.cols.dropLast) := by sorry

/-- D1.6b (`paperOp_special`†): the special output, in terms of `Hole.fill`. -/
theorem paperOp_special {E : Forest} {sd : StopData} {oe : EntryAddr} {col : Column} {p : Nat}
    {Fl : Forest} (hk : stepKind E = some .special) (hsd : stopData E = some sd)
    (hoe : sd.ownerEntry = some oe) (hcol : E.colAt oe.col = some col)
    (hlast : col.getLast? = some (p, Fl)) (n : Nat) :
    paperOp E n = some (Hole.fill ⟨E, sd.depth - 1⟩ 0 0
      (.node [col.dropLast ++
        List.replicate (n + if col.dropLast.isEmpty then 1 else 0) (p, .node Fl.cols.dropLast)])) := by
  sorry

/-- D1.6b (`paperOp_ordinary`†): the ordinary output, in terms of `Hole.fill` and `ordZ`. -/
theorem paperOp_ordinary {E : Forest} {sd : StopData} {rd : RootData}
    (hk : stepKind E = some .ordinary) (hsd : stopData E = some sd) (hrd : rootData E = some rd)
    (n : Nat) :
    paperOp E n =
      if rd.owner && n != 0 && (((E.colAt rd.col).getD []).drop rd.cursor).isEmpty then none
      else some (Hole.fill ⟨E, sd.depth⟩ 0 0 (ordZ E sd rd n)) := by sorry

/-- D1.6b: the ordinary step at parameter `0` deletes the whole stopping column (txt:132-133). -/
theorem paperOp_ordinary_zero {E : Forest} {sd : StopData} (hk : stepKind E = some .ordinary)
    (hsd : stopData E = some sd) : paperOp E 0 = some (Hole.put ⟨E, sd.depth⟩ Tree.empty) := by sorry

/-! ### D1.6c — agreement of the locked `expand` with `paperOp` (G-001, D-3) -/

/-- D1.6c: the reference's depth agrees with the paper's route whenever the latter stops
(no use of I). -/
theorem tailLayer_of_stopData {E : Forest} {sd : StopData} (h : stopData E = some sd) :
    tailLayer E = (sd.depth : Int) := by sorry

/-- D1.6c: the reference's deletion test. -/
theorem tailLayer_neg_iff {E : Forest} (hE : E ≠ Tree.empty) :
    tailLayer E < 0 ↔ E.cols.getLast? = some [] := by sorry

/-- D1.6c: the reference's layers are the paper's route forests. -/
theorem skipLayers_of_stopData {E : Forest} {sd : StopData} (h : stopData E = some sd) {d : Nat}
    (hd : d ≤ sd.depth) : E.forestAt (sd.col.path.take d) = some (skipLayers E d) := by sorry

theorem skipLayers_add (E : Forest) (a b : Nat) : skipLayers (skipLayers E a) b = skipLayers E (a + b) := by
  sorry

/-- D1.6c: `leftCount` counts the columns of the layers above `d` (no hypothesis). -/
theorem leftCount_eq_sum (E : Forest) (d : Nat) :
    leftCount E d = ((List.range d).map fun k => (skipLayers E k).cols.length).sum := by sorry

/-- D1.6c: `t` agrees (txt:101-103). -/
theorem tailNum_of_stopData {E : Forest} {sd : StopData} (h : stopData E = some sd) :
    tailNum E sd.depth = sd.t := by sorry

/-- D1.6c: `r` agrees. -/
theorem rootAt_of_stopData {E : Forest} {sd : StopData} (h : stopData E = some sd) :
    rootAt E sd.depth = sd.r := by sorry

/-- D1.6c: the special tests agree. -/
theorem isSpecial_of_stopData {E : Forest} {sd : StopData} (h : stopData E = some sd) :
    isSpecial E sd.depth = specialStop sd := by sorry

/-- D1.6c: the special outputs agree. -/
theorem expandSpecial_of_stopData {E : Forest} {sd : StopData} (h : stopData E = some sd)
    (hs : specialStop sd = true) (n : Nat) : some (expandSpecial n sd.depth E) = specialOut E sd n := by
  sorry

/-- D1.6c: the reference's root search finds the paper's visible root. -/
theorem rootLayer_of_resolve {E : Forest} {sd : StopData} {o : ColAddr} (h : stopData E = some sd)
    (ho : sd.col.resolve 0 sd.r = some o) : rootLayer E sd.r sd.depth = some (o.path.length, o.col) := by
  sorry

/-- D1.6c: the reference's scan start is the paper's cursor. -/
theorem rootAppendingStart_of_rootData {E : Forest} {sd : StopData} {rd : RootData}
    (hsd : stopData E = some sd) (hrd : rootData E = some rd) :
    rootAppendingStart ((E.colAt rd.col).getD []) sd.r (sd.Q ++ [(sd.r, Tree.empty)]) sd.t =
      rd.cursor := by sorry

/-- D1.6c: `ascendReplace` at a nonnegative depth is `Hole.fill`. -/
theorem ascendReplace_ofNat (r d k : Nat) (Z F : Forest) :
    ascendReplace r d (some (k : Int)) Z F = Hole.fill ⟨F, k⟩ r d Z := by sorry

/-- D1.6c: the loops agree. -/
theorem iterDown_eq_ordLoop (step : Nat → Forest → Forest) (n : Nat) (Z : Forest) :
    iterDown step n Z = ordLoop step n Z := by sorry

/-- D1.6c: agreement on every input where the paper's route stops at a special step. -/
theorem expand_eq_paperOp_special {E : Forest} {sd : StopData} (h : stopData E = some sd)
    (hs : specialStop sd = true) (n : Nat) : expand E n = paperOp E n := by sorry

/-- D1.6c: agreement on every input where the paper's route stops at a non-special step with a
visible root. -/
theorem expand_eq_paperOp_ordinary {E : Forest} {sd : StopData} {o : ColAddr}
    (h : stopData E = some sd) (hs : specialStop sd = false) (ho : sd.col.resolve 0 sd.r = some o)
    (n : Nat) : expand E n = paperOp E n := by sorry

/-- D1.6c: under V the root of a stop is visible. -/
theorem resolve_root_of_condV {E : Forest} (hV : CondV E) {sd : StopData} (h : stopData E = some sd) :
    (sd.col.resolve 0 sd.r).isSome := by sorry

/-! ## D2.2a — responses, edges and paths -/

/-- D2.2a: the start `x(c,k)` of the cut-`k` test of column `c` (codex-crosscheck-1 Q2):
`c - 1` at `k = 0`, else the parent of entry `k - 1`. -/
def cutStart (E : Forest) (c : ColAddr) (k : Nat) : Nat :=
  if k = 0 then c.num 0 - 1 else ((parents E c)[k - 1]?).getD 0

/-- D2.2a: condition A at entry `i` of column `c` in key system `ks`. -/
def AAt (E : Forest) (ks : KeySys) (c : ColAddr) (i : Nat) : Prop :=
  ∀ p, (parents E c)[i]? = some p → Path E ks c (cutQuery (ks c) i) (cutStart E c i) p

/-- D2.2a: `CondAK` is `AAt` at every entry. -/
theorem condAK_iff (E : Forest) (ks : KeySys) :
    CondAK E ks ↔ ∀ c ∈ E.colAddrs, ∀ i, AAt E ks c i := Iff.rfl

/-- D2.2a: the (deterministic) response function of an edge read on the stack of `c`. -/
def respEdge (E : Forest) (ks : KeySys) (c : ColAddr) (W : List (WithTop Key)) (x : Nat) :
    Option Nat :=
  (c.resolve 0 x).bind fun o => resp E ks o W

theorem edge_iff (E : Forest) (ks : KeySys) (c : ColAddr) (W : List (WithTop Key)) (x p : Nat) :
    Edge E ks c W x p ↔ respEdge E ks c W x = some p := by sorry

/-- D2.2a: `resp` in terms of the cursor. -/
theorem resp_eq_some {E : Forest} {ks : KeySys} {o : ColAddr} {W : List (WithTop Key)} {p : Nat} :
    resp E ks o W = some p ↔ ∃ H, ((E.colAt o).getD [])[cursor (ks o) W]? = some (p, H) := by sorry

/-- D2.2a: the number of keys is the number of entries, for actual and capped systems. -/
theorem length_actualKeys (E : Forest) (c : ColAddr) :
    (actualKeys E c).length = ((E.colAt c).getD []).length := by sorry

theorem length_capKeys (E : Forest) (sel : List ColAddr) (c : ColAddr) :
    (capKeys E sel c).length = ((E.colAt c).getD []).length := by sorry

/-- D2.2a (txt:179-180): under V every edge decreases the column number. -/
theorem edge_lt {E : Forest} (hV : CondV E) {ks : KeySys} {c : ColAddr} {W : List (WithTop Key)}
    {x p : Nat} (h : Edge E ks c W x p) : p < x := by sorry

/-- D2.2a: paths decrease. -/
theorem path_le {E : Forest} (hV : CondV E) {ks : KeySys} {c : ColAddr} {W : List (WithTop Key)}
    {x y : Nat} (h : Path E ks c W x y) : y ≤ x := by sorry

/-- D2.2a: the test starts strictly below the tested column. -/
theorem cutStart_lt {E : Forest} (hV : CondV E) {c : ColAddr} (hc : c ∈ E.colAddrs) {k : Nat}
    (hk : k ≤ (parents E c).length) (hpos : 0 < c.num 0) : cutStart E c k < c.num 0 := by sorry

/-- D2.2a (stack restriction): edges from numbers below `x₀` depend only on the stack below
`x₀`. -/
theorem edge_congr_stack {E : Forest} {ks : KeySys} {c c' : ColAddr} {W : List (WithTop Key)}
    {x₀ x p : Nat} (hst : ∀ q < x₀, c.resolve 0 q = c'.resolve 0 q) (hx : x < x₀) :
    Edge E ks c W x p ↔ Edge E ks c' W x p := by sorry

/-- D2.2a (stack restriction for paths, codex-crosscheck-1 Q2). -/
theorem path_congr_stack {E : Forest} (hV : CondV E) {ks : KeySys} {c c' : ColAddr}
    {W : List (WithTop Key)} {x₀ x y : Nat} (hst : ∀ q < x₀, c.resolve 0 q = c'.resolve 0 q)
    (hx : x < x₀) : Path E ks c W x y ↔ Path E ks c' W x y := by sorry

/-- D2.2a (txt:191-193): A implies parent monotonicity, in every key system. -/
theorem parents_antitone {E : Forest} (hV : CondV E) {ks : KeySys} (hA : CondAK E ks)
    {c : ColAddr} (hc : c ∈ E.colAddrs) {i p q : Nat} (hi : (parents E c)[i + 1]? = some p)
    (hq : (parents E c)[i]? = some q) : p ≤ q := by sorry

/-! ## D1.3a, D2.3a — the conditions in usable form -/

/-- D1.3a: V is "every parent is smaller than its column's printed number" (every smaller
number is visible, `resolve_isSome_iff`). -/
theorem condV_iff_lt (E : Forest) :
    CondV E ↔ ∀ e ∈ E.entryAddrs, ∀ p h, E.entryAt e = some (p, h) → p < e.col.num 0 := by sorry

/-- D2.2a: parents of a column, entrywise. -/
theorem parents_getElem? (E : Forest) (c : ColAddr) (k : Nat) :
    (parents E c)[k]? = (E.entryAt ⟨c, k⟩).map Prod.fst := by sorry

/-- D2.3a: an owner return is a contained column whose entry's parent resolves to the owner
column (definitional unfolding with `Contains`). -/
theorem isOwnerReturn_iff (E : Forest) (e₀ e : EntryAddr) :
    IsOwnerReturn E e₀ e ↔ e₀.Contains e.col ∧
      ∃ q J, E.entryAt e = some (q, J) ∧ e.col.resolve 0 q = some e₀.col := Iff.rfl

/-- D2.3a: an entry of a contained column whose parent is the host number is an owner return. -/
theorem isOwnerReturn_of_parent {E : Forest} {e₀ : EntryAddr} {c : ColAddr} {k : Nat} {J : Forest}
    (hc : e₀.Contains c) (hk : E.entryAt ⟨c, k⟩ = some (e₀.col.num 0, J)) :
    IsOwnerReturn E e₀ ⟨c, k⟩ := by sorry

/-! ## L2.2a — the path-nesting induction (G-006) -/

/-- L2.2a: the path-nesting predicate at source number `x`, quantified over every stack owner
`c` (all occurrences and scopes simultaneously, codex-crosscheck-1 Q2). -/
def NestPred (E : Forest) (ks : KeySys) (x : Nat) : Prop :=
  ∀ (c : ColAddr) (W Z : List (WithTop Key)) (p : Nat), Noninc W → Noninc Z → W ≤ Z →
    Edge E ks c Z x p → Path E ks c W x p

/-- L2.2a: the induction step (strong induction on `x`). -/
theorem nestPred_step {E : Forest} (hV : CondV E) {ks : KeySys} (hA : CondAK E ks) (x : Nat)
    (ih : ∀ y < x, NestPred E ks y) : NestPred E ks x := by sorry

/-- L2.2a. -/
theorem nestPred_all {E : Forest} (hV : CondV E) {ks : KeySys} (hA : CondAK E ks) (x : Nat) :
    NestPred E ks x := by sorry

/-! ## L2.3, L2.3a — the barrier (G-006 predicates) -/

/-- L2.3a: `C_e(c,k)`: an actual cut-`k` path of column `c` that reaches the host `a` of the
containing entry `e` has query strictly below `D_e = B_a(u)` (codex-crosscheck-1 Q2). -/
def CutBound (E : Forest) (e : EntryAddr) (c : ColAddr) (k : Nat) : Prop :=
  Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) (e.col.num 0) →
    cutQuery (actualKeys E c) k < boundary (actualKeys E e.col) e.idx

/-- L2.3a: `R_e(c,k)`: if entry `k` of `c` returns to the host of `e`, then `B_c(k) < D_e`. -/
def ReturnBound (E : Forest) (e : EntryAddr) (c : ColAddr) (k : Nat) : Prop :=
  (parents E c)[k]? = some (e.col.num 0) →
    boundary (actualKeys E c) k < boundary (actualKeys E e.col) e.idx

/-- L2.3a: the empty cut is below every boundary of an entry. -/
theorem cutBound_zero {E : Forest} {e : EntryAddr} (he : e ∈ E.entryAddrs) (c : ColAddr) :
    CutBound E e c 0 := by sorry

/-- L2.3a (localized pre-entry-cut barrier): `C_e(c,k)` follows from the return bounds at
smaller column numbers inside `H_e` and at earlier entries of `c`; no A at `(c,k)` is used. -/
theorem cutBound_of_returns {E : Forest} (hV : CondV E) {e : EntryAddr} (he : e ∈ E.entryAddrs)
    {c : ColAddr} (hc : c ∈ E.colAddrs) (hec : e.Contains c) {k : Nat}
    (hk : k ≤ (parents E c).length)
    (hlow : ∀ o ∈ E.colAddrs, e.Contains o → o.num 0 < c.num 0 → ∀ v, ReturnBound E e o v)
    (hprev : ∀ k' < k, ReturnBound E e c k') : CutBound E e c k := by sorry

/-- L2.3a: the return step: `C_e(c,k)`, actual A at `(c,k)` and S give `R_e(c,k)`. -/
theorem returnBound_of_cutBound {E : Forest} (hS : CondS E) {e : EntryAddr}
    (he : e ∈ E.entryAddrs) {c : ColAddr} (hc : c ∈ E.colAddrs) (hec : e.Contains c) {k : Nat}
    (hA : AAt E (actualKeys E) c k) (hcut : CutBound E e c k) : ReturnBound E e c k := by sorry

/-- L2.3a: the joint barrier predicate at `(c, k)` for the containing entry `e`. -/
def BarPred (E : Forest) (e : EntryAddr) (c : ColAddr) (k : Nat) : Prop :=
  CutBound E e c k ∧ ReturnBound E e c k

/-- L2.3a: the lexicographic induction step on `(c.num 0, k)`. -/
theorem barPred_step {E : Forest} (hV : CondV E) (hA : CondA E) (hS : CondS E) {e : EntryAddr}
    (he : e ∈ E.entryAddrs) {c : ColAddr} (hc : c ∈ E.colAddrs) (hec : e.Contains c) {k : Nat}
    (hk : k ≤ (parents E c).length)
    (ihlow : ∀ o ∈ E.colAddrs, e.Contains o → o.num 0 < c.num 0 →
      ∀ v ≤ (parents E o).length, BarPred E e o v)
    (ihprev : ∀ k' < k, BarPred E e c k') : BarPred E e c k := by sorry

/-- L2.3a: the joint induction on `(c.num 0, k)`, all occurrences and scopes simultaneously. -/
theorem barrier_joint {E : Forest} (hV : CondV E) (hA : CondA E) (hS : CondS E) {e : EntryAddr}
    (he : e ∈ E.entryAddrs) {c : ColAddr} (hc : c ∈ E.colAddrs) (hec : e.Contains c) {k : Nat}
    (hk : k ≤ (parents E c).length) : CutBound E e c k ∧ ReturnBound E e c k := by sorry

/-- L2.3 (`barrier`†, txt:205-207): at an owner return, `B_c(v) < B_a(u)`. -/
theorem barrier {E : Forest} (hV : CondV E) (hA : CondA E) (hS : CondS E) {e₀ e : EntryAddr}
    (he₀ : e₀ ∈ E.entryAddrs) (he : e ∈ E.entryAddrs) (hret : IsOwnerReturn E e₀ e) :
    boundary (actualKeys E e.col) e.idx < boundary (actualKeys E e₀.col) e₀.idx := by sorry

/-- L2.3 (`cut_barrier`†, txt:207-209): at any complete cut, including the full cut after the
last entry, a read of an active containing entry by the cut's ancestor path has query strictly
below that entry's boundary. -/
theorem cut_barrier {E : Forest} (hV : CondV E) (hA : CondA E) (hS : CondS E) {e : EntryAddr}
    (he : e ∈ E.entryAddrs) {c : ColAddr} (hc : c ∈ E.colAddrs) (hec : e.Contains c) {k : Nat}
    (hk : k ≤ (parents E c).length)
    (hpath : Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) (e.col.num 0)) :
    cutQuery (actualKeys E c) k < boundary (actualKeys E e.col) e.idx := by sorry

/-! ## L2.4, L2.4a, L2.4b — independent capping (G-006) -/

/-- L2.4b: an unselected column keeps its actual keys. -/
theorem capKeys_of_not_mem {E : Forest} {sel : List ColAddr} {c : ColAddr} (h : c ∉ sel) :
    capKeys E sel c = actualKeys E c := by sorry

/-- L2.4b (txt:222, point 1 of codex Q2): no entry query contains a capped last key. -/
theorem cutQuery_capKeys (E : Forest) (sel : List ColAddr) (c : ColAddr) {i : Nat}
    (hi : i < ((E.colAt c).getD []).length) :
    cutQuery (capKeys E sel c) i = cutQuery (actualKeys E c) i := by sorry

/-- L2.4b: a capped column whose actual scan is not exhausted gives the actual response
(L2.5 (2)). -/
theorem resp_capKeys {E : Forest} {sel : List ColAddr} {o : ColAddr} {W : List (WithTop Key)}
    (hnx : cursor (actualKeys E o) W < (actualKeys E o).length) :
    resp E (capKeys E sel) o W = resp E (actualKeys E) o W := by sorry

/-- L2.4b (point 2 of codex Q2): a route column visible from a column of `E` contains it. -/
theorem routeCols_visible {E : Forest} {c a : ColAddr} {z : Nat} (hc : c ∈ E.colAddrs)
    (ha : a ∈ routeCols E) (hres : c.resolve 0 z = some a) :
    ∃ v, (⟨a, v⟩ : EntryAddr) ∈ E.entryAddrs ∧ (⟨a, v⟩ : EntryAddr).Contains c := by sorry

/-- L2.4b: at a cut whose containing entries satisfy their cut bounds, actual paths are capped
paths (forward direction). -/
theorem capped_path_of_actual {E : Forest} (hV : CondV E) {sel : List ColAddr}
    (hsel : ∀ a ∈ sel, a ∈ routeCols E) {c : ColAddr} (hc : c ∈ E.colAddrs) {k : Nat}
    (hcut : ∀ e ∈ E.entryAddrs, e.Contains c → CutBound E e c k) {y : Nat}
    (h : Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) y) :
    Path E (capKeys E sel) c (cutQuery (actualKeys E c) k) (cutStart E c k) y := by sorry

/-- L2.4a (first divergence): under the same cut bounds, capped paths are actual paths. -/
theorem actual_path_of_capped {E : Forest} (hV : CondV E) {sel : List ColAddr}
    (hsel : ∀ a ∈ sel, a ∈ routeCols E) {c : ColAddr} (hc : c ∈ E.colAddrs) {k : Nat}
    (hcut : ∀ e ∈ E.entryAddrs, e.Contains c → CutBound E e c k) {y : Nat}
    (h : Path E (capKeys E sel) c (cutQuery (actualKeys E c) k) (cutStart E c k) y) :
    Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) y := by sorry

/-- L2.4: forward capping. -/
theorem capping_forward {E : Forest} (hV : CondV E) (hA : CondA E) (hS : CondS E)
    {sel : List ColAddr} (hsel : ∀ a ∈ sel, a ∈ routeCols E) : CondAK E (capKeys E sel) := by sorry

/-- L2.4a: the reverse-capping predicate at `(c, i)`: actual A at entry `i` together with the
actual return bounds of that entry for every containing entry (codex-crosscheck-1 Q2). -/
def RevPred (E : Forest) (c : ColAddr) (i : Nat) : Prop :=
  AAt E (actualKeys E) c i ∧ ∀ e ∈ E.entryAddrs, e.Contains c → ReturnBound E e c i

/-- L2.4a: the lexicographic induction step on `(c.num 0, i)`. -/
theorem revPred_step {E : Forest} (hV : CondV E) (hS : CondS E) {sel : List ColAddr}
    (hsel : ∀ a ∈ sel, a ∈ routeCols E) (hA : CondAK E (capKeys E sel)) {c : ColAddr}
    (hc : c ∈ E.colAddrs) (i : Nat)
    (ihlow : ∀ o ∈ E.colAddrs, o.num 0 < c.num 0 → ∀ v, RevPred E o v)
    (ihprev : ∀ i' < i, RevPred E c i') : RevPred E c i := by sorry

/-- L2.4a: the reverse joint induction on `(c.num 0, i)`: actual A together with the actual
return bounds. -/
theorem capping_reverse_joint {E : Forest} (hV : CondV E) (hS : CondS E) {sel : List ColAddr}
    (hsel : ∀ a ∈ sel, a ∈ routeCols E) (hA : CondAK E (capKeys E sel)) {c : ColAddr}
    (hc : c ∈ E.colAddrs) (i : Nat) :
    AAt E (actualKeys E) c i ∧ ∀ e ∈ E.entryAddrs, e.Contains c → ReturnBound E e c i := by sorry

/-- L2.4a: reverse capping. -/
theorem capping_reverse {E : Forest} (hV : CondV E) (hS : CondS E) {sel : List ColAddr}
    (hsel : ∀ a ∈ sel, a ∈ routeCols E) (hA : CondAK E (capKeys E sel)) : CondA E := by sorry

/-- L2.4 (`capping_iff`†, txt:223-224): on V, S inputs, A is equivalent to A in every
independently capped system on the terminal route. -/
theorem capping_iff {E : Forest} (hV : CondV E) (hS : CondS E) {sel : List ColAddr}
    (hsel : ∀ a ∈ sel, a ∈ routeCols E) : CondA E ↔ CondAK E (capKeys E sel) := by sorry

/-! ## L2.4c — every operation is defined on V, I, A, S -/

/-- L2.4c (txt:232-236): the owner root scan is not exhausted. -/
theorem owner_root_nonexhaust {E : Forest} (hV : CondV E) (hA : CondA E) (hS : CondS E)
    {sd : StopData} {rd : RootData} (hsd : stopData E = some sd) (hrd : rootData E = some rd)
    (ho : rd.owner = true) : rd.cursor < ((E.colAt rd.col).getD []).length := by sorry

/-- L2.4c: the paper's operation is defined on nonempty V, I, A, S inputs. -/
theorem paperOp_isSome {E : Forest} (hE : E ≠ Tree.empty) (hV : CondV E) (hI : CondI E)
    (hA : CondA E) (hS : CondS E) (n : Nat) : (paperOp E n).isSome := by sorry

/-- L2.4c (task form of `expand_isSome`). -/
theorem expand_ne_none {E : Forest} (hV : CondV E) (hI : CondI E) (hA : CondA E) (hS : CondS E)
    (n : Nat) : expand E n ≠ none := by sorry

/-- L2.4c: every operation on the class L is defined. -/
theorem inL_expand_ne_none {E : Forest} (h : InL E) (n : Nat) : expand E n ≠ none := by sorry

end Scan

/-! ## D1.7a — seeds and generation witnesses -/

theorem seed_ne_empty (m : Nat) : seed m ≠ Tree.empty := by sorry

/-- D1.7a: the seed's columns (txt:139-140): `L_0 = ()`, `L_{m+1} = (0)` followed by the branch. -/
theorem seed_cols (m : Nat) : (seed m).cols = if m = 0 then [[]] else [[], branch 0 (m - 1)] := by
  sorry

/-- D1.7a: the branch has singleton columns with parents `i, i+1, …`. -/
theorem branch_spec (i k : Nat) :
    branch i k = [(i, if k = 0 then Tree.empty else .node [branch (i + 1) (k - 1)])] := by sorry

/-- D1.7a (txt:141-142): a seed index and a finite parameter list are a generation witness. -/
theorem isStd_iff_witness (E : Forest) :
    IsStd E ↔ ∃ (m : Nat) (ns : List Nat), ns.foldlM (fun F n => expand F n) (seed m) = some E := by
  sorry

namespace Scan

/-! ## N1.1 — decidable mirrors and test generators (testing only) -/

/-- N1.1. -/
def condVb (E : Forest) : Bool :=
  E.entryAddrs.all fun e => match E.entryAt e with
    | some (p, _) => (e.col.resolve 0 p).isSome
    | none => true

/-- N1.1. -/
def condIb (E : Forest) : Bool :=
  E.entryAddrs.all fun e => match E.entryAt e with
    | some (_, h) => h.cols.isEmpty || h.cols.all fun col => match col with
        | (q, _) :: _ => decide (e.col.num 0 ≤ q)
        | [] => false
    | none => true

/-- N1.1. -/
def condHb (E : Forest) : Bool :=
  E.colAddrs.all fun c =>
    let col := (E.colAt c).getD []
    (List.range (col.length - 1)).all fun i => match col[i]?, col[i + 1]? with
      | some x, some y => decide (y.1 < x.1) || (decide (y.1 = x.1) && decide (y.2 ≤ x.2))
      | _, _ => true

/-- N1.1: the deterministic orbit search (fuel `x + 1` suffices under V, since edges decrease). -/
def pathAux (E : Forest) (ks : KeySys) (c : ColAddr) (W : List (WithTop Key)) (y : Nat) :
    Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, z => z == y || match respEdge E ks c W z with
    | some p => decide (p < z) && pathAux E ks c W y fuel p
    | none => false

def pathb (E : Forest) (ks : KeySys) (c : ColAddr) (W : List (WithTop Key)) (x y : Nat) : Bool :=
  pathAux E ks c W y (x + 1) x

/-- N1.1. -/
def condAKb (E : Forest) (ks : KeySys) : Bool :=
  E.colAddrs.all fun c => (List.range (parents E c).length).all fun i =>
    match (parents E c)[i]? with
    | some p => pathb E ks c (cutQuery (ks c) i) (cutStart E c i) p
    | none => true

/-- N1.1. -/
def isOwnerReturnb (E : Forest) (e₀ e : EntryAddr) : Bool :=
  e₀.heightPath.isPrefixOf e.col.path && match E.entryAt e with
    | some (q, _) => e.col.resolve 0 q == some e₀.col
    | none => false

/-- N1.1. -/
def condSb (E : Forest) : Bool :=
  E.entryAddrs.all fun e₀ => E.entryAddrs.all fun e => !isOwnerReturnb E e₀ e ||
    decide (relKey (e.col.num 0) ((E.heightAt e).getD Tree.empty) <
      relKey (e₀.col.num 0) ((E.heightAt e₀).getD Tree.empty))

def inLb (E : Forest) : Bool :=
  condVb E && condIb E && condHb E && condAKb E (actualKeys E) && condSb E

theorem condV_iff (E : Forest) : CondV E ↔ condVb E = true := by sorry
theorem condI_iff (E : Forest) : CondI E ↔ condIb E = true := by sorry
theorem condH_iff (E : Forest) : CondH E ↔ condHb E = true := by sorry
theorem path_iff_pathb {E : Forest} (hV : CondV E) (ks : KeySys) (c : ColAddr)
    (W : List (WithTop Key)) (x y : Nat) : Path E ks c W x y ↔ pathb E ks c W x y = true := by sorry
theorem condAK_iff_b {E : Forest} (hV : CondV E) (ks : KeySys) :
    CondAK E ks ↔ condAKb E ks = true := by sorry
theorem condS_iff (E : Forest) : CondS E ↔ condSb E = true := by sorry
theorem inL_iff (E : Forest) : InL E ↔ inLb E = true := by sorry

/-- N1.1: standard expressions reachable from the seeds `0…m` in at most `d` operations with
parameters `0…p` (breadth first; for bounded tests). -/
def stdUpTo (m d p : Nat) : List Forest :=
  ((List.range d).foldl
    (fun (st : List Forest × List Forest) _ =>
      let nxt := st.2.flatMap fun F => (List.range (p + 1)).filterMap (expand F)
      (st.1 ++ nxt, nxt))
    ((List.range (m + 1)).map seed, (List.range (m + 1)).map seed)).1

/-- N1.1: every listed expression is standard. -/
theorem isStd_of_mem_stdUpTo {m d p : Nat} {E : Forest} (h : E ∈ stdUpTo m d p) : IsStd E := by
  sorry

end Scan

/-! ## Integration additions (requested by U2, U3, U5; nodes D1.2e, D1.2f, D1.3b, D1.4b,
D1.5b, D1.6d, D1.9b, N1.4, L2.1d, L2.3c, L2.5d). Every statement below was a stub or a
Requires entry of another unit; the requester is named in each docstring. -/

namespace Tree

/-- D1.4b (moved from U3 L6.2a `roles_map`; requested by U5 R14): roles depend only on the
shape of a tree. -/
theorem roles_map {α β : Type} (f : α → β) (t : Tree α) : (t.map f).roles = t.roles := by sorry

/-- D1.2e (requested by U5 R12): the roles of an entry `e` are its slot, right after the prefix
`P(E, e)`, followed by the roles of its height placed under `e`'s height path; no later role lies
inside `e`. -/
theorem roles_entry {E : Forest} {e : EntryAddr} (he : e ∈ E.entryAddrs) :
    ∃ post, E.roles = Packet.prefixRoles E e ++ .slot e ::
      (((E.heightAt e).getD Tree.empty).roles.map (Role.under e.heightPath) ++ post) ∧
      ∀ x ∈ post, x.inEntry e = false := by sorry

/-- D1.2e (requested by U5 R13): `truncAfter_roles` in `Role.under` form. -/
theorem truncAfter_roles_under {E : Forest} {e : EntryAddr} (he : e ∈ E.entryAddrs) :
    (E.truncAfter e).roles = Packet.prefixRoles E e ++ .slot e ::
      ((E.heightAt e).getD Tree.empty).roles.map (Role.under e.heightPath) := by sorry

/-- D1.2e (requested by U3 D7.1b for U5 R19): the column of an entry, every column occurrence on
the visible stack of that column, and the slot of every entry containing that column precede the
entry's slot in reading order. -/
theorem stack_mem_prefix {E : Forest} {e : EntryAddr} (he : e ∈ E.entryAddrs) :
    Role.ord e.col ∈ Packet.prefixRoles E e ∧
    (∀ o, e.col.OnStack o → Role.ord o ∈ Packet.prefixRoles E e) ∧
    ∀ e' : EntryAddr, e'.Contains e.col → Role.slot e' ∈ Packet.prefixRoles E e := by sorry

/-- D1.2f (requested by U3 R1): truncation after an entry is idempotent and keeps the entry,
its height and its prefix. -/
theorem truncAfter_spec (t : Forest) (e : EntryAddr) (he : e ∈ t.entryAddrs) :
    (t.truncAfter e).truncAfter e = t.truncAfter e ∧ e ∈ (t.truncAfter e).entryAddrs ∧
    (t.truncAfter e).heightAt e = t.heightAt e ∧ (t.truncAfter e).entryAt e = t.entryAt e ∧
    (∀ x ∈ Packet.prefixRoles t e, x ∈ Packet.prefixRoles (t.truncAfter e) e) ∧
    Packet.prefixRoles (t.truncAfter e) e = Packet.prefixRoles t e := by sorry

/-- D1.2f (requested by U3 R2): basic laws of `setHeight`. -/
theorem setHeight_basic (t : Forest) (e : EntryAddr) (h : Forest) (he : e ∈ t.entryAddrs) :
    e ∈ (t.setHeight e h).entryAddrs ∧ (t.setHeight e h).heightAt e = some h ∧
    (∀ h', (t.setHeight e h).setHeight e h' = t.setHeight e h') ∧
    (t.heightAt e = some h → t.setHeight e h = t) ∧
    (t.truncAfter e = t → (t.setHeight e h).truncAfter e = t.setHeight e h) ∧
    ((t.setHeight e h).entryAt e).map Prod.fst = (t.entryAt e).map Prod.fst := by sorry

end Tree

/-- D1.4b (requested by U5 R14): a relative key has the roles of its height. -/
theorem relKey_roles (a : Nat) (B : Forest) : (relKey a B).roles = B.roles := by sorry

/-- D1.4b (requested by U5 R14): a relative key is empty exactly when its height is. -/
theorem relKey_eq_empty {a : Nat} {B : Forest} : relKey a B = Tree.empty ↔ B = Tree.empty := by
  sorry

namespace Scan

/-- D1.3b (requested by U5 R8): under V and I the first parent of a nonempty height is the
printed number of its host column. -/
theorem firstParent_host {E : Forest} (hV : CondV E) (hI : CondI E) {e : EntryAddr}
    (he : e ∈ E.entryAddrs) {h : Forest} (hh : E.heightAt e = some h) (hne : h ≠ Tree.empty) :
    ∃ H₀ rest, h.cols.head? = some ((e.col.num 0, H₀) :: rest) := by sorry

/-- D1.5b (requested by U2 REQ-U1-7, second form): a shift commutes with an unshifted placement. -/
theorem shift_replaceAt (r a δ : Nat) (Z G : Forest) :
    shift r a (replaceAt 0 0 Z δ G) = replaceAt r a (shift r a Z) δ G := by sorry

/-- D1.6d (requested by U5 R3): the closing slot reads the root column and is an entry
`(r, ∅)`. -/
theorem rootData_col {H : Forest} {sd : StopData} {rd : RootData}
    (hsd : stopData H = some sd) (hrd : rootData H = some rd) :
    sd.col.resolve 0 sd.r = some rd.col ∧ rd.col.num 0 = sd.r ∧
      closingSlot sd ∈ H.entryAddrs ∧ H.entryAt (closingSlot sd) = some (sd.r, Tree.empty) := by
  sorry

/-- D1.6d (requested by U5 R4): the stopping column is a column of the expression. -/
theorem stopData_col_mem {H : Forest} {sd : StopData} (hsd : stopData H = some sd) :
    Role.ord sd.col ∈ H.roles := by sorry

/-- D1.6d (requested by U5 R5): the owner entry of a special step is an entry containing the
stopping column, and its height ends with the column `[(a, ∅)]`, `a` the owner column's number. -/
theorem ownerEntry_mem {H : Forest} {sd : StopData} {e : EntryAddr}
    (hk : stepKind H = some .special) (hsd : stopData H = some sd) (he : sd.ownerEntry = some e) :
    e ∈ H.entryAddrs ∧ (Role.ord sd.col).inEntry e = true ∧
      ∃ h, H.heightAt e = some h ∧ h.cols.getLast? = some [(e.col.num 0, Tree.empty)] := by sorry

/-- D1.6d (requested by U5 R7): an ordinary step has a nonempty last outer column. -/
theorem lastCol_of_ordinary {E : Forest} (h : stepKind E = some .ordinary) :
    E.cols.getLast? ≠ some [] := by sorry

/-- D1.6d (requested by U3 R4): the stopping data in role form. -/
theorem stopData_roles {E : Forest} {sd : StopData} (h : stopData E = some sd) :
    sd.t = sd.col.num 0 ∧ sd.depth = sd.col.path.length ∧
    E.colAt sd.col = some (sd.Q ++ [(sd.r, Tree.empty)]) ∧
    E.entryAt (closingSlot sd) = some (sd.r, Tree.empty) ∧
    E.truncAfter (closingSlot sd) = E ∧
    ∃ qs : List Role, E.roles = Packet.rolesBefore E (.ord sd.col) ++ .ord sd.col ::
      (qs ++ [.slot (closingSlot sd)]) ∧ ∀ x ∈ qs, Packet.inQueryRegion sd x = true := by sorry

/-- D1.6d (requested by U3 R5): the root column lies on the stopping column's path, and the owner
flag is containment by the root's last entry. -/
theorem rootData_path {E : Forest} {sd : StopData} {rd : RootData}
    (hsd : stopData E = some sd) (h : rootData E = some rd) :
    sd.col.resolve 0 sd.r = some rd.col ∧ rd.col.num 0 = sd.r ∧ rd.layer = rd.col.path.length ∧
    rd.col.path <+: sd.col.path ∧
    rd.cursor = cursor (rootKeys E rd) (queryKeys sd) ∧
    (rd.owner = true ↔ (rd.col.container sd.col).isSome) ∧
    (∀ e, rd.col.container sd.col = some e → e.idx + 1 = Packet.rootLenOf E rd) := by sorry

/-- D1.6d (requested by U3 R6): the ordinary branch with `specialStop` unfolded. -/
theorem stepKind_ordinary_iff_unfold {E : Forest} (hE : E ≠ Tree.empty) (hV : CondV E)
    (hI : CondI E) :
    stepKind E = some .ordinary ↔
      ∃ sd, stopData E = some sd ∧
        ¬ (0 < sd.depth ∧ sd.Q = [] ∧ sd.r + (sd.col.col + 1) = sd.t) ∧
        (sd.col.resolve 0 sd.r).isSome := by sorry

/-- D1.6d (requested by U2 REQ-U1-3, converse; used by U2 D3.1e item 1): if the last route column
of `E` ends in an entry with empty height, the paper's route stops there. -/
theorem stopData_of_route {E : Forest} {c : ColAddr} {Q : Column} {r : Nat}
    (hc : (routeCols E).getLast? = some c) (hcol : E.colAt c = some (Q ++ [(r, Tree.empty)])) :
    stopData E = some { depth := c.path.length, col := c, t := c.num 0, r := r, Q := Q } := by
  sorry

/-- D1.9b (requested by U2 REQ-U1-14, for N2.1): a one-atom extension of a word. If
`w(E) = w(G) ⌢ [z]` with `z` an entry atom at depth `e` (`(2e,1,p)` if `first`, else
`(2e+1,0,p)`), then the last route column `c` of `E` has depth `e` and ends in its entry `k`,
which is `(p, ∅)`, `k = 0` iff `first`; `G` is the safe prefix of `E` without that atom; the route
columns of depth `< e` are shared; and for `k ≠ 0` the column `c` is the route column of `G` at
depth `e`, holding the first `k` entries of `E`'s column. -/
theorem routeCols_of_word_snoc {G E : Forest} {e p : Nat} {first : Bool}
    (hw : word E = word G ++
      [if first then toLex (2 * e, toLex (1, p)) else toLex (2 * e + 1, toLex (0, p))]) :
    ∃ (c : ColAddr) (k : Nat), c.path.length = e ∧ (k = 0 ↔ first = true) ∧
      (routeCols E).getLast? = some c ∧ E.entryAt ⟨c, k⟩ = some (p, Tree.empty) ∧
      ((E.colAt c).getD []).length = k + 1 ∧ G = safePrefix E (mu E - 1) ∧
      (routeCols G).take e = (routeCols E).take e ∧
      (k ≠ 0 → (routeCols G)[e]? = some c ∧ G.colAt c = some (((E.colAt c).getD []).take k)) := by
  sorry

/-- N1.4 (requested by U2 REQ-U1-18): the word at a deeper starting depth adds `2δ` to every depth
coordinate. -/
theorem wordAt_add (e δ : Nat) (X : Forest) :
    wordAt (e + δ) X = (wordAt e X).map fun A => toLex ((ofLex A).1 + 2 * δ, (ofLex A).2) := by
  sorry

/-- N1.4: relabelling of a word atom: the empty-column atom (even depth coordinate, marker `0`)
is fixed; every entry atom has its third coordinate relabelled. -/
def WordAtom.relabel (f : Nat → Nat) (A : WordAtom) : WordAtom :=
  if (ofLex A).1 % 2 = 0 ∧ (ofLex (ofLex A).2).1 = 0 then A
  else toLex ((ofLex A).1, toLex ((ofLex (ofLex A).2).1, f (ofLex (ofLex A).2).2))

/-- N1.4 (requested by U2 REQ-U1-18): relabelling a forest relabels its word atom by atom. -/
theorem wordAt_map (e : Nat) (f : Nat → Nat) (X : Forest) :
    wordAt e (Tree.map f X) = (wordAt e X).map (WordAtom.relabel f) := by sorry

/-- L2.1d (requested by U3 R7): a reduced `⊤`-free query below the boundary of entry `u` stops at
or before `u`, and the scan is unchanged when the column is cut after `u` with key `u` raised
to `⊤`. -/
theorem cursor_cappedAt (ks W : List (WithTop Key)) (u : Nat) (hu : u < ks.length)
    (hW : W.Pairwise fun x y => y ≤ x) (hT : ∀ y ∈ W, y ≠ ⊤)
    (hlt : W < cutQuery ks (u + 1)) :
    cursor ks W ≤ u ∧ cursor ks W = cursor (ks.take u ++ [⊤]) W := by sorry

/-- L2.3c (requested by U3 R8): the cut barrier read at a containing column on the cut chain. -/
theorem cut_barrier_read {E : Forest} (hE : InL E) {c : ColAddr} (hc : c ∈ E.colAddrs)
    {k : Nat} (hk : k ≤ (parents E c).length) {y : Nat}
    (hy : Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) y)
    {o : ColAddr} (ho : c.resolve 0 y = some o) {e : EntryAddr} (he : o.container c = some e) :
    cutQuery (actualKeys E c) k < cutQuery (actualKeys E o) (e.idx + 1) := by sorry

/-- L2.5d (requested by U5 R15): the trace of the raw scan starts at `(0,0)`, moves by the three
comparison rules, stays within the cursors, and ends at `(cursor, j)` with `j = |qry|` when the
source is not exhausted. -/
theorem trace_spec {α : Type} [LinearOrder α] (src qry : List α) :
    (trace src qry).head? = some (0, 0) ∧
    (∀ k s s', (trace src qry)[k]? = some s → (trace src qry)[k + 1]? = some s' →
      ∃ x y, src[s.1]? = some x ∧ qry[s.2]? = some y ∧
        ((x < y ∧ s' = (s.1 + 1, s.2)) ∨ (x = y ∧ s' = (s.1 + 1, s.2 + 1)) ∨
          (y < x ∧ s' = (s.1, s.2 + 1)))) ∧
    (∀ s ∈ trace src qry, s.1 ≤ cursor src qry ∧ s.2 ≤ qry.length) ∧
    ∃ j, (trace src qry).getLast? = some (cursor src qry, j) ∧
      (cursor src qry < src.length → j = qry.length) := by sorry

end Scan

end BTBMS
