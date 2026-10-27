/-!
# BTBMS blueprint — repair G-011 (U3 L4.2c, path transfer)

Companion of `blueprint/repairs/G-011.md`. Appended after the integrated check (spine, then
`U1.lean` … `U5.lean` without their import lines); it needs no imports beyond theirs. Every
declaration is new, with a fresh name, and every proof is `sorry`. Each docstring starts with the
repair's node ID (`G011-…`) and names the blueprint node it serves.

Namespaces follow the owner of each fact:
* `BTBMS.EntryAddr`, `BTBMS.Tree` (owner U1): relative entry addresses; the columns of a tree
  truncated after an entry whose height is then replaced (`G011-D0`, `G011-T1`, `G011-T2`;
  proposed node D1.2g);
* `BTBMS.Closure` (owner U2): the block form of two columns and the stack of an admissible cap,
  resp. of a repair list, against `E` (`G011-D1`, `G011-L1`, `G011-L2`; proposed node D3.1f);
* `BTBMS.Packet` (owner U3): κ on `WithTop Key`, the query transfer, the response lemmas and the
  phases of `firstDiff_path` (`G011-D2`, `G011-L3` … `G011-L11`; blueprint node L4.2e of
  `blueprint/repairs/G-011.md` §5.2).
-/

namespace BTBMS

open Scan

/-! ## U1 — relative addresses, truncated trees -/

namespace EntryAddr

/-- G011-D0 (owner U1): the address of `e` read inside a height whose height path is `pfx`
(`pfx <+: e.col.path`): drop the first `|pfx|` steps of the column path. -/
def relTo (e : EntryAddr) (pfx : List (Nat × Nat)) : EntryAddr :=
  ⟨⟨e.col.path.drop pfx.length, e.col.col⟩, e.idx⟩

end EntryAddr

namespace Tree

/-- G011-T1(a) (owner U1; used by U3 L4.2c step 4(c), G011-L7). Truncating after `e` and then
replacing the height of `e` leaves every column of `e`'s visible stack that does not contain `e`
unchanged. -/
theorem colAt_truncSet_closed {t : Forest} {e : EntryAddr} (he : e ∈ t.entryAddrs) (h : Forest)
    {o : ColAddr} (ho : e.col.OnStack o) (hno : o.container e.col = none) :
    ((t.truncAfter e).setHeight e h).colAt o = t.colAt o := by sorry

/-- G011-T1(b) (owner U1; used by G011-L7). The column of `e`, and every column containing `e`
(active entry `u`), keep their first `u` entries and the label of entry `u`, and end at `u`; the
height of entry `u` is `h` for `e`'s own column and the relative truncation with `h` placed at `e`
for a proper container. -/
theorem colAt_truncSet_active {t : Forest} {e : EntryAddr} (he : e ∈ t.entryAddrs) (h : Forest)
    {o : ColAddr} {u : Nat} (hou : (o = e.col ∧ u = e.idx) ∨ o.container e.col = some ⟨o, u⟩) :
    ∃ (col : Column) (q : Nat) (X : Forest), t.colAt o = some col ∧ col[u]? = some (q, X) ∧
      ((t.truncAfter e).setHeight e h).colAt o =
        some (col.take u ++ [(q, if o = e.col then h else
          (X.truncAfter (e.relTo (⟨o, u⟩ : EntryAddr).heightPath)).setHeight
            (e.relTo (⟨o, u⟩ : EntryAddr).heightPath) h)]) := by sorry

/-- G011-T2 (owner U1; used by G011-L7). Truncating after `e` and lowering the height of `e`
gives a smaller tree. -/
theorem truncSet_le {X : Forest} {e : EntryAddr} (he : e ∈ X.entryAddrs) {h : Forest}
    (hh : h ≤ (X.heightAt e).getD Tree.empty) : (X.truncAfter e).setHeight e h ≤ X := by sorry

end Tree

/-! ## U2 — block form; stacks of admissible caps and of repair lists -/

namespace Closure

/-- G011-D1 (owner U2). Block form of a column `colH` with active index `eH` against a column
`colE` with active index `eE`: `colH` ends at `eH`, agrees with `colE` before `eH`, and the entries
`eH … eE` of `colE` all carry the label of `colH[eH]` (a deleted same-parent block followed by the
active entry). `eH = eE` is the unmoved case. -/
def BlockForm (colH colE : Column) (eH eE : Nat) : Prop :=
  colH.length = eH + 1 ∧ eH ≤ eE ∧ eE < colE.length ∧ colH.take eH = colE.take eH ∧
    ∀ x, eH ≤ x → x ≤ eE → (colE[x]?).map Prod.fst = (colH[eH]?).map Prod.fst

/-- G011-L1 (owner U2; requested by U3 L4.2c steps 4(b3), 4(c)). The stack of an admissible cap
against `E`. The stopping column of `w.H` has the column indices of `w.col` (only entry indices
move). Below the host number `sd.t`, the two stacks resolve to columns of equal number that `χ`
maps to each other, and either
* neither contains its stopping column, and the two columns are equal (closed columns are
  carried unchanged), or
* both do, with active entries `eH`, `eE` (`χ` maps one to the other), in block form: the moves
  at that level deleted exactly the same-parent block `eH … eE-1` of `E`'s column. -/
theorem admCap_stack {E : Forest} (hE : InL E) (w : AdmCap E) {sd : StopData}
    (hsd : stopData w.H = some sd) :
    sd.col.path.length = w.col.path.length ∧ sd.col.col = w.col.col ∧
    sd.col.path.map Prod.fst = w.col.path.map Prod.fst ∧
    ∀ q, q < sd.t → ∃ oH oE, sd.col.resolve 0 q = some oH ∧ w.col.resolve 0 q = some oE ∧
      oH.num 0 = oE.num 0 ∧ w.origin (.ord oH) = some (.ord oE) ∧
      ((oH.container sd.col = none ∧ oE.container w.col = none ∧ w.H.colAt oH = E.colAt oE) ∨
       (∃ eH eE, oH.container sd.col = some ⟨oH, eH⟩ ∧ oE.container w.col = some ⟨oE, eE⟩ ∧
         w.origin (.slot ⟨oH, eH⟩) = some (.slot ⟨oE, eE⟩) ∧
         BlockForm ((w.H.colAt oH).getD []) ((E.colAt oE).getD []) eH eE)) := by sorry

/-- G011-L2 (owner U2; requested by U3 L4.2c step 4(c), repair records). The same for a repair
list: the moved truncation `applyMoves (E.truncAfter b) ms` read along the stack of
`moveAddr ms b`, against `E` read along the stack of `b`; the column of `b` itself is in block form
with active indices `(moveAddr ms b).idx` and `b.idx`. -/
theorem repairList_stack {E : Forest} {b : EntryAddr} (hb : b ∈ E.entryAddrs) {ms : List Move}
    (hms : RepairList (E.truncAfter b) b ms) :
    (moveAddr ms b).col.path.length = b.col.path.length ∧ (moveAddr ms b).col.col = b.col.col ∧
    (moveAddr ms b).col.path.map Prod.fst = b.col.path.map Prod.fst ∧
    moveAddr ms b ∈ (applyMoves (E.truncAfter b) ms).entryAddrs ∧
    BlockForm (((applyMoves (E.truncAfter b) ms).colAt (moveAddr ms b).col).getD [])
      ((E.colAt b.col).getD []) (moveAddr ms b).idx b.idx ∧
    ∀ q, q < b.col.num 0 → ∃ oX oE, (moveAddr ms b).col.resolve 0 q = some oX ∧
      b.col.resolve 0 q = some oE ∧ oX.num 0 = oE.num 0 ∧
      ((oX.container (moveAddr ms b).col = none ∧ oE.container b.col = none ∧
          (applyMoves (E.truncAfter b) ms).colAt oX = E.colAt oE) ∨
       (∃ eX eE, oX.container (moveAddr ms b).col = some ⟨oX, eX⟩ ∧
         oE.container b.col = some ⟨oE, eE⟩ ∧
         BlockForm (((applyMoves (E.truncAfter b) ms).colAt oX).getD []) ((E.colAt oE).getD [])
           eX eE)) := by sorry

end Closure

/-! ## U3 — κ on `WithTop Key`, query transfer, responses, the phases of `firstDiff_path` -/

namespace Packet

open Hier

/-- G011-D2: κ (L4.2a) on `WithTop Key` (`⊤ ↦ ⊤`). -/
def kappaW (r t : Nat) : WithTop Key → WithTop Key := WithTop.map (Tree.map (kappa r t))

/-- G011-D2: σ, the number map of L4.2c: numbers below `r` are fixed, the others move up by
`t - r`. -/
def sigmaNum (r t y : Nat) : Nat := if y < r then y else y + (t - r)

/-- G011-D2: the source column `c'` of a target column `c` inside the marked height. -/
def srcCol (rk : SrcRecord) (c : ColAddr) : ColAddr :=
  ⟨rk.a.heightPath ++ c.path.drop rk.b.heightPath.length, c.col⟩

/-- G011-D2: the stack owner `c_H` of the host crossing: the column of the anchor `H` at the
relative address of `c` inside the query entry `⟨sd.col, j⟩` (whose height is the target `B`). -/
def hostCol (sd : StopData) (j : Nat) (b : EntryAddr) (c : ColAddr) : ColAddr :=
  ⟨(⟨sd.col, j⟩ : EntryAddr).heightPath ++ c.path.drop b.heightPath.length, c.col⟩

/-- G011-D2: κ is strictly monotone on `WithTop Key` (L4.2a `kappa_cmp`, `keyCmp_map`). -/
theorem kappaW_strictMono {r t : Nat} (h : r ≤ t) : StrictMono (kappaW r t) := by sorry

/-- G011-D2: κ fixes the actual keys of a column whose number is at most `r` (L4.2a
`relKey_kappa_low`). -/
theorem kappaW_actualKeys_low {F : Forest} {o : ColAddr} {r t : Nat} (ho : o.num 0 ≤ r) :
    (actualKeys F o).map (kappaW r t) = actualKeys F o := by sorry

/-- G011-L3 (L4.2c steps 0–1). The source column exists with an entry `k`, whose parent `p'`
maps to `p` by σ; the target query is the κ-image of the source query; the starts correspond by
σ. -/
theorem query_transfer {rk : SrcRecord} (h : rk.Admitted) {c : ColAddr} {k p : Nat}
    (hfd : rk.firstDiff = .capAt c k p) :
    srcCol rk c ∈ rk.F.colAddrs ∧ k ≤ (parents rk.E c).length ∧
    (∃ p', (parents rk.F (srcCol rk c))[k]? = some p' ∧
      p = sigmaNum (rk.a.col.num 0) (rk.b.col.num 0) p') ∧
    cutQuery (actualKeys rk.E c) k =
      (cutQuery (actualKeys rk.F (srcCol rk c)) k).map (kappaW (rk.a.col.num 0) (rk.b.col.num 0)) ∧
    cutStart rk.E c k =
      sigmaNum (rk.a.col.num 0) (rk.b.col.num 0) (cutStart rk.F (srcCol rk c) k) := by sorry

/-- G011-L4 (L4.2c step 2). An edge of the source chain at a vertex `y > r` has its σ-twin on the
target chain (the target chain reaching `σ y` supplies R8 in `E`). -/
theorem internal_edge_eq {rk : SrcRecord} (h : rk.Admitted) {c : ColAddr} {k p : Nat}
    (hfd : rk.firstDiff = .capAt c k p) {y : Nat} (hy : rk.a.col.num 0 < y)
    (hsrc : Path rk.F (actualKeys rk.F) (srcCol rk c) (cutQuery (actualKeys rk.F (srcCol rk c)) k)
      (cutStart rk.F (srcCol rk c) k) y)
    (htgt : Path rk.E (actualKeys rk.E) c (cutQuery (actualKeys rk.E c) k) (cutStart rk.E c k)
      (sigmaNum (rk.a.col.num 0) (rk.b.col.num 0) y)) :
    respEdge rk.E (actualKeys rk.E) c (cutQuery (actualKeys rk.E c) k)
        (sigmaNum (rk.a.col.num 0) (rk.b.col.num 0) y) =
      (respEdge rk.F (actualKeys rk.F) (srcCol rk c) (cutQuery (actualKeys rk.F (srcCol rk c)) k)
        y).map (sigmaNum (rk.a.col.num 0) (rk.b.col.num 0)) := by sorry

/-- G011-L5 (L4.2b item 1 with R7 on the `E` side). Two columns in block form give the same
response: `E`'s actual response under the `E`-barrier at its active entry equals the response of
`H`'s column capped at its active entry. -/
theorem resp_blockForm {E H : Forest} {oE oH : ColAddr} {eE eH : Nat}
    (hnum : oH.num 0 = oE.num 0)
    (hbf : Closure.BlockForm ((H.colAt oH).getD []) ((E.colAt oE).getD []) eH eE)
    {W : List (WithTop Key)} (hW : W.Pairwise fun x y => y ≤ x) (hT : ∀ y ∈ W, y ≠ ⊤)
    (hbar : W < cutQuery (actualKeys E oE) (eE + 1)) :
    resp E (actualKeys E) oE W = (parents H oH)[cursor (cappedAt (actualKeys H oH) eH) W]? := by
  sorry

/-- G011-L5: the decorated keys of a route column are its actual keys capped at its last
index. -/
theorem capKeys_route_cappedAt {H : Forest} {o : ColAddr} (ho : o ∈ routeCols H) {e : Nat}
    (he : ((H.colAt o).getD []).length = e + 1) :
    capKeys H (routeCols H) o = cappedAt (actualKeys H o) e := by sorry

/-- G011-L6 (L4.2c step 4(b2)). The decorated host edge: read from any stack owner `d` that
resolves `sd.t` to the stopping column, the decorated stopping column answers `sd.r` to the query
`Z` of its full query prefix. -/
theorem decorated_host_edge {H : Forest} {sd : StopData} (hsd : stopData H = some sd)
    {d : ColAddr} (hd : d.resolve 0 sd.t = some sd.col) :
    Edge H (capKeys H (routeCols H)) d (cutQuery (actualKeys H sd.col) sd.Q.length) sd.t sd.r := by
  sorry

/-- G011-L7 (L4.2c step 4(b3)). At every vertex `z ≤ sd.t` reached by the target chain, the
decorated anchor answers on the stack of `hostCol` exactly as the actual `E` answers on the stack
of `c`. Cases: `z = sd.t` (R7 on both sides); a closed column (G011-L1, equal columns); a route
column (G011-L1 block form, R8 in `E`, G011-L5). -/
theorem host_edge_eq {E : Forest} (hE : InL E) {cap : Option (Closure.AdmCap E)} {sd : StopData}
    (hsd : stopData (Closure.anchor E cap) = some sd) {j : Nat} (hj : j < sd.Q.length)
    {b : EntryAddr} (hb : Closure.anchorOrigin E cap (.slot ⟨sd.col, j⟩) = some (.slot b))
    {c : ColAddr} (hc : c ∈ E.colAddrs) (hbc : b.heightPath <+: c.path) {k : Nat}
    (hk : k ≤ (parents E c).length) {z : Nat} (hz : z ≤ sd.t)
    (hreach : Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) z) :
    respEdge (Closure.anchor E cap)
        (capKeys (Closure.anchor E cap) (routeCols (Closure.anchor E cap)))
        (hostCol sd j b c) (cutQuery (actualKeys E c) k) z =
      respEdge E (actualKeys E) c (cutQuery (actualKeys E c) k) z := by sorry

/-- G011-L8 (L4.2c step 4(b), scan and descendant records, `E` or cap anchor). If the target
chain reaches the host `t = sd.t`, it continues to the source host `r = sd.r`. -/
theorem host_crossing {E : Forest} (hE : InL E) {cap : Option (Closure.AdmCap E)} {sd : StopData}
    (hsd : stopData (Closure.anchor E cap) = some sd) {j : Nat} (hj : j < sd.Q.length)
    {b : EntryAddr} (hb : Closure.anchorOrigin E cap (.slot ⟨sd.col, j⟩) = some (.slot b))
    {c : ColAddr} (hc : c ∈ E.colAddrs) (hbc : b.heightPath <+: c.path) {k : Nat}
    (hk : k ≤ (parents E c).length)
    (hreach : Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) sd.t) :
    Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) sd.r := by sorry

/-- G011-L9 (L4.2c step 4(c), the descendant identification at the source host). Let
`F = (H.truncAfter a).setHeight a A'` with `A' ≤ A_a`, and let `o` be `a`'s column or a column
containing it, with active entry `u`. If `F`'s scan of `o` stops at or before `u`, then `H`'s scan
of `o` has the same cursor and the same response (`cursor_raise` after the `F`-barrier). -/
theorem src_host_resp {H : Forest} {a : EntryAddr} (ha : a ∈ H.entryAddrs) {A' : Forest}
    (hA : A' ≤ (H.heightAt a).getD Tree.empty) {o : ColAddr} {u : Nat}
    (hou : (o = a.col ∧ u = a.idx) ∨ o.container a.col = some ⟨o, u⟩)
    {W : List (WithTop Key)} (hW : W.Pairwise fun x y => y ≤ x)
    (hcur : cursor (actualKeys ((H.truncAfter a).setHeight a A') o) W ≤ u) :
    cursor (actualKeys H o) W = cursor (actualKeys ((H.truncAfter a).setHeight a A') o) W ∧
    resp H (actualKeys H) o W =
      resp ((H.truncAfter a).setHeight a A') (actualKeys ((H.truncAfter a).setHeight a A')) o W := by
  sorry

/-- G011-L10 (L4.2c step 4(c), scan and descendant records). At every vertex `y ≤ r` reached by
both chains, the source edge (in `F`, query `W'`) equals the target edge (in `E`, query `W`). -/
theorem low_edge_eq {rk : SrcRecord} (h : rk.Admitted) {cap : Option (Closure.AdmCap rk.E)}
    {i j : Nat} (hkind : rk.kind = .scan cap i j ∨ rk.kind = .desc cap i j) {c : ColAddr}
    {k p : Nat} (hfd : rk.firstDiff = .capAt c k p) {y : Nat} (hyr : y ≤ rk.a.col.num 0)
    (hsrc : Path rk.F (actualKeys rk.F) (srcCol rk c) (cutQuery (actualKeys rk.F (srcCol rk c)) k)
      (cutStart rk.F (srcCol rk c) k) y)
    (htgt : Path rk.E (actualKeys rk.E) c (cutQuery (actualKeys rk.E c) k) (cutStart rk.E c k) y) :
    respEdge rk.F (actualKeys rk.F) (srcCol rk c) (cutQuery (actualKeys rk.F (srcCol rk c)) k) y =
      respEdge rk.E (actualKeys rk.E) c (cutQuery (actualKeys rk.E c) k) y := by sorry

/-- G011-L11 (L4.2c step 4(c), repair records). The same for repair records (`r = t`, κ = id),
through the repair list's block form (G011-L2). -/
theorem low_edge_eq_repair {rk : SrcRecord} (h : rk.Admitted) {ms : List Closure.Move}
    (hkind : rk.kind = .repair ms) {c : ColAddr} {k p : Nat} (hfd : rk.firstDiff = .capAt c k p)
    {y : Nat} (hyr : y ≤ rk.a.col.num 0)
    (hsrc : Path rk.F (actualKeys rk.F) (srcCol rk c) (cutQuery (actualKeys rk.F (srcCol rk c)) k)
      (cutStart rk.F (srcCol rk c) k) y)
    (htgt : Path rk.E (actualKeys rk.E) c (cutQuery (actualKeys rk.E c) k) (cutStart rk.E c k) y) :
    respEdge rk.F (actualKeys rk.F) (srcCol rk c) (cutQuery (actualKeys rk.F (srcCol rk c)) k) y =
      respEdge rk.E (actualKeys rk.E) c (cutQuery (actualKeys rk.E c) k) y := by sorry

end Packet

end BTBMS
