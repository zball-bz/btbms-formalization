/-!
# G-012 repair — the data of §8.5 Case 3 (U3 L7.5d) and its use in U5 L8.8f

Companion of `blueprint/repairs/G-012.md`. Appended after the integrated check
(`Spine.lean`, `U1.lean` … `U5.lean`); it needs no imports beyond the spine's.

**Corrected contracts** (`sorry`; their proofs are their owners', and the existing proofs in the
unit docs already argue in the corrected form, G-012.md §2.5):
* `Closure.MovesOutside` (new definition): "no move inside `B`" in current coordinates;
* [U2 D3.1e] `Closure.moves_spec_cur`, `Closure.applyMoves_litCap_addr_cur`: `moves_spec` and
  `applyMoves_litCap_addr` with `MovesOutside` for `hout` (both are false with the blueprint's
  `hout`; counterexample in G-012.md §2.5);
* [U3 L4.3c] `Packet.repair_moves_outside_cur`: the conclusion of `repair_moves_outside` in
  current coordinates;
* [U2 D3.1d] `Closure.origin_rep_of_mem` (added in verification): the rep clause of
  `origin_spec_full` at the columns of `w.H` (the clause as stated, for every `ColAddr`, is false;
  `blueprint/repairs/verification/G-012.md` §3.2). `frame_repair_cur` uses this form.

**Proved** (no `sorry` in the body; they depend only on cited statements):
* D1.2g [U1] `Tree.prefix_slot_before_inEntry`, `Tree.not_inEntry_of_mem_prefix`,
  `Tree.mem_rolesBefore_of_lt` (helpers `Tree.takeWhile_append_of_forall`,
  `Tree.mem_takeWhile_ne_of_lt`, `Tree.mem_under_of_inEntry`);
* L7.5a-1, L7.5a-2 [U3] `Packet.mapEntry_bwd_fwd`, `Packet.foldr_bwd_moveAddr`,
  `Packet.origin_moveAddr` (the step of L7.5a that had no source);
* L7.5a-3 [U3] `Packet.marked_entry_cap`;
* L7.5a [U3] `Packet.frame_repair_cur` (helper `Packet.exists_lt_of_mem_takeWhile_ne`):
  `frame_repair` with `MovesOutside`, its repaired proof written out;
* L7.5d-1 … L7.5d-4 [U3] `Packet.injOn_of_config`, `Packet.litCap_rolesBefore_col` (helper
  `Packet.takeWhile_ne_take_append`), `Packet.capRole_of_origin`, `Packet.origin_of_capRole_ne`;
* L7.5d [U3] `Packet.cap_package_derivation`: `cap_package`, field by field;
* L7.5e [U3] `Packet.CapData.preStop_marked`, `nmH_slot`, `nmH_host`, `nmH_prefix`,
  `nmH_prefix_low`, `val_slot`, `val_host`: what U5 L8.8f derives from `CapData`.
-/

namespace BTBMS

universe u

namespace Tree

/-- D1.2g helper (G-012): `takeWhile` passes a block all of whose members satisfy the test. -/
theorem takeWhile_append_of_forall {p : Role → Bool} :
    ∀ (l₁ l₂ : List Role), (∀ a ∈ l₁, p a = true) → (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p
  | [], _, _ => rfl
  | a :: l₁, l₂, h => by
    have ha : p a = true := h a (List.mem_cons_self ..)
    have ih := takeWhile_append_of_forall l₁ l₂ (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.cons_append, List.takeWhile_cons, ha, if_true, ih]

/-- D1.2g helper (G-012): in a duplicate-free list, an earlier element lies before a later one. -/
theorem mem_takeWhile_ne_of_lt :
    ∀ {l : List Role} {i j : Nat} {x y : Role}, l.Nodup → l[i]? = some x → l[j]? = some y →
      i < j → x ∈ l.takeWhile (· != y)
  | [], _, _, _, _, _, hi, _, _ => by simp at hi
  | _ :: _, _, 0, _, _, _, _, _, hij => absurd hij (Nat.not_lt_zero _)
  | a :: l, 0, j + 1, x, y, hnd, hi, hj, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    simp only [List.getElem?_cons_succ] at hj
    have hy : y ∈ l := List.mem_of_getElem? hj
    have hne : a ≠ y := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hy)
    simp [hne]
  | a :: l, i + 1, j + 1, x, y, hnd, hi, hj, hij => by
    simp only [List.getElem?_cons_succ] at hi hj
    have ih := mem_takeWhile_ne_of_lt (List.nodup_cons.mp hnd).2 hi hj (by omega)
    have hy : y ∈ l := List.mem_of_getElem? hj
    have hne : a ≠ y := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hy)
    simp [hne, ih]

/-- D1.2g helper (G-012): a role of `t` whose path extends `e.heightPath` is a role of the height
of `e`, placed under `e.heightPath`. -/
theorem mem_under_of_inEntry {t : Forest} {e : EntryAddr} (he : e ∈ t.entryAddrs) {x : Role}
    (hx : x ∈ t.roles) (hpath : e.heightPath <+: x.path) :
    x ∈ ((t.heightAt e).getD Tree.empty).roles.map (Role.under e.heightPath) := by
  obtain ⟨h, hh⟩ : ∃ h, t.heightAt e = some h := by
    have h1 := (mem_entryAddrs_iff _ _).mp he
    cases hE : t.entryAt e with
    | none => simp [hE] at h1
    | some v => exact ⟨v.2, by simp [Tree.heightAt, hE]⟩
  rw [hh, Option.getD_some, List.mem_map]
  obtain ⟨π', hπ'⟩ := hpath
  have hcol : ∀ d : ColAddr, d.path = e.heightPath ++ π' →
      t.colAt d = h.colAt ⟨π', d.col⟩ := by
    intro d hd
    unfold Tree.colAt
    rw [hd, forestAt_append, forestAt_heightPath, hh]
    rfl
  cases x with
  | ord d =>
    simp only [Role.path] at hπ'
    refine ⟨.ord ⟨π', d.col⟩, ?_, ?_⟩
    · have hx' := (mem_roles_iff _ _).mp hx
      rw [mem_roles_iff]
      simp only at hx' ⊢
      rwa [hcol d hπ'.symm] at hx'
    · simp only [Role.under]
      rw [hπ']
  | slot d =>
    simp only [Role.path] at hπ'
    refine ⟨.slot ⟨⟨π', d.col.col⟩, d.idx⟩, ?_, ?_⟩
    · have hx' := (mem_roles_iff _ _).mp hx
      rw [mem_roles_iff]
      simp only at hx' ⊢
      unfold Tree.entryAt at hx' ⊢
      rwa [hcol d.col hπ'.symm] at hx'
    · simp only [Role.under]
      rw [hπ']

-- provides: U1, D1.2g item 2 (G-012): no role of the prefix `P(t, e)` lies inside `e`.
theorem not_inEntry_of_mem_prefix {t : Forest} {e : EntryAddr} (he : e ∈ t.entryAddrs)
    {y : Role} (hy : y ∈ Packet.prefixRoles t e) : y.inEntry e = false := by
  obtain ⟨post, hroles, -⟩ := roles_entry he
  have hnd := roles_nodup t
  rw [hroles] at hnd
  have hdis := List.disjoint_of_nodup_append hnd
  have hyt : y ∈ t.roles := (List.takeWhile_sublist _).subset hy
  by_contra hin
  have hin' : y.inEntry e = true := by simpa using hin
  have hne : y ≠ .slot e := by
    rintro rfl
    exact hdis hy (List.mem_cons_self ..)
  have hpath : e.heightPath <+: y.path := by
    simpa [Role.inEntry, hne, List.isPrefixOf_iff_prefix] using hin'
  exact hdis hy (List.mem_cons_of_mem _ (List.mem_append_left _ (mem_under_of_inEntry he hyt hpath)))

-- provides: U1, D1.2g item 1 (G-012; consumers U3 L7.5a, L7.5d, U5 L8.8f): the prefix of an
-- entry and its slot precede every other role inside the entry.
theorem prefix_slot_before_inEntry {t : Forest} {e : EntryAddr} (he : e ∈ t.entryAddrs)
    {x : Role} (hx : x ∈ t.roles) (hin : x.inEntry e = true) (hne : x ≠ .slot e) :
    Packet.prefixRoles t e ++ [.slot e] <+: Packet.rolesBefore t x := by
  obtain ⟨post, hroles, -⟩ := roles_entry he
  have hxP : x ∉ Packet.prefixRoles t e := fun h => by
    have h1 := not_inEntry_of_mem_prefix he h
    rw [hin] at h1
    exact absurd h1 (by decide)
  unfold Packet.rolesBefore
  rw [hroles, takeWhile_append_of_forall]
  · simp only [List.takeWhile_cons, bne_iff_ne, ne_eq, Ne.symm hne, not_false_eq_true,
      if_true]
    exact ⟨_, by rw [List.append_assoc]; rfl⟩
  · intro a ha
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    exact hxP ha

-- provides: U1, D1.2g item 3 (G-012): a role at an earlier position lies before a later one.
theorem mem_rolesBefore_of_lt {t : Forest} {i j : Nat} {x y : Role} (hi : t.roles[i]? = some x)
    (hj : t.roles[j]? = some y) (hij : i < j) : x ∈ Packet.rolesBefore t y :=
  mem_takeWhile_ne_of_lt (roles_nodup t) hi hj hij

end Tree

namespace Closure

/-- G-012 (corrects the hypothesis `hout` of U2 D3.1e `moves_spec`, `applyMoves_litCap_addr`,
U3 L7.5a `frame_repair` and the conclusion of U3 L4.3c `repair_moves_outside`): no move lies inside
the *current* height of the marked entry. Move `idx` acts on the expression produced by the moves
before it, so its column is compared with `b`'s address at that time, `moveAddr (ms.take idx) b`.
The blueprint's `∀ m ∈ ms, ¬ b.heightPath <+: m.col.path` compares the original `b` with
current-coordinate columns and misses a move inside `B` after an outer move has relocated `b`
(counterexample in `blueprint/repairs/G-012.md` §2.5). -/
def MovesOutside (ms : List Move) (b : EntryAddr) : Prop :=
  ∀ idx (h : idx < ms.length), ¬ (moveAddr (ms.take idx) b).heightPath <+: (ms[idx]).col.path

-- provides: U2, D3.1e item 2, corrected (G-012): `moves_spec` with `MovesOutside` for `hout`.
-- The U2 proof (D3.1e proof item 5) already argues in current coordinates.
theorem moves_spec_cur {E : Forest} (hE : Scan.InL E) (w : AdmCap E) (b : EntryAddr)
    (hb : b.heightPath <+: w.col.path) (hout : MovesOutside w.moves b) :
    RepairList (E.truncAfter b) b w.moves ∧
    (moveAddr w.moves b).col.num 0 = b.col.num 0 ∧
    (∀ X, applyMoves ((E.truncAfter b).setHeight b X) w.moves =
      (applyMoves (E.truncAfter b) w.moves).setHeight (moveAddr w.moves b) X) ∧
    (applyMoves (E.truncAfter b) w.moves).heightAt (moveAddr w.moves b) = E.heightAt b ∧
    w.H = (applyMoves (E.truncAfter b) w.moves).setHeight (moveAddr w.moves b)
      ((w.H.heightAt (moveAddr w.moves b)).getD Tree.empty) := by sorry

-- provides: U2, D3.1e item 4, corrected (G-012): `applyMoves_litCap_addr` with `MovesOutside`.
-- The U2 proof (D3.1e proof item 6, induction on `q`) already argues in current coordinates.
theorem applyMoves_litCap_addr_cur {E : Forest} (hH : Scan.CondH E) (w : AdmCap E)
    {b : EntryAddr} (hb : b.heightPath <+: w.col.path) (hout : MovesOutside w.moves b) :
    ∀ q, q ≤ w.moves.length →
      IsUpward E ⟨(moveAddr (w.moves.take q) b).heightPath ++
          w.col.path.drop b.heightPath.length, w.col.col⟩ w.cut w.par ∧
      applyMoves (litCap E w.col w.cut w.par) (w.moves.take q) =
        litCap E ⟨(moveAddr (w.moves.take q) b).heightPath ++
          w.col.path.drop b.heightPath.length, w.col.col⟩ w.cut w.par ∧
      ((E.colAt ⟨(moveAddr (w.moves.take q) b).heightPath ++
          w.col.path.drop b.heightPath.length, w.col.col⟩).getD []).take w.cut =
        ((E.colAt w.col).getD []).take w.cut := by sorry

-- provides: U2, D3.1d item 1 rep clause, restricted (G-012 verification): representatives commute
-- with `χ` at the columns of `w.H`. `origin_spec_full` states this clause for every `ColAddr c`,
-- which is false: for a cap with a move, an address `c` under the closing slot has that slot as
-- a container on its stack, `χ` is `none` there and `anchorD` returns the moved slot, not
-- `U_⟨w.col, w.cut⟩` (counterexample in `blueprint/repairs/verification/G-012.md` §3.2). The U2
-- proof (D3.1d proof item 2, "χ maps the stack of `c` onto the stack of `c'`") is the proof of this
-- restricted form: the closing slot has empty height, so it contains no column of `w.H`.
theorem origin_rep_of_mem {E : Forest} (hE : Scan.InL E) (w : AdmCap E) {c c' : ColAddr}
    (hc : Role.ord c ∈ w.H.roles) (h : w.origin (.ord c) = some (.ord c')) :
    ∀ q, q < c.num 0 →
      (c.rep 0 q).map (fun ov => (Packet.anchorD E (some w) ov.1, Packet.anchorD E (some w) ov.2)) =
        c'.rep 0 q := by sorry

end Closure

namespace Packet

open Hier

-- provides: U3, L4.3c, corrected (G-012): `repair_moves_outside` in current coordinates. The U3
-- proof (L4.3c steps 1-5) takes the first move inside the current height `b_idx`; read that way it
-- proves exactly this.
theorem repair_moves_outside_cur {rk : SrcRecord} (h : rk.Admitted) {c : ColAddr} {k p : Nat}
    (hfd : rk.firstDiff = .capAt c k p) (w : Closure.AdmCap rk.E)
    (hw : w.col = c ∧ w.cut = k ∧ w.par = p) : Closure.MovesOutside w.moves rk.b := by sorry

/-! ## L7.5a-1, L7.5a-2: the origin of the moved marked entry -/

-- provides: U3, L7.5a-1 (G-012): a repair step that retains `e` (or a container of `e`) is undone
-- by the backward index map, on `U_e` and on `A_{e.col}`.
theorem mapEntry_bwd_fwd {K : Forest} {e : EntryAddr} {m : Closure.Move}
    (h : Closure.RepairStepOK K e m) :
    m.mapEntry m.bwdIdx (m.mapEntry m.fwdIdx e) = e ∧
      m.mapRole m.bwdIdx (m.mapRole m.fwdIdx (.ord e.col)) = .ord e.col := by
  obtain ⟨col, -, hij, -, -, -, hret⟩ := h
  rcases hret with hret | ⟨ρ, hρ⟩
  · -- the retained entry is `e` itself: `e.col = m.col`, `e.idx = m.j`
    subst hret
    have hp : ∀ g : Nat → Nat, m.mapPath g m.col.path = m.col.path := by
      intro g; unfold Closure.Move.mapPath; simp
    have hc : (⟨m.col.path, m.col.col⟩ : ColAddr) = m.col := rfl
    refine ⟨?_, ?_⟩
    · simp only [Closure.Move.mapEntry, hp, hc, if_true]
      congr 1
      simp only [Closure.Move.fwdIdx, Closure.Move.bwdIdx]
      split <;> split <;> omega
    · simp only [Closure.Move.mapRole, hp]
  · -- the retained entry contains `e.col`: `e.col.path = m.col.path ++ (m.col.col, m.j) :: ρ`
    obtain ⟨⟨π, cc⟩, idx⟩ := e
    simp only [EntryAddr.heightPath, List.append_assoc, List.singleton_append] at hρ
    subst hρ
    have hmp : ∀ (g : Nat → Nat) (x : Nat),
        m.mapPath g (m.col.path ++ (m.col.col, x) :: ρ) = m.col.path ++ (m.col.col, g x) :: ρ := by
      intro g x; unfold Closure.Move.mapPath; simp
    have hne : ∀ x : Nat, (⟨m.col.path ++ (m.col.col, x) :: ρ, cc⟩ : ColAddr) ≠ m.col := by
      intro x h
      have h' := congrArg (fun c : ColAddr => c.path.length) h
      simp at h'
    have hji : m.bwdIdx (m.fwdIdx m.j) = m.j := by
      simp only [Closure.Move.fwdIdx, Closure.Move.bwdIdx]
      split <;> split <;> omega
    refine ⟨?_, ?_⟩
    · simp only [Closure.Move.mapEntry, hmp, if_neg (hne _), hji]
    · simp only [Closure.Move.mapRole, hmp, hji]

-- provides: U3, L7.5a-1 (G-012): along a repair list for `b`, undoing the moves (last first)
-- sends the moved slot and host column back to `U_b` and `A_{b.col}`.
theorem foldr_bwd_moveAddr {K : Forest} {b : EntryAddr} {ms : List Closure.Move}
    (h : Closure.RepairList K b ms) :
    ms.foldr (fun m y => m.mapRole m.bwdIdx y) (.slot (Closure.moveAddr ms b)) = .slot b ∧
      ms.foldr (fun m y => m.mapRole m.bwdIdx y) (.ord (Closure.moveAddr ms b).col) =
        .ord b.col := by
  induction ms using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton ms m ih =>
    -- the prefix is a repair list, and the last step retains the current marked entry
    have hpre : Closure.RepairList K b ms := by
      intro idx hidx
      have h' := h idx (by simp; omega)
      rwa [List.take_append_of_le_length (by omega), List.getElem_append_left hidx] at h'
    have hlast : Closure.RepairStepOK (Closure.applyMoves K ms) (Closure.moveAddr ms b) m := by
      have h' := h ms.length (by simp)
      simpa using h'
    obtain ⟨ih1, ih2⟩ := ih hpre
    obtain ⟨hb1, hb2⟩ := mapEntry_bwd_fwd hlast
    have hma : Closure.moveAddr (ms ++ [m]) b = m.mapEntry m.fwdIdx (Closure.moveAddr ms b) := by
      show Closure.moveAddrBody _ _ = _
      simp [Closure.moveAddrBody, List.foldl_append]; rfl
    have hcol : ∀ (g : Nat → Nat) (e : EntryAddr),
        (m.mapEntry g e).col = ⟨m.mapPath g e.col.path, e.col.col⟩ := by
      intro g e
      unfold Closure.Move.mapEntry
      dsimp only
      split <;> rfl
    rw [hma, List.foldr_append, List.foldr_append]
    constructor
    · simp only [List.foldr_cons, List.foldr_nil, Closure.Move.mapRole, hb1]
      exact ih1
    · have hb2' : m.mapRole m.bwdIdx (.ord (m.mapEntry m.fwdIdx (Closure.moveAddr ms b)).col) =
          .ord (Closure.moveAddr ms b).col := by
        rw [hcol]; exact hb2
      simp only [List.foldr_cons, List.foldr_nil, hb2']
      exact ih2

-- provides: U3, L7.5a-2 (G-012; consumers L7.5a, L7.5d `marked_slot`, `marked_host`)
theorem origin_moveAddr {E : Forest} (hE : Scan.InL E) (w : Closure.AdmCap E) {b : EntryAddr}
    (hbc : b.heightPath <+: w.col.path) (hout : Closure.MovesOutside w.moves b) :
    w.origin (.slot (Closure.moveAddr w.moves b)) = some (.slot b) ∧
      w.origin (.ord (Closure.moveAddr w.moves b).col) = some (.ord b.col) := by
  obtain ⟨h1, h2⟩ := foldr_bwd_moveAddr (Closure.moves_spec_cur hE w b hbc hout).1
  have hne : (Role.slot b) ≠ .slot ⟨w.col, w.cut⟩ := by
    intro h
    have hb : b = ⟨w.col, w.cut⟩ := Role.slot.inj h
    have hlen := hbc.length_le
    simp [hb, EntryAddr.heightPath] at hlen
  constructor
  · show Closure.originBody w _ = _
    simp only [Closure.originBody, h1, if_neg hne]
  · show Closure.originBody w _ = _
    simp only [Closure.originBody, h2]
    simp

-- provides: U3, L7.5a-3 (G-012; consumers L7.5a, L7.5d `marked_mem`, `stop_inside`,
-- `marked_prefix`): the moved marked entry `bm` is an entry of `w.H`; `w.H` is the literal cap at
-- the relocated column `c'` inside `bm`; the stopping column and the closing slot lie inside
-- `bm`; every role of `P(w.H, bm)` has an origin.
theorem marked_entry_cap {E : Forest} (hE : IsStd E) (w : Closure.AdmCap E) {b : EntryAddr}
    (hb : b ∈ E.entryAddrs) (hbc : b.heightPath <+: w.col.path)
    (hout : Closure.MovesOutside w.moves b) :
    Closure.moveAddr w.moves b ∈ w.H.entryAddrs ∧
    w.H = Closure.litCap E ⟨(Closure.moveAddr w.moves b).heightPath ++
      w.col.path.drop b.heightPath.length, w.col.col⟩ w.cut w.par ∧
    (∀ sd, Scan.stopData w.H = some sd →
      sd.col = ⟨(Closure.moveAddr w.moves b).heightPath ++ w.col.path.drop b.heightPath.length,
        w.col.col⟩ ∧
      (Role.ord sd.col).inEntry (Closure.moveAddr w.moves b) = true ∧
      (Role.slot (Scan.closingSlot sd)).inEntry (Closure.moveAddr w.moves b) = true) ∧
    ∀ x ∈ prefixRoles w.H (Closure.moveAddr w.moves b), (w.origin x).isSome := by
  have hL : Scan.InL E := Closure.std_inL hE
  obtain ⟨-, -, -, hG, hH⟩ := Closure.moves_spec_cur hL w b hbc hout
  -- `bm` is an entry of `w.H` (U2 `moves_spec` items 4-5, U1 `setHeight_basic`)
  have hbE : (E.heightAt b).isSome := by
    have h := (Tree.mem_entryAddrs_iff _ _).mp hb
    simpa [Tree.heightAt] using h
  have hbmG : Closure.moveAddr w.moves b ∈
      (Closure.applyMoves (E.truncAfter b) w.moves).entryAddrs := by
    rw [Tree.mem_entryAddrs_iff]
    have h : ((Closure.applyMoves (E.truncAfter b) w.moves).heightAt
        (Closure.moveAddr w.moves b)).isSome := by rw [hG]; exact hbE
    simpa [Tree.heightAt] using h
  have hmem : Closure.moveAddr w.moves b ∈ w.H.entryAddrs := by
    rw [hH]; exact (Tree.setHeight_basic _ _ _ hbmG).1
  -- `w.H` is the literal cap at the relocated column (U2 `applyMoves_litCap_addr`, all moves)
  obtain ⟨hup', hlit, -⟩ := Closure.applyMoves_litCap_addr_cur hL.2.2.1 w hbc hout w.moves.length le_rfl
  rw [List.take_length] at hup' hlit
  have hwH : w.H = Closure.litCap E ⟨(Closure.moveAddr w.moves b).heightPath ++
      w.col.path.drop b.heightPath.length, w.col.col⟩ w.cut w.par := hlit
  -- the stopping column and the closing slot lie inside `bm` (U2 T3.8c `stopData_litCap`)
  have hin : ∀ sd, Scan.stopData w.H = some sd →
      sd.col = ⟨(Closure.moveAddr w.moves b).heightPath ++ w.col.path.drop b.heightPath.length,
        w.col.col⟩ ∧
      (Role.ord sd.col).inEntry (Closure.moveAddr w.moves b) = true ∧
      (Role.slot (Scan.closingSlot sd)).inEntry (Closure.moveAddr w.moves b) = true := by
    intro sd hsd
    rw [hwH, Closure.stopData_litCap hup'] at hsd
    obtain rfl := Option.some.inj hsd
    refine ⟨rfl, ?_, ?_⟩ <;>
      simp [Role.inEntry, Role.path, Scan.closingSlot, List.isPrefixOf_iff_prefix]
  refine ⟨hmem, hwH, hin, ?_⟩
  -- origins on the prefix: `none` only at the closing slot (U2 `origin_spec_full` item 2), which
  -- is inside `bm`, hence not in `P(w.H, bm)` (D1.2g item 2)
  intro x hx
  by_contra hno
  have hxH : x ∈ w.H.roles := (List.takeWhile_sublist _).subset hx
  obtain ⟨sd, hsd, rfl⟩ := ((Closure.origin_spec_full hL w).2.1 x hxH).mp
    (Option.not_isSome_iff_eq_none.mp hno)
  have h1 := Tree.not_inEntry_of_mem_prefix hmem hx
  rw [(hin sd hsd).2.2] at h1
  exact absurd h1 (by decide)

/-! ## L7.5d-1 … L7.5d-4: glue of `cap_package` -/

/-- L7.5d-1 (G-012): value separation in its exact form. A configuration is strictly increasing
along the reading order, so a chart `f` through which a configuration `a ∘ f` is read is
injective on the roles. -/
theorem injOn_of_config {P : Prims.{u}} {E : Forest} {V : Type} {f : Role → V}
    {a : V → Ordinal.{u}} (h : IsConfig P E (a ∘ f)) : Set.InjOn f {x | x ∈ E.roles} := by
  intro x hx y hy hxy
  by_contra hne
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
  have hij : i ≠ j := by
    rintro rfl
    exact hne (Option.some.inj (hi.symm.trans hj))
  rcases Nat.lt_or_gt_of_ne hij with h1 | h1
  · have h2 := isConfig_before h ⟨i, j, hi, hj, h1⟩
    simp [Function.comp, hxy] at h2
  · have h2 := isConfig_before h ⟨j, i, hj, hi, h1⟩
    simp [Function.comp, hxy] at h2

/-- L7.5d-2 helper (G-012): `takeWhile (· != x)` stops inside a prefix that contains `x`. -/
theorem takeWhile_ne_take_append {x : Role} :
    ∀ (l r : List Role) (m : Nat), x ∈ l.take m →
      (l.take m ++ r).takeWhile (· != x) = l.takeWhile (· != x)
  | [], _, _, h => by simp at h
  | _ :: _, _, 0, h => by simp at h
  | y :: l, r, m + 1, h => by
    by_cases hy : y = x
    · subst hy; simp
    · have h' : x ∈ l.take m := by
        simp only [List.take_succ_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hy
        · exact h
      simp only [List.take_succ_cons, List.cons_append, List.takeWhile_cons]
      simp [hy, takeWhile_ne_take_append l r m h']

-- provides: U3, L7.5d-2 (G-012): the literal cap keeps `A_c` and everything before it.
theorem litCap_rolesBefore_col {E : Forest} {c : ColAddr} {k p : Nat}
    (hup : Closure.IsUpward E c k p) :
    Role.ord c ∈ (Closure.litCap E c k p).roles ∧
      rolesBefore (Closure.litCap E c k p) (.ord c) = rolesBefore E (.ord c) := by
  have hcol : ∃ col, E.colAt c = some col ∧ k ≤ col.length := by
    unfold Closure.IsUpward at hup
    split at hup
    · rename_i col hc
      refine ⟨col, hc, ?_⟩
      split at hup
      · rename_i hk
        exact (List.getElem?_eq_some_iff.mp hk).1.le
      · omega
    · exact hup.elim
  obtain ⟨col, hc, hk⟩ := hcol
  have hcE : c ∈ E.colAddrs := (Tree.mem_colAddrs_iff _ _).mpr (by simp [hc])
  have hkp : k ≤ (Scan.parents E c).length := by simp [Scan.parents, hc, hk]
  obtain ⟨⟨m, hm⟩, -⟩ := Closure.litCap_spec (p := p) hcE hkp
  have hmem : Role.ord c ∈ (Closure.litCap E c k p).roles :=
    Scan.stopData_col_mem (Closure.stopData_litCap hup)
  refine ⟨hmem, ?_⟩
  have h1 : Role.ord c ∈ E.roles.take m := by
    rw [hm] at hmem
    simpa using hmem
  unfold rolesBefore
  rw [hm]
  exact takeWhile_ne_take_append _ _ m h1

/-- L7.5d-3 (G-012): `capRole` is the origin wherever the origin is defined. -/
theorem capRole_of_origin {E : Forest} (w : Closure.AdmCap E) {x y : Role}
    (h : w.origin x = some y) : capRole w x = y := by
  simp [capRole, h]

/-- L7.5d-4 (G-012): a value of `capRole` other than the cap slot `U_⟨w.col, w.cut⟩` is an origin. -/
theorem origin_of_capRole_ne {E : Forest} (w : Closure.AdmCap E) {x y : Role}
    (h : capRole w x = y) (hne : y ≠ .slot ⟨w.col, w.cut⟩) : w.origin x = some y := by
  unfold capRole at h
  cases ho : w.origin x with
  | none => rw [ho] at h; exact absurd h.symm hne
  | some z => rw [ho] at h; simp only [Option.getD_some] at h; rw [h]

/-! ## L7.5a: `frame_repair` with the corrected hypothesis -/

/-- L7.5a helper (G-012): a role before `y` in `takeWhile` order has an earlier index. -/
theorem exists_lt_of_mem_takeWhile_ne :
    ∀ {l : List Role} {x y : Role}, x ∈ l.takeWhile (· != y) → y ∈ l →
      ∃ i j : Nat, l[i]? = some x ∧ l[j]? = some y ∧ i < j
  | [], _, _, hx, _ => by simp at hx
  | a :: l, x, y, hx, hy => by
    by_cases hay : a = y
    · subst hay; simp at hx
    · simp only [List.takeWhile_cons, bne_iff_ne, ne_eq, hay, not_false_eq_true, if_true,
        List.mem_cons] at hx
      have hy' : y ∈ l := by
        rcases List.mem_cons.mp hy with h | h
        · exact absurd h.symm hay
        · exact h
      rcases hx with rfl | hx
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy'
        exact ⟨0, j + 1, rfl, by simpa using hj, by omega⟩
      · obtain ⟨i, j, hi, hj, hij⟩ := exists_lt_of_mem_takeWhile_ne hx hy'
        exact ⟨i + 1, j + 1, by simpa using hi, by simpa using hj, by omega⟩

-- provides: U3, L7.5a, corrected (G-012): `frame_repair` with `MovesOutside` for `hout`, and the
-- repaired proof (G-012.md §4.5) written out.
theorem frame_repair_cur {E : Forest} (hE : IsStd E) (w : Closure.AdmCap E) {b : EntryAddr}
    (hb : b ∈ E.entryAddrs) (hbc : b.heightPath <+: w.col.path)
    (hout : Closure.MovesOutside w.moves b) :
    let bm := Closure.moveAddr w.moves b
    (frameOf bm).map (capRole w) = frameOf b ∧ capRole w (.slot bm) = .slot b ∧
    (∀ x ∈ prefixRoles w.H bm, capRole w x ∈ prefixRoles E b) ∧
    Set.InjOn (capRole w) {x | x ∈ prefixRoles w.H bm} := by
  intro bm
  have hL : Scan.InL E := Closure.std_inL hE
  obtain ⟨hmem, -, -, horig⟩ := marked_entry_cap hE w hb hbc hout
  obtain ⟨hOs, hOc⟩ := origin_moveAddr hL w hbc hout
  obtain ⟨hinj, -, -, -, -, -, -, hord⟩ := Closure.origin_spec_full hL w
  -- on `P(w.H, bm)` the origin is defined, so `capRole` and `anchorD` are the origin
  have hcr : ∀ x ∈ prefixRoles w.H bm, w.origin x = some (capRole w x) := by
    intro x hx
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (horig x hx)
    rw [hz, capRole_of_origin w hz]
  have hanc : ∀ x ∈ prefixRoles w.H bm, anchorD E (some w) x = capRole w x := by
    intro x hx
    simp [anchorD, Closure.anchorOrigin, hcr x hx]
  have hpre := frameOf_mem_prefix hmem
  -- the host column of `bm` is a column of `w.H`, where the rep clause applies
  have hbmcol : Role.ord bm.col ∈ w.H.roles := (List.takeWhile_sublist _).subset hpre.1
  have hrep := Closure.origin_rep_of_mem hL w hbmcol hOc
  have hmemR : Role.slot bm ∈ w.H.roles :=
    (Tree.mem_roles_iff _ _).mpr ((Tree.mem_entryAddrs_iff _ _).mp hmem)
  refine ⟨?_, capRole_of_origin w hOs, ?_, ?_⟩
  · -- host and the whole list of representatives ("induction through the containers")
    have hnum : bm.col.num 0 = b.col.num 0 := Closure.moveAddr_num _ _
    simp only [frameOf, Frame.map, Frame.mk.injEq]
    refine ⟨capRole_of_origin w hOc, ?_⟩
    unfold ColAddr.reps0
    rw [List.map_filterMap, hnum]
    apply List.filterMap_congr
    intro q hq
    have hq' : q < bm.col.num 0 := by rw [hnum]; exact List.mem_range.mp hq
    rw [← hrep q hq']
    cases hr : bm.col.rep 0 q with
    | none => rfl
    | some ov =>
      have hov : ov ∈ bm.col.reps0 := by
        unfold ColAddr.reps0
        exact List.mem_filterMap.mpr ⟨q, List.mem_range.mpr hq', hr⟩
      obtain ⟨h1, h2⟩ := hpre.2 ov hov
      simp only [Option.map_some, hanc _ h1, hanc _ h2]
  · -- prefix: the origin keeps the reading order (R10 item 8), and D1.2g item 3
    intro x hx
    obtain ⟨i, j, hi, hj, hij⟩ := exists_lt_of_mem_takeWhile_ne hx hmemR
    obtain ⟨i', j', hi', hj', hij'⟩ := hord x (.slot bm) ⟨i, j, hi, hj, hij⟩ (horig x hx)
      (by rw [hOs]; rfl)
    have e1 : anchorD E (some w) x = capRole w x := hanc x hx
    have e2 : anchorD E (some w) (.slot bm) = .slot b := by
      show (w.origin (Role.slot (Closure.moveAddr w.moves b))).getD _ = _
      rw [hOs]
      rfl
    rw [e1] at hi'
    rw [e2] at hj'
    exact Tree.mem_rolesBefore_of_lt hi' hj' hij'
  · -- injective: the origin is injective on `w.H.roles` (R10 item 1)
    intro x hx y hy hxy
    have hxH : x ∈ w.H.roles := (List.takeWhile_sublist _).subset hx
    have hyH : y ∈ w.H.roles := (List.takeWhile_sublist _).subset hy
    exact hinj hxH hyH (by rw [hcr x hx, hcr y hy, hxy])

/-! ## L7.5d: `cap_package`, field by field -/

-- provides: U3, L7.5d (G-012): the proof plan of `cap_package`, written out in Lean. Every field
-- is a projection of a named source (or of a G-012 lemma); the body has no `sorry`.
theorem cap_package_derivation {P : Prims.{u}} (pk : SourcePacket.{u}) (hadm : pk.rk.Admitted)
    (hv : pk.Valid P) {c : ColAddr} {k p : Nat} (hfd : pk.rk.firstDiff = .capAt c k p) :
    Nonempty (CapData P pk) := by
  -- sources: L4.2 `firstDiff_cap`, U2 L3.1 `repair`, T3.2 `std_inL`/`std_condP`
  obtain ⟨hbc, hcE, hup, hKV, hKI, -, hKA, -, -⟩ := firstDiff_cap hadm hfd
  have hstd : IsStd pk.rk.E := hadm.1
  have hL : Scan.InL pk.rk.E := Closure.std_inL hstd
  obtain ⟨w, hwc, hwk, hwp, ⟨sd, hsd, -, -⟩, c₀, hup₀, hwH⟩ :=
    Closure.repair hL (Closure.std_condP hstd) hup hKV hKI hKA
  have hw : w.col = c ∧ w.cut = k ∧ w.par = p := ⟨hwc, hwk, hwp⟩
  -- `ordinary`: U2 T3.8c `litCap_ordinary` at the relocated column; `root`: spine
  have hHL : Scan.InL w.H := w.inL
  have hord : Scan.stepKind w.H = some .ordinary := by
    rw [hwH] at hHL ⊢
    exact Closure.litCap_ordinary hL.2.1 hup₀ hHL.1 hHL.2.1
  obtain ⟨rd, hrd⟩ := Option.isSome_iff_exists.mp (Scan.rootData_of_ordinary hord)
  -- sources: L7.4 `joint_cap`, L7.5 `joint_repair`
  have JC := joint_cap pk hadm hv hfd
  have JR := joint_repair pk hadm hv hfd w hw
  dsimp only at JC JR
  obtain ⟨hKcfg, hκtgt, hκown, -, hown_lt, -, hbelow, -, hholds⟩ := JC
  obtain ⟨hHcfg, -, -, hframe, -, -, -⟩ := JR
  -- the marked entry: L4.3c (corrected), L7.5a (corrected), L7.5a-2, L7.5a-3
  have hbc' : pk.rk.b.heightPath <+: w.col.path := hwc ▸ hbc
  have hout := repair_moves_outside_cur hadm hfd w hw
  have hME := marked_entry_cap hstd w hadm.2.1 hbc' hout
  have hOM := origin_moveAddr hL w hbc' hout
  have hFR := frame_repair_cur hstd w hadm.2.1 hbc' hout
  dsimp only at hFR
  -- the `E`-prefix: U2 D3.1d `admCap_query`, L7.5d-2, D1.2g
  have hT : w.origin (.ord sd.col) = some (.ord c) := by
    have h := (Closure.admCap_query hL w hsd).2.2.2.1
    rwa [hwc] at h
  have hePre : ePrefix pk.rk.E (some w) sd = rolesBefore pk.rk.E (.ord c) := by
    simp [ePrefix, Closure.anchorOrigin, hT]
  have hlit := litCap_rolesBefore_col hup
  have hcapT : capRole w (.ord sd.col) = .ord c := capRole_of_origin w hT
  have hcE' : Role.ord c ∈ pk.rk.E.roles :=
    (Tree.mem_roles_iff _ _).mpr ((Tree.mem_colAddrs_iff _ _).mp hcE)
  have hcin : (Role.ord c).inEntry pk.rk.b = true := by
    simp [Role.inEntry, Role.path, List.isPrefixOf_iff_prefix.mpr hbc]
  have hpre := Tree.prefix_slot_before_inEntry hadm.2.1 hcE' hcin (by simp)
  refine ⟨{
    w := w, sd := sd, rd := rd, nm := capChart pk, nmH := capChart pk ∘ capRole w,
    asg' := pk.asg, ordinary := hord, stop := hsd, root := hrd,
    qsize := (query_size_bound hadm hfd w hw hsd).2.2,
    nm_tgt := hκtgt, nm_owner := hκown,
    pre_sub := fun y hy => by rw [hePre]; exact hpre.subset (List.mem_append_left _ hy),
    nm_inj := ?_, nmH_inj := injOn_of_config hHcfg,
    compat := fun x _ y h => by simp only [Function.comp, capRole_of_origin w h],
    asg_old := fun _ _ => rfl, config := hHcfg,
    ePrefix_holds := ?_, ePrefix_below := ?_,
    marked_mem := hME.1, marked_slot := hOM.1, marked_host := hOM.2,
    marked_prefix := ?_, marked_frame := congrArg Frame.reps hframe,
    stop_inside := (hME.2.2.1 sd hsd).2.1,
    owner_lt := ?_,
    readmit := fun n H' hexp habove => (repair_output hadm hfd w hw hexp habove).2.2.2.2 }⟩
  · -- `nm_inj`: L7.4 (a) and L7.5d-1 on `K`, since `ePrefix = rolesBefore K A_c ⊆ K.roles`
    intro y hy y' hy' h
    have h1 : y ∈ rolesBefore (Closure.litCap pk.rk.E c k p) (.ord c) := by
      rw [hlit.2, ← hePre]; exact hy
    have h2 : y' ∈ rolesBefore (Closure.litCap pk.rk.E c k p) (.ord c) := by
      rw [hlit.2, ← hePre]; exact hy'
    exact injOn_of_config hKcfg ((List.takeWhile_sublist _).subset h1)
      ((List.takeWhile_sublist _).subset h2) h
  · -- `ePrefix_holds`: L7.4 (f) and N3.1 `baseHolds_map`
    rw [hePre]
    exact (baseHolds_map P (capChart pk) _ pk.asg).mp hholds
  · -- `ePrefix_below`: L7.4 (e), `rolesBefore K A_c = rolesBefore E A_c`, `capRole T = A_c`
    intro y hy
    rw [hePre, ← hlit.2] at hy
    show pk.asg (capChart pk y) < pk.asg (capChart pk (capRole w (.ord sd.col)))
    rw [hcapT]
    exact hbelow y hy
  · -- `marked_prefix`: L7.5a (prefix clause) and L7.5a-3 (origins defined on the prefix)
    intro x hx
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hME.2.2.2 x hx)
    exact ⟨z, capRole_of_origin w hz ▸ hFR.2.2.1 x hx, hz⟩
  · -- `owner_lt`: L7.4 (d)
    show pk.asg pk.owner < pk.asg (capChart pk (capRole w (.ord sd.col)))
    rw [hcapT]
    exact hown_lt

/-! ## L7.5e: what U5 L8.8f derives from `CapData` -/

namespace CapData

variable {P : Prims.{u}} {pk : SourcePacket.{u}}

-- provides: U3, L7.5e (G-012; consumer U5 L8.8f): the marked slot, its host column and the
-- prefix `P(H, a')` are pre-stop roles of `H`, so `compat` applies to them.
theorem preStop_marked (D : CapData P pk) :
    Role.slot (Closure.moveAddr D.w.moves pk.rk.b) ∈ rolesBefore D.w.H (.ord D.sd.col) ∧
    Role.ord (Closure.moveAddr D.w.moves pk.rk.b).col ∈ rolesBefore D.w.H (.ord D.sd.col) ∧
    ∀ x ∈ prefixRoles D.w.H (Closure.moveAddr D.w.moves pk.rk.b),
      x ∈ rolesBefore D.w.H (.ord D.sd.col) := by
  have hT : Role.ord D.sd.col ∈ D.w.H.roles := Scan.stopData_col_mem D.stop
  have hpre := Tree.prefix_slot_before_inEntry D.marked_mem hT D.stop_inside (by simp)
  refine ⟨hpre.subset (by simp), hpre.subset (List.mem_append_left _
    (Tree.stack_mem_prefix D.marked_mem).1), fun x hx => hpre.subset (List.mem_append_left _ hx)⟩

-- provides: U3, L7.5e (G-012; consumer U5 L8.8f "two derived equalities")
theorem nmH_slot (D : CapData P pk) :
    D.nmH (.slot (Closure.moveAddr D.w.moves pk.rk.b)) = pk.owner := by
  rw [D.compat _ D.preStop_marked.1 _ D.marked_slot, D.nm_owner]

-- provides: U3, L7.5e (G-012; consumer U5 L8.8f "two derived equalities")
theorem nmH_host (D : CapData P pk) (hadm : pk.rk.Admitted) (hv : pk.Valid P) :
    D.nmH (.ord (Closure.moveAddr D.w.moves pk.rk.b).col) = pk.host := by
  rw [D.compat _ D.preStop_marked.2.1 _ D.marked_host,
    D.nm_tgt _ (Tree.stack_mem_prefix hadm.2.1).1]
  exact hv.2.2.1

-- provides: U3, L7.5e (G-012; consumer U5 L8.8f steps 5(6), 6): prefix names of the repaired
-- context are target-prefix names.
theorem nmH_prefix (D : CapData P pk) :
    ∀ x ∈ prefixRoles D.w.H (Closure.moveAddr D.w.moves pk.rk.b),
      ∃ y ∈ prefixRoles pk.rk.E pk.rk.b, D.w.origin x = some y ∧ D.nmH x = pk.tgtChart y := by
  intro x hx
  obtain ⟨y, hy, ho⟩ := D.marked_prefix x hx
  exact ⟨y, hy, ho, by rw [D.compat x (D.preStop_marked.2.2 x hx) y ho, D.nm_tgt y hy]⟩

-- provides: U3, L7.5e (G-012; consumer U5 L8.8f steps 5(6), 6)
theorem nmH_prefix_low (D : CapData P pk) :
    ∀ x ∈ prefixRoles D.w.H (Closure.moveAddr D.w.moves pk.rk.b), D.nmH x ∈ pk.lowNames := by
  intro x hx
  obtain ⟨y, hy, -, he⟩ := D.nmH_prefix x hx
  rw [he]
  unfold SourcePacket.lowNames
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨y, hy, rfl⟩))

-- provides: U3, L7.5e (G-012; consumer U5 L8.8f step 4): `α(U_{a'}) = u`.
theorem val_slot (D : CapData P pk) :
    D.asg' (D.nmH (.slot (Closure.moveAddr D.w.moves pk.rk.b))) = pk.asg pk.owner := by
  rw [D.nmH_slot]
  exact D.asg_old _ (Or.inr rfl)

-- provides: U3, L7.5e (G-012; consumer U5 L8.8f step 4): `α(A_{a'.col}) = ρ`.
theorem val_host (D : CapData P pk) (hadm : pk.rk.Admitted) (hv : pk.Valid P) :
    D.asg' (D.nmH (.ord (Closure.moveAddr D.w.moves pk.rk.b).col)) = pk.asg pk.host := by
  rw [D.nmH_host hadm hv]
  exact D.asg_old _ (Or.inl (Descent.lowNames_spec pk hadm hv).1)

end CapData

end Packet

end BTBMS
