# U2 closure-cofinality — blueprint (paper §3, txt:252-646)

**Unit:** U2. **Namespace:** `BTBMS.Closure`. **Lean signatures:** `blueprint/lean/U2.lean`
(appended after `blueprint/lean/Spine.lean`; typechecks with only `sorry` warnings, command in §h of
the spine with this unit's file). **Owned ledger nodes:** D3.1 L3.1 T3.2 D3.3 L3.4 L3.5 L3.6 L3.7
T3.8, plus the spine's new nodes D3.1a, L3.1a, T3.2a.

## Overview

U2 proves the two finite gates of the S-5 abstract theorem (spine §a, N5.1):

- **(C) closure** `Closure.std_inL` (T3.2): standard expressions lie in `L = V∧I∧H∧A∧S`, `L` is
  closed under safe prefixes and defined operations, P is preserved when present (P is *not* part
  of `L`, S-6), and every defined operation on a nonempty V∧I input strictly decreases it.
- **(F) cofinality** `Closure.cofinal`, `Closure.cofinal_bound` (T3.8): for standard `B` and any
  `E ∈ L` with `B < E`, some approximant `E[n]` covers `B`, with `1 ≤ n ≤ µ(B)+1` when `E` ends
  in a nonempty column. This is used for admissible caps in §8.5 Case 3.

Organization (dependency order of the entries below):

1. **Definitions** (D3.1, D3.1a–c): profiles, tower keys, literal caps and their word positions,
   moves, repair lists, admissible caps and their origin map χ. All have real Lean bodies.
2. **Word library, U2 half** (S-6): the two-position word fact (T3.2b), the word criterion
   (L3.4), delayed change (L3.7), reset/head-cursor identities (T3.2p). All pure list lemmas,
   bounded-tested (scratch/blueprint/U2/wordlemmas_test.py, 0 failures).
3. **Profile and repair** (L3.1, L3.1a–h, N2.1): `V∧I∧H∧P ⇒ S` (G-002 repaired), S for upward
   caps, the interval fact, and repair of an upward cap with decorated A into an `AdmCap`.
4. **Kernels** (D3.3, D3.3a–c, L3.5): the one-period kernel `F_E`, context `C_E`, the iterate
   identity `E[n] = C_E(F_E^n(∅))`, the word forms `w(F_E(X)) = P⌢Σ(w X)`, the filling identity
   (1) and the cancellation identity (2). The kernel is checked against the locked `expand` by
   `#eval` on body, owner, consumed-root and side-height examples (scratch/blueprint/U2/eval*.lean).
5. **Closure** (T3.2, T3.2b–w, T3.2a): safe prefixes; the ordinary step through a phase
   classification of output addresses (T3.2i, shared with T3.8 and, as proposed, with U3's
   occurrence maps); special steps; seeds; the agreement `IsStd ↔` paper's Std (G-001).
6. **Cofinality** (T3.8, T3.8a–m, L3.6, L3.4f, N2.2): cofinality is reduced to *kernel success*
   `KS(B)` for every upward literal L cap of `B`; `KS` is proved by induction on a generation
   witness of `B`. The ordinary induction step (R-2) is decomposed into 19 sub-lemmas
   T3.8la–T3.8ls by cut location (head query part, seam, restored suffix, phase material) and
   selected-root position (`ρ > s_φ`, `ρ = s_φ`, `r < ρ < s_φ`, `ρ ≤ r`).

## Conventions of this unit

Spine conventions §c.0 apply. Additionally:

- **Ordinary data.** For an ordinary input `A` with `stopData A = some sd`, `rootData A = some rd`:
  `ℓ = sd.depth`, `t = sd.t`, `r = sd.r`, `Q = sd.Q`, `m = |Q|`, root layer `j = rd.layer`, root
  index `ι = rd.idx`, root column `R = rootCol A rd`, root cursor `c_A = rd.cursor` (the paper's
  `c`), `U = R[c_A:] = unconsumed A rd`, period `d = t − r = period sd`, hole depth
  `δ = ℓ − j = holeDepth sd rd`. `F_A = kernel A sd rd`, `C_A = context A sd`.
  `A_n` is the output of `expand A n`.
- **Phases.** `s_i = r + i·d`, `τ_i = T_{r,id} = shift r (i*d)`, `κ_i = kappa r d i` on keys.
  The output `A_n = C_A(F_A^n(∅))` consists of *layers* `1…n` (layer `i` is the `i`-th kernel from
  the outside). Layer `i` contains head `i` (column number `s_i`): its query part `τ_{i−1}(Q)` has
  *phase* `i−1`, its restored part (entries of `U` with heights `τ_i`) and the body have phase `i`
  (T3.2i; `phaseOff`).
- **Caps.** A cap of a target `B` is written `(col, k, ρ)`, i.e. `K = litCap B col k ρ`; its cut
  position is `π_K = capPos B col k`, its complete local suffix is `Y_K = localSuffix B col`.
  In Lean the column address is `c`; in this document the root cursor is `c_A` to avoid the clash.
- **Words.** `w(·)` is `Scan.word`, `µ` is `Scan.mu`, `D_e` is `depthShift e` mapped over a word.
  For words, `<` is Mathlib's lexicographic order (proper prefix smaller). "`X'` first decreases
  at `a`" is `FirstDec X X' a`.
- **Bodies of spine names.** The spine keeps `profile`, `litCap`, `applyMove`, `MovesValid`,
  `RepairList`, `moveAddr`, `AdmCap.origin` with `sorry` bodies owed by U2. U2.lean gives
  `profileBody`, `litCapBody`, … with real bodies and bridge theorems `profile_eq_body`, … (proved
  by `rfl` once the bodies are moved into the spine declarations at T-018), the pattern U1 uses.
- **Standing hypotheses (G-002).** Every lemma about profiles, towers, Γ-bounds and repairs
  carries V, I, H of the expression explicitly; none relies on P alone.

---

## Entries

### D3.1 Profile, condition P, literal and upward caps   (paper: txt:254-262)
**Fidelity:** as in paper (totalized: `profile ∅ = ⊥`, `litCap` is the identity off the tree).
**Statement.**
1. `profile H : WithBot (Nat ×ₗ Nat)`. `profile ∅ = ⊥` (the paper's `(−1,0)`). For `H ≠ ∅`: put
   `H_0 = H`; while the first entry of the first column of `H_k` has a nonempty height, let
   `H_{k+1}` be that height; let `d` be the number of steps. If the first column of `H_d` is
   `(p,∅) :: rest`, then `profile H = (d, 1 + |takeWhile (parent = p) rest|)`; if `H_d`'s first
   column is empty (impossible under I, see L3.1b), `profile H = (d, 0)`. Order: lexicographic,
   `⊥` least. (Lean: `profileAux`, `profileBody`; spine `profile`.)
2. `CondP E` (spine, real body): at every owner return `(e0, e)` (spine `IsOwnerReturn`),
   `profile J < profile H`, with `H`, `J` the heights at `e0`, `e`.
3. `litCap E c k p`, `c = ⟨[(c_0,i_0),…,(c_{m−1},i_{m−1})], j⟩`: at every level `d < m` keep columns
   `0…c_d` of that forest, in column `c_d` keep entries `0…i_d` and recurse into the height of
   entry `i_d`; at `c`'s own level keep columns `0…j`, and replace column `j` by its first `k`
   entries (complete heights) followed by `(p, ∅)`. If `E.colAt c = none`, the result is `E`.
   (Lean: `litCapAux`, `litCapBody`.)
4. `IsUpward E c k p` (spine, real body): `E.colAt c = some col` and either `col[k]` exists with
   parent `< p`, or `k = |col|`.
**Proof.** Definitions; bridges `profile_eq_body`, `litCap_eq_body` are `rfl` after T-018.
**Uses:** —
**Lean:** `Closure.profileAux`, `profileBody`, `profile_eq_body`, `litCapAux`, `litCapBody`,
`litCap_eq_body` (spine: `profile`, `CondP`, `litCap`, `IsUpward`). Planned file
`Closure/Profile.lean` (profile, P) and `Closure/Caps.lean` (caps).
**Integration note:** At integration, SCR-U2-2: the body definitions `profileAux`, `profileBody`, `litCapAux`, `litCapBody` moved verbatim into `Spine.lean`; they remain U2-owned, and the bridges hold by `rfl`.
**Difficulty:** S — structural recursions; checked by `#eval` (profile of `[[(1,[[(2,∅),(2,∅),(1,∅)]])]]` is `(1,2)`).
**Testable:** yes: compare with `profile` and `caps` of checks/python/finite_model.py.

### D3.1b Tower keys   (paper: new; txt:269-272)
**Fidelity:** new (makes the paper's `Γ(J)` a concrete key).
**Statement.** `towKeyAt k 0 m = node [replicate m ((true,k), ∅)]`,
`towKeyAt k (d+1) m = node [[((true,k), towKeyAt (k+1) d m)]]`, `towKey d m = towKeyAt 0 d m`.
For `π(J) = (d, m)`, the paper's greatest I-legal upward literal cap `Γ(J)` (txt:269-271) has
relative key `towKey d (m+1)` at the host of `J`.
**Proof.** Definition.
**Uses:** —
**Lean:** `Closure.towKeyAt`, `towKey`; `Closure/Profile.lean`.
**Difficulty:** S — two-clause recursion.
**Testable:** no (definition).

### D3.1c Cap positions and local suffixes   (paper: new; txt:440, 460, 478)
**Fidelity:** new (word-position bookkeeping the paper leaves implicit).
**Statement.**
1. `colDepth c = |c.path|`.
2. `capAtom c k p = (2·colDepth c, 1, p)` if `k = 0`, else `(2·colDepth c + 1, 0, p)` — the atom of
   the appended `(p, ∅)`.
3. `capPos E c k = |w(litCap E c k 0)| − 1`: the number of atoms of `w(E)` a cap at `(c, k)` keeps
   (justified by L3.1c).
4. `localSuffix B c = node (columns c.col, c.col+1, … of the forest at c.path in B)`: the complete
   local suffix `Y` of the paper.
**Proof.** Definitions.
**Uses:** D3.1.
**Lean:** `Closure.colDepth`, `capAtom`, `capPos`, `localSuffix`; `Closure/Caps.lean`.
**Difficulty:** S.
**Testable:** yes (checked by `#eval` with `word_litCap` on 5 caps).

### D3.1a Moves, repair lists, admissible caps, origin map   (paper: txt:283-286, 655-658)
**Fidelity:** repaired (G-003: exact move and repair-record predicates; spine node D3.1a).
**Statement.**
1. `modifyCol E c f` applies `f` to the column at address `c` (identity off the tree).
2. `applyMove E ⟨col, i, j⟩`: if `E.colAt col = some C` and `i < j < |C|`, replace `C` by
   `C.take i ++ C.drop j` (entries `i…j−1` deleted, entry `j` and all later ones move back by
   `j−i`); otherwise `E`. `applyMoves E ms = foldl applyMove E ms` (spine).
3. `MoveOK K m` (one legal repair move of the current expression `K`): `K.colAt m.col = some C`,
   `stopData K = some sd`, `j+1 = |C|` (j is the last, active entry), `i < j`, the stopping column
   lies strictly inside entry `j` (`⟨m.col, j⟩.heightPath` is a prefix of `sd.col.path`), entries
   `i…j` all have the parent of entry `j`, `C[i].height < C[j].height`, and no index `x < i` with
   the same parent has `C[x].height < C[j].height` (so `i` is the least index of the same-parent
   run below `C`).
4. `MovesValid K ms` (spine name; body `MovesValidBody`): for every `idx < |ms|`,
   `MoveOK (applyMoves K (ms.take idx)) ms[idx]`.
5. `RepairStepOK K b m`: `K.colAt m.col = some C`, `i < j < |C|`, `m.col = b.col` or `m.col` is a
   strict container column of `b` (some `⟨m.col, i'⟩.heightPath` is a prefix of `b.col.path`),
   entries `i…j` share the parent of `j`, and `⟨m.col, j⟩ = b` or contains `b`.
   `RepairList K b ms` (spine; body `RepairListBody`): every move, applied in order, satisfies
   `RepairStepOK` for the current expression and `b`'s current address `moveAddr (ms.take idx) b`.
   Deleted entries `i…j−1` never contain `b` (they precede the retained index `j` at that level).
6. Index maps: `fwdIdx m e = e − (j−i)` if `e ≥ j`, else `e` (meaningful on retained indices);
   `bwdIdx m e = e + (j−i)` if `e ≥ i`, else `e`. `mapPath g m π` rewrites the step of `π` at level
   `|m.col.path|` when it passes through column `m.col.col`; `mapEntry`, `mapRole` extend this
   (an entry of `m.col` itself has its index rewritten). `moveAddr ms b = foldl (fwd) b ms`.
7. `AdmCap.origin w x` (χ; body `originBody`): undo the moves last-first with `bwdIdx`, giving
   `x0`; return `none` if `x0 = slot ⟨w.col, w.cut⟩` (the appended closing slot), else `some x0`.
8. **`origin_spec`†** (refinement of the spine's `origin_spec`): for `w : AdmCap E`,
   (a) χ is injective on the roles of `w.H` where defined; (b) for a role `x` of `w.H`,
   `χ x = none` iff `x` is the closing slot `closingSlot sd` of `stopData w.H = some sd`;
   (c) with no moves, χ is the identity on every role other than `slot ⟨w.col, w.cut⟩`;
   (d) every value of χ is a role of `E`.
**Proof** (of 8).
1. `roles (litCap E c k p) = (roles of E strictly before position capPos) ++ [slot ⟨c,k⟩]`, all
   with unchanged addresses — by induction on `c.path` over `litCapAux` and `Tree.rolesF` (spine).
2. For a legal move (`MoveOK`), `roles (applyMove K m)` is the image of the roles of `K` outside
   the deleted entries under `mapRole fwdIdx`, and `mapRole bwdIdx ∘ mapRole fwdIdx = id` on them
   (index arithmetic: retained indices are `< i` or `≥ j`).
3. (a): composition of injective maps (step 2) and the identity (step 1). (b): the closing slot of
   `w.H` is the image of `slot ⟨c, k⟩` under the forward maps, because by `MoveOK` every move's
   entry `j` contains the stopping column [T3.8c `stopData_litCap`]; undo with step 2. (c): step 1.
   (d): steps 1, 2.
**Uses:** D3.1, T3.8c.
**Lean:** `Closure.modifyColAux`, `modifyCol`, `applyMoveBody`, `applyMove_eq_body`,
`Move.fwdIdx`, `Move.bwdIdx`, `Move.mapPath`, `Move.mapEntry`, `Move.mapRole`, `moveAddrBody`,
`moveAddr_eq_body`, `MoveOK`, `MovesValidBody`, `movesValid_eq_body`, `RepairStepOK`,
`RepairListBody`, `repairList_eq_body`, `originBody`, `origin_eq_body`, `origin_spec`;
`Closure/Caps.lean`.
**Integration note:** At integration, SCR-U2-2: every definition of this list moved verbatim into `Spine.lean`; they remain U2-owned, and the bridges hold by `rfl`.
**Difficulty:** M — address arithmetic over role lists; about 300 LOC.
**Testable:** yes: random `AdmCap`s from `caps` of finite_model.py plus repair moves; check (a)–(d).

### T3.2b Word fact: two first-change positions   (paper: txt:304-307)
**Fidelity:** simplified (S-6: part of the single word library; stated for any linear order).
**Statement.** Let `α` be a linear order and `X Y X' Y' : List α`.
1. (`lt_of_firstDec`) If `X < Y`, `FirstDec X X' a` (`X'` agrees with `X` before `a`, `a ≤ |X'|`,
   and at `a` either `X'` ends while `X` continues or `X'[a] < X[a]`), `Y'.take b = Y.take b`,
   `b ≤ |Y'|`, and `a < b`, then `X' < Y'`.
2. (`lt_of_take_succ`) If `X < Y` and `Y'.take (|X|+1) = Y.take (|X|+1)`, then `X < Y'`.
**Proof.**
1. Let `δ` be the decision position of `X < Y` (first difference, or `δ = |X|` if `X` is a proper
   prefix of `Y`).
2. Case `δ < a`: `X'[δ] = X[δ] < Y[δ] = Y'[δ]` (as `δ < a < b`), with agreement before `δ`.
3. Case `a ≤ δ`: `X'`, `X`, `Y`, `Y'` agree before `a` (`a ≤ δ`, `a < b`); at `a`, `X'` ends or
   `X'[a] < X[a] ≤ Y[a] = Y'[a]`; `Y'` has a letter at `a` because `|Y'| ≥ b > a`.
4. Part 2: `X < Y` is decided within the first `|X|+1` letters of `Y`; these letters are unchanged.
**Uses:** —
**Lean:** `Closure.FirstDec`, `lt_of_firstDec`, `lt_of_take_succ`; `Closure/WordCancel.lean`.
**Difficulty:** S — list case analysis, about 60 LOC.
**Testable:** yes; exhaustive over `{0,1,2}`, lengths ≤ 3 (119,236 cases, 0 failures).

### L3.4 Word criterion   (paper: txt:427-437)
**Fidelity:** simplified (S-6: an abstract lemma on `F(y) = P ⌢ Σ(y)`; the forest form is L3.4f
and T3.8f).
**Statement.** Let `α` be a linear order, `P ≠ []`, `σ : α → α` strictly monotone,
`kerIter P σ 0 = []`, `kerIter P σ (q+1) = P ++ (kerIter P σ q).map σ`.
- **L3.4a** `kerIter q` is a proper prefix of `kerIter (q+1)`; `|kerIter q| = q·|P|`.
- **L3.4b** (`word_criterion`) `Y < P ++ Y.map σ ↔ ∃ q, Y < kerIter P σ q`.
- **L3.4c** (`success_anti`) If `Y' ≤ Y` and `Y < P ++ Y.map σ`, then `Y' < P ++ Y'.map σ`.
- **L3.4d** (`cover_of_success`) If `Y < P ++ Y.map σ` and `|Y| < q·|P|`, then
  `Y < kerIter P σ q`.
- **L3.4e** (`kernel_ne`) `P ++ Y.map σ ≠ Y`.
**Proof.**
1. L3.4a by induction on `q`; `map` preserves the prefix relation.
2. L3.4b. Put `I = kerIter P σ (|Y|+1)`; `|I| > |Y|` by L3.4a. Write `I = P ++ σ(I')` with
   `I' = kerIter (|Y|)`, a prefix of `I` of length `≥ |Y|`.
   (a) If `Y` is a prefix of `I`: then `I'.take |Y| = Y`, so `I.take (|P|+|Y|) = P ++ σ(Y)`; hence `Y` is
       a proper prefix of `P ++ σ(Y)`, and `Y < P ++ σ(Y)`, `Y < I`.
   (b) Else let `δ < |Y|` be the first difference of `Y` and `I`. `P ++ σ(Y)` agrees with `I` on
       `[0, |P|+δ) ⊇ [0, δ]` (as `|P| ≥ 1`). If `Y[δ] < I[δ]`, both `Y < I` and `Y < P ++ σ(Y)`. If
       `Y[δ] > I[δ]`, both `I < Y` and `P ++ σ(Y) < Y`.
   So `Y < P ++ σ(Y) ↔ Y < I`. Finally `(∃ q, Y < kerIter q) ↔ Y < I`: for `q ≤ |Y|+1` use L3.4a;
   for larger `q`, `Y < kerIter q` is decided within the first `|Y|+1` letters, which are those of `I`.
3. L3.4c from L3.4b: `Y' ≤ Y < kerIter q`.
4. L3.4d: as in step 2, `Y < kerIter q` is decided within `|Y|+1 ≤ q·|P|` letters, on which
   `kerIter q` and `I` agree (L3.4a).
5. L3.4e by length (`|P| ≥ 1`).
**Uses:** —
**Lean:** `Closure.kerIter`, `kerIter_prefix`, `kerIter_length`, `word_criterion`, `success_anti`,
`cover_of_success`, `kernel_ne`; `Closure/Kernel.lean`.
**Difficulty:** S — list lemmas, about 120 LOC.
**Testable:** yes; exhaustive (12,276 cases with three choices of `σ`, 0 failures).

### L3.7 Delayed-change lemma   (paper: txt:482-487)
**Fidelity:** simplified (S-6: abstract word lemma; the positions are supplied by its users).
**Statement.** If `R < L`, `|R| ≤ λ`, `L'.take λ = L.take λ`, `λ ≤ |L'|`, and `R' < R`, then
`R' < L'`.
**Proof.**
1. Let `δ ≤ |R| ≤ λ` decide `R < L`.
2. If `δ < |R|`: `R[δ] < L[δ] = L'[δ]` with agreement before, so `R < L'`, hence `R' < R < L'`.
3. If `δ = |R|` (`R` a proper prefix of `L`): `L'` starts with `L.take |R| = R`, so `R ≤ L'` and
   `R' < R ≤ L'`.
**Uses:** —
**Lean:** `Closure.delayed_change`; `Closure/WordCancel.lean`.
**Difficulty:** S — about 30 LOC.
**Testable:** yes; exhaustive (95,725 cases, 0 failures).

### T3.2p Reset identity and head cursor   (paper: txt:377-389)
**Fidelity:** simplified (S-6: generic word lemmas; the paper's instance is in T3.2r and T3.8).
**Statement.** Let `α` be a linear order, `ks qs Z V : List α`.
1. (`reset_nu`) If `c < |ks|`, `Z` is nonincreasing, `cutQuery ks c ≤ Z < cutQuery ks (c+1)`, then
   for `1 ≤ v ≤ |ks| − c`: `ν(Z ⌢ ks[c..c+v)) = cutQuery ks (c+v)`.
2. (`head_cursor`) If `c ≤ |ks|`, `cutQuery ks c ≤ ν(qs)`, and `c < |ks| → ν(qs) < cutQuery ks (c+1)`,
   then for every nonincreasing `V`: if `V < ν(qs)` then `cursor (qs ++ ks[c:]) V < |qs|`; if
   `ν(qs) ≤ V` then `c ≤ cursor ks V` and `cursor (qs ++ ks[c:]) V = |qs| + cursor ks V − c`
   (including exhaustion).
**Proof.**
1. Write `B_{c−1} = cutQuery ks c = P ⌢ D` where `ν` deletes `D` (all letters `< K_c := ks[c]`) when
   `K_c` is appended, so `B_c = P ⌢ [K_c]` [U1 `nu_append_singleton`, REQ-U1-13].
2. From `P⌢D ≤ Z < P⌢[K_c]`: `Z = P ⌢ Z'` with `Z' = []` or `Z'[0] < K_c` (a first difference before
   `|P|` would put `Z` below `P⌢D`); `Z` nonincreasing gives every letter of `Z'` `< K_c`.
3. `ν(Z⌢[K_c])` deletes `Z'` and stops at `P`'s last letter `≥ K_c`: it is `B_c`. Iterate with
   `ν(ν(l) ⌢ m) = ν(l ⌢ m)` [REQ-U1-13] for `v ≥ 2`.
4. Part 2: the head boundaries are `ν(qs[0..j])` for `j < |qs|`, then `ν(ν(qs) ⌢ ks[c..c+v)) =
   cutQuery ks (c+v)` by part 1 with `Z = ν(qs)`. The final cursor is the unique index between
   consecutive boundaries [spine `cursor_spec`, L2.1; U1 `cursor_unique`, REQ-U1-17]: below `|qs|`
   if `V < ν(qs)`, else `|qs| + (cursor ks V − c)`.
**Uses:** U1: D2.1, L2.1 (word library: REQ-U1-13, REQ-U1-17).
**Lean:** `Closure.reset_nu`, `head_cursor`; `Closure/WordCancel.lean`.
**Difficulty:** S — about 120 LOC.
**Testable:** yes; exhaustive over `{0,1,2}`, `|qs| ≤ 3`, `|ks| ≤ 4` (169,400 cases, 0 failures).

### L3.1c Word of a literal cap   (paper: new; txt:261-262, 495-498)
**Fidelity:** new (makes "a cap is a safe prefix plus one larger atom" explicit).
**Statement.** Let `c ∈ E.colAddrs` and `k ≤ |E.colAt c|`.
1. (`word_litCap`) `w(litCap E c k p) = w(E).take (capPos E c k) ++ [capAtom c k p]`.
2. (`isUpward_iff_atom`) `IsUpward E c k p ↔` every atom `y = w(E)[capPos E c k]` (if it exists)
   satisfies `y < capAtom c k p`.
3. (`lt_litCap`) `IsUpward E c k p → E < litCap E c k p`.
**Proof.**
1. Part 1 by induction on `c.path` along `litCapAux`, unfolding `wordAt/wordCols/wordCol/wordLater`
   (spine bodies): at each containing level the kept columns and entries contribute the same atoms
   as in `w(E)`, the containing entry's atom is followed by the recursive cap; at the own level the
   first `k` entries contribute their atoms, then `capAtom`.
2. Part 2. If `k < |col|`, the atom at `capPos` is entry `k`'s atom, `(2e, 1, q)` (k = 0) or
   `(2e+1, 0, q)`, of the same kind as `capAtom`; it is smaller iff `q < p`. If `k = |col|`, the next
   atom (if any) starts a later column at depth `e` or continues a shallower level, so its depth
   coordinate is `≤ 2e`; if `k ≥ 1` it is below `(2e+1,0,p)`; if `k = 0` the column is empty and the
   atom is `(2e,0,0) < (2e,1,p)` [U1 `gwordAt_fst_ge`, REQ-U1-2].
3. Part 3 from parts 1–2 and `word_lt_iff` (spine C1.8).
**Uses:** D3.1, D3.1c; U1: C1.8.
**Lean:** `Closure.word_litCap`, `isUpward_iff_atom`, `lt_litCap`; `Closure/Caps.lean`.
**Difficulty:** M — mutual word recursion, about 250 LOC.
**Testable:** yes (part 1 checked by `#eval` on 5 caps; extend with random caps from finite_model.py).

### N2.1 Literal caps from words   (paper: new; used at txt:286-288, 497-498)
**Fidelity:** new (converse of L3.1c; the paper uses it silently in "E is an upward literal cap of
B" and in the interval fact).
**Statement.** Let `B, E` be forests, `π ≤ µ(B)`, `z = (2e,1,p)` (`first = true`) or `(2e+1,0,p)`
(`first = false`), with `w(E) = w(B).take π ++ [z]`. Assume every atom `y = w(B)[π]` satisfies
`y < z`, and, if `first`, `w(B)[π]` exists with depth coordinate `≥ 2e`. Then there are `c, k` with
`c ∈ B.colAddrs`, `k ≤ |B.colAt c|`, `colDepth c = e`, `k = 0 ↔ first`, `capPos B c k = π`,
`IsUpward B c k p`, and `litCap B c k p = E`.
**Proof.**
1. Let `G = safePrefix B π`; `w(G) = w(B).take π` [spine `word_safePrefix`].
2. Decoding (REQ-U1-14, stated as U1 D1.9b `routeCols_of_word_snoc`): the forests whose word is
   `w(G) ⌢ [z]` are exactly: `G` with `(p,∅)`
   appended to its route column at depth `e` (`first = false`), or `G` with a new column `[(p,∅)]`
   appended to its route forest at depth `e` (`first = true`); in particular such a route column or
   forest exists, and `E` is that forest [`word_injective`].
3. The route column at depth `e` of `G` is (an initial part of) a column `c` of `B` with the same
   address [U1 `colAt_safePrefix`]; let `k` be its number of entries in `G`. Since the next atom `y`
   of `B` is `< z`, it is not inside the height of entry `k−1` (such atoms have depth `≥ 2e+2`), so
   the first `k` entries of `c` are complete in `G`; for `first = true`, `y` has depth coordinate
   exactly `2e` and starts column `c` of `B` at that position.
4. `capPos B c k = π` and `w(litCap B c k p) = w(E)` by L3.1c.1; conclude by `word_injective`.
   Upward by L3.1c.2.
**Uses:** L3.1c, D3.1c; U1: C1.8, D1.9, D1.9b (REQ-U1-14).
**Lean:** `Closure.exists_litCap_of_word`; `Closure/Caps.lean`.
**Difficulty:** M — needs U1's decoding of one-atom extensions; about 300 LOC.
**Testable:** yes: for all standards `B` of a bounded generation, all positions `π` and atoms `z`
satisfying the hypotheses, decode and compare with `caps`.

### L3.1b Pure towers   (paper: txt:265-268)
**Fidelity:** repaired (G-002: V, I, H are explicit hypotheses; without I the first-entry branch
need not be a pure tower, codex X-03).
**Statement.** Let `E` satisfy V, I, H, and let `e` be an entry of `E` with height `J`, host
`a = e.col.num 0`.
1. (`profile_of_entry`) If `J ≠ ∅` then `profile J = (d, m)` with `m ≥ 1`.
2. (`relKey_lt_towKey`) If `J ≠ ∅` and `profile J = (d, m)`, then `relKey a J < towKey d (m+1)`.
3. (`towKey_le_relKey`) If `(d, m) < profile H` for the height `H` of `e`, then
   `towKey d (m+1) ≤ relKey a H`.
**Proof.**
1. Tower shape. For `k ≤ d`, let `J_k` be the first-entry branch forest at depth `k` (attached to
   the column of number `a + k`). By I, the first column of `J_k` is nonempty with first parent
   `≥ a + k`; by V (parents are below the column number, REQ-U1-9) that parent is `< a + k + 1`.
   Hence the first parent is `a + k`, with relative label `(true, k)` at threshold `a`.
2. Part 1: at `k = d` the first entry has empty height; the run counted by `profileAux` has length
   `m ≥ 1`. By H, every entry of the run after the first has height `≤ ∅`, hence `= ∅` (spine
   `Forest.empty_lt`). The entry after the run (if any) has parent `< a + d` (H: parents
   nonincreasing; maximality of the run), so its label is `< (true, d)`.
3. Part 2 by induction on `d − k` comparing `relKey a J_k` with `towKeyAt k (d−k) (m+1)`: at `k = d`
   the first columns agree on `m` entries and then `J` has a smaller label or ends, so `J_d` is
   strictly smaller (decided in the first column); at `k < d` the first entries have equal labels
   and strictly smaller heights. Later columns of `J` do not matter (decided earlier).
4. Part 3: if `d < d_H`, at level `d` the tower's first entry has height `∅` while `H`'s has a
   nonempty height: strictly smaller. If `d = d_H` and `m < m_H`, the tower's column (`m+1 ≤ m_H`
   entries `((true,d),∅)`) is a prefix of `H`'s first column, and the tower has no further columns:
   `≤`. Above level `d`, equal labels and `≤` heights, and the tower's columns are prefixes.
**Uses:** D3.1, D3.1b; U1: D1.1, D1.2a.
**Lean:** `Closure.profile_of_entry`, `relKey_lt_towKey`, `towKey_le_relKey`; `Closure/Profile.lean`.
**Difficulty:** M — induction along the branch with address bookkeeping; about 250 LOC.
**Testable:** yes: all entries of all generated standards and of random V,I,H expressions.

### L3.1a `V ∧ I ∧ H ∧ P ⇒ S`   (paper: txt:263-268)
**Fidelity:** repaired (G-002: the paper states "P implies S"; false without V, I, H by codex X-03,
checks/results/quick-hypothesis-counterexample.json).
**Statement.** `condS_of_condP`: `CondV E → CondI E → CondH E → CondP E → CondS E`.
**Proof.** Fix an owner return `(e0, e)` with upper height `H` (host `a`) and lower `J` (host `c`).
1. `H ≠ ∅`, since `e` lies inside it.
2. If `J = ∅`: `relKey c ∅ = node []` is below every nonempty key (`keyCmp (node []) (node (_::_)) =
   .lt` by computation).
3. If `J ≠ ∅`: `profile J = (d, m)` [L3.1b.1]; P gives `(d, m) < profile H`; then
   `relKey c J < towKey d (m+1) ≤ relKey a H` [L3.1b.2, L3.1b.3].
**Uses:** L3.1b.
**Lean:** spine `Closure.condS_of_condP`; `Closure/Profile.lean`.
**Difficulty:** S — about 40 LOC given L3.1b.
**Testable:** yes: random V,I,H,P expressions (the finite_model `properties` checker).

### L3.1d Γ bound for V,I-legal upward caps   (paper: txt:269-273)
**Fidelity:** repaired (G-002: V, I, H of `E` and V, I of the cap are explicit).
**Statement.** `capKey_le_towKey`: let `E` satisfy V, I, H, `IsUpward E c k p`, and let
`K = litCap E c k p` satisfy V and I. For every containing entry `e` of `c` (`e.heightPath` a prefix
of `c.path`) with height `J` in `E` and `profile J = (d, m)`, the height `J'` of `e` in `K` satisfies
`relKey a J' ≤ towKey d (m+1)` (`a = e.col.num 0`).
**Proof.**
1. `J'` is the literal cap of `J` at the relative address of `c` [L3.1c family: `heightAt` of a
   `litCapAux` at a container is the `litCapAux` of the height, by induction on the path].
2. Walk the first-entry branch of `J` (tower shape, L3.1b step 1), comparing `relKey a J'` with
   `towKeyAt k (d−k) (m+1)` at level `k`:
   (a) cap at the first column of `J_k` at cut `0`: in `K` its first entry is `(p,∅)`; I (in `K`)
       gives `p ≥ a+k`, V gives `p < a+k+1`, so `p = a+k`, contradicting upwardness (`p >` first
       parent `a+k`);
   (b) cap at the first column of `J_k`, `k < d`, cut `≥ 1`, or anywhere after the first entry of
       `J_k`'s first column: the first entry `((true,k), J_{k+1})` is retained completely and
       `relKey J_{k+1} <` the tower below [L3.1b.2]: strictly smaller;
   (c) cap inside the first entry's height at level `k < d`: recurse to level `k+1`;
   (d) level `d`, first column, cut `k' ∈ [1, m)`: upward needs `p > a+d`, V forbids it (as in (a));
   (e) level `d`, cut `k' = m`: the column becomes `m` entries `((true,d),∅)` then `(p,∅)` with
       `p ≤ a+d` (V): `≤` the tower's `m+1` entries; nothing else is retained after it;
   (f) level `d`, cut `k' > m` or later columns/entries: the retained run is followed by a smaller
       label or ends: strictly smaller.
**Uses:** L3.1b, L3.1c.
**Lean:** `Closure.capKey_le_towKey`; `Closure/Profile.lean`.
**Difficulty:** M — six-way case analysis along the branch; about 300 LOC.
**Testable:** yes: all `caps` of generated standards that satisfy V and I.

### L3.1e S for upward caps (`upward_condS`†)   (paper: txt:274-282)
**Fidelity:** repaired (G-002: hypotheses V, I, H, P of `E` and V, I of the cap).
**Statement.** If `E` satisfies V, I, H, P, `IsUpward E c k p`, and `K = litCap E c k p`
satisfies V and I, then `CondS K`.
REFINABLE contract from the spine (§c.6); consumers: U3 `firstDiff_cap` (gives `CondS K` for the
first-difference cap of a standard `E`, which has V, I, H, P by T3.2), U2 L3.1.
**Proof.** Owner returns of `K` and their addresses are those of `E` before the cut, plus returns
involving the closing slot (addresses are preserved by `litCap`, and `IsOwnerReturn` is address
arithmetic, spine `resolve`). Fix an owner return `(e0', e')` of `K`.
1. `e0'` not a container of `c`: its height and everything inside it are unchanged; S holds in `E`
   [L3.1a].
2. `e0'` a container with heights `H` (in `E`), `H'` (in `K`): `H < H'` [L3.1c.3 applied inside the
   height], hence `relKey a H < relKey a H'` [spine `relKey_lt_iff`].
   (a) `e'` the closing slot: lower height `∅`; S as in L3.1a step 2.
   (b) `e'` an unchanged entry with height `J`: `(e0', e')` is an owner return of `E`, so
       `relKey J < relKey a H < relKey a H'` [L3.1a].
   (c) `e'` a container with heights `J`, `J'`: `relKey J' ≤ towKey (π(J)+1)` [L3.1d],
       `towKey (π(J)+1) ≤ relKey a H` [L3.1b.3 with P of `E`], `< relKey a H'`.
**Uses:** L3.1a, L3.1b, L3.1c, L3.1d; U1: D1.4.
**Lean:** `Closure.upward_condS`; `Closure/Caps.lean`.
**Difficulty:** M — case analysis on returns; about 200 LOC.
**Testable:** yes: all V,I-legal upward caps of generated standards.

### L3.1f Interval fact   (paper: txt:286-288)
**Fidelity:** as in paper (proved through words).
**Statement.** `interval_cap`: if `IsUpward X c k p`, `X ≤ Y < litCap X c k p`, then
`IsUpward Y c k p` and `litCap Y c k p = litCap X c k p`.
**Proof.**
1. `w(C) = w(X).take π ⌢ [z]` with `π = capPos X c k`, `z = capAtom c k p` [L3.1c.1].
2. `w(X) ≤ w(Y) < w(C)` [`word_lt_iff`]. A first difference of `w(Y)` with `w(X).take π` before `π`
   would decide both comparisons the same way, contradicting one of them; so `w(Y).take π =
   w(X).take π`, and `w(Y)[π] < z` (or `w(Y)` ends at `π`), while `w(X)[π] ≤ w(Y)[π]`.
3. For `k = 0`, `w(X)[π]` has depth coordinate `2e` (it starts column `c`), hence so does
   `w(Y)[π]`.
4. N2.1 with `B = Y`, `E = C` gives a cap of `Y` at position `π`; its address is `c` and its cut is
   `k` (same position and depth, L3.1c), so `litCap Y c k p = C`, upward.
**Uses:** L3.1c, N2.1; U1: C1.8.
**Lean:** `Closure.interval_cap`; `Closure/Caps.lean`.
**Difficulty:** S — about 80 LOC given N2.1.
**Testable:** yes: triples `X ≤ Y < C` among small forests.

### L3.1g A legal move keeps decorated responses   (paper: txt:289-293)
**Fidelity:** as in paper.
**Statement.** `decoratedA_applyMove`: if `MoveOK K m`, `CondV K`, and decorated A
`CondAK K (capKeys K (routeCols K))`, then `K' = applyMove K m` satisfies V, `CondI K → CondI K'`,
and decorated A `CondAK K' (capKeys K' (routeCols K'))`.
**Proof.**
1. Column numbers do not depend on entry indices (spine `ColAddr.num`), so every column keeps its
   number; `m.col` is a route column of `K` and of `K'`.
2. Decorated keys of `m.col`: in `K`, `P ⌢ [K_i,…,K_{j−1}, ⊤]`; in `K'`, `P ⌢ [⊤]`, where the block
   entries all have parent `p` (MoveOK).
3. Every query used by a test is a `cutQuery` of some column at an index below its length, hence
   contains no `⊤` (a capped key is last). For such a reduced query `W`, the cursor in `m.col` either
   stops inside `P` (equal in both) or enters the block, where the first unconsumed entry has parent
   `p` in both (⊤ is never consumed); never exhausted. So `resp K ks m.col W = resp K' ks' m.col W`.
   All other columns have identical decorated keys and responses.
4. The new entry at index `i` has the old test of entry `i` (same parent `p`, same preceding prefix
   `P`); tests inside the moved height see the same external responses (step 3); other tests are
   unchanged. Hence decorated A for `K'`.
5. V: parents and numbers unchanged. I: if `i = 0` the new first entry has the old first parent `p`.
**Uses:** D3.1a.
**Lean:** `Closure.decoratedA_applyMove`; `Closure/Caps.lean`.
**Difficulty:** M — path transport through an address change; about 250 LOC.
**Testable:** yes: random moves on V-valid caps with decorated A.

### L3.1h Legal moves keep literal caps   (paper: txt:286-288, 294-295)
**Fidelity:** as in paper.
**Statement.** `applyMoves_litCap`: if `CondH E`, `IsUpward E c k p`, and
`MovesValid (litCap E c k p) ms`, then there is `c'` with `IsUpward E c' k p`,
`applyMoves (litCap E c k p) ms = litCap E c' k p`, and the first `k` entries of `E`'s columns at
`c'` and `c` agree ("unchanged internal cap").
**Proof.** Induction on `ms`, invariant: the current expression is `litCap E c_s k p`, upward, with
the same first `k` entries.
1. A move `⟨b, i, j⟩`: entry `j` of `b` contains `c_s`; its height `C` is the literal cap of `E`'s
   height `H_j` at the relative address [L3.1c family].
2. In `E`, `H_j ≤ H_i` (H, same parent, `i < j`); MoveOK gives `H_i < C`; L3.1f with `X = H_j`,
   `Y = H_i` gives that `C` is the same literal cap of `H_i`, upward.
3. Hence the result is `litCap E c_{s+1} k p`, with `c_{s+1}` obtained from `c_s` by replacing the
   step `(b.col, j)` by `(b.col, i)`; entries before `i` of `b` are `E`'s.
**Uses:** L3.1f, L3.1c, D3.1a.
**Lean:** `Closure.applyMoves_litCap`; `Closure/Caps.lean`.
**Difficulty:** M — about 150 LOC.
**Testable:** yes, with L3.1 (repair).

### L3.1 Profile and repair lemma (`repair`†)   (paper: txt:263-298)
**Fidelity:** repaired (G-002 in the S part; G-003: explicit `AdmCap` with moves).
**Statement.** `repair`: let `E ∈ L` with P, `IsUpward E c k p`, and let `K = litCap E c k p`
satisfy V, I and decorated A `CondAK K (capKeys K (routeCols K))`. Then there is `w : AdmCap E`
with `w.col = c`, `w.cut = k`, `w.par = p`, `stopData w.H = some sd` with `sd.r = p` and
`sd.Q = (E.colAt c).take k`, and `w.H = litCap E c' k p` for some `c'` with `IsUpward E c' k p`.
REFINABLE contract (spine §c.6); consumer: U5 L8.8 Case 3 (repaired cap `H` of the first-difference
cap), U3 `joint_repair`. The added conclusions (stop data; `w.H` a literal cap) only strengthen it.
**Proof.**
1. `CondS K` [L3.1e]; `CondA K` from decorated A [U1 `capping_iff`, L2.4, REQ-U1-12].
2. H can fail in `K` only at the active last entry of a containing column of `c`: non-container
   columns are unchanged; the cap column satisfies H because A gives parent monotonicity
   (`p ≤` previous parent, txt:190-192) and `(p,∅)` is the least entry with parent `p`.
3. Repair from the inside out: let `b` be the innermost violating container, `j` its last entry with
   height `C > H_{j−1}` and the same parent. Let `i` be the least index of the same-parent run with
   `H_i < C`. Then `⟨b,i,j⟩` is `MoveOK`.
4. After the move: decorated A and V, I [L3.1g]; a literal upward cap of `E` [L3.1h]; hence S
   [L3.1e] and A [capping_iff]. H holds at `b` (minimality of `i`), inside the moved height
   (unchanged and already repaired) and at the cap column.
5. Iterate outward; at most `|c.path|` moves. The result has V, I, H, A, S: an `AdmCap` with
   `moves = ms`, `movesValid` by construction. Stop data by T3.8c (`stopData_litCap`) and L3.1h.
**Uses:** L3.1e, L3.1g, L3.1h, T3.8c; U1: L2.4.
**Lean:** `Closure.repair`; `Closure/Caps.lean`.
**Difficulty:** L — the induction over containers with all invariants; about 500 LOC.
**Testable:** yes: for all V,I-legal upward caps with decorated A of generated standards, run the
repair and check membership in `L` (the Codex cap test checked 84,291 admissible caps).

### D3.1d The surviving-role map: full specification   (paper: new; txt:1107-1110, 1416-1421)
**Fidelity:** new (requested by U3 R10, R15 and U5 R16, R17 at integration; formerly stubs in
`U3.lean` and `U5.lean`).
**Statement.** Let `w : AdmCap E` and write `χ = w.origin`; `anchorD` is the spine's totalized
origin (`(anchorOrigin E cap x).getD x`, §c.11).
1. `origin_spec_full` (U3 R10), for `E ∈ L`:
   - `χ` is injective on `w.H.roles`; `χ x = none` iff `x` is the closing slot of `w.H`; its values
     are roles of `E`;
   - `χ` sends each ordinary role to an ordinary role or to `none`, and `χ (A_c) = A_{c'}` implies
     `c'.num 0 = c.num 0`;
   - for slots, `χ (U_e) = U_{e'}` implies that `e` (in `w.H`) and `e'` (in `E`) have the same label,
     and `χ (A_{e.col}) = A_{e'.col}`;
   - representatives commute: `χ (A_c) = A_{c'}` and `q < c.num 0` give
     `(c.rep 0 q).map (anchorD × anchorD) = c'.rep 0 q`;
   - reading order is preserved on the roles where `χ` is defined (written with explicit indices,
     which is U3's `Before` unfolded).
2. `admCap_query` (U3 R15), for `E ∈ L` and `stopData w.H = some sd`: `sd.t = w.col.num 0`,
   `sd.r = w.par`, `|sd.Q| = w.cut`, `χ (A_{sd.col}) = A_{w.col}`, and for `j < w.cut`,
   `χ (U_{⟨sd.col, j⟩}) = U_{⟨w.col, j⟩}` and `sd.Q[j]? = (E.colAt w.col)[j]?`.
3. `anchorOrigin_prefix` (U5 R16), for `E ∈ L`, `cap : Option (AdmCap E)` and
   `stopData (anchor E cap) = some sd`: some `T'` has `anchorOrigin E cap (A_{sd.col}) = some T'`;
   `anchorOrigin E cap` is injective where defined; every `x ∈ rolesBefore (anchor E cap) A_{sd.col}`
   has an origin `y ∈ rolesBefore E T'` with `y ∈ E.roles`.
4. `lt_admCap` (U5 R17): `E < w.H`.
**Proof.**
1. *Shape of `χ`.* The spine body `originBody` (moved from D3.1a at integration) undoes the moves
   last-first by `Move.mapRole bwdIdx` and returns `none` only on `U_{⟨w.col, w.cut⟩}`.
2. *Item 1.* Injectivity, `none` exactly on the closing slot and values in `E`: D3.1a
   `origin_spec`, clauses 1, 2 and 4. Ordinary roles: `Move.mapRole` sends `ord c` to
   `ord ⟨mapPath …, c.col⟩` (spine body), and `mapPath` rewrites only entry indices, so
   `ColAddr.num`, which reads only column indices, is unchanged (the argument of D3.1e item 5). For
   a literal cap `χ` is the identity off the closing slot (D3.1a `origin_spec`, clause 3), and the
   cap keeps the label of every kept entry (D3.1e item 1). A move transports entry `j` with its label
   to index `i` (spine body `applyMoveBody`), and `mapEntry` and `mapRole` apply the same `mapPath`
   to an entry and to its column, so `χ (A_{e.col}) = A_{χ(e).col}`. Representatives: `rep 0 q`
   resolves `q` on the visible stack (D1.2b `resolve_spec`) and reads the container of the column
   (spine body of `rep`); `χ` maps the stack of `c` onto the stack of `c'` keeping numbers (previous
   clause) and containment (one `mapPath` for a column and its containers), so the resolved column
   and the container correspond. Reading order: a move deletes entries `i…j−1` and lowers the later
   indices of that column by `j − i` (`fwdIdx`), which keeps the relative order of the surviving
   roles; the literal cap keeps the order of `E` (D3.1e item 1, roles clause).
3. *Item 2.* D3.1e item 1 (last clause, with I of `E` and V of the cap from `w.inL`): the literal
   cap has stopping column `w.col`, `r = w.par` and `Q` the first `w.cut` entries of `E`'s column.
   Each move is at a container column of the current stopping column and its moved entry contains
   that column (D3.1e item 3), so the entries of the stopping column are untouched and only its
   address changes, by `mapPath`, which `χ` undoes (step 1). `sd.t = sd.col.num 0` (D1.6b
   `stopData_spec`) and item 1's number clause give `sd.t = w.col.num 0`.
4. *Item 3.* `cap = none`: `anchorOrigin = some` (spine), take `T' = A_{sd.col}` and `y = x`.
   `cap = some w`: `T' = A_{w.col}` by item 2; injectivity by item 1. A role `x` before `A_{sd.col}`
   is not the closing slot, which comes after `A_{sd.col}` (D1.6d `stopData_roles`), so `χ x = some y`
   with `y ∈ E.roles` (item 1); by item 1's order clause `y` precedes `χ (A_{sd.col}) = T'` in
   `E.roles`, hence `y ∈ rolesBefore E T' = takeWhile (· ≠ T') E.roles` (D1.2b `roles_nodup`).
5. *Item 4.* `E < litCap E w.col w.cut w.par` by L3.1c `lt_litCap` (from `w.upward`). Each move `m`
   is legal for the current expression `K` (D3.1e item 3): it replaces entry `i` `(q, H_i)` of column
   `m.col` by entry `j` `(q, C)` with `H_i < C` and keeps every earlier role, so `K < applyMove K m`
   by the lexicographic definition of the order (spine `Forest.instLinearOrder`, D1.1a). Transitivity
   (D1.1) gives `E < w.H`.
**Uses:** D1.1, D1.1a, D1.2b, D1.6b, D1.6d, D3.1, D3.1a, D3.1e, L3.1c.
**Lean:** `Closure.origin_spec_full`, `Closure.admCap_query`, `Closure.anchorOrigin_prefix`,
`Closure.lt_admCap`; `Closure/Caps.lean`.
**Difficulty:** M — about 400 LOC; the representative clause of item 1 is the longest.
**Testable:** yes. Item 1 was tested by U3's verifier (T7: 3,421 moved caps, 31,335 roles,
0 failures) and item 2 on the caps of T3 and T4; items 3 and 4 were not tested.

### D3.1e Literal caps and moves: address facts   (paper: new; txt:261-262, 283-295, 655-658)
**Fidelity:** new (requested by U3 R11, R12, R13, R18, R19 at integration; formerly stubs in
`U3.lean`).
**Statement.**
1. `litCap_spec` (R11): for `c ∈ E.colAddrs`, `k ≤ |parents E c|` and `K = litCap E c k p`:
   `K.roles = E.roles.take m ++ [U_{⟨c,k⟩}]` for some `m`; every entry `e ≠ ⟨c,k⟩` of `K` has the
   label it has in `E`; such an entry that does not contain `c` has the same label and height as in
   `E`; `K.entryAt ⟨c,k⟩ = some (p, ∅)`; and if `c.path ≠ []`, `CondI E` and `CondV K`, then
   `stopData K` has column `c`, `r = p` and `Q` the first `k` entries of `c`.
2. `moves_spec` (R12): for `E ∈ L`, `w : AdmCap E`, `b` with `b.heightPath <+: w.col.path` and no move
   inside the height of `b`: `RepairList (E.truncAfter b) b w.moves`; `moveAddr w.moves b` has the
   printed host of `b`; `applyMoves` commutes with replacing the height at `b`; the moved truncation
   has `E`'s height of `b` at `moveAddr w.moves b`; and `w.H` is the moved truncation with that height
   replaced by `w.H`'s.
3. `moves_violate` (R13): every move `w.moves[idx]` satisfies `MoveOK` for
   `X = applyMoves (litCap E w.col w.cut w.par) (w.moves.take idx)`, written out: its column is a
   column of `X` whose last entry `j` contains the stopping column of `X`, `i < j`, entries `i…j`
   share a parent `q`, and `H_i < C` for the heights of entries `i` and `j`.
4. `applyMoves_litCap_addr` (R18): for `CondH E`, `b` as in item 2 and `q ≤ |w.moves|`, with
   `c_q = ⟨(moveAddr (w.moves.take q) b).heightPath ++ w.col.path.drop |b.heightPath|, w.col.col⟩`:
   `IsUpward E c_q w.cut w.par`; `applyMoves (litCap E w.col …) (w.moves.take q) = litCap E c_q w.cut
   w.par`; and the first `w.cut` entries of `c_q` and `w.col` in `E` agree.
5. `moveAddr_num` (R19a): `(moveAddr ms b).col.num 0 = b.col.num 0`.
6. `repairList_height` (R19b): `RepairList K b ms → (applyMoves K ms).heightAt (moveAddr ms b) =
   K.heightAt b`.
**Proof.**
1. *Item 1.* Induction on `c.path` with the spine body `litCapAux`. At each level the kept columns
   `0…c_d` and entries `0…i_d` form a prefix in reading order (spine `rolesF`), and at the last level
   the first `k` entries of column `j` keep their heights, followed by `(p, ∅)`; so the roles are a
   prefix of `E.roles` followed by `U_{⟨c,k⟩}`. Every kept label is copied, and heights off the path
   of `c` are copied. Stop data: in `K` every forest on the path of `c` ends with its path column,
   which is nonempty (it holds the containing entry, or `(p, ∅)` at the last level), and each
   containing entry is the last entry of its column; so the route of `K` ends at `c` with last entry
   `(p, ∅)` (D1.2d `mem_routeCols_iff`), and D1.6d `stopData_of_route` returns this stop. The hypotheses `CondI E`, `CondV K` are not needed for this; they are kept as
   in the requested statement.
2. *Item 5.* `moveAddrBody` folds `Move.mapEntry fwdIdx`, which changes only entry indices of one
   step of the path and the entry's own index; `ColAddr.num` (spine) sums only `(·.1 + 1)` over the
   path and adds the column index. Induction on `ms`.
3. *Item 3.* `w.movesValid : MovesValid (litCap …) w.moves`, whose spine body (moved from D3.1a) is
   `∀ idx < |ms|, MoveOK (applyMoves K (ms.take idx)) ms[idx]`. Unfold `MoveOK` (D3.1a, real body)
   and take `q`, `H_i`, `C` from entries `i` and `j` of `col` (`col.getD` agrees with `col[·]?` below
   `|col|`, and `i < j < |col|`).
4. *Item 6.* Induction on `ms` with the spine body `RepairListBody`: each step is `RepairStepOK` at
   the current address of `b`; the move retains `b` or `b`'s container as entry `j`, and `applyMove`
   moves entry `j` with its height to index `i` (spine body `applyMoveBody`), which is the new address
   given by `mapEntry fwdIdx`; every other height on `b`'s path is carried unchanged.
5. *Item 2.* Every move of `w` is at a container column of the stopping column (item 3), which lies in
   the height of `b` (`b.heightPath <+: w.col.path`); by `hout` no move lies inside the height of `b`,
   so each move is in `b`'s column or in a strict container column of `b`, and its retained entry `j`
   (which contains the stopping column) is `b` or `b`'s container. Its parents and column lengths are
   the same in the current cap and in the moved truncation of `E` after `b`, since `litCap` and
   `truncAfter b` agree at the levels of `b`'s container chain (item 1; D1.2c body of `truncAux`).
   So every step is `RepairStepOK` for `E.truncAfter b`, which is the spine body of `RepairList`.
   The number clause is item 5. Commutation with `setHeight` at `b`: `applyMove` acts by `modifyCol`
   on `m.col` and carries the entry at `b`'s current address unchanged (item 6's argument), so
   replacing that height before or after a move gives the same tree (induction on the moves, D1.2f
   `setHeight_basic`). The height clause is item 6. Last clause: `w.H` is the moved literal cap, and
   the literal cap agrees with `E.truncAfter b` outside the height of `b` (both keep exactly the
   context up to `b`'s container chain), so the two moved trees differ only in the height at
   `moveAddr w.moves b`.
6. *Item 4.* Induction on `q`, following the proof of L3.1h (`applyMoves_litCap`), whose step 3
   builds exactly `c_{q+1}` from `c_q`: a move outside the height of `b` relocates `b`'s container
   chain by `mapPath`, so the cap column `c_q` inside that height becomes `c_{q+1}` and the moved
   tree is again the literal cap at `c_{q+1}` (L3.1h); upwardness and the first `w.cut` entries are
   kept because the moves do not touch the height of `b` (L3.1f `interval_cap`, as in L3.1h).
**Uses:** D1.2c, D1.2d, D1.2f, D1.6b, D1.6d, D3.1, D3.1a, L3.1f, L3.1h.
**Lean:** `Closure.litCap_spec`, `Closure.moves_spec`, `Closure.moves_violate`,
`Closure.applyMoves_litCap_addr`, `Closure.moveAddr_num`, `Closure.repairList_height`;
`Closure/Caps.lean`.
**Difficulty:** M — about 450 LOC.
**Testable:** yes. Items 1, 2, 4, 5 and 6 were tested by U3's verifier under the names R11, R12, R18
and R19 (T3: 480,781 caps; T4(b): 942,009 marked pairs; T4(e): 96,199 repair records), 0 failures.

### D3.3 Kernel `F_E` and context `C_E`   (paper: txt:421-426)
**Fidelity:** simplified (S-6: one typed continuation hole; the kernel is written with the locked
`replaceAt`, i.e. `Scan.Hole.fill`, and both root locations share one definition).
**Statement.** For an ordinary input `E` with data `sd`, `rd` (Conventions):
1. `rootForest`, `rootCol`, `unconsumed = R[c_A:]`, `period = t − r`, `holeDepth = ℓ − j`,
   `KernelDefined E rd :⇔ (rd.owner → U ≠ [])` (txt:129).
2. `kernel E sd rd X` (`F_E(X)`):
   - body case (`¬rd.owner`): `node ((Q ++ U') :: (replaceAt r d (T_d X) δ (node F[ι+1:])).cols)`,
     where `U'` keeps every outer parent of `U` and shifts its heights by `T_{r,d}`;
   - owner case: `node [Q ++ mapLast (shift heights by T_{r,d})
     (last height ↦ replaceAt r d (T_d X) (δ−1) height) U]`.
3. `context E sd Z = replaceAt 0 0 Z ℓ E` (`C_E(Z)`, also the paper's `fill(E, Z)`, txt:440).
4. `kerPrefix E sd rd = w(F_E(∅))`; `kerSigma sd rd (e, μ, q) = (e + 2δ, μ, q)` if `e` is even and
   `μ = 0` (an empty-column atom `(2e', 0, 0)`; its third coordinate is not a parent), and
   `(e + 2δ, μ, shiftVal r d q)` otherwise; `depthShift e (e', μ, q) = (e' + 2e, μ, q)`.
   [VERIFY-U2 F1: the drafted `Σ` shifted every third coordinate; for `r = 0` it maps `(2e,0,0)` to
   `(2e,0,d)`, and `word_kernel` is false, e.g. `E = L_1 = [[],[(0,∅)]]`, `X = [[],[]]`.]
**Proof.** Definitions. Checked by `#eval` against the locked `expand` (scratch/blueprint/U2/eval.lean,
eval2.lean: `expand E n = some (context E sd ((kernel E sd rd)^[n] ∅))` for `n ≤ 3` on a body-case,
an owner-case, a consumed-root case with nonempty `Q`, and a side-height case).
**Uses:** —
**Lean:** `Closure.rootForest`, `rootCol`, `unconsumed`, `period`, `holeDepth`, `KernelDefined`,
`kernel`, `context`, `kerPrefix`, `kerSigma`, `depthShift`; `Closure/Kernel.lean`.
**Difficulty:** S.
**Testable:** yes (as above; extend to all generated ordinary standards with U1's `stopData`).

### D3.3a Iterate identity   (paper: txt:422)
**Fidelity:** as in paper (G-001: stated for the locked `expand` on nonempty V∧I inputs).
**Statement.**
1. (`expand_eq_iterate`) If `E ≠ ∅`, V, I, `stepKind E = some .ordinary`, `stopData E = some sd`,
   `rootData E = some rd`, and `KernelDefined E rd`, then for all `n`,
   `expand E n = some (C_E(F_E^n(∅)))`.
2. (`expand_none_iff`) Under the same hypotheses without `KernelDefined`:
   `expand E n = none ↔ 1 ≤ n ∧ ¬KernelDefined E rd`.
3. (`expand_zero_eq_context`) [VERIFY-U2 F2: added] If `E ≠ ∅`, V, I, `stepKind E = some .ordinary`
   and `stopData E = some sd`, then `expand E 0 = some (C_E(∅))`; no `KernelDefined` hypothesis.
   (Instance with `¬KernelDefined`: `E = [[],[(0,H)]]`, `H = [[(1,∅)],[(2,G),(1,∅)]]`,
   `G = [[(3,∅),(3,∅)]]`; V and I hold, the owner root is exhausted, and the locked `expand` gives
   `expand E 0 = some [[],[(0,[[(1,∅)]])]] = some (C_E ∅)`, `expand E 1 = none`.) Used by T3.2g,
   T3.2 (`expand_lt`) and T3.8c.3, whose inputs need not satisfy `KernelDefined`.
**Proof.**
1. `expand E n = paperOp E n` [spine `expand_eq_paperOp`, D1.6a].
2. `paperOp E n` is `none` iff `owner ∧ n ≠ 0 ∧ U = []`, else `some (replaceAt 0 0 (ordZ E sd rd n) ℓ E)`
   [U1 `paperOp_ordinary`, REQ-U1-1]. This gives part 2. Part 3: at `n = 0` the loop makes no pass,
   so `ordZ E sd rd 0 = ∅` (REQ-U1-1) and `paperOp E 0 = some (C_E ∅)` [VERIFY-U2 F2].
3. Loop identity: with `step_k(Z) = head_k ⌢ A_{r,kd,δ,Z}(F[ι+1:])` (resp. owner form),
   `step_k(T_{(k−1)d} Y) = T_{(k−1)d}(step_1 Y)`. Proof: `T_{(k−1)d}` fixes the outer parents of `U`
   (they are `< r`: the root column has number `r` [U1 `rootData_spec`, REQ-U1-4] and V);
   `T_{r,a} ∘ T_{r,b} = T_{r,a+b}` [U1 `shift_add`, REQ-U1-8];
   `T_{r,a}(A_{r,b,δ,Z}(G)) = A_{r,a+b,δ,T_{r,a}Z}(G)` [U1 `Hole.fill_eq_put`, REQ-U1-7].
4. By induction on `n − k`, after the passes `n, …, k` the loop variable is `T_{(k−1)d}(F_E^{n−k+1}(∅))`;
   at `k = 1` it is `F_E^n(∅)`. So `ordZ E sd rd n = F_E^n(∅)`.
**Uses:** D3.3; U1: D1.5, D1.5b (REQ-U1-7), D1.6, D1.6a.
**Lean:** `Closure.expand_eq_iterate`, `expand_none_iff`, `expand_zero_eq_context` [VERIFY-U2 F2];
`Closure/Kernel.lean`.
**Difficulty:** M — loop induction with shift algebra; about 250 LOC.
**Testable:** yes (D3.3 checks).

### D3.3b Words of kernels and contexts   (paper: txt:422)
**Fidelity:** as in paper.
**Statement.**
1. (`word_context`) If `stopData E = some sd`: `w(C_E(Z)) = w(C_E(∅)) ++ D_ℓ(w(Z))`.
2. (`word_kernel`) If V, `stopData E = some sd`, `rootData E = some rd`:
   `w(F_E(X)) = P ++ (w X).map Σ` with `P = kerPrefix`, `Σ = kerSigma`.
3. `P ≠ []`; `Σ` and `depthShift e` are strictly monotone.
**Proof.**
1. Part 1: `C_E(Z)` is `Hole.put ⟨E, ℓ⟩ Z`, whose word is `w(Hole.put ⟨E, ℓ⟩ ∅) ++ wordAt ℓ Z`
   [U1 `word_put`, REQ-U1-6, with `ℓ < |routeCols E|` from `stopData_spec`, REQ-U1-3], and
   `wordAt ℓ Z = D_ℓ(w Z)` [REQ-U1-18].
2. Part 2: `F_E(X) = Hole.put ⟨node (head :: (T_d F[ι+1:]).cols), δ⟩ (T_d X)` (body; owner: hole
   at depth `δ` through the last restored height) [REQ-U1-7]; then `word_put`, and
   `wordAt δ (T_d X) = (w X).map Σ` [REQ-U1-18 and relabelling, REQ-U1-2]: `T_d` relabels the
   parent coordinate of entry atoms only; empty-column atoms `(2e,0,0)` are unchanged, which is why
   `Σ` fixes the third coordinate of atoms with even depth coordinate and marker `0` (D3.3 item 4).
3. Part 3: the kernel output has a first column, which contributes at least one atom. `Σ` maps the
   block of atoms with first two coordinates `(e, μ)` into the block `(e + 2δ, μ)`, so it preserves the
   order between blocks; inside a block it is the identity (even `e`, `μ = 0`) or `shiftVal r d`, both
   strictly monotone. [VERIFY-U2 F1: proof adapted to the corrected `Σ`.]
**Uses:** D3.3; U1: C1.8, D1.5, D1.5b (REQ-U1-7), D1.6, N1.4 (REQ-U1-18).
**Lean:** `Closure.word_context`, `word_kernel`, `kerPrefix_ne_nil`, `kerSigma_strictMono`,
`depthShift_strictMono`; `Closure/Kernel.lean`.
**Difficulty:** M — about 200 LOC given U1's `word_put`.
**Testable:** yes (`#eval`-checked on 4 kernels and 3 contexts).

### D3.3c Success, covering, kernel conjugacy   (paper: txt:427, 542-546)
**Fidelity:** new (names the two forms of "kernel success" and the phase-conjugacy computation).
**Statement.**
1. `Success K Y :⇔ ∃ sd rd, stopData K = some sd ∧ rootData K = some rd ∧ KernelDefined K rd ∧
   Y < F_K(Y)`.
2. `Covers K B :⇔ ∃ q K', expand K q = some K' ∧ B < K'`.
3. (`kernel_conj`) Let `K, K'` be ordinary with data `(sd, rd)`, `(sd', rd')`, and `r ≤ sd'.r`.
   If `sd.Q = mapCol (shiftVal r δ) sd'.Q`, `sd.r = sd'.r + δ`, `sd.t = sd'.t + δ`,
   `U_K = mapCol (shiftVal r δ) U_{K'}`, equal owner flags, equal hole depths, and the root forest's
   later columns satisfy `node F_K[ι+1:] = shift r δ (node F_{K'}[ι'+1:])`, then
   `F_K(shift r δ X) = shift r δ (F_{K'}(X))` for all `X`.
**Proof** (of 3).
1. Unfold `kernel`; both have the same period `d`.
2. `T_{sd.r,d} ∘ T_{r,δ} = T_{r,δ} ∘ T_{sd'.r,d}` on parents [T3.2h `shiftVal_conj`, `r ≤ sd'.r`];
   it maps over trees, `mapLast`, and `replaceAt` (U1 `Hole.fill_eq_put`, REQ-U1-7).
**Uses:** D3.3, T3.2h; U1: D1.5, D1.5b (REQ-U1-7).
**Lean:** `Closure.Success`, `Covers`, `kernel_conj`; `Closure/Kernel.lean`.
**Difficulty:** S — about 100 LOC.
**Testable:** yes: random `δ` and pairs of kernels built from shifted copies.

### L3.5 Filling identity (1), cancellation (2), root restriction   (paper: txt:438-458, 476-478)
**Fidelity:** simplified (S-6: cancellation `∂_Q` and `e_0/e_1` in the word library).
**Statement.**
1. `rootTail D rd γ = node ((D.colAt rd.col).drop γ :: (forest at rd.col.path).cols.drop (ι+1))`
   (the paper's `rt_{ρ,γ}(D)`, first column retained even if empty); `diamond Q X` (`Q ⋄ X`) prepends
   `Q` to the first column of a nonempty `X`; `encOne X = wordLater 0 X.col₀ ++ wordCols 0 X.rest`
   (`e_1`); `encEps Q X = if Q = [] then w(X) else encOne X` (`e_{ε(Q)}`).
2. **(1)** (`filling_identity`) For an ordinary `K` with V, `stopData K = some sd`,
   `rootData K = some rd`: `F_K(Y) = Q ⋄ T_{ρ,x−ρ}(rt_{ρ,c}(C_K(Y)))`, with `x = t`, `ρ = r`,
   `c = rd.cursor` frozen (no rescan of the filled object).
3. **(2)** (`cancel_eq`) For `X ≠ ∅`: `w(Q ⋄ X) = (if Q = [] then [] else w([Q])) ++ e_{ε(Q)}(X)`;
   (`diamond_lt_iff`) for `Q ≠ []`: `Q ⋄ X < Q ⋄ X' ↔ e_1(X) < e_1(X')`.
4. **L3.5c** (`rootTail_extension`) If `D₁ = safePrefix D₂ π`, `π < µ(D₂)`, `rd.col ∈ D₂.colAddrs`,
   the root entry `γ` starts before the cut (`capPos D₂ rd.col γ < π`), and every atom of `w(D₂)` from
   that start on has depth coordinate `≥ 2·colDepth rd.col` (the root forest is last in `D₂`), then
   `Q ⋄ T_{ρ,δ}(rt(D₁)) < Q ⋄ T_{ρ,δ}(rt(D₂))` for all `Q, ρ, δ`.
**Proof.**
1. (1): `C_K(Y)` changes only the stopping column, which lies in `F[ι+1:]`'s subtree (body case) or
   in the last root entry's height (owner case) [U1 `stopData_spec`, `rootData_spec`; `rootData_owner_iff`
   in U1's draft]. So `rt_{ρ,c}(C_K(Y))` is `node (U :: (replaceAt 0 0 Y δ (node F[ι+1:])).cols)`
   (body) or `node [U with the last height filled]` (owner). Apply `T_{r,d}`: outer parents of `U` are
   `< r`, and `T_{r,d}(replaceAt 0 0 Y δ G) = replaceAt r d (T_d Y) δ G` [REQ-U1-7]. Prepending `Q`
   gives `kernel`.
2. (2): unfold `wordCol` on `Q ++ c` and use `wordLater (l₁ ++ l₂) = wordLater l₁ ++ wordLater l₂`.
   `diamond_lt_iff`: cancel the common prefix `w([Q])`.
3. L3.5c: `w(D₁) = w(D₂).take π` [`word_safePrefix`]. If `γ < |root column|`, the word of `rt(D)` is
   the suffix of `w(D)` from the atom of root entry `γ`, depth-shifted by `−2·colDepth rd.col`, with
   that first atom recoded as a column start; if `γ = |root column|`, it is the marker `(0,0,0)` of the
   retained empty first column followed by the depth-shifted suffix of `w(D)` from position
   `capPos D rd.col γ`. [VERIFY-U2 F9: the draft called both cases a positionwise correspondence; the
   second is shifted by one atom.] In both cases, under the hypothesis on later atoms, `w(rt(D₁))` is a
   proper prefix of `w(rt(D₂))`; `T` (letterwise) and `Q ⋄ ·` ((2)) preserve proper prefixes; a proper
   prefix is smaller.
**Uses:** D3.3, D3.3b, D3.1c; U1: D1.5, D1.5b (REQ-U1-7), D1.9.
**Lean:** `Closure.rootTail`, `diamond`, `encOne`, `encEps`, `filling_identity`, `cancel_eq`,
`diamond_lt_iff`, `rootTail_extension`; `Closure/Kernel.lean` ((1)), `Closure/WordCancel.lean` ((2), L3.5c).
**Difficulty:** M — (1) about 200 LOC, (2) 60 LOC, L3.5c 150 LOC.
**Testable:** yes ((1) checked by `#eval` on the three D3.3 examples).

### T3.2h Shift and normalization identities   (paper: txt:331-336, 572-575)
**Fidelity:** as in paper.
**Statement.** `kappaLabel r d j (false, p) = (false, p + jd)` if `p ≥ r`, identity otherwise;
`kappa r d j = Tree.map (kappaLabel r d j)` (`κ_j`). Then:
1. (`relKey_shift`) `x ≥ r → relKey (x + jd) (T_{r,jd} H) = κ_j (relKey x H)`.
2. (`kappa_add`) `κ_i ∘ κ_j = κ_{i+j}`.
3. (`kappa_strictMono`) `κ_j` is strictly monotone on keys.
4. (`kappa_nu`) `ν(l.map κ_j) = (ν l).map κ_j`.
5. (`kappa_fix`) `x ≤ r → κ_j (relKey x H) = relKey x H`.
6. (`shiftVal_comp`, identity (3)) `ρ ≤ r ≤ x → shiftVal ρ (x+δ−ρ) = shiftVal r δ ∘ shiftVal ρ (x−ρ)`.
7. (`shiftVal_conj`) `r ≤ ρ' → shiftVal (ρ'+δ) d ∘ shiftVal r δ = shiftVal r δ ∘ shiftVal ρ' d`.
8. (`shift_lt_shift`) `T_{r,d} X < T_{r,d} Y ↔ X < Y`.
**Proof.**
1. Part 1: three cases `p < r`, `r ≤ p < x`, `p ≥ x` on each parent (all agree with `relKey` labels).
2. Parts 2, 5, 6, 7: case analysis on `p` against the thresholds.
3. Part 3: `kappaLabel` is strictly monotone in the key-label order (false fields before true ones);
   `Tree.map` of a strictly monotone labelling preserves `Tree.cmp` [U1 `gword_map`, `gword_lt_iff`,
   `list_map_lt_iff`, REQ-U1-2, REQ-U1-16]. Part 8 the same with `shiftVal r d`.
4. Part 4: induction on `l` with `nu_append_singleton` [REQ-U1-13]; a strictly monotone map commutes
   with deleting strictly smaller terminal letters.
**Uses:** U1: C1.8, D2.1.
**Lean:** `Closure.kappaLabel`, `Closure.kappa`, `relKey_shift`, `kappa_add`, `kappa_strictMono`, `kappa_nu`,
`kappa_fix`, `shiftVal_comp`, `shiftVal_conj`, `shift_lt_shift`; `Closure/Ordinary.lean`.
**Difficulty:** S — about 150 LOC.
**Testable:** yes: random forests and thresholds.

### T3.2i Phase classification of ordinary outputs   (paper: txt:318-330)
**Fidelity:** repaired (G-003-style exactness: the paper's "occurrence classes" become explicit
address maps; also R-3).
**Statement.** Let `A ∈ L` be ordinary (data `sd`, `rd`) and `expand A n = some B`.
1. Address maps (real bodies). `underCol h a` places address `a` of a forest whose columns are put at
   hole column `h`. `isQMat sd a` holds iff `a` lies in the height of an entry `j < m` of the stopping
   column. `kerCol sd rd a` maps a template address of `A` to its address in the kernel output:
   Q-heights of entry `j` ↦ under head entry `j`; the root column ↦ the head (column 0); heights of
   root entries `c_A + v` ↦ under head entry `m + v`; body columns `ι+1+z` (body case) ↦ column `1+z`;
   `none` outside the template. `kerHole = kerCol sd.col`. `phaseCol sd rd i a =
   underCol sd.col ((underCol kerHole)^[i−1] (kerCol a))`. `phaseOff sd i a = i − 1` for Q-material,
   else `i`. `IsTmplCol A sd rd a`: a column of `A` with `kerCol a ≠ none`, other than `sd.col`,
   `rd.col`. `OnHoleRoute sd a :⇔ a.path` is a prefix of `sd.col.path`.
2. (`classify_cols`) Every column address `c` of `B` is either a column of `C_A(∅)` other than
   `sd.col`, or `phaseCol i a = some c` for exactly one `(i, a)` with `1 ≤ i ≤ n` and
   `a = rd.col ∨ IsTmplCol a`.
3. (`num_phaseCol`) `phaseCol i a = some c → num(c) = num(a) + phaseOff i a · d` (`i ≥ 1`).
4. (`colAt_phaseCol`) If `IsTmplCol a`, `¬OnHoleRoute a`, `1 ≤ i ≤ n`: the column of `B` at
   `phaseCol i a` is `mapCol (shiftVal r (phaseOff i a · d))` of `A`'s column `a` (pure copy).
5. (`colAt_head`) The head of layer `i` (`phaseCol i rd.col`) has `m + |U|` entries: the first `m`
   are `τ_{i−1}(Q)`, entry `m+v` has `U[v]`'s outer parent and, except for the last entry in the owner
   case, height `τ_i(U[v].height)`.
6. (`localSuffix_phase`) For `IsTmplCol a` and `expand A (n−i) = some A'`: the local suffix of `B` at
   `phaseCol i a` is `τ_{i−1}(localSuffix A a)` for Q-material and `τ_i(localSuffix A' a)` otherwise.
7. (`localSuffix_head`) The local suffix of `B` at the head of layer `i` is `τ_{i−1}(F_A^{n−i+1}(∅))`.
**Proof.**
1. `B = C_A(F_A^n(∅))` [D3.3a; `KernelDefined` from `expand_none_iff`].
2. Fill laws (U2-internal lemmas, part of this node): `colAt (C_A Z) (underCol sd.col a) = colAt Z a`,
   columns of `C_A Z` off `sd.col`'s subtree are those of `C_A ∅`; `colAt (F_A X) (underCol kerHole a)
   = colAt (T_d X) a`; template columns of `F_A X` are `kerCol`-images of `A`'s, shifted by `T_{r,d}`
   (root-tail material) or unshifted (Q-material, the head's first `m` entries are `Q`). By induction on
   `replaceAt`'s depth argument and `Tree.colAt`.
3. Induction on `i`: the content of layer `i` has been shifted by the `i − 1` outer kernels' `T_{r,d}`,
   so its total shift is `τ_i` (root-tail) or `τ_{i−1}` (Q-material) [U1 `shift_add`, REQ-U1-8]. This
   gives parts 4, 5; hole-route columns are excluded in part 4 because their last entries carry the
   next layer.
4. Part 2: a column of `C_A(Z)` is in `C_A(∅)` or under `sd.col`; under `sd.col` it is a template
   image of the outermost kernel (`kerCol` is injective on its domain) or lies under `kerHole` (recurse
   on `F^{n−1}`); the recursion stops after `n` layers (`F^0 = ∅`).
5. Part 3: `num_0(underCol h a) = num_0(h) + num_0(a)` (spine `ColAddr.num`); relative to the kernel
   output, `num_0(kerCol a) = num(a) + d − t` for root-tail material and `num(a) − t` for Q-material;
   in particular `num_0(kerHole) = num(sd.col) + d − t = d`, so each layer adds `d`, and layer `i` is
   placed at absolute offset `t + (i−1)d`.
6. Parts 6, 7: layer `i` from the head on is `τ_{i−1}(F^{n−i+1}(∅))` (step 3), and
   `F(F^{n−i}∅) = Q ⋄ T_d(rt(C_A(F^{n−i}∅))) = Q ⋄ T_d(rt(A'))` [L3.5 (1), D3.3a]; the template local
   suffixes inside are those of `A'` shifted by `τ_i` (Q-heights: unchanged in `A'` only if `n − i ≥ 1`,
   hence the separate Q-material clause using `A` itself).
**Uses:** D3.3, D3.3a, L3.5, T3.2h; U1: D1.5.
**Lean:** `Closure.underCol`, `isQMat`, `kerCol`, `kerHole`, `phaseCol`, `phaseOff`, `IsTmplCol`,
`OnHoleRoute`, `classify_cols`, `num_phaseCol`, `colAt_phaseCol`, `colAt_head`, `localSuffix_phase`,
`localSuffix_head`; `Closure/Ordinary.lean`.
**Difficulty:** L — address algebra through nested holes; about 800 LOC.
**Testable:** yes: `#eval`-checked on two examples (heads and body/side-height copies at phases 1–3,
numbers `+φd`); extend to all generated ordinary standards.

### T3.2l Changed continuations decrease   (paper: txt:345-349)
**Fidelity:** as in paper.
**Statement.** `localSuffix_cont_le`: for `A ∈ L` ordinary, `expand A n = some A'` (any `n`), and `a`
a template column or `rd.col`: `localSuffix A' a ≤ localSuffix A a`, strictly if `OnHoleRoute a` or
(`a = rd.col` and owner).
**Proof.**
1. `A' = C_A(Z')` with `Z' = F^n(∅)`, and `A = C_A(S_0)` with `S_0 = node [Q ⌢ [(r,∅)]]` (the stopping
   column is `Q ⌢ [(r,∅)]` [REQ-U1-3]).
2. `Z' < S_0`: the first column of `Z'` is `Q` followed by `U`'s first entry (parent `< r`, V) or
   ends; `S_0`'s continues with `(r, ∅)`; `n = 0` gives `Z' = ∅`.
3. Off the hole route the local suffix does not contain `sd.col`: equal. On it, the hole is the last
   part of the local suffix's word [D3.3b relativized], so the comparison is decided by step 2.
**Uses:** D3.3a, D3.3b; U1: D1.6.
**Lean:** `Closure.localSuffix_cont_le`; `Closure/Ordinary.lean`.
**Difficulty:** S — about 120 LOC.
**Testable:** yes, on generated ordinary standards.

### T3.2j Body columns lie in the root subtree   (paper: txt:337-340)
**Fidelity:** as in paper.
**Statement.** `body_firstParent`: for `A ∈ L` ordinary and every `x` with `r < x < t` and
`sd.col.resolve 0 x = some o`, column `o` is nonempty with first parent `≥ r`.
**Proof.**
1. Let `fp(y)` be the first parent of a nonempty visible column `y`. At query `∅` the response of a
   nonempty column is `fp` (cursor 0), so A for entry 0 of column `y` says `fp(y)` is an
   `fp`-ancestor of `y − 1` (spine `CondAK`, `Path` at `cutQuery … 0 = []`).
2. The terminal's A-test (entry `m` of column `t`, parent `r`) is a `g_Z`-path to `r` from
   `q_{m−1}` (or `t−1`); by path nesting with `∅ ≤ Z` [spine `path_nesting`, L2.2] it is an
   `fp`-path; with the A-tests of `Q`'s entries, `r` is an `fp`-ancestor of `t − 1`.
3. Downward induction on `x` from `t − 1`: if `r` is an `fp`-ancestor of `x > r`, then of `fp(x)`, and
   `fp(x)` is an ancestor of `x − 1` (step 1), so `r` is an ancestor of `x − 1`.
4. Being a proper `fp`-descendant of `r`, column `x` is nonempty, and `fp(x) ≥ r` (V: `fp` decreases).
**Uses:** U1: L2.2, D2.2 (`CondAK`), D1.2a (`resolve_spec`, REQ-U1-9).
**Lean:** `Closure.body_firstParent`; `Closure/Ordinary.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes, on generated ordinary standards and random L inputs.

### T3.2c Safe prefixes keep V, I, H   (paper: txt:311-312)
**Fidelity:** as in paper.
**Statement.** `safePrefix_condV`, `safePrefix_condI`, `safePrefix_condH`: each of V, I, H passes from
`E` to `safePrefix E k`.
**Proof.**
1. Structure of safe prefixes [REQ-U1-14]: addresses are preserved, every column of the prefix is a
   prefix of the column of `E`, only the last retained entry of a column can have a truncated height,
   which is a safe prefix of the old height, and no new empty internal column arises (a first entry
   carries its column marker, txt:152-153).
2. V: same parents, address-based `resolve`. I: first entries and parents unchanged, columns of
   nonempty heights stay nonempty. H: earlier entries unchanged; a truncated height is `≤` the old one
   [U1 `safePrefix_le`, REQ-U1-14].
**Uses:** U1: D1.9, D1.9b (REQ-U1-14).
**Lean:** `Closure.safePrefix_condV`, `safePrefix_condI`, `safePrefix_condH`; `Closure/SafePrefix.lean`.
**Difficulty:** S — about 150 LOC given REQ-U1-14.
**Testable:** yes (Codex: 280,150 safe prefixes, finite-invariants).

### T3.2d Safe prefixes keep S   (paper: txt:308-311)
**Fidelity:** as in paper (containment-offset argument written with key words).
**Statement.** `safePrefix_condS`: `CondV E → CondS E → CondS (safePrefix E k)`.
**Proof.** Let `γ` be the cut; owner returns of the prefix are owner returns of `E` (addresses and
parents preserved, T3.2c step 1). Fix one with heights `H, J` in `E`.
1. Key words `keyWord (relKey a H)` have the positions and length of `w(H)` [`keyWord` via U1's
   generic word; `gword_map`, REQ-U1-2]. Truncating a height at a word position truncates its key word
   there.
2. `J`'s word occurs in `w(E)` at offset `o_J`, inside `H`'s at `o_H`, with `δ = o_J − o_H ≥ 1`.
3. Cut after `H`: unchanged. Cut in `H` after `J`: `β = γ − o_H ≥ δ + |w J| ≥ |w J| + 1`, so
   T3.2b.2 applies. Cut inside `J` at `α`: `FirstDec` at `α` for the lower key word, and the upper
   one agrees up to `β = α + δ > α`: T3.2b.1. Cut before `J`'s entry: no return.
4. Key-word order is key order [REQ-U1-2].
**Uses:** T3.2b, T3.2c; U1: C1.8.
**Lean:** `Closure.keyWord`, `safePrefix_condS`; `Closure/SafePrefix.lean`.
**Difficulty:** M — offsets of nested words; about 250 LOC.
**Testable:** yes (as T3.2c).

### T3.2e Safe prefixes keep A   (paper: txt:312-313)
**Fidelity:** as in paper (with the explicit barrier and capping lemmas of G-006).
**Statement.** `safePrefix_condA`: `InL E → CondA (safePrefix E k)`.
**Proof.** Let `E' = safePrefix E k`.
1. `E'` has V and S [T3.2c, T3.2d].
2. Decorated A for `E'` with `sel = routeCols E'`: take any entry test of `E'` and its actual A-path
   in `E` (same query: an entry's query uses only earlier keys, which are complete). For an edge at a
   column `o`: if `o` is not on `E'`'s route, keys and response are those of `E`. If it is, `o` is a
   container of the tested column (route columns are last in their forests, so a visible route column
   is a container; codex-crosscheck-1 Q2, point 2), and the complete-cut barrier gives `W < B_o(v)` for
   its active entry `v` [U1 `cut_barrier`, L2.3, REQ-U1-11]; so the cursor stops at or before `v`,
   and replacing key `v` by `⊤` and deleting later keys preserves it [trace facts (2), L2.5, REQ-U1-10].
3. `capping_iff` on `E'` (V, S) turns decorated A into A [L2.4, REQ-U1-12].
**Uses:** T3.2c, T3.2d; U1: L2.3, L2.4, L2.5.
**Lean:** `Closure.safePrefix_condA`; `Closure/SafePrefix.lean`.
**Difficulty:** M — about 250 LOC.
**Testable:** yes (as T3.2c).

### T3.2f Safe prefixes keep P   (paper: txt:314-318)
**Fidelity:** as in paper.
**Statement.** `safePrefix_condP`: `InL E → CondP E → CondP (safePrefix E k)`.
**Proof.**
1. A safe prefix of a height has profile `≤` the old one (the first-entry branch is a prefix).
2. If the upper profile is unchanged: `π(J') ≤ π(J) < π(H) = π(H')`.
3. If it decreased, the cut lies within the first `d + m` atoms of `w(H)`, which are the branch
   (L3.1b tower shape): `H'` is a pure tower `(d', m') < (d, m)` and nothing else. Its owner returns:
   the first entry of the next level (`π` loses a level) or run entries at depth 0 (height `∅`).
**Uses:** L3.1b, T3.2c.
**Lean:** `Closure.safePrefix_condP`; `Closure/SafePrefix.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes (as T3.2c).

### T3.2g Deletions and zero-parameter ordinary steps are safe prefixes   (paper: txt:96-97, 132-133)
**Fidelity:** as in paper (G-001: nonempty V∧I hypothesis).
**Statement.** `expand_safePrefix`: if `E ≠ ∅`, V, I, the step is a deletion, or ordinary with `n = 0`,
and `expand E n = some E'`, then `E' = safePrefix E k` for some `k < µ(E)`.
**Proof.** Deletion: `E' = node (E.cols.dropLast)` [spine `expand_deletion`], `w(E) = w(E') ++ [(0,0,0)]`;
conclude by `word_safePrefix`, `word_injective`. Ordinary `n = 0`: `E' = C_E(∅)` [D3.3a part 3,
`expand_zero_eq_context`; VERIFY-U2 F2: part 1 needs `KernelDefined`, unavailable under V, I], and
`w(E) = w(C_E ∅) ++ D_ℓ(w S_0)` [D3.3b, T3.2l step 1].
**Uses:** D3.3a, D3.3b; U1: C1.8, D1.6a, D1.9.
**Lean:** `Closure.expand_safePrefix`; `Closure/SafePrefix.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.2k Ordinary outputs satisfy V and I   (paper: txt:340-344)
**Fidelity:** as in paper.
**Statement.** `condV_ord`, `condI_ord`: `InL A`, ordinary, `expand A n = some B` imply V and I of `B`.
**Proof.**
1. V means "every parent is below its column's number" [U1 `resolve_spec`, REQ-U1-9]. By T3.2i,
   context entries are unchanged; a phase copy has parent `shiftVal r (φd) p` and column number
   `num + φd` [T3.2i.3–5], and `shiftVal r δ p ≤ p + δ`; head query entries: `τ_{i−1}(q) < t+(i−1)d = s_i`;
   restored entries: parents `< r < s_i`.
2. I for copied heights: shifting a height and its host by the same `T_{r,φd}` preserves
   "first parent ≥ host" (cases host `≥ r` and `< r`); body forests placed in the stopping forest have
   first parents `≥ r` [T3.2j], shifted `≥ r + φd`, above the host.
3. I for the head as a column of a nonempty height (`ℓ > 0`, host `a` of the stopping forest): if
   `Q ≠ []` its first parent is `τ_{i−1}(q_0)` and `q_0 ≥ a` (I in `A`); if `Q = []`, I in `A` gives
   `r ≥ a` and `r ≠ a` (else the step is special), so `a < r < t` and the root column `R` is a column
   of the stopping forest; the cursor against the empty query is 0, so the whole `R` is restored and
   the head's first parent is `R`'s, which is `≥ a` by I in `A`. Layer `i ≥ 2` is the image of layer 1
   under the shifts of T3.2i, which preserve "first parent `≥` host".
**Uses:** T3.2i, T3.2j; U1: D1.2a.
**Lean:** `Closure.condV_ord`, `condI_ord`; `Closure/Ordinary.lean`.
**Difficulty:** M — about 300 LOC.
**Testable:** yes (general-L check: 93,960 operations).

### T3.2x Ordinary outputs satisfy H   (paper: txt:345-349)
**Fidelity:** as in paper.
**Statement.** `condH_ord`: `InL A`, ordinary, `expand A n = some B` imply H of `B`.
**Proof.**
1. Heads: `τ_{i−1}(Q)` is nonincreasing (H in `A`, monotone shift); its last parent is `≥ r` (A gives
   parent monotonicity on column `t`, whose last parent is `r`), the restored parents are `< r`; the
   restored entries are nonincreasing (H of `R`, heights shifted by the same `τ_i` [T3.2h.8]).
2. Pure copies: monotone maps preserve H. Continuation entries: their height is `≤` the shifted
   prototype [T3.2l], so still `≤` the previous entry.
3. Context containers of `sd.col`: last heights decreased [T3.2l]; other context entries unchanged.
**Uses:** T3.2i, T3.2l, T3.2h.
**Lean:** `Closure.condH_ord` (strict decrease is proved in T3.2); `Closure/Ordinary.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes.

### T3.2m Owner returns of ordinary outputs have old origins   (paper: txt:350-362)
**Fidelity:** as in paper (the "list of returns" becomes an existence statement with word positions).
**Statement.** `ownerReturn_origin`: for `A ∈ L` ordinary, `expand A n = some B`, and an owner return
`(e0', e')` of `B` with heights `H', J'`, there are an owner return `(e0, e)` of `A` with heights
`H, J` and a phase `j` such that, writing `kX` for `keyWord` of the normalized key and `κ_j`-images of
the old keys: either `kH' = kH` and `kJ' = kJ`, or there is `b` with `kH'.take b = kH.take b`,
`b ≤ |kH'|`, `kH' ≤ kH`, and either `kJ' = kJ` with `|kJ| < b`, or `FirstDec kJ kJ' a` for some `a < b`.
**Proof.** By T3.2i classify `e0'` and `e'`.
1. Pure-copy upper height (closed copy or unchanged): `e'` lies in the copy; parent equality with the
   owner number is preserved by the injective shift; keys are `κ_φ`-images [T3.2h.1] or unchanged.
2. Upper owner fixed, `a < r` (a context container): the whole template lies in its height (all
   visible columns `> a` lie inside it); a shifted parent equals `a` iff the old parent did; use the
   lower phase's `κ_j`, which fixes the upper key [T3.2h.5].
3. Upper owner `a + jd` with `r ≤ a < t` (a phase-`j` route container): later body/restored phases
   `k ≥ j+1` have parents `< r` or `≥ r + kd > a + jd`; restored outer parents are `< r`; a query
   copy in layer `k` returns iff `p + (k−1)d = a + jd`, impossible for `k ≥ j+2` (it would give
   `p < r`, contradicting that `p` was shifted); so only the first following query (layer `j+1`,
   phase `j`) can return, with origin the old query entry inside the same old height.
4. Positions: both changed heights change first at the image of the old terminal; the lower's first
   change precedes the upper's by its positive containment offset (T3.2d step 2); if only the upper
   changes, the whole lower occurrence ends before it [T3.2l].
**Uses:** T3.2i, T3.2h, T3.2l, T3.2b.
**Lean:** `Closure.ownerReturn_origin`; `Closure/Ordinary.lean`.
**Difficulty:** L — exhaustive origin analysis; about 700 LOC.
**Testable:** yes: enumerate owner returns of outputs of generated ordinary standards.

### T3.2n Ordinary outputs satisfy S   (paper: txt:363-366)
**Fidelity:** as in paper (no output A assertion is used).
**Statement.** `condS_ord`: `InL A`, ordinary, `expand A n = some B` imply S of `B`.
**Proof.** For each owner return, T3.2m gives the old pair; S in `A` and `κ_j` order-preserving
[T3.2h.3] give `kJ < kH`; T3.2b.1 or T3.2b.2 give `kJ' < kH'`; key-word order is key order
[REQ-U1-2].
**Uses:** T3.2m, T3.2b, T3.2h; U1: C1.8.
**Lean:** `Closure.condS_ord`; `Closure/Ordinary.lean`.
**Difficulty:** S — about 80 LOC.
**Testable:** yes.

### T3.2o Ordinary steps preserve P   (paper: txt:367-376)
**Fidelity:** as in paper (S-6: P separate from L).
**Statement.** `condP_ord`: `InL A`, `CondP A`, ordinary, `expand A n = some B` imply `CondP B`.
**Proof.**
1. Pure copies preserve profiles (an injective parent map keeps the tower depth and the run length);
   continuations can only lower a profile.
2. Upper profile unchanged: `π(J') ≤ π(J) < π(H) = π(H')`.
3. Upper profile decreased while a head remains: its first-entry branch reaches the old terminal,
   intervening containers are singletons, and the stopping column is `m ≥ 2` empty entries with parent
   `r = t − 1`, `d = 1` (otherwise the leading profile is unchanged, or the step would be special);
   the profile goes from `(h, m)` to `(h, m−1)`. Returns: owners before `r−1` have only their first
   chain return (one level lost); owner `r−1` sees restored returns of depth 0 or empty height; owner
   `r` and its copies see only the empty entries of the next query.
4. Continuation heights without a head (layer `n`) are safe prefixes: T3.2f.
**Uses:** T3.2i, T3.2m, T3.2f, L3.1b.
**Lean:** `Closure.condP_ord`; `Closure/Ordinary.lean`.
**Difficulty:** L — the decreased-profile case; about 500 LOC.
**Testable:** yes (Codex finite invariants include P on 8,361 standards).

### T3.2q Paths through heads   (paper: txt:390-394, 524-530)
**Fidelity:** as in paper (the detour deletion is stated as a path-transport lemma in both
directions).
**Statement.** Let `A ∈ L` be ordinary, `expand A n = some B`, `1 ≤ j ≤ n`, `a` a template column with
copy `c = phaseCol j a`, `φ = phaseOff j a`, `W` a reduced query, `y < r`.
1. (`head_path`) A `g_{κ_φ W}`-path in `B` on `c`'s stack from `x ≥ s_φ` to `y` gives a `g_W`-path in
   `A` on `a`'s stack from `x − φd` (from `r` if `x = s_φ`) to `y`.
2. (`head_path_rev`) Conversely, a `g_W`-path in `A` (actual keys) from `x0 ≥ r` to `y` gives a
   `g_{κ_φ W}`-path in `B` **in the decorated system `capKeys B (routeCols B)`** from `x0 + φd` (from
   `s_φ` if `x0 = r`) to `y`. [VERIFY-U2 F4: the draft concluded a path for the actual keys of `B`,
   which is false: in `A = [[],[(0,[[(1,[[(2,∅),(1,∅)]])]])]]`, `n = 1`, template `a` = the column of
   number 2, `W = B_a(0)`, the old path `1 → 0` exists, but in `B` the head `s_1 = 3` has the
   continuation last key `h_3([[(3,∅)]])`, which `κ_1 W` consumes, so the scan is exhausted. In the
   decorated system that key is `⊤` and the cursor is `m + γ − c_A` (T3.2p.2 after trace fact (2)).]
**Proof.**
1. Edges at phase-`φ` body columns are copies: keys `κ_φ`-related [T3.2h.1, T3.2i.4], equal cursors
   [trace fact (1), REQ-U1-10], shifted responses.
2. At a head `s_h` (`1 ≤ h ≤ φ`) with query `V = κ_{h−1}(W_h)`, `W_h = κ_{φ−h+1} W`: if `W_h ≥ Z` (high)
   the cursor is `m + γ − c_A` [T3.2p.2 with `qs = κ_{h−1}(y)`, root keys `κ`-fixed T3.2h.5,
   `κ_{h−1}Z` between the boundaries `B_{c_A−1}`, `B_{c_A}` (spine L2.1, T3.2h)], so the response is
   `R`'s response at `W` (`γ = cursor R V = cursor R W` by T3.2h.5 and trace fact (1)). If low, the
   response is `τ_{h−1}` of the old terminal's response at `κ_1 W_h' < Z`; path nesting [L2.2] turns the
   terminal-to-root path at `Z` into one at that query, with vertices in `(r, t)`; its copy in phase
   `h−1` leads to `s_{h−1}`.
3. The head index decreases at each detour; the process ends at a high exit or at `r` itself, whose
   keys are fixed, giving `R`'s response at `W` again. Deleting the detours gives the old path; below
   `r` all columns and responses are shared (keys normalized below `r` are `κ`-fixed).
4. Part 2 runs the same construction forwards, in the decorated system of `B`: at a head `s_h` the
   decorated keys are `κ_{h−1}(qs) ⌢ R[c_A:]` with the last key replaced by `⊤` when the head is a route
   column (owner case); the old scan of `R` at `W` is not exhausted (the old path has an edge there), so
   trace fact (2) [REQ-U1-10] replaces `R`'s last key by `⊤` without changing its cursor, and T3.2p.2
   applies to the decorated head keys. Phase-`φ` route columns of `B` likewise carry `⊤` as last key; an
   old non-exhausted scan at the corresponding column of `A` has the same cursor against `⊤` (trace fact
   (2)). [VERIFY-U2 F4]
**Uses:** T3.2h, T3.2i, T3.2p; U1: L2.1, L2.2, L2.5.
**Lean:** `Closure.head_path`, `head_path_rev`; `Closure/Ordinary.lean`.
**Difficulty:** L — path surgery with an induction on the head index; about 600 LOC.
**Testable:** yes: all tests of outputs of generated ordinary standards.

### T3.2r Ordinary outputs satisfy A   (paper: txt:377-403)
**Fidelity:** as in paper.
**Statement.** `condA_ord`: `InL A`, ordinary, `expand A n = some B` imply A of `B`.
**Proof.**
1. Work with independently capped continuation-dependent last keys: decorated A of `A`
   [`capping_iff`, L2.4, REQ-U1-12] and target decorated A of `B` (S of `B` by T3.2n, V by T3.2k; then
   `capping_iff` gives A).
2. Classes [T3.2i]: (a) retained context entries have the same assigned fields and paths;
   (b) body entries and entries in restored heights copy their source paths, with the head
   substitution at the root [T3.2q.2, which yields paths in the decorated system of `B`, exactly the
   target of step 1; VERIFY-U2 F4]; (c) entries inside a query height read their head only below
   that query entry's complete boundary [U1 `barrier`, L2.3, REQ-U1-11], hence use the pure query part,
   then (b); (d) query-prefix entries copy the old terminal tests; (e) the first restored entry: the old
   terminal's last test reaches `r` (copied to `s_{i−1}`), and at `s_{i−1}` the high response is the
   restored parent `p_{c_A}` [T3.2p.2]; (f) later restored entries: the reset query is the old root
   boundary [T3.2p.1], both endpoints `< r`, the old test of `R[c_A+v]`.
3. Uncap by `capping_iff`.
**Uses:** T3.2i, T3.2k, T3.2n, T3.2p, T3.2q; U1: L2.3, L2.4.
**Lean:** `Closure.condA_ord`; `Closure/Ordinary.lean`.
**Difficulty:** XL — six test classes over all layers, with decorated systems on both sides; about
2000 LOC.
**Testable:** yes (general-L check).

### T3.2s Special outputs satisfy V, I, H   (paper: txt:404-407)
**Fidelity:** as in paper.
**Statement.** `condVIH_special`: `InL A`, `stepKind A = some .special`, `expand A n = some B`
imply V, I, H of `B`.
**Proof.** `B` replaces the owner column `P ⌢ [(p, C ⌢ [[(a,∅)]])]` by `P ⌢ [(p,C)]^{n+ε}`
[U1 `paperOp_special`, REQ-U1-5]. Copies of `(p, C)` have the same parent and host; `C` keeps its
columns, numbers and first parents (I); equal copies and `P`'s last entry `≥ (p, C⌢[[(a,∅)]]) > (p,C)`
give H.
**Uses:** U1: D1.6a.
**Lean:** `Closure.condVIH_special`; `Closure/Special.lean`.
**Difficulty:** S — about 150 LOC.
**Testable:** yes.

### T3.2t Special outputs satisfy S, and P when present   (paper: txt:406-409)
**Fidelity:** as in paper.
**Statement.** `condS_special`, `condP_special` (the latter with `CondP A`).
**Proof.** Returns cannot cross sibling copies (separate scopes). Every changed height (`C` for
`C⌢[[(a,∅)]]`, and the containers) is a decrease first changing at the old last atom; the
containment-offset argument of T3.2d gives S [T3.2b]. P: a changed first-entry profile forces singleton
containers, `P = ∅`, `C` a pure tower shortened by one level ending in `n+1` empty entries; its returns
lose a level or have empty height; otherwise the profile is unchanged or the output is a safe prefix
[T3.2f].
**Uses:** T3.2b, T3.2d, T3.2f, L3.1b.
**Lean:** `Closure.condS_special`, `condP_special`; `Closure/Special.lean`.
**Difficulty:** M — about 300 LOC.
**Testable:** yes.

### T3.2u Special outputs satisfy A   (paper: txt:410-412)
**Fidelity:** as in paper.
**Statement.** `condA_special`: `InL A`, special, `expand A n = some B` imply A of `B`.
**Proof.** Cap the changed final entry and its active ancestors: the old decorated suffix is `(p, ⊤)`,
the new one is parent-`p` entries ending in `(p, ⊤)`; every finite query returns `p` (as in L3.1g step 3).
The first new entry uses the old test; later ones use the reflexive start `p`; internal copies see the
same external responses. S of `B` [T3.2t] and `capping_iff` [L2.4] uncap.
**Uses:** T3.2t, T3.2s; U1: L2.4.
**Lean:** `Closure.condA_special`; `Closure/Special.lean`.
**Difficulty:** M — about 250 LOC.
**Testable:** yes.

### T3.2v Seeds; T3.2w the empty forest   (paper: txt:412-413)
**Fidelity:** as in paper.
**Statement.** `seed_inL m`, `seed_condP m`, `inL_empty`, `condP_empty`.
**Proof.** `L_m`: column `i` has the single entry with parent `i−1` (visible: V), each height has one
column with first parent equal to its host (I), singletons (H), entry tests are reflexive (start
`c − 1 = i − 1`: A), the only returns are first entries of the next level with profile `(d−1, 1) <
(d, 1)` (P), and S follows by L3.1a. `L_0 = [[]]` and `∅` have no entries.
**Uses:** L3.1a.
**Lean:** `Closure.seed_inL`, `seed_condP`, `inL_empty`, `condP_empty`; `Closure/Special.lean`.
**Difficulty:** S — induction on `m` with `branch`.
**Testable:** yes (`#eval` of the checkers on seeds).

### T3.2 Closure theorem   (paper: txt:301-414)
**Fidelity:** repaired (G-001: decrease and closure are stated for the locked `expand`; `∅[n] = ∅`
is handled by `expand_empty`; S-6: P is a separate invariant).
**Statement** (spine contracts):
`std_inL : IsStd E → InL E`; `std_condP : IsStd E → CondP E`;
`inL_expand : InL E → expand E n = some E' → InL E'`;
`condP_expand : InL E → CondP E → expand E n = some E' → CondP E'`;
`inL_safePrefix : InL E → InL (safePrefix E k)`;
`expand_lt : E ≠ ∅ → CondV E → CondI E → expand E n = some E' → E' < E`.
**Proof.**
1. `inL_safePrefix`: T3.2c, T3.2d, T3.2e.
2. `inL_expand`: if `E = ∅`, `E' = ∅` [spine `expand_empty`], `inL_empty`. Otherwise `stepKind E` is
   some [spine `stepKind_isSome`]: deletion or ordinary `n = 0` — T3.2g and step 1; special — T3.2s,
   T3.2t, T3.2u; ordinary `n ≥ 1` — T3.2k, T3.2x, T3.2r, T3.2n.
3. `condP_expand`: the same split with T3.2f, T3.2t, T3.2o.
4. `std_inL`, `std_condP`: induction on `IsStd` (D1.7) with T3.2v and steps 2–3.
5. `expand_lt`: `expand = paperOp` [D1.6a]; deletion: proper prefix; special: the owner column
   `P ⌢ [(p, C⌢[[(a,∅)]])]` becomes `P ⌢ [(p,C)]^{n+ε}` [REQ-U1-5], and the comparison is decided at
   entry `|P|`: `(p, C) < (p, C⌢[[(a,∅)]])` because `C` is a proper prefix, or the new column ends
   there (`n + ε = 0`) [VERIFY-U2 F8: the draft cited T3.2s, which assumes `InL`]; ordinary:
   `E = C_E(S_0)`, `E' = C_E(Z')` with `Z' = F^n(∅)` [D3.3a part 1 for `n ≥ 1`, where `KernelDefined`
   follows from definedness by `expand_none_iff`; part 3 for `n = 0`], `Z' < S_0`, and `w(C_E ·)` is
   `w(C_E ∅) ++ D_ℓ(w ·)` [D3.3b, T3.2l steps 1–2]. Only V and I are used (U's parents `< r` by V).
**Uses:** T3.2c, T3.2d, T3.2e, T3.2f, T3.2g, T3.2k, T3.2l, T3.2x, T3.2n, T3.2o, T3.2r, T3.2s, T3.2t,
T3.2u, T3.2v, T3.2w, D3.3a, D3.3b; U1: D1.6a, D1.7.
**Lean:** spine `Closure.std_inL`, `std_condP`, `inL_expand`, `condP_expand`, `inL_safePrefix`,
`expand_lt`; `Closure/Special.lean` (assembly).
**Difficulty:** S — assembly, about 150 LOC.
**Testable:** yes (claude-cofinality, general-l, finite-invariants checks).

### T3.2a The Lean `IsStd` is the paper's Std   (paper: txt:138-143)
**Fidelity:** repaired (G-001, spine node T3.2a).
**Statement.** `isStd_iff_paper E : IsStd E ↔ ∃ m ns, ns.foldlM paperOp (seed m) = some E`.
**Proof.**
1. (→) Induction on `IsStd`. Seed: `ns = []`. Step `expand e n = some e'`: if `e = ∅` then `e' = ∅ = e`
   [`expand_empty`], same `ns`; else `e ∈ L` [T3.2 `std_inL`], so `expand e n = paperOp e n`
   [D1.6a], append `n` (`List.foldlM_append`).
2. (←) Induction on `ns` from the right: `paperOp F n = some F'` forces `F ≠ ∅` (paperOp's step 1);
   `F` standard gives V, I [T3.2]; so `expand F n = some F'` and `IsStd F'`.
**Uses:** T3.2; U1: D1.6a, D1.7.
**Lean:** spine `Closure.isStd_iff_paper`; `Closure/Special.lean`.
**Difficulty:** S — about 80 LOC.
**Testable:** yes (reference-diff check compares the operations).

### T3.8n Cofinality predicates   (paper: txt:489-494, 504)
**Fidelity:** new (names the induction predicates of the proof).
**Statement.**
1. `Cof B :⇔ ∀ E, InL E → B < E → ∃ n E', expand E n = some E' ∧ B ≤ E' ∧ E' < E` (T3.8 for the
   single target `B`).
2. `KS B :⇔ ∀ c k p, IsUpward B c k p → InL (litCap B c k p) → Covers (litCap B c k p) B` ("kernel
   success for ordinary L caps of `B`", txt:504, in covering form; ordinariness is derived, T3.8c).
3. `CC B :⇔` every upward cap `K = litCap B c k p` with V, I and decorated A has `Success K (Y_K)`
   (the conclusion of L3.6).
**Proof.** Definitions.
**Uses:** D3.3c.
**Lean:** `Closure.Cof`, `KS`, `CC`; `Closure/Cofinality.lean` (`CC` in `Closure/CapCompletion.lean`).
**Difficulty:** S.
**Testable:** `KS` on bounded targets is the Codex "admissible upward caps at µ(B)+1" check (394
quick, 84,291 full-run caps; 0 failures).

### T3.8a An empty last column is least   (paper: txt:493)
**Fidelity:** as in paper.
**Statement.** `le_of_lt_append_empty`: `B < node (F.cols ++ [[]]) → B ≤ F`.
**Proof.** Compare `B.cols` with `F.cols ++ [[]]` columnwise (`Tree.cmpCols`, locked): a first
difference inside `F.cols` decides `B < F`; if `F.cols` is a proper prefix of `B.cols`, the next column
of `B` is `≥ []` (the empty column is least), giving `B ≥ node (F.cols ++ [[]])`, a contradiction
unless `B = F`; if `B.cols` is a prefix of `F.cols`, `B ≤ F`.
**Uses:** —
**Lean:** `Closure.le_of_lt_append_empty`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes (random forests).

### T3.8b Approximants strictly increase   (paper: txt:494)
**Fidelity:** as in paper.
**Statement.** `expand_strictMono`: for `E ∈ L`, `E ≠ ∅`, last outer column nonempty, `n < n'`,
`expand E n = some X`, `expand E n' = some Y`: `X < Y`.
**Proof.** Ordinary: `X = C_E(F^n ∅)`, `Y = C_E(F^{n'} ∅)` [D3.3a]; words `w(C_E ∅) ++ D_ℓ(kerIter n)` and
`… kerIter n'` [D3.3b]; proper prefix [L3.4a]. Special: the owner column has `n+ε < n'+ε` copies of
`(p, C)` and is the last thing in the word [REQ-U1-5, REQ-U1-6]: proper prefix.
**Uses:** D3.3a, D3.3b, L3.4; U1: D1.5, D1.6a.
**Lean:** `Closure.expand_strictMono`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.8c Caps are ordinary, their data and zero approximant   (paper: txt:539-540)
**Fidelity:** as in paper.
**Statement.**
1. (`stopData_litCap`) `IsUpward B c k p → stopData (litCap B c k p) = some ⟨colDepth c, c,
   c.num 0, p, (B.colAt c).take k⟩`.
2. (`litCap_ordinary`) If `B` has I, `IsUpward B c k p`, and `K = litCap B c k p` has V and I, then
   `stepKind K = some .ordinary`.
3. (`expand_zero_litCap_lt`) Under the hypotheses of 2, `expand K 0 = some K0 → K0 < B`.
**Proof.**
1. Part 1: `litCap` keeps only last columns and last entries along `c.path`, and column `c` ends with
   `(p, ∅)`, so the route stops there [U1 `stopData_spec` / route characterization, REQ-U1-3].
2. Part 2: not a deletion (the last outer column contains a containing entry or `(p,∅)`). Special
   would need depth `> 0`, `k = 0` and `p` the direct owner `a`; but column `c` of `B` is a column of
   a nonempty height, nonempty by I with first parent `≥ a`, and upwardness gives `p >` that parent.
   The root `p` resolves by V of `K` [U1 `stepKind_ordinary_iff`, REQ-U1-15].
3. Part 3: `K0 = C_K(∅)` [D3.3a part 3, with `K` ordinary by part 2; VERIFY-U2 F2/F6: part 1 would
   need `KernelDefined`, and the Lean signature now carries `CondI B`, as part 2 requires], whose word is
   `w(B).take (capPos B c 0)` [L3.1c.1, D3.3b];
   column `c` contributes at least one atom after it, so this is a proper prefix of `w(B)`.
**Uses:** L3.1c, D3.3a, D3.3b; U1: D1.6, D1.6a.
**Lean:** `Closure.stopData_litCap`, `litCap_ordinary`, `expand_zero_litCap_lt`; `Closure/Cofinality.lean`.
**Difficulty:** S — about 150 LOC.
**Testable:** yes (all `caps` of generated standards).

### N2.2 Local suffix decomposition and fill   (paper: new; txt:440, 460, 586-589)
**Fidelity:** new.
**Statement.**
1. (`word_localSuffix`) For `c ∈ B.colAddrs`: `w(B) = w(B).take (capPos B c 0) ++ D_e(w(Y)) ++ S`
   with `e = colDepth c`, `Y = localSuffix B c`, and the first atom of `S` (if any) has depth
   coordinate `< 2e`.
2. (`context_litCap_localSuffix`) For an upward cap `K = litCap B c k p` with stop data `sd`:
   `C_K(Y_K) = safePrefix B (capPos B c 0 + µ(Y_K))`; it equals `B` iff `S = []` in part 1 (the forest of
   `c` is on `B`'s route).
**Proof.** Part 1 from the word recursion (the columns of `c`'s forest from `c` on are contiguous in
`w(B)`, followed by the continuation of the containing levels, whose atoms are shallower)
[REQ-U1-2 `gwordAt_fst_ge`]. Part 2: `w(C_K Y_K) = w(C_K ∅) ++ D_e(w Y_K)` [D3.3b], `w(C_K ∅) =
w(B).take (capPos B c 0)` [T3.8c.3 step], then `word_safePrefix`, `word_injective`.
**Uses:** D3.3b, T3.8c, L3.1c; U1: C1.8, D1.9.
**Lean:** `Closure.word_localSuffix`, `context_litCap_localSuffix`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes.

### T3.8d Between `E[1]` and `E`, `E` is a cap of the target   (paper: txt:496-499)
**Fidelity:** as in paper.
**Statement.** `ordinary_cap_of_between`: for `E ∈ L` ordinary with stop data `sd`,
`expand E 1 = some E1`, and `E1 < B < E`: `IsUpward B sd.col |Q| r` and `litCap B sd.col |Q| r = E`.
(`B` is an arbitrary forest.)
**Proof.**
1. `E = C_E(S_0)`, `E1 = C_E(F_E ∅)` [D3.3a; `KernelDefined` from `expand_isSome` (spine L2.4) and
   `expand_none_iff`].
2. `w(E) = X ⌢ [z]` with `X = w(C_E ∅) ++ D_ℓ(w([Q]))`, `z = capAtom sd.col |Q| r`; `w(E1) = X ⌢ T`,
   `T ≠ []`, and if `Q = []` the first atom of `T` has depth coordinate `2ℓ` (the head column's marker)
   [D3.3b, D3.3 kernel's first column is `Q ++ …`].
3. From `X⌢T < w(B) < X⌢[z]` [`word_lt_iff`]: `w(B) = X ⌢ [y] ⌢ …` with `T[0] ≤ y < z` (a first
   difference inside `X` would decide both comparisons alike).
4. N2.1 (`π = |X|`, `first = (Q = [])`; the depth hypothesis from step 3) gives `c, k` with
   `litCap B c k r = E`, upward; T3.8c.1 applied to both sides identifies `c = sd.col`, `k = |Q|`.
**Uses:** D3.3a, D3.3b, N2.1, T3.8c; U1: C1.8, L2.4.
**Lean:** `Closure.ordinary_cap_of_between`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes: all pairs `E1 < B < E` among generated forests.

### T3.8e Special steps cover   (paper: txt:500-503)
**Fidelity:** as in paper.
**Statement.** `special_cover`: for `E ∈ L` special, `B ∈ L`, `B < E`: some `1 ≤ n ≤ µ(B)+1` has
`B < E[n]`.
**Proof.** Let the owner column be `P ⌢ [(p, C ⌢ [[(a,∅)]])]` at depth `ℓ−1` [REQ-U1-5].
1. If `B < E[1]`, `n = 1`. If `B = E[1]`, `n = 2` [T3.8b]; `µ(B) ≥ 1` since `B` keeps the empty outer
   column 0 (V).
2. If `E[1] < B < E`: `w(B)` agrees with `w(E)` through `w(C)` inside the owner entry, and its next atom
   `y < (2ℓ, 1, a)`; a column start `(2ℓ, μ, q)` there would be an empty internal column (`μ = 0`) or
   have first parent `q < a` (violating I of `B`); so `y` is shallower and `B`'s entry is exactly
   `(p, C)`.
3. By H of `B`, the entries `R_B` after it in that column are `≤ (p, C)`; `|R_B| + 2 ≤ µ(B)` (one atom
   per entry, plus the outer column 0).
4. `n = |R_B| + 2`: `E[n]` has `n + ε ≥ |R_B| + 2` copies, so the column comparison is decided in
   `E[n]`'s favour (at the first entry of `R_B` below `(p, C)`, or when `B`'s column ends).
**Uses:** T3.8b, D3.1c; U1: D1.6a.
**Lean:** `Closure.special_cover`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 250 LOC.
**Testable:** yes (claude-cofinality check covers special steps on standards).

### T3.8f Covering is kernel success   (paper: txt:427-437, 497-499)
**Fidelity:** as in paper (the word criterion transported to forests).
**Statement.** Let `B` have I, `IsUpward B c k p`, `K = litCap B c k p` with V and I.
1. (`covers_iff_success`) If `K`'s kernel is defined: `Covers K B ↔ Success K (localSuffix B c)`.
2. (`covers_bound`) If `K ∈ L` and `Success K Y_K`: some `1 ≤ q ≤ µ(B)+1` has `B < K[q]`.
**Proof.**
1. `K` ordinary [T3.8c.2], stop data [T3.8c.1]; `K[q] = C_K(F_K^q ∅)` [D3.3a].
2. `w(C_K ∅) = w(B).take (capPos B c 0)` and `w(B) = that ++ D_e(w Y) ++ S` [N2.2.1].
3. `B < K[q] ↔ Y < F_K^q(∅)`: compare `D_e(w Y) ++ S` with `D_e(w F^q∅)`, all of whose atoms have depth
   `≥ 2e` while `S`'s first atom is shallower [REQ-U1-2 `gwordAt_append_lt_iff`].
4. `w(F_K^q ∅) = kerIter P Σ q`, `w(F_K Y) = P ++ Σ(w Y)` [D3.3b]; L3.4b gives part 1.
5. Part 2: `q = µ(Y) + 1` satisfies `|w Y| < q·|P|` [L3.4d]; `µ(Y) ≤ µ(B)` by N2.2.1; definedness from
   `InL K` [L2.4].
**Uses:** T3.8c, D3.3a, D3.3b, N2.2, L3.4; U1: C1.8, L2.4.
**Lean:** `Closure.covers_iff_success`, `covers_bound`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes.

### L3.4f Full one-column cuts succeed   (paper: txt:428-429, 436-437)
**Fidelity:** as in paper.
**Statement.** `fullCut_success`: if `IsUpward B c k p`, `K = litCap B c k p ∈ L`, and
`capPos B c k = µ(B)`, then `Success K (localSuffix B c)`.
**Proof.**
1. `capPos = µ(B)` means nothing of `B` follows the cut: `k = |col c|`, `c` is the last column of its
   forest and every container is a last entry of a last column; so `Y = node [col c]` [N2.2.1].
2. `K`'s query is `Q = col c` [T3.8c.1]; `F_K(Y)`'s first column is `Q ++ U'`; `KernelDefined` from
   `InL K` [L2.4, D3.3a]: either `U' ≠ []`, or the body case, where at least one further column follows.
3. Either way `w(Y)` is a proper prefix of `w(F_K Y)`.
**Uses:** N2.2, T3.8c, D3.3; U1: L2.4.
**Lean:** `Closure.fullCut_success`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.8h Caps above a covered old target   (paper: txt:505-506, 511-512)
**Fidelity:** as in paper.
**Statement.** `covers_of_gt`: if `Cof A`, `K ∈ L`, `K ≠ ∅` with nonempty last column, `A < K`,
`B ≤ A`, and `expand K 0 = some K0 → K0 < B`, then `Covers K B`.
**Proof.** `Cof A` gives `A ≤ K[m] < K`. If `B < K[m]`, done. Otherwise `B = A = K[m]`; `m ≠ 0` (else
`K0 = B`), and `K[m+1] > K[m]` [T3.8b, defined by L2.4].
**Uses:** T3.8b; U1: L2.4.
**Lean:** `Closure.covers_of_gt`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** no (pure logic).

### T3.8g Kernel success gives cofinality   (paper: txt:493-499)
**Fidelity:** as in paper.
**Statement.** `cof_of_KS : InL B → KS B → Cof B`; `bound_of_KS`: under the same hypotheses, for
`E ∈ L`, `B < E` and `E`'s last outer column nonempty, some `1 ≤ n ≤ µ(B)+1` has `B < E[n]`.
**Proof.**
1. `E ≠ ∅` (spine `Forest.empty_lt`). Last column empty: `E[0] = node E.cols.dropLast`
   [spine `expand_deletion`], `B ≤ E[0]` [T3.8a], `E[0] < E` [T3.2 `expand_lt`].
2. Otherwise `E[1]` exists [L2.4]. `B < E[1]` or `B = E[1]`: as T3.8e step 1. `E[1] < B`: special —
   T3.8e; ordinary — T3.8d makes `E` an upward L cap of `B`; `KS B` gives `Covers E B`; for the bound,
   T3.8f.1 then T3.8f.2.
3. `E' < E` in all cases by `expand_lt`.
**Uses:** T3.8a, T3.8b, T3.8d, T3.8e, T3.8f, T3.2; U1: D1.1, D1.6a, L2.4.
**Lean:** `Closure.cof_of_KS`, `bound_of_KS`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes (claude-cofinality: 276,818,685 standard pairs in Claude's original run).

### L3.6a Reversed repairs compare suffixes   (paper: txt:463-465)
**Fidelity:** as in paper.
**Statement.** `repair_suffix_ge`: if `B` has H, both `(cj, k, p)` and `(ci, k, p)` are upward caps of
`B`, and a legal move turns `litCap B cj k p` into `litCap B ci k p`, then
`localSuffix B cj ≤ localSuffix B ci` (`Y_j ≤ Y_i`).
**Proof.** The move is `⟨b, i, j⟩` with heights `H_j ≤ H_i` (H); both caps share the internal cap
[L3.1f], so `H_i`, `H_j` agree up to the internal cut position. The local suffix is the middle part
`D_e(w Y)` of the height's word followed by shallower atoms [N2.2.1 relativized], so `H_j ≤ H_i` gives
`Y_j ≤ Y_i` [REQ-U1-2 `gwordAt_append_lt_iff`].
**Uses:** L3.1f, N2.2; U1: C1.8.
**Lean:** `Closure.repair_suffix_ge`; `Closure/CapCompletion.lean`.
**Difficulty:** S.
**Testable:** yes.

### L3.6b Success transfers backward through one move   (paper: txt:466-481)
**Fidelity:** as in paper.
**Statement.** `success_unmove`: with `B ∈ L` and `CondP B` [VERIFY-U2 F5: P added; step 1 uses
L3.1e, which needs P of `B`; the only consumer, L3.6, has it], caps `K_j = litCap B cj k p` (V, I,
decorated A) and
`K_i = litCap B ci k p` related by one legal move `⟨b, i, j⟩` of column `b`, `Success K_i Y_i` implies
`Success K_j Y_j`. Let `ρ = p` be the common root number.
**Proof.**
1. `Y_i ≥ Y_j` [L3.6a]. `K_j` is defined (S by L3.1e, A by `capping_iff`, then L2.4).
2. Case `b < ρ`: the root column, the scan and the hole lie inside the moved subtree, identical in
   both caps (column numbers do not depend on entry indices): `F_{K_j} = F_{K_i}`; downward success
   [L3.4c via D3.3b].
3. Case `b = ρ` (the root is the move column, an owner): the old heights `H_i … H_{j−1}` and the active
   cap agree beyond every query height plus its entry atom, so they have the same strict sign against
   every query key [U1 `sign_of_agreement`, REQ-U1-10]; consuming entry `i` would consume all of them and
   exhaust the owner root, contradicting definedness; hence the cursor is `≤ i` and trace fact (3)
   [`trace_agree`] identifies both scans.
4. Case `b > ρ`: the root is unchanged, or only an owner's last active key changes; both scans leave it
   unconsumed; trace fact (2) [`trace_cap_top`] identifies them.
5. In cases 3–4 the cursors, `Q`, `x`, `ρ` agree; `C_{K_i}(Y_i)` and `C_{K_j}(Y_j)` are safe truncations of
   `B`, the second properly extending the first [N2.2.2; `j > i`]; L3.5c (with `c ≤ i` in case 3
   keeping the deciding part) and (1) [L3.5] give `F_{K_j}(Y_j) > F_{K_i}(Y_i) > Y_i ≥ Y_j`.
**Uses:** L3.6a, L3.5, L3.4, N2.2, L3.1e; U1: L2.4, L2.5.
**Lean:** `Closure.success_unmove`; `Closure/CapCompletion.lean`.
**Difficulty:** L — three scan cases with trace facts; about 600 LOC.
**Testable:** yes: caps with decorated A of generated standards, compare kernel successes before and
after each repair move.

### L3.6 Cap completion lemma   (paper: txt:459-481)
**Fidelity:** as in paper (conditional on `Cof B`, induction-safe: codex review txt:438).
**Statement.** `cap_completion : InL B → CondP B → Cof B → CC B`.
**Proof.**
1. Let `K = litCap B c k p` be upward with V, I, decorated A. `repair` [L3.1] gives `w : AdmCap B`,
   `w.H = litCap B c' k p ∈ L`, upward, reached by legal moves `ms`.
2. `B < w.H` [L3.1c.3]; `Cof B` gives `B ≤ w.H[m] < w.H`; `m ≥ 1` [T3.8c.3]; if `B = w.H[m]` use
   `w.H[m+1]` [T3.8b]. So `Covers w.H B`, hence `Success w.H Y'` [T3.8f.1].
3. The intermediate caps `K_s = applyMoves K (ms.take s)` are upward literal caps `litCap B c_s k p`
   [L3.1h] with V, I, decorated A [L3.1g]. Apply L3.6b from `s = |ms|` down to `0`.
**Uses:** L3.1, L3.1c, L3.1g, L3.1h, L3.6b, T3.8b, T3.8c, T3.8f.
**Lean:** `Closure.cap_completion`; `Closure/CapCompletion.lean`.
**Difficulty:** S — assembly, about 100 LOC.
**Testable:** yes (via L3.6b's test).

### T3.8i Seeds   (paper: txt:505)
**Fidelity:** as in paper.
**Statement.** `KS_seed m : KS (seed m)`.
**Proof.** Upward caps of `L_m` with V: column 0 (number 0) admits no visible parent; a singleton
column `[(x−1, ·)]` (number `x`) at cut 0 needs `p > x − 1` and `p < x`. So only cut 1 remains, which
is at the end of `w(L_m)` (the branch is last): `capPos = µ`; L3.4f and T3.8f.1.
**Uses:** L3.4f, T3.8f.
**Lean:** `Closure.KS_seed`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.8j Safe prefixes of a covered target   (paper: txt:505-506)
**Fidelity:** as in paper.
**Statement.** `KS_safePrefix : InL A → Cof A → KS (safePrefix A k)`.
**Proof.** `B = safePrefix A k ∈ L` [T3.2]. For an upward L cap `K` of `B` at position `π`: if
`π = µ(B)`, L3.4f and T3.8f. Otherwise `w(B)[π] = w(A)[π]` [`word_safePrefix`], the cap atom beats it,
so `A < K` [L3.1c]; `B ≤ A` [REQ-U1-14 `safePrefix_le`]; T3.8h with T3.8c.3.
**Uses:** L3.4f, T3.8f, L3.1c, T3.8h, T3.8c, T3.2; U1: D1.9, D1.9b (REQ-U1-14).
**Lean:** `Closure.KS_safePrefix`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.8k Special outputs   (paper: txt:506-510)
**Fidelity:** as in paper.
**Statement.** `KS_special : InL A → Cof A → stepKind A = some .special → expand A n = some B → KS B`.
**Proof.** Let `K` be an upward L cap of `B` (`B ∈ L` by T3.2) at position `π`.
1. Cut inside `P`, at the cut just before the first copy, or inside the first copy of `C` (at an existing
   column of `C`): the increase precedes the appended least column of `A`, so `A < K` [L3.1c]; T3.8h.
2. Cut inside a later copy: the capped copy exceeds the preceding equal entry `(p, C)`: H fails in `K`.
3. Nonfull cut between equal entries: needs a parent `> p`, again violating H.
4. Full cuts of the owner column and of its containers are at `µ(B)`: L3.4f.
5. Earlier columns: as in 1.
**Uses:** L3.1c, T3.8h, L3.4f, T3.8f, T3.2.
**Lean:** `Closure.KS_special`; `Closure/Cofinality.lean`.
**Difficulty:** M — positions of the copies; about 250 LOC.
**Testable:** yes.

### T3.8l The ordinary induction step   (paper: txt:511-643)
**Fidelity:** as in paper, fully decomposed (R-2) into T3.8la–T3.8ls.
**Statement.** `OrdStep` bundles: `A` standard, `A ∈ L`, `CondP A`, `Cof A`, `A` ordinary with `sd`,
`rd`, `n ≥ 1`, `expand A n = some B`; derived `d`, `s i`, `m`, `τ_i`, and
`proj φ ρ = ρ − φd` if `ρ > s_φ`, `r` if `ρ = s_φ`, `ρ` otherwise. `KS_ordinary S : KS S.B`.
**Proof.** Let `K = litCap B c k ρ` be an upward L cap; `CC A` by L3.6.
1. `A < K`: T3.8h (`B ≤ A` by `expand_lt`, `K0 < B` by T3.8c.3). `capPos = µ(B)`: L3.4f, T3.8f.1.
2. Otherwise T3.8la gives three cases.
   (a) Head 1 (`c = sd.col`, `k ≥ m`): `k = m` — T3.8le gives `ρ ≥ r`; `ρ = r`: T3.8ld with `i = 1`
       (`K[q] = A[q]`, take `q = n + 1`, T3.8b); `ρ > r` gives `A < K` by L3.1c (excluded). `k > m`:
       T3.8lg, `CC A`, T3.8lh.
   (b) Head `i ≥ 2`: `k < m`, or `k = m` and `ρ > s_{i−1}`: T3.8lc. `k = m`, `ρ = s_{i−1}`: T3.8ld,
       `q = n − i + 2`. `k = m`, `ρ < s_{i−1}`: impossible by T3.8le. `k > m`: as in (a).
   (c) Template column `a`, layer `i`, `φ = phaseOff i a`: `ρ > s_φ` — T3.8li, `CC A`, T3.8lj;
       `ρ = s_φ` — T3.8li, `CC A`, T3.8lk; `r < ρ < s_φ` — T3.8lp; `ρ ≤ r` — T3.8li, `CC A`, then
       T3.8ls if `OnHoleRoute a`, else T3.8lr.
3. Every `Success` gives `Covers` by T3.8f.1.
**Uses:** T3.8la, T3.8lb, T3.8lc, T3.8ld, T3.8le, T3.8lf, T3.8lg, T3.8lh, T3.8li, T3.8lj, T3.8lk, T3.8ll, T3.8lm, T3.8ln, T3.8lo, T3.8lp, T3.8lq, T3.8lr, T3.8ls, L3.6, T3.8h, L3.4f, T3.8f, T3.8b, T3.8c, L3.1c.
**Lean:** `Closure.OrdStep` (`d`, `s`, `m`, `tau`, `proj`), `KS_ordinary`; `Closure/Cofinality.lean`.
**Difficulty:** M — assembly over the cases, about 300 LOC.
**Testable:** yes: all upward L caps of outputs of generated ordinary standards (the Codex cap check
restricted to ordinary outputs).

### T3.8la Cut locations   (paper: txt:511-519)
**Fidelity:** as in paper (the occurrence classification T3.2i made explicit).
**Statement.** `cut_location`: if `K` is an upward L cap of `B` with `¬ A < K` and `capPos < µ(B)`,
then either `c = sd.col` and `m ≤ k` (head 1); or `c` is the head of a layer `2 ≤ i ≤ n`; or
`c = phaseCol i a` for a template column `a`, `1 ≤ i ≤ n`, with `i ≥ 2` for Q-material.
**Proof.**
1. `w(A) = X_A ⌢ [z_A]`, `w(B) = X_A ⌢ T_n` [D3.3a, D3.3b; `X_A = w(C_A ∅) ++ D_ℓ(w([Q]))`]. If
   `π < |X_A|`, the cap atom beats `w(B)[π] = w(A)[π]`: `A < K` [L3.1c].
2. By T3.2i.2, `c` is a context column, a head, or a template copy. Context columns: non-route cuts are
   inside `w(C_A ∅)`; route containers of `sd.col` at a nonfull cut are before `|X_A|` (their active
   entry's atom is there), full cuts are at `µ(B)`. Head 1 at `k < m`: inside `X_A`. Q-material of
   head 1: inside `D_ℓ(w([Q])) ⊆ X_A`.
**Uses:** T3.2i, D3.3a, D3.3b, L3.1c.
**Lean:** `Closure.cut_location`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes.

### T3.8lb Old terminal cap of a head-query cut   (paper: txt:607-608)
**Fidelity:** as in paper (the "phase-(i−1) cap at the old terminal" made explicit).
**Statement.** `headQuery_oldCap`: for the head `c` of layer `2 ≤ i ≤ n`, `k < m` or (`k = m` and
`ρ > s_{i−1}`), and `K` an upward L cap: `ρ > s_{i−1}`, and `K' = litCap A sd.col k (ρ − (i−1)d)` is an
upward cap of `A` with V, I and decorated A.
**Proof.**
1. For `k < m` the next entry is `τ_{i−1}(Q[k])` with parent `τ_{i−1}(q_k) ≥ s_{i−1}` (Q's parents
   `≥ r`, parent monotonicity); upwardness gives `ρ > s_{i−1}`. V of `K` gives `ρ < s_i`. So
   `ρ − (i−1)d ∈ (r, t)`, a body column of `A` (or the root's suffix region in the owner case).
2. Upward: the next old parent is `q_k` (or `r` at `k = m`) and `ρ − (i−1)d` exceeds it.
3. V, I: as T3.8li steps 3–4 with phase `i − 1`.
4. Decorated A: as T3.8li step 5 with phase `i − 1`; the head of layer `i` plays the old terminal `t`
   (`τ_{i−1}(t) = s_i`), and the path to `ρ > s_{i−1}` stays in phase `i − 1` material [T3.2q].
**Uses:** T3.8li, T3.2i, T3.2q.
**Lean:** `Closure.headQuery_oldCap`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 300 LOC (shares T3.8li's machinery).
**Testable:** yes.

### T3.8lc Head-query cuts succeed   (paper: txt:607-611)
**Fidelity:** as in paper.
**Statement.** `headQuery_cut`: in the setting of T3.8lb, `Covers K B`.
**Proof.**
1. `Success K' Y'` with `Y' = localSuffix A sd.col = node [Q ⌢ [(r, ∅)]]` by `CC A` [L3.6] and T3.8lb.
2. Conjugacy: `K`'s root `ρ`, scan and kernel are the `τ_{i−1}`-copies of `K'`'s [T3.2i.4,
   T3.2h.1, trace fact (1), REQ-U1-10]; D3.3c gives `F_K(τ_{i−1} X) = τ_{i−1}(F_{K'} X)`.
3. Target: `Y_K = τ_{i−1}(W)` with `W = F_A^{n−i+1}(∅)` [T3.2i.7]; `W < Y'`: after `Q`, `W`'s first column
   continues with a restored parent `< r` or ends, `Y'`'s with `(r, ∅)`.
4. Downward success [L3.4c via D3.3b], then the conjugacy and T3.2h.8: `Success K Y_K`; T3.8f.1.
**Uses:** T3.8lb, L3.6, D3.3c, T3.2i, T3.2h, L3.4, T3.8f; U1: L2.5.
**Lean:** `Closure.headQuery_cut`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes.

### T3.8ld The seam   (paper: txt:613-617)
**Fidelity:** as in paper.
**Statement.** `expand_seam`: for the head `c` of layer `1 ≤ i ≤ n`:
`expand (litCap B c m s_{i−1}) q = expand A (i − 1 + q)` for all `q`.
**Proof.**
1. `K = litCap B c m s_{i−1} = C_A(F_A^{i−1}(S_0))`, `S_0 = node [Q ⌢ [(r,∅)]]`: the cap keeps `i − 1`
   complete periods and replaces head `i` by `τ_{i−1}(Q ⌢ [(r,∅)])` [T3.2i, D3.3a].
2. `K`'s root is head `i − 1` (or `r` if `i = 1`); its scan against `κ_{i−1}(Z)` is high because `κ_1`
   is inflationary (`κ_1 Z ≥ Z`), with cursor `m + γ − c_A` [T3.2p.2]; `γ = c_A` because
   `B_{c_A−1} ≤ Z ≤ κ_1 Z < B_{c_A}` (root keys `κ`-fixed, T3.2h.5). So the unconsumed suffix is the
   copy of `U` ("the actual reset scan leaves exactly `U`").
3. Hence `F_K` is the `τ_{i−1}`-conjugate of `F_A` placed at the innermost hole, and
   `C_K(F_K^q ∅) = C_A(F_A^{i−1}(F_A^q ∅)) = C_A(F_A^{i−1+q} ∅)` [D3.3c, D3.3a]; definedness agrees
   [`expand_none_iff`].
**Uses:** T3.2i, T3.2p, T3.2h, D3.3a, D3.3c.
**Lean:** `Closure.expand_seam`; `Closure/Cofinality.lean`.
**Difficulty:** L — the identification of `K` with an iterate; about 500 LOC.
**Testable:** yes: compare `expand` of the seam cap with `expand A (i−1+q)` on generated standards.

### T3.8le No smaller closing parent at the seam   (paper: txt:617-620)
**Fidelity:** as in paper.
**Statement.** `seam_parent`: for the head `c` of layer `1 ≤ i ≤ n` and an upward L cap at `k = m`
with parent `ρ`: `s_{i−1} ≤ ρ`.
**Proof.**
1. A of `K` at its final entry: a path at the complete query `κ_{i−1}(Z)` from `τ_{i−1}(q_{m−1})` (or
   `s_i − 1`) to `ρ`.
2. It is the copy of the old terminal path and first reaches `s_{i−1}` [T3.2q]; capping the active
   ancestors does not change this response [L2.3 barrier, REQ-U1-11].
3. At `s_{i−1}` the scan is high with cursor `m` (`c_A` for `i = 1`): the response is `p_{c_A}`, the first
   restored parent, or the scan is exhausted (`U = []`) [T3.2p.2].
4. Every later endpoint is `≤ p_{c_A}` (V); upwardness needs `ρ > p_{c_A}` (the next entry of the head is
   `U[0]`), or, if `U = []`, no endpoint below `s_{i−1}` is reachable. Hence `ρ ≥ s_{i−1}`.
**Uses:** T3.2q, T3.2p; U1: L2.3.
**Lean:** `Closure.seam_parent`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes.

### T3.8lf Restored-suffix cuts have `ρ < r`   (paper: txt:623-624)
**Fidelity:** as in paper.
**Statement.** `restored_parent`: for the head `c` of layer `i` and `k > m`: `ρ < r`.
**Proof.** H of `K`: `(ρ, ∅) ≤` the previous entry, whose parent is a restored parent `p_{c_A+v−1} < r`
(V of `A`: root entries have parents below `r`) [T3.2i.5].
**Uses:** T3.2i.
**Lean:** `Closure.restored_parent`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.8lg The old root cap of a restored-suffix cut   (paper: txt:624-626)
**Fidelity:** as in paper.
**Statement.** `restored_oldCap`: for the head `c` of layer `i`, `k = m + v > m`, `capPos < µ(B)`:
`K' = litCap A rd.col (c_A + v) ρ` is an upward cap of `A` with V, I, decorated A.
**Proof.**
1. Upward: `K`'s next entry is the copy of `R[c_A + v]` with the same outer parent (or `w = |R|`).
2. V: `ρ < r` [T3.8lf]. I: the cut is not at index 0.
3. Decorated A: retained tests as in T3.2e (barrier + trace fact (2)). The final test: `K`'s query is
   `ν(κ_{i−1}(y) ⌢ R[c_A..w))`, equal to `B_{w−1}` [T3.2p.1], which is `K'`'s query; its path from
   `p_{w−1}` to `ρ` lies below `r` (fixed region, identical in `A` and `B`).
**Uses:** T3.8lf, T3.2p, T3.2e.
**Lean:** `Closure.restored_oldCap`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 200 LOC.
**Testable:** yes.

### T3.8lh Restored-suffix cuts succeed   (paper: txt:621-640)
**Fidelity:** as in paper.
**Statement.** `restored_cut`: in the setting of T3.8lg, `Success K' (localSuffix A rd.col)` implies
`Success K (localSuffix B c)`.
**Proof.**
1. Cursors agree (`γ`): identical closed sources with equal reduced queries [T3.2p.1, spine
   `cursor_nu`]; a containing owner is first capped after the nonexhaustion check [trace fact (2)].
2. Fillings: `C_{K'}(Y') = A`, `C_K(Y_K) = B` (both cap columns are on the route) [N2.2.2].
3. (1) [L3.5]: `F_{K'}(Y') = R[:w] ⋄ T_{ρ,r−ρ}(rt_{ρ,γ}(A))`, `F_K(Y_K) = Q_K ⋄ T_{ρ,s_i−ρ}(rt_{ρ,γ}(B))`.
4. Cancel the different nonempty prefixes [L3.5 (2)]; use (3) `T_{ρ,s_i−ρ} = τ_i ∘ T_{ρ,r−ρ}` [T3.2h.6];
   `node(head[m+v:] :: …) = τ_i(rt_{r,w}(A_{n−i}))` [T3.2i.7, L3.5 (1)]; `e_1` commutes with `τ_i` and
   `τ_i` is an order embedding. Success of `K` becomes `R_H < L_H` with
   `L_K = e_1(T_{ρ,r−ρ} rt_{ρ,γ}(A))`, `R_K = e_1(rt_{r,w}(A))`, `L_H = e_1(T_{ρ,r−ρ} rt_{ρ,γ}(B))`,
   `R_H = e_1(rt_{r,w}(A_{n−i}))` (paper (5)); success of `K'` is `R_K < L_K`.
5. `R_H < R_K`: `A_{n−i} < A` with first difference at the old terminal, which lies in the retained
   part (`w < |R|` keeps the active origin in the owner case; `D` contains it otherwise) [T3.2l].
6. `L_H` agrees with `L_K` before `L_K`'s last atom (the old terminal; `A`, `B` agree before it), and
   `|R_K| ≤ |L_K| − 1` since `L_K` is `P ⌢ Σ(w Y')` minus a common prefix, `|P| ≥ 1` [D3.3b].
7. L3.7 gives `R_H < L_H`.
**Uses:** T3.8lg, T3.2p, N2.2, L3.5, T3.2h, T3.2i, T3.2l, D3.3b, L3.7; U1: L2.1.
**Lean:** `Closure.restored_cut`; `Closure/Cofinality.lean`.
**Difficulty:** L — remainders with two different prefixes; about 600 LOC.
**Testable:** yes.

### T3.8li Projection to an old cap   (paper: txt:520-541)
**Fidelity:** as in paper (decomposed; the detour argument is T3.2q).
**Statement.** `projection`: for a template column `a`, `c = phaseCol i a` (`i ≥ 2` for Q-material),
`φ = phaseOff i a`, an upward L cap `K` of `B` at `(c, k, ρ)` with `capPos < µ(B)` and `ρ ≤ r ∨ s_φ ≤ ρ`:
`K' = litCap A a k (proj φ ρ)` is an upward cap of `A` with V, I and decorated A.
**Proof.**
1. The retained part of `K` from the root to the cut is the `τ_φ`-copy of `K'`'s [T3.2i.4–6]; the cut is
   pure because `capPos < µ(B)` excludes full cuts of continuation entries.
2. Upward: the next parent `q'` of `B` is `shiftVal r (φd) q` [T3.2i.4]; in each case of `proj`
   (`ρ > s_φ`; `ρ = s_φ`, where `q' < s_φ` forces `q' = q < r` by T3.8ln; `ρ ≤ r`) `proj ρ > q`.
3. V: `ρ < num(c) = num(a) + φd` [T3.2i.3] gives `proj ρ < num(a)` (for `ρ = s_φ`: `proj ρ = r <
   num(a)`, since every template column has number `> r`).
4. I (only at `k = 0` and only when `a` lies in a height; write `h_a`, `h_c` for the hosts) [VERIFY-U2
   F7: the draft said "`h_c` is the image of `h_a`", which fails for the columns of the root forest
   after the root when `δ > 0`: in `B` they lie in the stopping forest, whose host is not `h_a`].
   (a) `a` is a column of the root forest `F` (a body column): `h_a < r` because the root column, of
       number `r`, is a column of the same forest. I of `K` gives `ρ ≥ h_c`, and `h_c ≥ h_a` (if `δ = 0`
       the copy lies in the same forest, `h_c = h_a`; if `δ > 0`, `h_c` is the image of the stopping
       forest's host, which is `≥ r`). Then `proj ρ ≥ h_a`: `ρ − φd > r > h_a` if `ρ > s_φ`; `r > h_a`
       if `ρ = s_φ`; `ρ ≥ h_c ≥ h_a` if `ρ ≤ r`.
   (b) otherwise `a` lies in the height of an entry of a column of number `≥ r` (a body column, the
       root column, the stopping column or a column inside their heights), so `h_a ≥ r` and
       `h_c = h_a + φd` [T3.2i.3 applied to the host column; for a restored height the host is the head
       `s_φ`, the image of `r`]. I of `K` gives `ρ ≥ h_a + φd ≥ s_φ`, so `ρ ≤ r` is impossible
       (`φ ≥ 1`, `d ≥ 1`); if `ρ > s_φ`, `proj ρ = ρ − φd ≥ h_a`; if `ρ = s_φ`, then `h_a ≤ r`, so
       `h_a = r = proj ρ`.
5. Decorated A. Retained tests: tests of `A`, protected by the old complete-cut barriers after capping
   the strict active ancestors [L2.3, REQ-U1-11; trace fact (2)]. Final test, from `K`'s actual final
   test at query `V = κ_φ(W)` (`W` the old cut query, T3.2h.1):
   (a) `ρ > s_φ`: the path stays above `ρ > s_φ`, in phase-`φ` copies: project edgewise [T3.2q.1];
   (b) `ρ = s_φ`, and `ρ = r` (whose path must pass `s_φ`, since an exit below `r` cannot return to
       `r`): stop the path at `s_φ`, project to `r`;
   (c) `ρ < r`: T3.2q.1 (detours through heads deleted).
   A cut inside a restored origin `u ≥ c_A`: use the old root through `u` with its key capped; at the
   complete query its cursor is still `c_A`, at low queries `≤ c_A ≤ u` with the same response.
   A cut in a copied query height: the head of layer `i` is the old terminal truncated in phase `i−1`;
   its edge projects directly, then (a)–(c).
**Uses:** T3.2i, T3.2q, T3.2h, T3.8ln, T3.2e; U1: L2.3.
**Lean:** `Closure.projection`; `Closure/Cofinality.lean`.
**Difficulty:** XL — the central path projection with capped containers; about 2000 LOC.
**Testable:** yes: for every upward L cap of outputs of generated ordinary standards, build `K'` and
check V, I and decorated A with the decorated checker of checks/python/run_checks.py.

### T3.8lj Proper current root `ρ > s_φ`   (paper: txt:542-546)
**Fidelity:** as in paper.
**Statement.** `root_current`: in the setting of T3.8li with `ρ > s_φ`, `Success K' (localSuffix A a)`
implies `Success K (localSuffix B c)` (`K' = litCap A a k (ρ − φd)`).
**Proof.**
1. Stop data of `K` and `K'` are `τ_φ`-related [T3.8c.1, T3.2i.3–4]; root column, owner flag, hole
   depth, root tail are pure copies; cursors agree [T3.2h.1, trace fact (1)].
2. D3.3c: `F_K(τ_φ X) = τ_φ(F_{K'} X)`.
3. `Y_K = τ_φ(W)` with `W ≤ Y_{K'}` [T3.2i.6, T3.2l].
4. Downward success [L3.4c via D3.3b] at `W`, then T3.2h.8; `KernelDefined K` from `InL K` [L2.4].
**Uses:** T3.8c, T3.2i, T3.2h, D3.3c, T3.2l, L3.4; U1: L2.4.
**Lean:** `Closure.root_current`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 250 LOC.
**Testable:** yes.

### T3.8lk Current head root `ρ = s_φ`   (paper: txt:547-552)
**Fidelity:** as in paper.
**Statement.** `root_head`: with `ρ = s_φ`, `Success K' (localSuffix A a)` (`K' = litCap A a k r`)
implies `Success K (localSuffix B c)`.
**Proof.**
1. `K`'s root is the head of layer `φ` (`φ ≥ 1`), keys `κ_{φ−1}(y) ⌢ R[c_A:]` [T3.2i.5, T3.2h.1,
   T3.2h.5]; `K`'s query is `V = κ_φ(W)`.
2. High (`V ≥ κ_{φ−1}(Z)`): cursor `m + γ − c_A` [T3.2p.2] with `γ` = `K'`'s cursor [T3.2h.5, trace fact
   (1)]; a containing head or old root is first checked nonexhausting, then capped [trace fact (2)].
   The unconsumed suffix, body and hole are `τ_φ`-copies of `K'`'s: conclude as in T3.8lj.
3. Low: the cursor is `< m`, the first unconsumed entry is `τ_{φ−1}(Q[γ'])` with parent `≥ r`. The next
   target parent is `< s_φ` (upward) and hence `< r` [T3.8ln], or absent: T3.8ll.
**Uses:** T3.2i, T3.2h, T3.2p, T3.8lj, T3.8ln, T3.8ll.
**Lean:** `Closure.root_head`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 300 LOC.
**Testable:** yes.

### T3.8ll Wins at once   (paper: txt:551-552, 560-561)
**Fidelity:** as in paper.
**Statement.** `success_of_first`: if `K` is ordinary with data `sd`, `rd`, defined, `Y` has first
column `Q ++ rest`, `U_K = u :: us`, and the first entry of `rest` (if any) has parent `< u.1`, then
`Success K Y`.
**Proof.** `F_K(Y)`'s first column is `Q ++ (u.1, …) :: …` [D3.3]; compare at index `|Q|`.
**Uses:** D3.3.
**Lean:** `Closure.success_of_first`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.8lm Sign independence   (paper: txt:555-559)
**Fidelity:** as in paper.
**Statement.** `sign_indep`: for `h, h' < φ`, any key `w` and forest `J`:
`keyCmp (κ_φ w) (κ_h (relKey (r+d) J)) = keyCmp (κ_φ w) (κ_{h'} (relKey (r+d) J))`;
`sign_indep_list`: the same for the lexicographic comparison of reduced queries.
**Proof.** Labelwise: moving false fields of `κ_φ w` are `≥ s_φ`, those of `κ_h z` (`z` normalized at
`t = r + d`, so false fields `< r + d`) lie in `[s_h, s_{h+1}) ⊆ [r, s_φ)`; fixed false fields are `< r`;
true fields follow all false ones and are untouched. Every label comparison and label equality is
independent of `h`; `Tree.cmp` is determined by them.
**Uses:** T3.2h.
**Lean:** `Closure.sign_indep`, `sign_indep_list`; `Closure/Cofinality.lean`.
**Difficulty:** S — about 100 LOC.
**Testable:** yes (20,000 random cases, 0 failures).

### T3.8ln Parent dichotomy for phase material   (paper: txt:530, 549-551)
**Fidelity:** as in paper.
**Statement.** `phase_parent_dichotomy`: every entry of `B`'s column `phaseCol i a` has parent `< r` or
`≥ s_φ`.
**Proof.** Parents are `shiftVal r (φd) p` [T3.2i.4–5]; continuation entries keep their outer parent.
**Uses:** T3.2i.
**Lean:** `Closure.phase_parent_dichotomy`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.8lo The response at a previous-phase root   (paper: txt:553-560)
**Fidelity:** as in paper (compressed in the paper; see Open problems OP-1).
**Statement.** `prev_root_response`: with `r < ρ < s_φ` and `K` an upward L cap of `B` at `phaseCol i a`:
the unconsumed root suffix of `K` is `u :: us` with `u.1 ≥ r`.
**Proof.**
1. `K`'s final test is a path at `V = κ_φ(W)` from a phase-`φ` vertex to `ρ`. Leaving phase `φ` goes
   through the head `s_φ` or below `r` [T3.8ln]; below `r` it cannot return above `r` (V). At `s_φ` a
   high response is `R`'s response `< r` [T3.2q step 2]; so `s_φ` is low and the path enters phase
   `φ − 1` along the copy of the old terminal-to-root path.
2. Every later head `s_h`, `1 ≤ h < φ`, compares `V` with `κ_{h−1}(Z)`; by T3.8lm the sign is the same
   as at `s_φ`: low.
3. If `ρ` is a head `s_h`: its response is a query parent `τ_{h−1}(q) ≥ r`. If `ρ` is a phase-`h` body
   column `x + hd`: it lies on the copied terminal-to-root path, its response at `V` is that path's next
   vertex (sign independence relates the comparison of `V` with `κ_h(x`'s keys`)` to the old one), a
   column in `[r, t)` copied to `[s_h, s_{h+1})`, so its parent is `≥ r`. Capping an unconsumed owner key
   does not change this actual response [trace fact (2)].
**Uses:** T3.8ln, T3.8lm, T3.2q.
**Lean:** `Closure.prev_root_response`; `Closure/Cofinality.lean`.
**Difficulty:** L — about 500 LOC; highest residual risk.
**Testable:** yes: for all upward L caps with `r < ρ < s_φ` of outputs of generated ordinary standards,
check the parent of the first unconsumed root entry.

### T3.8lp Previous-phase root `r < ρ < s_φ`   (paper: txt:553-561)
**Fidelity:** as in paper.
**Statement.** `root_prev`: with `r < ρ < s_φ`, `Success K (localSuffix B c)` (no old cap needed).
**Proof.** T3.8lo gives `u.1 ≥ r`; the next target parent is `< ρ < s_φ`, hence `< r` [T3.8ln], or
absent; `Y_K`'s first column is `Q_K ++ rest` [T3.8c.1, D3.1c]; T3.8ll.
**Uses:** T3.8lo, T3.8ln, T3.8ll, T3.8c.
**Lean:** `Closure.root_prev`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes.

### T3.8lq Fixed roots: the cursors agree   (paper: txt:564-571)
**Fidelity:** as in paper.
**Statement.** `root_fixed_cursor`: with `ρ ≤ r`, the root data of `K` and of `K' = litCap A a k ρ`
have equal cursor and root column. [VERIFY-U2 F3: the draft also claimed equal owner flags. False:
for `ρ = r` and a cut inside a restored origin `u`, the old cap's root `R` contains the cut (owner),
while in `B` the cut lies in the head and `R` is an earlier column (body). Instance:
`A = [[],[(0,[[(1,∅)]])],[(1,∅),(1,∅),(1,∅)]]`, `n = 2`, layer `1`, `a` = the column inside `R[0]`,
`k = 1`, `ρ = 1`. T3.8lr and T3.8ls use only the cursor and the root column, through the filling
identity (1), which is uniform in the owner flag.]
**Proof.**
1. `ρ < r`: the root column is a context column; old and new keys agree except possibly the last
   active key of a containing owner; both scans are nonexhausting there (`K ∈ L`; `K'` has S by L3.1e and
   A by `capping_iff`, hence definedness by L2.4); cap both to `⊤` [trace fact (2)]; source keys are
   `κ_φ`-fixed [T3.2h.5], query keys `κ_φ`-related [T3.2h.1]: trace fact (1).
2. `ρ = r` with the cut inside a restored origin `u`: the old projected key and the complete key agree
   beyond each query height [U1 `sign_of_agreement`]; the old owner scan ends at or before `u`; trace
   fact (3) [`trace_agree`] identifies it with the full root scan; the new root's possibly changed last
   key by trace fact (2). Direct body and query-height cuts: only the last-key argument.
**Uses:** T3.2h, L3.1e, T3.2i; U1: L2.4.
**Lean:** `Closure.root_fixed_cursor`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 300 LOC.
**Testable:** yes.

### T3.8lr Closed side targets   (paper: txt:576-582)
**Fidelity:** as in paper.
**Statement.** `closed_side`: with `ρ ≤ r` and `¬OnHoleRoute a`, `Success K' (localSuffix A a)` implies
`Success K (localSuffix B c)`.
**Proof.**
1. Common cursor `γ` [T3.8lq]; `Q_K = τ_φ Q_{K'}`, `Y_K = τ_φ Y_{K'}` [T3.2i.4, T3.2i.6].
2. `C_{K'}(Y')` is a safe prefix of `A` ending before the terminal, hence of `B`; `C_K(Y_K)` is a safe prefix
   of `B` at a later copy, properly extending it [N2.2.2].
3. L3.5c (the root entry `γ` starts before the shorter cut: an owner cursor retains the active origin):
   `Q' ⋄ T_{ρ,x−ρ}(rt(C_{K'} Y')) < Q' ⋄ T_{ρ,x−ρ}(rt(C_K Y_K))`.
4. With (1)–(3) [L3.5, T3.2h.6]: `θ_φ ∂_{Q_K} w(F_K Y_K) > ∂_{Q'} w(F_{K'} Y') > ∂_{Q'} w(Y') =
   θ_φ ∂_{Q_K} w(Y_K)`, where `θ_φ` inverts `τ_φ` on its image (both sides are images); same `ε`.
**Uses:** T3.8lq, T3.2i, N2.2, L3.5, T3.2h.
**Lean:** `Closure.closed_side`; `Closure/Cofinality.lean`.
**Difficulty:** M — about 400 LOC.
**Testable:** yes.

### T3.8ls Direct body targets   (paper: txt:583-605)
**Fidelity:** as in paper.
**Statement.** `direct_body`: with `ρ ≤ r` and `OnHoleRoute a`, `Success K' (localSuffix A a)` implies
`Success K (localSuffix B c)`.
**Proof.**
1. Common cursor `γ` [T3.8lq]; `Y' = Y_x(A)`, `Y_K = τ_i(Y_x(A_{n−i}))`, `Q_K = τ_i Q'` [T3.2i.6].
2. `C_{K'}(Y') = A`, `C_K(Y_K) = B` [N2.2.2, the cap column's forest is on the route].
3. Remainders (4) via (1)–(3) and `θ_i`: `L_K = e_ε(T_{ρ,x−ρ} rt_{ρ,γ}(A))`, `R_K = ∂_{Q'} w(Y_x(A))`,
   `L_H = e_ε(T_{ρ,x−ρ} rt_{ρ,γ}(B))`, `R_H = ∂_{Q'} w(Y_x(A_{n−i}))`; success of `K'` is `R_K < L_K`.
4. `R_H < R_K`: `Y_x(A_{n−i}) < Y_x(A)` [T3.2l, strict on the hole route; `n − i = 0` included]; the cut
   is before the terminal (`capPos < µ(B)`).
5. `L_H` agrees with `L_K` before `L_K`'s position `p + N − 1 − a` of the old terminal (`A`, `B` agree
   before it; rooting keeps it: an earlier root retains its following forest, an owner cursor its active
   height); `p + N − 1 − a ≥ N − a = |R_K|` (`p = |P| ≥ 1`, `N = µ(Y')`, `a = |w([Q'])|`).
6. L3.7 gives `R_H < L_H`; restore the phase and the prefix.
**Uses:** T3.8lq, T3.2i, N2.2, L3.5, T3.2h, T3.2l, L3.7, D3.3b.
**Lean:** `Closure.direct_body`; `Closure/Cofinality.lean`.
**Difficulty:** L — about 600 LOC.
**Testable:** yes.

### T3.8m Kernel success for standard targets   (paper: txt:504)
**Fidelity:** as in paper (induction on a generation witness, never on the syntax order).
**Statement.** `KS_std : IsStd B → KS B`.
**Proof.** Induction on `IsStd` (D1.7).
1. Seeds: T3.8i.
2. `expand A n = some B`, `IsStd A`, `KS A`: `A ∈ L ∩ P` [T3.2], `Cof A` [T3.8g]. If `A = ∅`, `B = ∅`
   and `KS ∅` is vacuous (no columns). Otherwise by `stepKind A` [spine `stepKind_isSome`]: deletion or
   ordinary `n = 0` — `B` is a safe prefix [T3.2g], T3.8j; special — T3.8k; ordinary `n ≥ 1` — T3.8l.
**Uses:** T3.8i, T3.8j, T3.8k, T3.8l, T3.8g, T3.2, T3.2g; U1: D1.6a, D1.7.
**Lean:** `Closure.KS_std`; `Closure/Cofinality.lean`.
**Difficulty:** S.
**Testable:** yes (as T3.8n).

### T3.8 Cofinality theorem   (paper: txt:489-643)
**Fidelity:** as in paper (R-2: decomposed into T3.8a–m, L3.6, L3.4f, N2.2).
**Statement** (spine contracts).
`cofinal : IsStd B → InL E → B < E → ∃ n E', expand E n = some E' ∧ B ≤ E' ∧ E' < E`;
`cofinal_bound : IsStd B → InL E → B < E → E.cols.getLast? ≠ some [] →
∃ n E', 1 ≤ n ∧ n ≤ µ(B)+1 ∧ expand E n = some E' ∧ B < E'`.
Consumers: U5 `FinalHyps.cofinal` (N5.1, only the lower bound), U3 `repair_output` and U5 L8.8 Case 3
(with an admissible cap `E = anchor E₀ (some w)`, which lies in `L`; its last outer column is nonempty).
**Proof.** `KS_std` [T3.8m], `std_inL` [T3.2], then `cof_of_KS` and `bound_of_KS` [T3.8g].
**Uses:** T3.8m, T3.8g, T3.2.
**Lean:** spine `Closure.cofinal`, `Closure.cofinal_bound`; `Closure/Cofinality.lean`.
**Difficulty:** S (assembly); the unit total for T3.8 with L3.6 is XL (about 10,000 LOC).
**Testable:** yes (claude-cofinality; finite-invariants cap covers).

---

## Requires (facts from other units not already provided by the spine)

All are owned by U1 (U2 imports only `Scan`). **Integration:** every row now names its provider node in the last column; the two stubs are removed (U1 provides `Scan.ordZ` and `Scan.gwordAt`). "Matches" names the U1 draft declaration
(scratch/blueprint/U1/check.lean, 2026-10-27) or spine node believed to cover it. Two of them are
stubbed in `section Stubs` of U2.lean because U2's *statements* mention them (deleted at integration:
U1 now provides both).

| ID | Needed by | Exact statement | Matches | Provider (integration) |
|---|---|---|---|---|
| REQ-U1-1 | D3.3a | `Scan.ordZ E sd rd n` is the final `Z` of the §1.2 loop (`ordLoop (ordStep sd rd F U) n ∅`, `F = rootForest`, `U = unconsumed`), and for `stepKind E = some .ordinary`, `stopData E = some sd`, `rootData E = some rd`: `paperOp E n = if rd.owner ∧ n ≠ 0 ∧ U = [] then none else some (replaceAt 0 0 (ordZ E sd rd n) sd.depth E)`. **Stubbed** (`Scan.ordZ`). | U1 draft `Scan.ordZ`, `Scan.paperOp_ordinary` (D1.6a†) | U1 D1.6 (`Scan.ordZ`, spine body since SCR-2) and D1.6b `paperOp_ordinary`; stub removed |
| REQ-U1-2 | T3.2d, T3.2h, L3.1c, N2.2, T3.8f, L3.6a | Generic word `Scan.gwordAt e : Tree α → List (Nat ×ₗ Nat ×ₗ WithBot α)` with: `gword_map` (relabelling commutes, positions unchanged); `gword_lt_iff` (`gword s < gword t ↔ Tree.cmp compare s t = .lt` for any linear label order); `gwordAt_fst_ge` (depth coordinates `≥ 2e`); `gwordAt_append_lt_iff` (`gwordAt e s ++ xs < gwordAt e t ++ ys ↔ s < t ∨ (s = t ∧ xs < ys)` when the heads of `xs`, `ys` are shallower than `2e`); `gword_eq_map_word`. **Stubbed** (`Scan.gwordAt`). | U1 draft N1.2, C1.8a | U1 N1.2, C1.8a (`gwordAt`, `gword_map`, `gwordAt_fst_ge`, `gwordAt_append_lt_iff`, `gword_eq_map_word`, `gword_lt_iff`); stub removed |
| REQ-U1-3 | D3.3b, T3.2l, L3.5, T3.8c | `stopData E = some sd →` the stopping column is `sd.Q ++ [(sd.r, ∅)]`, `sd.depth = |sd.col.path|`, `sd.t = sd.col.num 0`, `sd.col` is the last element of `routeCols E` and `|routeCols E| = sd.depth + 1`; conversely, if following last columns and last entries reaches a column ending in an entry with empty height, `stopData` returns that column (used for `litCap`). | U1 draft `stopData_spec`, `mem_routeCols_iff` | U1 D1.6b `stopData_spec`, D1.2d `mem_routeCols_iff`; converse: U1 D1.6d `stopData_of_route` (new) |
| REQ-U1-4 | D3.3a, L3.5, T3.2i | `rootData E = some rd →` `sd.col.resolve 0 sd.r = some rd.col`, `rd.layer = |rd.col.path|`, `rd.idx = rd.col.col`, `rd.col.num 0 = sd.r < sd.t`, `rd.cursor = cursor (rootKeys E rd) (queryKeys sd)`, and `rd.owner ↔` the root's last entry contains `sd.col`. | U1 draft `rootData_spec`, `rootData_owner_iff` | U1 D1.6b `rootData_spec`, `rootData_owner_iff` |
| REQ-U1-5 | T3.2s, T3.8b, T3.8e, T3.8k | Special output: `paperOp E n = some (Hole.fill ⟨E, sd.depth − 1⟩ 0 0 (node [col.dropLast ++ replicate (n + ε) (p, node Fl.cols.dropLast)]))` for the owner column `col` with last entry `(p, Fl)`. | U1 draft `paperOp_special` | U1 D1.6b `paperOp_special` |
| REQ-U1-6 | D3.3b, T3.8b | `depth < |routeCols outer| → w(replaceAt 0 0 Z depth outer) = w(replaceAt 0 0 ∅ depth outer) ++ wordAt depth Z`. | U1 draft `word_put` | U1 D1.5a `word_put` |
| REQ-U1-7 | D3.3a–c, L3.5 | `replaceAt r d Z δ G = replaceAt 0 0 Z δ (shift r d G)` and `shift r a (replaceAt 0 0 Z δ G) = replaceAt r a (shift r a Z) δ G`. | U1 draft `Hole.fill_eq_put` (second form derivable) | U1 D1.5a `Hole.fill_eq_put` (first form); U1 D1.5b `shift_replaceAt` (second form, new) |
| REQ-U1-8 | D3.3a, T3.2i | `shift r d (shift r d' F) = shift r (d + d') F`, `shift r 0 F = F`. | U1 draft `shift_add`, `shift_zero` | U1 D1.5a `shift_add`, `shift_zero` |
| REQ-U1-9 | L3.1b, L3.1d, T3.2j, T3.2k | `c.resolve 0 q = some o ↔ q < c.num 0 ∧` `o` is the unique stack column numbered `q`; hence `CondV E ↔` every parent is below its column's number. | U1 draft `resolve_spec`† (spine §d) | U1 D1.2b `resolve_spec`, `resolve_isSome_iff`; D1.3a `condV_iff_lt` |
| REQ-U1-10 | T3.2e, T3.2q, L3.6b, T3.8lj–T3.8lq | Trace facts (1) `cursor_map`/`trace_map`, (2) `trace_cap_top`, (3) `trace_agree`, and `sign_of_agreement` (txt:237-249). | spine L2.5 names; U1 draft | U1 L2.5 `trace_map`, `cursor_map`, `trace_cap_top`, `trace_agree`; L2.5c `sign_of_agreement`, `sign_of_agreement_compare` |
| REQ-U1-11 | T3.2e, T3.2r, T3.8le, T3.8li | Complete-cut barrier: under V, A, S, for a containing entry `e = (a, u)` of column `c` and every cut `0 ≤ k ≤ |c|`, every actual `g_{W(c,k)}`-path from `x(c,k)` that reads column `a` does so at a query `< B_a(u)` (codex-crosscheck-1 Q2, `C_e(c,k)`, including the full cut). | spine L2.3, L2.3a (`cut_barrier`†) | U1 L2.3 `cut_barrier` (predicates of L2.3a) |
| REQ-U1-12 | L3.1, T3.2e, T3.2r, T3.2u, L3.6 | `CondV E → CondS E → sel ⊆ routeCols E → (CondA E ↔ CondAK E (capKeys E sel))`. | spine L2.4, L2.4a (`capping_iff`†) | U1 L2.4 `capping_iff` |
| REQ-U1-13 | T3.2p, T3.2h | `nu (l ++ [x]) = nuStep (nu l) x`, `nu` is nonincreasing, `nu l = l` for nonincreasing `l`, `nu (nu l ++ m) = nu (l ++ m)`. | U1 draft `nu_append_singleton`, `nu_noninc`, `nu_of_noninc`, `nu_append_nu` | U1 D2.1a `nu_append_singleton`, `nu_noninc`, `nu_of_noninc`, `nu_append_nu` |
| REQ-U1-14 | N2.1, T3.2c, T3.8j | `safePrefix E k ≤ E`; `safePrefix E k = E` for `k ≥ µ(E)`; structure (addresses preserved, columns are prefixes, only last entries truncated, truncated heights are safe prefixes, no new empty internal column); **one-atom decoding**: for `G = safePrefix B π`, every forest whose word is `w(G) ⌢ [z]` is `G` extended at its route by one entry or one column as in N2.1 step 2. | U1 draft `safePrefix_le`, `safePrefix_of_le`, `colAt_safePrefix`; decoding not yet stated | U1 D1.9 `safePrefix_le`, `safePrefix_of_le`, `colAt_safePrefix`; decoding: U1 D1.9b `routeCols_of_word_snoc` (new) |
| REQ-U1-15 | T3.8c | `stepKind E = some .deletion ↔ E.cols.getLast? = some []`; special iff `specialStop sd`; ordinary iff a non-special stop with a visible root. | U1 draft `stepKind_*_iff` | U1 D1.6b `stepKind_deletion_iff`, `stepKind_special_iff`, `stepKind_ordinary_iff` |
| REQ-U1-16 | T3.2h | A map strictly monotone on the occurring letters preserves and reflects list order. | U1 draft `list_map_lt_iff` (N1.3) | U1 N1.3 `list_map_lt_iff` |
| REQ-U1-17 | T3.2p | `cursor_unique` (the final cursor is the unique index between consecutive boundaries), `cursor_le_length`, `cursor_mono`. | U1 draft | U1 L2.1 `cursor_unique`, `cursor_mono`; L2.1a `cursor_le_length` |
| REQ-U1-18 | D3.3b | `wordAt (e + δ) X = (wordAt e X).map (depthShift δ)`; `wordAt e (Tree.map f X)` is `wordAt e X` with `f` applied to the third coordinate of every entry atom (marker `1`, or odd depth coordinate); empty-column atoms `(2e', 0, 0)` are unchanged. [VERIFY-U2 F1: the draft said "relabels the parent coordinate", false for empty-column atoms when `f 0 ≠ 0`.] | follows from REQ-U1-2 | U1 N1.4 `wordAt_add`, `wordAt_map` (new); U2's `depthShift` and `kerSigma` forms follow by unfolding |

No facts are needed from U3, U4 or U5 (U2 precedes them in the import order).

## Spine change requests

**SCR-U2-1 (procedural; stubs). Status: applied at integration** (spine §i.1, §i.5): U1's `Scan.gwordAt`, `Scan.ordZ` and `paperOp_ordinary` are registered as U1 contracts and U2's stubs are deleted. *Item:* spine §h.2 ("no imports", stubs "in a final section").
*Missing case:* Lean requires declare-before-use, and U2's statements mention two U1 names the spine
lacks (`Scan.ordZ` in REQ-U1-1's statement is only used in proofs, but `Scan.gwordAt` appears in
`keyWord`, hence in `ownerReturn_origin`). *Workaround (marked in U2.lean):* `section Stubs` is placed
first. *Proposal:* allow the stub section at the top, and add `Scan.gwordAt` (generic word with
`gword_lt_iff`, `gword_map`) and `Scan.ordZ`/`paperOp_ordinary` to the spine's U1 contracts (§c.4,
§c.5). *Consumers:* U2 (T3.2d, T3.2m, D3.3a); U3 if it reuses key words.

**SCR-U2-2 (merge of U2-owned bodies). Status: applied at integration** (spine §i.3): the bodies are in `Spine.lean` and every bridge `*_eq_body` holds by `rfl`. *Item:* `Closure.profile`, `litCap`, `applyMove`,
`MovesValid`, `RepairList`, `moveAddr`, `AdmCap.origin` (spine, `sorry` bodies owed by U2). *Missing
case:* a unit file cannot fill a spine body without redeclaring it. *Workaround:* U2.lean defines
`profileBody`, `litCapBody`, `applyMoveBody`, `MovesValidBody`, `RepairListBody`, `moveAddrBody`,
`originBody` with real bodies and bridge theorems `*_eq_body` (sorry). *Proposal:* at T-018 replace each
spine `sorry` body by the corresponding U2 body; the bridges become `rfl`. *Consumers:* U3 (records:
`RepairList`, `moveAddr`, `AdmCap.origin`), U5 (`anchorOrigin`).

No FIRM item was found wrong. The refinements `origin_spec`†, `upward_condS`†, `repair`† strengthen
only conclusions (or add hypotheses that every consumer has: `E` standard gives V, I, H, A, S, P).

## Proposed simplifications (flagged, not applied)

- **PS-U2-1 (T3.8lr, T3.8ls): conjugate instead of invert.** Since `Q_K = τ_φ Q'` and
  `T_{ρ,x+φd−ρ} = τ_φ ∘ T_{ρ,x−ρ}` (3), filling identity (1) gives
  `F_K(Y_K) = τ_φ(Q' ⋄ T_{ρ,x−ρ}(rt(C_K Y_K)))`. With `Y_K = τ_φ(·)`, success of `K` is a comparison of
  untransformed forests, so the inverse phase map `θ_i` and the cancellation `∂` are unnecessary in the
  closed-side and direct-body cases; cancellation remains only for (5) (T3.8lh), whose prefixes differ.
  Saves an estimated 400 LOC; the paper's route is kept in the entries.
- **PS-U2-2 (U3 L6.2): one occurrence classification.** U3's `qMap`/`fMap` can be defined from U2's
  `kerCol`/`phaseCol` (U2 precedes U3 in the import order), so T3.2i, T3.8 and §6.1 share one address
  algebra (R-3).
- **PS-U2-3 (T3.8lb, T3.8li): one projection lemma.** State the projection once, for an old column that
  is either a template column or the stopping column `sd.col` (phase `i − 1`); T3.8lb becomes an instance.
- **PS-U2-4 (words): generic word everywhere.** Prove `word_lt_iff`, `keyWord` order and the depth-shift
  lemmas as instances of U1's generic `gword_lt_iff` (REQ-U1-2); U2's L3.1c and N2.1 could then be stated
  for `Tree α`.

## Open problems

| ID | Node | Issue | Severity |
|---|---|---|---|
| OP-U2-1 | T3.8lo | The paper's argument for "the response at a previous-phase root is a parent `≥ r`" (txt:553-560) is compressed. Step 3 (a body-column root's response equals the next vertex of the copied terminal-to-root path) needs an explicit invariant relating `V = κ_φ W` to the old terminal queries along the low-head detour. Not yet verified beyond the paper's text. [VERIFY-U2: the bounded test of the entry's statement ran: 647 caps with `r < ρ < s_φ`, 0 failures (scratch/blueprint/U2-verify/test_phase.py); the proof-level invariant is still open.] | major |
| OP-U2-2 | T3.8li, T3.2q | The projection of the final A-test with capped strict containers, the restored-origin case and the copied-query-height case are reconstructions of txt:520-541. `head_path` is stated for actual keys only; the projection needs a decorated-key variant (containers capped to `⊤`), whose exact hypotheses are not yet fixed. [VERIFY-U2: `head_path_rev` was false for actual keys of `B` and now concludes in the decorated system of `B` (F4); `head_path` (actual keys) passed 30,484 bounded cases. The projection's conclusion passed 32,183 bounded caps; the decorated variant of `head_path` it needs is still unstated. It must restrict the query: with decorated keys on both sides and arbitrary reduced `W` it fails (74 bounded failures, none with `⊤` in `W`), while for `W` a cut query of `a` it held in 9,420 cases.] | major |
| OP-U2-3 | T3.2m | The Lean statement uses one phase `j` for both heights (justified by T3.2h.5: `κ_j` fixes keys normalized at or below `r`). The offset conditions are stated with an existential position `b`; the formalizer may need the explicit position of the old terminal in each key word. REFINABLE. | minor |
| OP-U2-4 | N2.1 | Needs U1's one-atom decoding of safe prefixes (REQ-U1-14). **Integration:** stated as U1 D1.9b `routeCols_of_word_snoc` with a proof plan; not yet tested. | minor |
| OP-U2-5 | T3.8li–T3.8ls | Q-material of head `i` is treated uniformly with phase `i − 1` (the paper has one sentence, txt:535-537). Consistent with `num_phaseCol` and checked on one example only. [VERIFY-U2: now bounded-tested on 4,386 Q-material phase copies and 3,394 Q-material caps (projection, kernel comparison), 0 failures.] | minor |
| OP-U2-6 | T3.8l | No bounded test yet of the ordinary-step sub-lemmas on caps of `A_n`; an address-level model (`kerCol`, `phaseCol` in Python) must be added to checks/. Each entry gives its test. [VERIFY-U2: an address-level model now exists in scratch/blueprint/U2-verify/ (test_phase.py, test_phase_maps.py); T3.2i–T3.2l and T3.8la–T3.8ls were tested on 54,194 caps of outputs of 4,289 ordinary standards. Porting it to checks/ remains.] | minor |
| OP-U2-7 | T3.2k | The I case for heads of layers `i ≥ 2` relies on "shifts preserve first parent `≥` host" for nested placements; written as one step. | minor |
| OP-U2-8 | Stubs | Closed at integration: the stubs are deleted and U1's declarations are used (SCR-U2-1). | — |
