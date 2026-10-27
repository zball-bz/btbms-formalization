# U5 descent-main — blueprint

**Unit:** U5 (`BTBMS.Descent`). **Nodes:** L6.7, D8.1, L8.2–L8.8, T9.1, R9.2, plus the spine's new
nodes D8.1a, N5.1, T9.1a and the sub-nodes below.
**Lean signatures:** `blueprint/lean/U5.lean` (163 declarations [V-fix]). Checked with
`{ grep -h '^import ' blueprint/lean/U5.lean; cat blueprint/lean/Spine.lean; grep -v '^import ' blueprint/lean/U5.lean; } > scratch/blueprint/U5/check.lean && (cd lean && PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake env lean ../scratch/blueprint/U5/check.lean)`:
no errors, only `declaration uses 'sorry'` warnings.
**Inputs read:** paper §5.2, §6–§9 (txt:855-1515), §7 for packets; `00-spine.md`, `Spine.lean`;
`tracker/ledger.json` (G-001, G-003, S-1…S-6, R-3, R-4, D-1…D-3); `claude-review.md` C-02…C-05,
C-10; `codex-review.md` §§6–9 and simplifications 1, 2, 6, 7, 9; `codex-crosscheck-1.md` Q1.
**Marker:** `[V-fix]` marks text that the adversarial verification pass changed or added. Each
marked passage is self-contained.

---

## Overview

U5 proves the top of the argument against the S-4 interface (`Hier.Interface`), using no
J-hierarchy internals.

1. **Seeds (L6.7).** The graph of `L_m` is computed explicitly (L6.7a). It is realized by a
   descending chain of club/stationary choices from a weakly `(m−1)`-Mahlo cardinal (L6.7b, S-1).
2. **The induction (18)** `S_{<n} ⇒ W_{<n} ⇒ D_{<n} ⇒ S_n` on the target size `n`:
   - §8.1: (19) as a syntactic chain lemma plus one generic interface lemma (L8.2), the
     two-candidate fact (L8.3), and `S_0` (L8.4).
   - §8.2: `W` by induction along the actual finite scan trace (L8.5).
   - §8.3: `D` by induction on copy stages. Each stage is one transport of an explicit finite
     diagram `stageDiagram` (L8.6).
   - §8.4: special descent by iterated capture (L8.7).
   - §8.5: `S_n` by well-founded induction on the host-owner pair in `Ordinal ×ₗ Ordinal`
     (L8.8). Each case either contradicts the failure directly (Case 1) or builds a new packet
     and checks all six validity clauses explicitly (G-003).
3. **§9 via S-2/S-5.** Strict descent (27) by case split on the step kind (T9.1). The abstract
   theorem `FinalHyps Conf → IsWellOrder Std Std.lt` is proved by accessibility on the
   configuration maximum (N5.1). The assembly is `finalHyps` (T9.1a).

All budget statements are in the ordinal form of spine §c.7: a certificate in `J_w` is
"every coordinate `< w`".

---

## Mechanical checks done for this draft

All in scratch (`scratch/blueprint/U5/`).
- The top-level wiring typechecks with real proof terms over sorry'd leaves: (18), `finalHyps`,
  `strictDescent`, `seed_config`, `dCore_of_dLab`, the ordinary case of (27),
  `sStrict_of_dLab`, `least_failure`, `std_configured`, `acc_of_conf`, `abstract_wellOrder`,
  `abstract_implies_main` and the `MainTheorem` assembly. Files: `glue.lean`, `glue2.lean`,
  `glue3.lean`.
- By `#eval`, these hold on bounded instances:
  - `seed_roles` and `seed_graph_sub` for `m ≤ 6`, and `seed_zero_graph`;
  - `persist_prefix` / `ι = id`: roles of `E[m]` are a prefix of roles of `E[m+1]`, for
    `m ≤ 3` on 2199 standard expressions;
  - `graph_chain`, `localStruct_vars`, `Req.graph_block` and its converse, and
    `freeBlock_prefix`, on the same 2199 expressions;
  - `Req.reps0_length` on a bounded grid of column addresses (`repstest.lean`).
- [V-fix] Bounded Python tests in `scratch/blueprint/U5-verify/`, against an independent port of
  the spine's real bodies (`spine_model.py`). The expressions are up to 4000 standard expressions
  with at most 40 roles, from seeds 0–5 at parameters 0–3. All checks passed:
  - the stage form R22 for `m ≤ 3`, in both directions, with `retAtoms` as now defined;
  - the special form R27;
  - R3, R4, R5, R10, R12, R15 and R23;
  - `firstK_cases`, `root_position`, `graph_chain`, `route_chain` (syntactic part),
    `localStruct_vars`, `graph_block`, `posBlock_vars`, `seed_roles`, and set equality of
    `graph (seed (m+1))` with `seedGraph m` for `m ≤ 7`.

  `vglue_tail.lean` re-checks the (18) wiring, `seed_config` and `stage_step` with real terms.

---

## Conventions used in the proofs

- `P := I.toPrims` for the interface `I`. "By the interface field `f`" cites the S-4 field
  (spine §c.7).
- Values are compared in reading order through **N5.4** `config_lt_of_before`. "`x` before
  `y`" means `x ∈ rolesBefore E y`.
- For a packet `pk`:
  - `ρ := asg host` and `u := asg owner`;
  - `α_F := asg ∘ srcChart`, a configuration of `F` by [N5.8];
  - `frv := fun w => (tgtFrame.toFr w).map asg`, the frame values of the target block;
  - `B := tgtHeight` and `n := B.size`.
- **(23) at `Ls`** abbreviates three facts:
  - `Ls < u`;
  - `∀ x ∈ lowNames, asg x < Ls`;
  - `¬ BlockAbove P (posBlock tgtKey tgtSel) frv Ls u`.
- `Req.X` is a stub for another unit's declaration (section "Requires"). `[R-k]` cites
  requirement `k`.

---

## Nodes (dependency order)

**N5.7 (moved at integration).** The syntactic helpers `isStruct`, `entrySel`, `entryKey`,
`ePrefix`, `queryAtoms`, `retAtoms` and `specialKey` are now U3 node **D6.1c** (same bodies, namespace
`Packet`, read here through `open Packet`), because the U3 statements that U5 requested (L6.2e,
L6.2f, L7.5d) mention them. Every former citation of N5.7 in this unit now cites D6.1c.

### N5.2 Elementarity chains   (paper: new; generic core of (19), txt:1190-1200, 1289-1291)
**Fidelity:** new (S-4, S-6).
**Statement.** `ElemStep D x y` holds iff one of these is an atom of `D`:
- `elem x y`;
- `edge y x a` for some `a`;
- `edge c y x` for some `c`.

`elem_of_steps`: assume `BaseHolds I.toPrims D β`, `IsLim (β x)` and
`ReflTransGen (ElemStep D) x y`. Then `I.Elem (β x) (β y)`.

`steps_mono`: chains survive enlarging `D`.

**Proof.** Induction on `ReflTransGen`.
1. Reflexive case: `I.elem_refl hx`.
2. Tail step `z → y`, with `Elem (β x) (β z)` by induction:
   - `elem z y ∈ D` gives `Elem (β z) (β y)` directly from `hD`;
   - `edge y z a ∈ D` gives `Edge (β y) (β z) (β a)`, hence `Elem (β z) (β y)` by
     `edge_elem_high`;
   - `edge c y z ∈ D` gives `Edge (β c) (β y) (β z)`, hence `Elem (β z) (β y)` by
     `edge_elem_low`.
3. Compose with `elem_trans`.
4. `steps_mono` is `ReflTransGen.mono`.

**Uses:** none (interface fields only).
**Lean:** `ElemStep`, `elem_of_steps`, `steps_mono`. Planned file `Descent/OwnerPath.lean`.
**Difficulty:** S (about 30 LOC).
**Testable:** no (semantic).

### N5.3 Block problems: floor encoding, capture, monotonicity   (paper: new; L5.8/L5.9 in ordinal form)
**Fidelity:** new (S-4, R-4).
**Statement.**
- `floorDiagram D fr` is a diagram over `Option W`, with `none` the floor. It consists of the
  atoms of `D` renamed by `some`, and `lt none (some x)` for each `x ∈ baseVars D` with
  `fr x = none`.
- `floorFixed fr` fixes `none` and every `some x` with `fr x` defined. `floorSigma fr L` gives
  them the values `L` and `(fr x).getD 0`.
- (a) `blockAbove_iff_floor`: if `L < w`, then
  `BlockAbove P D fr L w ↔ (floorDiagram D fr).RealizableBelow P (floorFixed fr) (floorSigma fr L) w`.
- (b) `blockAbove_capture`: assume
  - `I.Elem a b` and `L < a`;
  - `fr x = some o → o < a` for every `x ∈ baseVars D`;
  - `BlockAbove … L b`.

  Then `BlockAbove … L a`.
- (c) `blockAbove_mono`: if `L ≤ L'`, `w ≤ w'` and `BlockAbove D fr L' w`, then
  `BlockAbove D fr L w'`.
- (d) `blockAbove_of_targetAbove`: `pk.TargetAbove P L` implies
  `BlockAbove P (posBlock tgtKey tgtSel) frv L (asg owner)`.

**Proof.**
1. (a →) From `β`, set `a none = L` and `a (some x) = β x`. Agreement on the fixed variables
   holds by the frame clause of `β`. The variables are below `w`: `β x < w`, and `L < w`.
   Atoms: the `D` atoms hold by N5.4 `baseHolds_map`; `L < β x` holds for new `x`.
2. (a ←) From `a`, set `β x := o` if `fr x = some o`, and `β x := a (some x)` otherwise.
   - `a none = L`, since `none` is fixed.
   - For `x ∈ baseVars D` with `fr x = some o`, `a (some x) = o` since `some x` is fixed. Hence
     `β` and `a ∘ some` agree on `baseVars D`. `BaseHolds D (a ∘ some)` follows from N5.4
     `baseHolds_map`, and `BaseHolds D β` then follows from N5.4 `baseHolds_congr` [V-fix].
   - Floors come from the `lt none (some x)` atoms.
3. (b) `L < a ≤ b` by `elem_le`. Encode by (a) at `b`. Apply `I.capture` with fixed set
   `floorFixed fr`. Its precondition, fixed variables of the diagram below `a`, holds because:
   - `none ↦ L < a`;
   - `some x ↦ o < a` by `hfr`.

   Decode by (a) at `a`.
4. (c) The same witness works.
5. (d) Forget the low-value clause of `TargetAbove`.

**Uses:** N5.4.
**Lean:** `floorDiagram`, `floorFixed`, `floorSigma`, `blockAbove_iff_floor`,
`blockAbove_capture`, `blockAbove_mono`, `blockAbove_of_targetAbove`. Planned file
`Descent/OwnerPath.lean`.
**Difficulty:** M (about 150 LOC of list and `Option` bookkeeping).
**Testable:** no.

### N5.4 Order facts of configurations and maxima   (paper: new; reading-order inequalities used throughout)
**Fidelity:** new.
**Statement.**
- `chain_pairwise`: if `D` contains `lt l[i] l[i+1]` for all consecutive pairs and holds at `β`,
  then `l.Pairwise (β · < β ·)`.
- `config_lim`, `config_pairwise`, `config_lt_of_before`: for a configuration `α` of `E`,
  - roles have limit values;
  - values strictly increase in reading order;
  - `x ∈ rolesBefore E y` and `y ∈ E.roles` give `α x < α y`.
- `le_cfgMax` and `cfgMax_lt` (the latter needs `0 < θ`): at integration these are U3 D6.1a
  `le_cfgMax`, `cfgMax_lt` (same statements), and U5's copies are removed.
- `config_of_sub`: `graph F ⊆ graph E` and `IsConfig E α` give `IsConfig F α`.
- `holds_ofBase`, `toFr_map`: renaming lemmas. (`baseHolds_map` is U3 N3.1 `Hier.baseHolds_map`;
  U5's copy is removed at integration.)
- `baseHolds_congr` [V-fix, new]: if `a = a'` on `baseVars D`, then
  `BaseHolds P D a ↔ BaseHolds P D a'`. At integration this is U4 N4.1b `Hier.baseHolds_congr`
  (same statement); U5's copy is removed.
- `isLim_add_omega` [V-fix]: `ω ≤ o` gives `IsLim (o + ω)` and `o < o + ω`. The earlier
  hypothesis `0 < o` was false at `o = 1`: `1 + ω = ω` is not `> ω` (Mathlib
  `Ordinal.one_add_omega0`).

**Proof.**
1. `chain_pairwise`: the `lt` atoms give `List.Chain'`, and transitivity gives `Pairwise`.
2. `config_pairwise`: apply step 1 to the `zip rs rs.tail` block of `graph`, which has a real
   body.
3. `config_lt_of_before`: `takeWhile` splits `E.roles` as `pre ++ y :: post` with `x ∈ pre`;
   apply step 2.
4. `cfgMax`: provided by U3 D6.1a (`le_cfgMax`, `cfgMax_lt`).
5. `isLim_add_omega` [V-fix]: `o + ω` is a successor limit because `ω` is a limit
   (Mathlib `Ordinal.isSuccLimit_add`-style lemmas). Also `ω ≤ o < o + ω`, since `0 < ω`, so
   `ω < o + ω`.
6. `baseHolds_congr`: provided by U4 N4.1b.

**Uses:** D6.1a, F5.1a, N3.1, N4.1b (providers of the removed duplicates; F5.1a's `isLim_add_omega0` is
the first conjunct of `isLim_add_omega`).
**Lean:** the names listed above. Planned file `Descent/Predicates.lean`.
**Difficulty:** S.
**Testable:** no.

### N5.5 Fresh names   (paper: new; "fresh names", txt:1017-1021)
**Fidelity:** new.
**Statement.** `tagBound l` is one more than the largest role tag in `l`.
`Name.role (tagBound l) r ∉ l` for every `r`.
**Proof.** Induction on `l`.
**Uses:** none.
**Lean:** `tagBound`, `tagBound_fresh`. Planned file `Descent/Predicates.lean`.
**Difficulty:** S.
**Testable:** yes, by enumeration.

### N5.6 Prefix monotonicity of free blocks   (paper: new; used at txt:1358 and txt:1326-1327)
**Fidelity:** new.
**Statement.** Assume `K.cols = K'.cols.take K.cols.length`. Then:
- every atom of `freeBlock K` is an atom of `freeBlock K'`, and `K.roles <+: K'.roles`
  (`freeBlock_prefix`);
- the same holds for `posBlock K sel ⊆ posBlock K' sel` (`posBlock_prefix`).

`posBlock_vars` [V-fix, new], for every `K` and `sel`. Every `w ∈ baseVars (posBlock K sel)`
is one of:
- `host` or `owner`;
- `ord q` or `cur q` for some `q`;
- `inner r` with `r ∈ K.roles`.

Since `freeBlock K` is a sublist of `posBlock K sel`, the same holds for `freeBlock K`.

**Proof of `posBlock_vars`.** Go through the blocks of the real body of `freeBlock`.
- The `lim`, `lt` and `elem` atoms read `owner` and `inner r` for `r ∈ K.roles`, or
  `r = ord c` for `c ∈ K.colAddrs`.
- An edge atom of an entry `e ∈ K.entryAddrs` reads `inner (slot e)` and `inner (ord e.col)`.
  - A false label adds `ord q` and `cur q`.
  - The label `(true, 0)` adds `host` and `owner`.
  - The label `(true, v+1)` adds the pair `e.col.rep 1 (v+1) = (o, w)`. Here `o` is
    `ord` of a column on the visible stack of `e.col`. That column is a containing column of
    `e.col`, or an earlier column of a containing forest or of `e.col`'s own forest (real body
    of `resolveAux`). All of these are columns of `K`, because `e.col` is one. `w` is `o`
    again, or the slot of the entry of `o` on `e.col`'s path, which is an entry of `K`.
- The two head atoms read `owner`, `host`, `ord sel` and `cur sel`.

**Proof.**
1. `rolesCols π 0 (cs ++ ds) = rolesCols π 0 cs ++ rolesCols π |cs| ds`, by induction on `cs`
   (real body of `Tree.rolesCols`). This gives the role prefix, hence the `lim` and `lt`-chain
   atoms.
2. `colAddrs` and `entryAddrs` of `K` embed in those of `K'` with the same addresses. Also
   `K.colAt c = K'.colAt c` and `K.entryAt e = K'.entryAt e` on them, so the `elem` and `edge`
   blocks of `freeBlock` are produced identically. `ColAddr.rep` depends only on the address.
3. The heads of `posBlock` are the same two atoms.

**Uses:** none.
**Lean:** `freeBlock_prefix`, `posBlock_prefix`, `posBlock_vars` [V-fix]. Planned file
`Descent/OwnerPath.lean`.
**Difficulty:** M (mutual recursion over `rolesF/rolesCols/rolesCol`, about 150 LOC).
**Testable:** yes. `freeBlock_prefix` was checked on every entry key and every outer-column
prefix of 2199 standard expressions (`scratch/blueprint/U5/blocktest.lean`). [V-fix] The `inner`
clause of `posBlock_vars` was checked on the entry keys of 2500 standard expressions and on 3000
random raw keys (`scratch/blueprint/U5-verify/test_misc.py`).

### N5.8 Projections of packet validity   (paper: new; txt:1045-1065)
**Fidelity:** new.
**Statement.** For `pk.Valid P`:
- `valid_src_config`: `IsConfig P pk.rk.F (asg ∘ srcChart)`.
- `valid_tgt_prefix`: `BaseHolds P (prefixGraph E b) (asg ∘ tgtChart)`.
- `valid_aux`: `aux.Holds P asg`.

With `pk.rk.Admitted`, `lowNames_spec` gives:
- `host ∈ lowNames`;
- every target frame name is in `lowNames`;
- `owner ∉ lowNames`.

**Proof.**
1. Valid clause 4 is `joint.Holds`. `joint` is three `ofBase`/`++` blocks; use N5.4
   `holds_ofBase` and `baseHolds_map`.
2. The host is `srcChart (ord a.col)`, and `ord a.col ∈ prefixRoles F a` by [R19].
3. Target frame roles are in `prefixRoles E b` by [R19].
4. The owner is not low: Valid clause 6 gives `asg x < asg owner` for every low `x`, so
   `owner = x` would give `asg owner < asg owner`.

**Uses:** N5.4, [R19].
**Lean:** `valid_src_config`, `valid_tgt_prefix`, `valid_aux`, `lowNames_spec`. Planned file
`Descent/Predicates.lean`.
**Difficulty:** S.
**Testable:** no.

### L6.7a Seed syntax   (paper: txt:138-140, 1000-1004)
**Fidelity:** as in paper, made explicit.
**Statement.**
- `seedCol 0 = ⟨[],0⟩`, `seedCol 1 = ⟨[],1⟩`, and `seedCol (i+2) = ⟨(1,0) :: replicate i (0,0), 0⟩`.
- `seedA i = ord (seedCol i)` and `seedU i = slot ⟨seedCol i, 0⟩`.
- `seedRoles m = A_0 :: [A_1, U_1, …, A_{m+1}, U_{m+1}]`.
- `seedGraph m` consists of:
  - `lim` on `seedRoles m`;
  - the consecutive `lt` chain;
  - `elem A_0 A_1`;
  - for `i ≤ m`: `edge U_{i+1} A_{i+1} A_i`, and `edge U_{i+1} A_{i+1} (if i = 0 then A_0 else U_i)`.

Claims:
1. `seed_roles`: `(seed (m+1)).roles = seedRoles m`.
2. `seed_graph_sub`: `∀ a ∈ graph (seed (m+1)), a ∈ seedGraph m`.
3. `seed_zero_graph`: `(seed 0).roles = [ord ⟨[],0⟩]` and `graph (seed 0) = [lim (ord ⟨[],0⟩)]`.

**Proof.**
1. `seed (m+1) = .node [[], branch 0 m]` (locked). By induction on `k`, the roles of
   `rolesF π (.node [branch i k])` are `ord ⟨π,0⟩, slot ⟨⟨π,0⟩,0⟩`, followed by the roles of
   `rolesF (π ++ [(0,0)]) (.node [branch (i+1) (k−1)])`. Here `π` starts with `(1,0)`.
2. Edges: entry `U_{i+1}` has parent `i`. `ColAddr.rep 0 (seedCol (i+1)) i` is:
   - `(A_0, A_0)` for `i = 0`, since column 0 does not contain column 1;
   - `(A_i, U_i)` for `i ≥ 1`, since column `i` contains column `i+1`.

   The second case is `Req.rep_host` [R9] with `e = ⟨seedCol i, 0⟩`.
3. The `elem` block: only the outer forest has two columns.
4. `seed_zero_graph`: by computation.

**Uses:** [R9].
**Lean:** `seedCol`, `seedA`, `seedU`, `seedRoles`, `seedGraph`, `seed_roles`,
`seed_graph_sub`, `seed_zero_graph`. Planned file `Descent/Seed.lean`.
**Difficulty:** M (about 250 LOC; induction on the branch through mutual `rolesF`).
**Testable:** yes. `(seed (m+1)).roles == seedRoles m` and set equality of `graph (seed (m+1))`
with `seedGraph m` were checked by `#eval` for `m = 0…6`; `seed_zero_graph` too
(`scratch/blueprint/U5/seedtest.lean`).

### L6.7b Descending Mahlo chain   (paper: txt:1005-1011)
**Fidelity:** simplified (S-1: weakly `k`-Mahlo; only regularity and stationarity are used).
**Statement.** `mahlo_chain`. For every `k`, `κ` and `w` with `IsWeaklyMahlo k κ`, `IsLim w` and
`κ.ord < w`, there are `a, v : ℕ → Ordinal` with:
- `a (k+1) = κ.ord` and `v (k+1) = w`;
- `Edge (v (i+1)) (a (i+1)) (a i)` for `i ≤ k`;
- `Edge (v (i+1)) (a (i+1)) (v i)` for `1 ≤ i ≤ k`;
- `a i < v i` for `1 ≤ i ≤ k+1`.

**Proof.** Induction on `k`.
1. **`k = 0`.**
   - `ℵ₀ < κ` and `κ` is regular by [R31] `weaklyMahlo_regular`.
   - `club_edge κ w` gives a club `C ⊆ Iio κ.ord` with `Edge w κ.ord x` for every `x ∈ C`.
   - `C` is nonempty: `IsClub.nonempty`, with `0 < κ.ord`.
   - Pick `x₀ ∈ C` and set `a 0 = x₀`, `a 1 = κ.ord`, `v ≡ w`. The clauses are the club
     property and `κ.ord < w`.
2. **`k+1`.**
   - Regularity and stationarity of `S = {μ.ord | IsWeaklyMahlo k μ}` in `κ`, by [R31].
   - `club_edge κ w` gives `C`. Stationarity (`IsStationary`) gives `x₁ ∈ C` with
     `x₁ = μ.ord` and `IsWeaklyMahlo k μ`.
   - Cofinality of `C` (`IsClub.isCofinal`) at `succ x₁`, which is `< κ.ord` because
     `IsLim κ.ord` (`isLim_ord`), gives `y ∈ C` with `x₁ < y`.
   - `IsLim y` holds by `edge_lim` of `Edge w κ.ord y`.
   - The induction hypothesis at `(k, μ, y)` gives `a', v'`. Set `a = a'` and `v = v'` below
     `k+2`, with `a (k+2) = κ.ord` and `v (k+2) = w`.
   - New clauses at `i = k+1`: `Edge w κ.ord x₁` and `Edge w κ.ord y` (club), and `κ.ord < w`.
     The other clauses come from the induction hypothesis.

**Uses:** [R31]; interface fields `club_edge`, `edge_lim`; `Hier.isLim_ord`.
**Lean:** `mahlo_chain`. Planned file `Descent/Seed.lean`.
**Difficulty:** M (about 150 LOC; `Set.Iio` subtype bookkeeping).
**Testable:** no.

### L6.7c Seed values   (paper: txt:1011-1012)
**Fidelity:** as in paper.
**Statement.** `seedVal a v` sends:
- `ord c` to `a 0` if `c = ⟨[],0⟩`, and to `a (c.path.length + 1)` otherwise;
- `slot e` to `v (e.col.path.length + 1)`.

`seedGraph_holds`: the three clause families of L6.7b at `k = m` give
`BaseHolds I.toPrims (seedGraph m) (seedVal a v)`.

**Proof.**
1. `seedVal (seedA i) = a i` and `seedVal (seedU (i+1)) = v (i+1)`, by computation on
   `seedCol`.
2. `lim` atoms: `edge_lim` of the edges `Edge (v(i+1)) (a(i+1)) (a i)` covers `a 0…a(m+1)` and
   `v 1…v(m+1)`.
3. Chain atoms:
   - `a 0 < a 1`: `edge_lt` of the `i = 0` edge;
   - `a i < v i`: third clause;
   - `v i < a (i+1)` for `1 ≤ i ≤ m`: `edge_lt` of `Edge (v(i+1)) (a(i+1)) (v i)`.
4. `elem A_0 A_1`: `edge_elem_low` of the `i = 0` edge.
5. Edges: the clauses themselves.

**Uses:** L6.7a.
**Lean:** `seedVal`, `seedGraph_holds`. Planned file `Descent/Seed.lean`.
**Difficulty:** S.
**Testable:** no.

### L6.7 Seed lemma   (paper: txt:1000-1013)
**Fidelity:** simplified (S-1). For `m = 0` the value `κ.ord` (any limit) replaces `ω·2`.
**Statement.** `seed_config I m (hM : ∃ κ, IsWeaklyMahlo (m − 1) κ) : ∃ α, IsConfig I.toPrims (seed m) α`.
This is spine-declared.
**Proof.** Verified in scratch as `glue_seed_config`.
1. `m = 0`: take `α ≡ κ.ord`. By L6.7a `seed_zero_graph`, the only atom is `lim A_0`. It holds
   by `isLim_ord` of [R31] `(weaklyMahlo_regular hκ).1`.
2. `m+1`: `κ.ord` is a limit, so `ω < κ.ord` (the second conjunct of `IsLim`), hence
   `ω ≤ κ.ord`. By N5.4 `isLim_add_omega` [V-fix], `w = κ.ord + ω` is a limit with `κ.ord < w`.
3. L6.7b gives `a, v`. L6.7c gives `seedGraph` at `seedVal a v`. L6.7a `seed_graph_sub` gives
   `IsConfig`.

**Uses:** L6.7a, L6.7b, L6.7c, N5.4, [R31].
**Lean:** `seed_config` (spine). Planned file `Descent/Seed.lean`.
**Difficulty:** S.
**Testable:** no.

### D8.1 `S_n`, `W_{<n}`, `D_{<n}` and the induction (18)   (paper: txt:1171-1189)
**Fidelity:** as in paper, in the spine's FIRM ordinal form (`SStrict`, `WFit`,
`AllowedInput`, `DCore`, `DLab`). No change requested.
**Statement.** For every `n`, with spine names:
- `sStrict_all I n : SStrict I.toPrims n`;
- `wFit_all I n : WFit I.toPrims n`;
- `dLab_all I n : DLab I.toPrims n`;
- `dCore_all I n : DCore I.toPrims n`.

**Proof.** [V-fix] The base case now goes through L8.4. Verified in scratch as
`vglue_sStrict_all` and `vglue_dCore_all` (`scratch/blueprint/U5-verify/vglue_tail.lean`).
1. `sStrict_all` by `Nat.strong_induction_on n`, splitting on `n`.
   - `n = 0`: [L8.4] `sStrict_zero I`. This is the paper's direct base case (txt:1211-1214).
   - `n = k + 1`, with `ih : ∀ m < k + 1, SStrict m`:
     - [L8.5] `wFit_of_sStrict I (k+1) ih : WFit (k+1)`;
     - [L8.6] `dLab_of_wFit I (k+1) : DLab (k+1)`;
     - [L8.8] `sStrict_of_dLab I (k+1) : SStrict (k+1)`.
2. `wFit_all n := wFit_of_sStrict I n (fun m _ => sStrict_all I m)`.
3. `dLab_all n := dLab_of_wFit I n (wFit_all n)`.
4. `dCore_all n := dCore_of_dLab _ n (dLab_all n)` [D8.1a].

L8.8 is stated for every `n`. At `n = 0` its proof would also work, because an empty target
can only end first (Case 1). That would however depend on U3's classifier `firstDiff` returning
`wholeEnds` for every admitted record with an empty target. Routing `n = 0` through L8.4
removes that dependency.

**Uses:** L8.4, L8.5, L8.6, L8.8, D8.1a.
**Lean:** `sStrict_all`, `wFit_all`, `dLab_all`, `dCore_all` (spine). Planned file
`Descent/Induction.lean`.
**Difficulty:** S.
**Testable:** no.

### D8.1b Failures and the host-owner pair   (paper: txt:1349-1352)
**Fidelity:** new (makes the minimal-counterexample measure explicit; G-003).
**Statement.** `Fails P n pk L` is the conjunction of:
- `pk.rk.Admitted`;
- `pk.Valid P`;
- `tgtHeight.size = n`;
- `L < asg owner`;
- `¬ TargetAbove P L`.

`failPair pk := toLex (asg host, asg owner) : Ordinal ×ₗ Ordinal`.

**Proof.** Definitions.
**Uses:** none.
**Lean:** `Fails`, `failPair`. Planned file `Descent/Strict.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.2a Local steps of Γ(E)   (paper: txt:1194-1197)
**Fidelity:** as in paper (the three step kinds of the owner path).
**Statement.** `localStruct E e` is the list of structural atoms of `graph E` with a variable
`v` satisfying `v.inEntry e`.
1. `elem_col_succ`: `c ∈ E.colAddrs` and `(E.colAt ⟨c.path, c.col+1⟩).isSome` give
   `elem (ord c) (ord ⟨c.path, c.col+1⟩) ∈ graph E`.
2. `step_col_slot`: under V, for `e` an entry, `∃ o, edge (slot e) (ord e.col) o ∈ graph E`.
3. `step_slot_child`: under V and I, for `e` an entry with height `h ≠ ∅`:
   `edge (slot ⟨⟨e.heightPath,0⟩,0⟩) (ord ⟨e.heightPath,0⟩) (slot e) ∈ graph E`.

**Proof.**
1. Claim 1: the `elem` block of `graph` (real body).
2. Claim 2: V gives `(e.col.resolve 0 p).isSome`, so `rep` is `some`, and the edge block emits
   both atoms.
3. Claim 3:
   - [R8] `firstParent_host`: the first entry of the first column of `h` has parent
     `a = e.col.num 0`.
   - [R9] `rep_host`: `rep 0 ⟨e.heightPath,0⟩ a = some (ord e.col, slot e)`.
   - The edge block then emits `edge (slot first) (ord first col) (slot e)`.

**Uses:** [R8], [R9].
**Lean:** `localStruct`, `elem_col_succ`, `step_col_slot`, `step_slot_child`. Planned file
`Descent/OwnerPath.lean`.
**Difficulty:** M (address arithmetic, about 150 LOC).
**Testable:** yes (computable; covered by the L8.2b test).

### L8.2b Owner-path chain   (paper: txt:1194-1200)
**Fidelity:** as in paper ("induction through the finite tree").
**Statement.** `graph_chain`: under V and I, with `e` an entry, `z ∈ E.roles` and
`z.inEntry e`, we have `ReflTransGen (ElemStep (localStruct E e)) (slot e) z`.
**Proof.** Strong induction on `z.path.length − e.heightPath.length`, generalizing `e`.
1. If `z = slot e`: refl.
2. Otherwise [R12] `roles_entry` gives `z = roleUnder e.heightPath r` for a role `r` of the
   height `h`. In particular `h ≠ ∅`.
3. If `r = ord ⟨[], c⟩`: go `slot e → ord ⟨hp,0⟩` [L8.2a(3)], then
   `ord ⟨hp,0⟩ → … → ord ⟨hp,c⟩` by [L8.2a(1)] `c` times. Here `hp = e.heightPath`; columns
   `0…c` exist because `z` is a role. All these atoms touch `e`.
4. If `r = slot ⟨⟨[],c⟩,i⟩`: reach `ord ⟨hp,c⟩` by step 3, then [L8.2a(2)] gives the step to
   the slot. Its edge atom touches the slot, which is inside `e`.
5. If `r` lies inside the height of the entry `e' = ⟨⟨hp,c⟩,i⟩`: reach `slot e'` by step 4.
   The induction hypothesis at `e'` gives a chain in `localStruct E e'`. It lies in
   `localStruct E e`, because `inEntry e'` implies `inEntry e` (the paths extend). Conclude
   with [N5.2] `steps_mono`.

**Uses:** L8.2a, N5.2, [R12].
**Lean:** `graph_chain`. Planned file `Descent/OwnerPath.lean`.
**Difficulty:** M (about 200 LOC).
**Testable:** yes. Reachability from `slot e` of every role inside `e`, in the step graph of
`localStruct E e`, was checked for every entry of 2199 standard expressions
(`scratch/blueprint/U5/chaintest.lean`).

### L8.2c Variables of local atoms   (paper: txt:1059, 1074-1077, 1152-1154: "old edges read no new role")
**Fidelity:** new (makes the frame discipline explicit).
**Statement.** `localStruct_vars`: under V, for `e` an entry, every variable `v` of every atom of
`localStruct E e` satisfies one of:
- `v.inEntry e`;
- `v = ord e.col`;
- `v ∈ {o, p}` for some `(o, p) ∈ e.col.reps0`.

**Proof.**
1. `elem` atoms join consecutive columns of one forest. If one is inside `e`, both have the same
   path, hence both are inside `e`.
2. An edge atom of an entry `e''` has variables `slot e''`, `ord e''.col` and the two
   representatives `rep 0 e''.col p`.
   - If a variable inside `e` is `slot e''` or `ord e''.col`, then `e''` is `e` or inside `e`.
   - The representatives lie on the visible stack of `e''.col`. By `resolve_spec` [R11], this
     stack consists of columns inside `e`, the host `e.col` with current representative
     `slot e` ([R9] `rep_host`), and the numbers below `e.col.num 0`. [V-fix] For those numbers,
     [R10] `reps0_take` with `d = e''.col` and `c = e.col` shows that the representative pairs
     seen from `e''.col` are exactly the entries of `e.col.reps0`. `resolve_spec` alone gives
     the ordinary roles, but not the agreement of the current representatives.
   - If only a representative is inside `e`, then `e''.col` sees an internal role, so
     `e''.col` is inside `e`. This is the first case again.

**Uses:** [R9], [R10], [R11] (spine `resolve_spec`†). [V-fix] R9 and R10 added.
**Lean:** `localStruct_vars`. Planned file `Descent/OwnerPath.lean`.
**Difficulty:** M.
**Testable:** yes. Checked on 2199 standard expressions (`chaintest.lean`).

### L8.2 (19) Owner-path elementarity   (paper: txt:1190-1200)
**Fidelity:** as in paper, stated for any realized diagram containing the local atoms. This
covers configurations, bank graphs and query graphs.
**Statement.**
- `owner_path_elem`: assume
  - V and I;
  - `e` is an entry;
  - `localStruct E e ⊆ D` and `BaseHolds P D β`;
  - `IsLim (β (slot e))`;
  - `z ∈ E.roles` with `z.inEntry e`.

  Then `I.Elem (β (slot e)) (β z)`.
- `owner_path_elem_config`: the same for `D = graph E` and `β = α`, a configuration.

**Proof.**
1. [L8.2b] gives a chain in `localStruct E e`. [N5.2] `steps_mono` moves it to `D`.
2. [N5.2] `elem_of_steps` concludes.
3. For configurations, `IsLim` holds by [N5.4] `config_lim`.

**Uses:** L8.2b, N5.2, N5.4.
**Lean:** `owner_path_elem`, `owner_path_elem_config`. Planned file `Descent/OwnerPath.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.2d Route elementarity   (paper: txt:1289-1291)
**Fidelity:** as in paper.
**Statement.** `OnRoute sd v` holds in two cases:
- `v = ord c` with `c.path = sd.col.path.take d` and `c.col ≤` the route column index at depth
  `d`;
- `v = slot e` with `e.heightPath <+: sd.col.path`.

`route_chain`: under V and I, with `stopData H = sd`, a configuration `α`, `v ∈ H.roles` and
`OnRoute sd v`, we have `I.Elem (α v) (α (ord sd.col))`.

**Proof.** Induction on `ℓ − d`, with `ℓ = |sd.col.path|`.
1. **Ordinary `v` at depth `d`.** Use `elem` steps [L8.2a(1)] along the route forest up to its
   route column.
   - If `d = ℓ`, that column is `T`.
   - Otherwise its route entry `e_d` contains `T`. Step to `slot e_d` [L8.2a(2)], then to the
     first column of its height [L8.2a(3)], then apply the induction hypothesis at depth `d+1`
     and column 0.
2. **Slot `v`.** Step to the height's first column [L8.2a(3)] and apply the ordinary case.
3. The route entries exist because `ord sd.col ∈ H.roles` [R4].
4. Conclude with [N5.2] `elem_of_steps`.

**Uses:** L8.2a, N5.2, [R4].
**Lean:** `OnRoute`, `route_chain`. Planned file `Descent/OwnerPath.lean`.
**Difficulty:** M.
**Testable:** yes (syntactic part, once `stopData` has a body).

### L8.3 Two-candidate fact   (paper: txt:1201-1210)
**Fidelity:** as in paper. Two hypotheses are added: the owner paths of both candidates, which
the paper derives from (19), and "frame values at most the floor", which the paper takes from
"frame and floor lie in `J_{h_Y}`".
**Statement.**
- `IsFreeReal P K fr L β` holds iff:
  - `β` agrees with `fr` where `fr` is defined;
  - `L < β w` for every `w ∈ baseVars (freeBlock K)` with `fr w = none`;
  - `BaseHolds P (freeBlock K) β`.
- `blkMax K β` is the `foldr max 0` of `β` over `owner :: K.roles.map inner`.
- `two_candidates`: assume
  - `IsFreeReal … βX` and `IsFreeReal … βY`;
  - owner paths: `∀ r ∈ K.roles, Elem (β owner) (β (inner r))` for `β = βX, βY`;
  - frame bound: `fr w = some o → o ≤ L` for `w ∈ baseVars (freeBlock K)`;
  - completeness of the frame: every `w ∈ baseVars (freeBlock K)` with `fr w = none` is the
    owner or an `inner` variable.

  Then some `β` satisfies `IsFreeReal`, with owner `≤` both owners and `blkMax ≤` both
  maxima.

**Proof.**
1. Order the candidates. Let `(A, B)` be `(βX, βY)` if
   `(blkMax βX, βX owner) ≤ (blkMax βY, βY owner)` lexicographically, and `(βY, βX)` otherwise.
   So `blkMax A ≤ blkMax B`, and equality of maxima implies `A owner ≤ B owner`.
2. If `A owner ≤ B owner`, take `β = A`.
3. Otherwise `B owner < A owner`. Then:
   - `blkMax A < blkMax B`, by step 1;
   - `A owner ≤ blkMax A`, since the owner is in the list;
   - hence `h_B < h_A ≤ c_A < c_B` (txt:1205).
4. `c_B > h_B`, so the maximum is attained at some `inner r`. Hence `K.roles ≠ []`, and the owner
   path gives `Elem h_B c_B`.
5. `A` witnesses `BlockAbove (freeBlock K) fr L c_B`:
   - its new values are `≤ c_A < c_B`;
   - its frame values are `≤ L < h_B < c_B`.

   Frame variables are not new: `fr` is complete, by hypothesis. [V-fix] A new variable `w` is
   the owner or `inner r` by `hnew`. By [N5.6] `posBlock_vars`, `r ∈ K.roles`, so `w` is
   one of the variables over which `blkMax` is taken, and `A w ≤ blkMax A = c_A`.
6. [N5.3] `blockAbove_capture`, with `Elem h_B c_B`, floor `L < h_B` and frame values
   `≤ L < h_B`, gives a realization with all coordinates `< h_B`. Its owner is
   `< h_B < h_A` and its maximum `< h_B ≤ c_A < c_B`.

**Uses:** N5.3, N5.4, N5.6 [V-fix: N5.6 added].
**Lean:** `IsFreeReal`, `blkMax`, `two_candidates`. Planned file `Descent/OwnerPath.lean`.
**Difficulty:** M (about 200 LOC).
**Testable:** no.

### L8.4 Base `S_0`   (paper: txt:1211-1214; codex-crosscheck-1 Q1)
**Fidelity:** as in paper. S-3 is rejected, so the capture along `J_u ≺ J_b` is kept. The
existence of a limit `s ∈ (L*, u)` is a [N5.3] capture of the one-atom problem `[lim x]`.
**Statement.** `sStrict_zero I : SStrict I.toPrims 0`.
**Proof.** Fix `pk`, admitted and valid, with `tgtHeight.size = 0`, and `L < u`.
1. `B = ∅`: a forest of size 0 has no columns.
2. Factorization (spine L7.3) gives `Ls` with:
   - `L ≤ Ls < u`;
   - low values `< Ls`;
   - `BlockAbove (posBlock tgtKey sel) frv Ls u → TargetAbove L`.
3. The source is nonempty:
   - `tgtKey = relKey t ∅ = ∅`;
   - if `srcHeight = ∅` then `srcKey = ∅` by [R14], contradicting `tgtKey < srcKey` from
     Admitted.

   So, by [R12], `z := roleUnder a.heightPath (ord ⟨[],0⟩)` is a role of `F` inside `a`.
4. Let `b := α_F z`. Then:
   - [L8.2] `owner_path_elem_config` on `F`, with V and I from `InL F` (Admitted) and `α_F` a
     configuration [N5.8], gives `Elem u b`;
   - `u < b` by [N5.4].
5. Choose a limit `s` with `Ls < s < u`: apply [N5.3] `blockAbove_capture`, with
   `W = Unit`, `D = [lim ()]`, `fr = none`, floor `Ls < u` and `Elem u b`, to the witness
   `() ↦ u`, which satisfies `Ls < u < b`.
6. Valid clause 5 gives `Edge u ρ o` and `Edge u ρ v` for `(o, v) = tgtFrame.reps[sel]`.
   `edge_restrict`, with `ρ < s` (`ρ` is low [N5.8], hence `< Ls < s`) and `s ≤ u`, gives
   `Edge s ρ o` and `Edge s ρ v`.
7. `posBlock ∅ sel = [lim owner] ++ heads` (computation of `freeBlock (.node [])`). Set
   `β := frv` on frame variables and `β owner = s`. Check `BlockAbove … Ls u`:
   - the new value `s > Ls`;
   - all values `< u`: frame names are low [N5.8];
   - `IsLim s`, and the heads hold (step 6).

   Factorization (step 2) gives `TargetAbove L`.

**Uses:** N5.3, N5.4, N5.8, L8.2, [R12], [R14]; spine `factorization`.
**Lean:** `sStrict_zero`. Planned file `Descent/Base.lean`.
**Difficulty:** M (about 200 LOC).
**Testable:** no.

### L8.5a Setup notation   (paper: txt:1126-1137, 1217-1219)
**Fidelity:** repaired (G-003: the §7.3 hypotheses as exact clauses).
**Statement.** These are definitions with real bodies, for a scan setup `S`:
- `setupBank S`: roles of root entries `0…c`;
- `setupPreRoot S`;
- `setupBankGraph S`: the atoms of `Γ(H)` inside `preRoot ∪ {R} ∪ bank` involving `R` or the
  bank;
- `setupBankVal S`: bank roles through `bankNm`, `R ↦ asg stopNm`, otherwise `baseVal`;
- `setupPosVal S = fitVal (asg ∘ qNm)`;
- `setupEPrefix S`;
- `queryKey S j`, `querySel S j`;
- `queryOwnerVal S j` (`h_j`), `queryBlockMax S j` (`c_0`), `bankBlockMax S i` (`M_i`).

`SetupClauses P S` is S1–S6 of spine §c.11 written out. At integration the spine body of
`ScanSetup.Valid` is U3's `ValidDef` (SCR2 of U3); L8.5h proves the two equivalent.
**Proof.** Definitions.
**Uses:** D6.1c.
**Lean:** `setupBank`, `setupPreRoot`, `setupBankGraph`, `setupBankVal`, `setupPosVal`,
`setupEPrefix`, `queryKey`, `querySel`, `queryOwnerVal`, `queryBlockMax`, `bankBlockMax`,
`SetupClauses`. Planned file `Descent/Fitting.lean`.
**Difficulty:** S.
**Testable:** yes (definitions computable once U1 bodies exist).

### L8.5h `ScanSetup.Valid` written out   (paper: txt:1127-1137)
**Fidelity:** new (requested by L8.5 and L8.6h; it replaces the stub `Req.valid_iff` (R24) and
U5's SCR-2 at integration).
**Statement.** `valid_iff`: `S.Valid P ↔ SetupClauses P S`.
**Proof.** At integration the spine body of `ScanSetup.Valid` is `S.ValidDef P` (U3 D7.2b, SCR2 of
U3). Compare its clauses with `SetupClauses` (L8.5a) one by one.
1. S1: identical, except that `S.rootLen` is `((S.H.colAt S.rd.col).getD []).length` by the spine
   body of `rootLenOf`.
2. S2: `S.PE = rolesBefore S.E (S.chi (A_{sd.col}))` and `setupEPrefix S = ePrefix S.E S.cap S.sd`.
   Under S1 (`stopData S.H = some S.sd` and `InL S.E` from `IsStd S.E`, T3.2 `std_inL`), U2 D3.1d
   `anchorOrigin_prefix` gives `anchorOrigin E cap A_{sd.col} = some T'`, so
   `S.chi A_{sd.col} = T'` (spine `anchorD` is `getD`) and `ePrefix = rolesBefore E T'` (U3 D6.1c
   body): the two lists are equal. The graph clause: U3 N3.1 `baseHolds_map` turns
   `(D.map (BaseAtom.map ePre))` at `asg` into `D` at `asg ∘ ePre`.
3. S3: identical.
4. S4: `S.qVal x = if x ∈ queryRoles then asg (qNm x) else baseVal x`, which is
   `setupPosVal S = S.fitVal (asg ∘ qNm)` by the spine body of `fitVal`.
5. S5: `S.bankGraph = setupBankGraph S`, since both restrict `Γ(H)` to `preRoot ++ [R] ++ bank`
   and keep the atoms with a variable equal to `R` or in the bank. The values `S.bankVal` and
   `setupBankVal S` agree on every variable of that graph, so U4 N4.1b `baseHolds_congr` applies:
   on `R` both are `asg stopNm` (`R ∉ bank`, because a role in an entry of the root column is a slot
   or lies in a height, spine `Role.inEntry`); on bank roles both are `asg (bankNm x)`; on a
   pre-root role `x` (before `R`, hence before `T` and not the closing slot) `S.chi x = y` with
   `anchorOrigin x = some y` (U2 D3.1d `anchorOrigin_prefix`), so `asg (ePre (chi x)) = baseVal x`
   (spine body of `baseVal`, `x ≠ T`).
6. S6: identical up to `x ∉ l.map f ↔ ∀ y ∈ l, x ≠ f y` (`List.mem_map`), with the lists of step 2.
**Uses:** D3.1d, D6.1c, D7.2b, L8.5a, N3.1, N4.1b, T3.2.
**Lean:** `Descent.valid_iff`. Planned file `Descent/Fitting.lean`.
**Difficulty:** S (about 100 LOC).
**Testable:** no (semantic).

### L8.5b Scan invariant and its start   (paper: txt:1220-1221)
**Fidelity:** as in paper.
**Statement.** `ScanInv P S i j β` holds iff:
- `S.Fitted P j β`;
- `S.Lmax j β < S.ownerVal i`;
- `S.Lmax j β ≤ S.Cmax j`.

This is (17) plus the fitting. `scan_init`: `SetupClauses P S → ScanInv P S 0 0 β` for every `β`.
**Proof.**
1. `Fitted 0`: the restriction of `queryGraph` to `P⁻ ++ [T]` holds at `fitVal β`. `fitVal β`
   agrees with `setupPosVal` there, and S4 gives the full `queryGraph`.
2. `Lmax 0 = Cmax 0 = ρ`, since `fittedRoles 0 = []`.
3. `ρ < u_0`: `lt (R, slot 0)` is in `setupBankGraph`, because `slot 0` directly follows `R` in
   reading order and `c ≥ 0` is a bank index (S1: `c < |root|`). It holds at `setupBankVal` by
   S5.

**Uses:** L8.5a, N5.4.
**Lean:** `ScanInv`, `scan_init`. Planned file `Descent/Fitting.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.5c Source advance   (paper: txt:1222-1224)
**Fidelity:** as in paper.
**Statement.** `scan_lt`: `ScanInv i j β` and `i < c` give `ScanInv (i+1) j β`.
**Proof.**
1. `u_i < u_{i+1}` by S5 and [N5.4] `chain_pairwise` on the bank: `slot i` precedes
   `slot (i+1)` and both are bank roles.
2. `Fitted` and `Cmax` are unchanged.

No strict-source call is used.
**Uses:** L8.5a, N5.4.
**Lean:** `scan_lt`. Planned file `Descent/Fitting.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.5d Target heads at the source owner   (paper: txt:1228-1231)
**Fidelity:** as in paper.
**Statement.** `heads_at_owner`: assume
- `SetupClauses`;
- `j < |Q|` and `i ≤ c`;
- `u_i ≤ c_0 := queryBlockMax S j`;
- `Lmax j β < u_i`.

Then `S.HeadsAt P j i β`.
**Proof.**
1. The positive heads: [R18] `graph_block` for query entry `j` puts both head edges of
   `slot j` in `queryGraph`. They hold at `setupPosVal` (S4), so `Edge h ρ o` and `Edge h ρ v`
   hold, where `o, v` are representatives in `P⁻` and `setupPosVal = fitVal β` there.
2. `IsLim u_i` holds from the `lim` atom of `slot i` in `setupBankGraph`. `ρ ≤ Lmax j < u_i`.
3. If `u_i ≤ h`: `edge_restrict` (`ρ < u_i ≤ h`).
4. If `h < u_i ≤ c_0`, the block is nonempty, with `c_0` attained at a role `z` inside query
   entry `j`. Then:
   - [L8.2] `owner_path_elem`, with `D = queryGraph ⊇ localStruct H ⟨sd.col,j⟩` by [L8.2c]
     (all variables in `P⁻ ∪ {T} ∪ Q`), gives `Elem h c_0`;
   - `elem_mid` gives `Elem h u_i`;
   - `edge_extend` gives `Edge u_i ρ ·`.

**Uses:** L8.2, L8.2c, L8.5a, [R18].
**Lean:** `heads_at_owner`. Planned file `Descent/Fitting.lean`.
**Difficulty:** M.
**Testable:** no.

### L8.5e Strict comparison `x_i > y_j`   (paper: txt:1227-1234)
**Fidelity:** as in paper.
**Statement.** `scan_gt`: assume
- `∀ m < n, SStrict m`;
- `S.Valid` and query sizes `< n`;
- `ScanInv i j β`, `ReachesGT … i j` and `i ≤ c`.

Then `∃ β', ScanInv i (j+1) β'`.
**Proof.** Let `h = queryOwnerVal S j` and `c_0 = queryBlockMax S j`. By S4 and [N5.4],
`h > Cmax j ≥ Lmax j`.
1. **`c_0 < u_i` (reuse).** Apply [R26] `fit_of_block` with `L = Lmax j` and
   `βb := frv_j ⊕ (setupPosVal ∘ blockMap ⟨sd.col,j⟩)`, where `frv_j` is the frame values under
   `fitVal β`.
   - `posBlock (queryKey S j) (querySel S j)` holds at `βb`: it is the image of graph atoms by
     [R18], and these lie in `queryGraph` by [L8.2c].
   - New values are `> h > Lmax j`.

   This gives `β'`. Its entry values are `≤ c_0 < u_i`, and `c_0 ≤ Cmax (j+1)`.
2. **`c_0 ≥ u_i`.** [L8.5d] gives `HeadsAt j i β`. Spine `scan_packet` (L7.6), with (17),
   gives a packet `pk` with:
   - `pk.rk = scanRecord i j`, admitted and valid;
   - owner value `u_i`.
3. `size (tgtHeight) = size (Q_j) < n` by [R25]. Apply `SStrict` at that size with
   `L := Lmax j β < u_i`: this gives `TargetAbove`.
4. `scan_packet`'s last clause gives `β'` with entry values in `(Lmax j, u_i)`. So:
   - `Lmax (j+1) β' < u_i`;
   - `Lmax (j+1) β' ≤ Cmax (j+1)`, since `Cmax (j+1) ≥ c_0 ≥ u_i`.

**Uses:** L8.5d, L8.2c, N5.4, [R18], [R25], [R26]; spine `scan_packet`.
**Lean:** `scan_gt`. Planned file `Descent/Fitting.lean`.
**Difficulty:** M (about 250 LOC).
**Testable:** no.

### L8.5f Equal comparison `x_i = y_j`   (paper: txt:1235-1241)
**Fidelity:** as in paper.
**Statement.** `scan_eq`: assume `S.Valid`, `ScanInv i j β`, `rootKeys[i] = queryKeys[j] = x`
and `i < c`. Then `∃ β', ScanInv (i+1) (j+1) β'`.
**Proof.** Let `K := x`, and let `fr := frv_j` be the full target frame of query entry `j`
under `fitVal β`.
1. **Source candidate.** `βS := fr ⊕ (setupBankVal ∘ blockMap ⟨rd.col,i⟩)`.
   - [R18] `graph_block` for root entry `i` maps `freeBlock (rootKey i)` into `graph H`.
   - Its atoms involve the owner or inner variables (bank), and all their variables lie in
     `preRoot ∪ {R} ∪ bank` by [L8.2c]. So they are in `setupBankGraph` and hold by S5.
   - Agreement of `βS` with `setupBankVal ∘ blockMap` on the variables of `freeBlock K`:
     - false labels `(false, q)` of `K` have `q < r` (`relKey` definition);
     - `sd.col.resolve 0 r = rd.col` [R3], so [R10] `reps0_take` makes the frame fields
       `q < r` the same roles;
     - those roles are pre-root, where `setupBankVal = baseVal = fitVal β`;
     - the host is `R ↦ ρ` on one side and `T ↦ ρ` on the other.
2. **Positive candidate.** `βP := fr ⊕ (setupPosVal ∘ blockMap ⟨sd.col,j⟩)`. It holds by [R18],
   [L8.2c] and S4.
3. Floor `L := Lmax j β`. The frame `fr` is complete:
   - the false labels `q` of `K` satisfy `q < t`;
   - `reps0` has length `t` [R10 `reps0_length`].

   Then:
   - `βS`'s new values are `≥ u_i > L`, by (17) and the bank chain;
   - `βP`'s new values are `≥ h > Cmax j ≥ L`;
   - frame values `≤ ρ ≤ L`.
4. Owner paths: [L8.2] `owner_path_elem`, on `setupBankGraph` for `βS` and on `queryGraph` for
   `βP`. The inner roles are images inside the entries by [R12].
5. [L8.3] gives `β*`, with owner `≤ min(u_i, h)` and `blkMax β* ≤ min(M_i, c_0)`. Here
   `blkMax βS = M_i` and `blkMax βP = c_0` by [R12].
6. Heads: restrict the positive heads `Edge h ρ ·` (from [L8.5d] step 1) to `β* owner` by
   `edge_restrict`. Its conditions: `ρ ≤ L < β* owner ≤ h`, and `β* owner` is a limit.
   Then `β*` with heads realizes `posBlock K (querySel S j)`.
7. [R26] `fit_of_block` with `L` gives `β'`. Its entry values are new values of `β*`.
8. (17) at `(i+1, j+1)`:
   - `Lmax (j+1) ≤ max(Lmax j, M_i) < u_{i+1}`, since `M_i < u_{i+1}` by the bank chain.
     [V-fix] Each entry value is `β* w` for a new variable `w` of the block (step 7), and
     `β* w ≤ blkMax β* ≤ M_i` by [N5.6] `posBlock_vars`;
   - `Lmax (j+1) ≤ max(Cmax j, c_0) = Cmax (j+1)`.

   Empty `K` is covered: the maxima are the owners.

**Uses:** L8.2, L8.2c, L8.3, L8.5d, N5.4, N5.6, [R3], [R10], [R12], [R18], [R26]. [V-fix] N5.6 added.
**Lean:** `scan_eq`. Planned file `Descent/Fitting.lean`.
**Difficulty:** L (about 500 LOC; frame bookkeeping).
**Testable:** no.

### L8.5g Along the trace   (paper: txt:1242-1244)
**Fidelity:** as in paper (termination is the finiteness of `trace`).
**Statement.** `scan_trace`: under the hypotheses of `WFit`, every state `s` on the actual trace
has `∃ β, ScanInv s.1 s.2 β`.
**Proof.** Induction on the index in `trace` [R15].
1. Head `(0,0)`: [L8.5b].
2. Each consecutive pair moves by one of the three rules [R15]. Apply [L8.5c], [L8.5f] or
   [L8.5e].
   - The index side conditions `i < c` and `i ≤ c` hold by [R15] (`s.1 ≤ cursor`).
   - In the moving cases the source key exists, so `i < c` when the source cursor advances.
3. `ReachesGT` at `(i,j)` is the trace membership plus the comparison.

**Uses:** L8.5b, L8.5c, L8.5e, L8.5f, [R15].
**Lean:** `scan_trace`. Planned file `Descent/Fitting.lean`.
**Difficulty:** M.
**Testable:** no.

### L8.5 `S_{<n} ⇒ W_{<n}`   (paper: txt:1216-1248)
**Fidelity:** as in paper.
**Statement.** `wFit_of_sStrict I n (h : ∀ m < n, SStrict I.toPrims m) : WFit I.toPrims n`.
**Proof.**
1. `S.Valid` gives `SetupClauses` by [R24].
2. The last trace state is `(c, j)` with `c < |root|` (S1), hence `j = |Q|` [R15].
3. [L8.5g] gives `β` with `ScanInv c |Q| β`.
4. `Fitted |Q| β` is `queryGraph` at `fitVal β`: `fittedRoles |Q| = queryRoles`.
5. `Lmax |Q| β < u_c` bounds every query value.
6. For an empty query, `c = 0` and the claim is `ρ < u_0` ([L8.5b]).

**Uses:** L8.5b, L8.5g, [R15], [R24].
**Lean:** `wFit_of_sStrict`. Planned file `Descent/Fitting.lean`.
**Difficulty:** M.
**Testable:** no.

### L8.6a `DLab` unfolded   (paper: txt:1255-1263)
**Fidelity:** as in paper (spine FIRM `DLab`).
**Statement.**
- `DLabHyps` bundles the twelve hypotheses of `DLab` for one input and one label. `dLab_iff`:
  `DLab P n` is "`DLabHyps` implies the spine conclusion".
- `roleSets_eq`: under `stopData = sd` and `rootData = rd`, `roleSets H = some rs` with:
  - `rs.T = ord sd.col`, `rs.R = ord rd.col`, `rs.N = slot (closingSlot sd)`;
  - `rs.P = rolesBefore H T`;
  - `rs.D = rolesBefore H R ++ [R] ++ rs.K`.
- `nu_mem_vars`: under `DLabHyps`, every pre-stop role `x` has `ν x ∈ Λ.vars`.

**Proof.**
1. `dLab_iff` and `roleSets_eq`: unfold (real bodies).
2. `nu_mem_vars`:
   - `χ x = y ∈ ePrefix` with `y ∈ E.roles` [R16];
   - `lim y ∈ restrictTo (graph E) (ePrefix)`;
   - `pre` puts `base (lim (eν y))` in `Λ`;
   - `eν y = ν x` (`origin`).

   Hence the hypothesis `fixBelow`, which only bounds `v ∈ Λ.vars`, applies to every `ν x`.
   With `bind` and [N5.4], a fixed `ν x` forces `x` before `R`. The moving clause therefore
   concerns every `x` at or after `R`.

**Uses:** N5.4, D6.1c, [R16].
**Lean:** `DLabHyps`, `dLab_iff`, `roleSets_eq`, `nu_mem_vars`. Planned file
`Descent/Ordinary.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.6b (20) Control edge   (paper: txt:1253-1254)
**Fidelity:** as in paper.
**Statement.** `control_edge`: under V, with `stopData = sd`, `rootData = rd` and a
configuration `α`:
- `Edge (α N) (α T) (α R)`;
- `α R < α T < α N`.

**Proof.**
1. [R3]: `closingSlot sd` is an entry with parent `sd.r`, and
   `sd.col.resolve 0 sd.r = rd.col`.
2. `rep` gives `O = ord rd.col`, so `edge N T R ∈ graph H` (edge block).
3. `edge_lt` gives the inequalities.

**Uses:** [R3].
**Lean:** `control_edge`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** S.
**Testable:** yes (syntactic part).

### L8.6c First retained role   (paper: txt:1288-1297)
**Fidelity:** as in paper (the three cases).
**Statement.** `firstK_cases`: for ordinary `H` in L, one of:
- `rs.K = []`;
- `K = v :: _` with `OnRoute sd v`;
- `K = slot ⟨rd.col, c⟩ :: _` with `c < |root|` and root entry `c` closed.

**Proof.**
1. By the reading order (`Tree.rolesCols` real body), the roles after `R` are the slots and
   heights of its entries `0, 1, …`, then the later columns of its forest.
2. `K` drops the entries `< c`. Its first role is:
   - `slot c`, if `c < |root|`;
   - otherwise the next column `⟨π_j, i+1⟩`, or nothing if that is `T` or absent.
3. `slot c` is either the active owner (it contains `T`, so it is `OnRoute`) or closed.
4. The next column is `OnRoute`: `R` is on `T`'s stack [R3], so `i < ` the route index at depth
   `j`. Equality would make `R` contain `T`, and its active entry would be unconsumed.

**Uses:** L8.2d, [R3].
**Lean:** `firstK_cases`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** M.
**Testable:** yes (once U1 bodies exist).

### L8.6d The stage problem   (paper: txt:1268-1281, (21))
**Fidelity:** simplified (S-4, ordinal form):
- certificates and budgets `w_old ∈ J_t` become atoms `x < t`;
- the floor `η` of txt:1259-1262 is not needed, because the transported diagram contains the
  `lt` atoms between fixed and moving coordinates;
- the reference chart at every stage carries the original label values `b ∘ eν`. The latest
  retained copy of `D` has the original values `α|D` (the invariant of L8.6e), so the same
  chart serves every stage.

**Statement.** These are definitions with real bodies.
- Variables `SVar V`: `main x` (roles of `H[m]`), `lab v`, `ref y` (`E`-prefix roles),
  `qry x` (`Q`), and `top` (the head `t`).
- `refVar y` is `main (f_m x)` if `x ∈ D` has `χ x = y`, and `ref y` otherwise. This shares
  `χ(D)` with the latest main copy, txt:1268-1269.
- `qryVar x` is `top` for `T`, `qry x` on `Q`, and `refVar (χ x)` on the rest of `P`.
- `stageDiagram` consists of:
  - `Γ(H[m])` renamed by `main`;
  - `Λ` renamed by `lab`;
  - the `E`-prefix graph through `refVar`;
  - `queryAtoms` through `qryVar`;
  - `eq (lab (ν x)) (main x)` for `x ∈ P`;
  - `lt (main x) top` for `x ∈ H[m].roles`;
  - `lt (lab v) top` for `v ∈ Λ.vars`;
  - `lt (refVar y) top` for `y ∈ ePrefix`.
- `stageFixed`: `main x` for `x` before `R`, and `lab v` with `Fix v`.
- `stageSigma α g b' eb t`: `main ↦ g`, `lab ↦ b'`, `ref ↦ eb`, `qry ↦ α`, `top ↦ t`.

**Proof.** Definitions.
**Uses:** D6.1c.
**Lean:** `SVar`, `refVar`, `qryVar`, `stageDiagram`, `stageFixed`, `stageSigma`. Planned file
`Descent/Ordinary.lean`.
**Difficulty:** S.
**Testable:** yes, for computable `fMap` (definitions only).

### L8.6e Stage invariant and stage zero   (paper: txt:1264-1267, 1312)
**Fidelity:** simplified (S-4). The invariant reads `ι_m = id` (spine `iota`).
**Statement.** `StageInv P H rs α Λ ν b Fix m G g b'` is the conjunction of:
1. `expand H m = some G` and `IsConfig P G g`;
2. `g < α T` on `G.roles`;
3. `g (f_m R) = α R`, and `g (f_m x) = α x` on `K`;
4. `g = α` before `R`;
5. `b' = b` on `Fix`;
6. `b' (ν x) = g x` on `P`;
7. `Λ.Holds P b'`, with `b' < α T` on `Λ.vars`;
8. for `m > 0`: `g x < α R` for `x ∈ P` at or after `R` with `¬ Fix (ν x)`.

Claims:
- `stage_zero_inv`: `DLabHyps` and `roleSets = rs` give `∃ G, StageInv … 0 G α b`.
- `persist_prefix`: `rs.P <+: (H[m]).roles` for every `m`.

**Proof.**
1. `stage_zero_inv`:
   - `H[0]` exists [U1 `expand_isSome`];
   - [R22] `stage_zero`: `roles = P`, `graph ⊆ graph H`, and `f_0 = id` on `D`;
   - `IsConfig` restricts [N5.4 `config_of_sub`];
   - `g < α T` on `P` [N5.4];
   - clauses 5–7 come from `DLabHyps`; clause 8 is vacuous.
2. `persist_prefix`: induction on `m` with [R22] `stage_zero` and `stage_succ`, whose first
   clause appends roles.

**Uses:** N5.4, L8.6a, [R22]; U1 `expand_isSome`.
**Lean:** `StageInv`, `stage_zero_inv`, `persist_prefix`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** M.
**Testable:** yes. `persist_prefix`, as the role-prefix property of `E[m]` in `E[m+1]` for
`m ≤ 3`, was checked on 2199 standard expressions (`scratch/blueprint/U5/stagetest.lean`).

### L8.6f Control transport of the stage   (paper: txt:1281-1287)
**Fidelity:** simplified (S-4). Transport and the capture into `J_W` are one interface field.
**Statement.** `stage_transport`: assume `StageInv … m G g b'`. Then `stageDiagram` is
`RealizableBelow (α T)` with fixed `stageFixed ∨ top` at `stageSigma α g b' (b ∘ eν) (α R)`.
**Proof.**
1. **The current values realize the diagram below `C = α N`.** Take `σ := stageSigma … (α T)`.
   - `Γ(G)` holds at `g` (clause 1); `Λ` holds at `b'` (clause 7).
   - The `E`-prefix graph: `σ ∘ refVar = b ∘ eν` on `ePrefix`. For shared `y = χ x` with
     `x ∈ D`:
     - `g (f_m x) = α x` by clauses 3–4, using [R22] `f_m = id` below `R`;
     - `b (eν (χ x)) = b (ν x) = α x` by `origin` and `bind`.

     The prefix graph holds at `b ∘ eν` because `pre` puts it in `Λ`, which holds at `b`.
   - Query atoms: `σ ∘ qryVar = α` on `P ∪ {T} ∪ Q`. [V-fix] Spelled out:
     - `qryVar T = top ↦ α T`;
     - `qryVar x = qry x ↦ α x` on `Q`;
     - on the rest of `P`, `qryVar x = refVar (χ x)` ([R16]: `χ x` is defined). By the
       previous bullet, `σ (refVar (χ x)) = b (eν (χ x))`, and this is `b (ν x) = α x` by
       `origin` and `bind`.

     They are atoms of `Γ(H)`, which holds at `α` (`config`).
   - Bindings: clause 6.
   - Budget atoms: clause 2, clause 7, and `b (eν y) < α T` (`below`, with `eν y ∈ Λ.vars` by
     the `lim` atom).
   - All values are `< α N`. Query values satisfy `α x < α N`, since `x` is before `N`
     [N5.4].
2. **Apply `I.transport`** with:
   - `Edge (α N) (α T) (α R)` [L8.6b];
   - `t = top`, not fixed;
   - fixed values `< α R`: pre-root `main x ↦ α x < α R` [N5.4]; `lab v ↦ b v < α R` by
     `fixBelow` and [L8.6a] `nu_mem_vars` (`lab` variables of the diagram are in `Λ.vars` or
     of the form `ν x`).
3. Rewrite `Function.update σ top _` as `stageSigma … _` (funext, classical decidability).

**Uses:** L8.6a, L8.6b, L8.6d, L8.6e, N5.4, [R22].
**Lean:** `stage_transport`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** L (about 600 LOC: eight atom blocks).
**Testable:** no.

### L8.6g Scan setup of the closed-owner case   (paper: txt:1295-1303)
**Fidelity:** repaired (G-003: the setup is an explicit term, and validity is a proof
obligation).
**Statement.** `stageSetup E cap sd rd rs m α a` is a scan setup with:
- `ePre = role 0` with values `a ∘ refVar`;
- `qNm = role 1` with values `a ∘ qry`;
- `bankNm = role 2` with values `α`;
- `stopNm = aux 0` with value `a top`;
- `aux = []`.

`stageSetup_clauses`: assume
- `DLabHyps`, `IsStd E`, and root entry `c` exists and is closed;
- `a` realizes `stageDiagram`, with `a top = α R` and all values `< α T`;
- [V-fix, added hypothesis `hfix`] `a (main x) = α x` for every `x` before `R`.

Then `SetupClauses` holds.

[V-fix] Without `hfix` the statement is not provable. The bank is placed at the original values
`α`, and its edges read pre-root representatives through `baseVal`, that is through
`a (main x)`. A realization of `stageDiagram` alone does not determine these values. In the
use (L8.6h) they are fixed at `α x`.
**Proof.**
1. S1: `DLabHyps` and the hypotheses.
2. S2: the `E`-prefix block of the diagram, with values `< a top` (budget atoms).
3. S3: vacuous.
4. S4: the query block, since `setupPosVal` is `a ∘ qryVar` (definitions).
5. S5:
   - pre-root roles: `refVar (χ x) = main x`. `find?` returns `x` itself, because `χ` is
     injective [R16], and `f_m = id` below `R` [R22]. Then `a (main x) = α x` by `hfix`;
   - `R ↦ α R`;
   - bank `↦ α`.

   These are atoms of `Γ(H)` at `α`.
6. S6: distinct tags.

**Uses:** L8.5a, L8.6d, [R16], [R22].
**Lean:** `stageSetup`, `stageSetup_clauses`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** L (about 400 LOC).
**Testable:** no.

### L8.6h Fit before `K`   (paper: txt:1288-1304)
**Fidelity:** as in paper (three cases), in ordinal form.
**Statement.** `stage_fit`: assume
- `WFit n` and `DLabHyps`;
- a realization of the transported problem below `α T`, with fixed values `σ` and
  `σ top = α R`;
- [V-fix, added hypothesis `hσ`] on fixed variables, `σ` equals the stage-zero values
  `stageSigma α α b (b ∘ eν) (α R)`: `σ (main x) = α x` for `x` before `R`, and
  `σ (lab v) = b v` when `Fix v`.

Then there is a realization `a` with:
- the same fixed values;
- all values `< α T`;
- `a (qry x) < α v` for `x ∈ Q`, where `v` is the first role of `K`; if `K = []`, the bound is
  `α T`.

[V-fix] `hσ` is needed in case 3: it supplies `hfix` of L8.6g. In the one use, L8.6j,
`σ = stageSigma α g b' (b ∘ eν) (α R)`, and `hσ` is StageInv clauses 4 and 5.

**Proof.** Split by [L8.6c]. Let `a₀` be the given realization.
1. `K = []`: `a₀`.
2. `OnRoute v`:
   - [L8.2d] gives `Elem (α v) (α T)`;
   - `I.capture`, with fixed values `< α v`. By `hσ`, pre-root values are `α x < α R < α v`
     ([N5.4]; `v ∈ K` is after `R`). Fixed label values are `b v' < α R`, by `fixBelow`, since
     every `lab` variable of the diagram is in `Λ.vars` ([L8.6a] `nu_mem_vars`). Finally
     `top = α R`.
3. Closed root owner:
   - if `Q = []`, step 1 applies;
   - otherwise `DLabHyps.query` gives `IsStd E` and sizes `< n`. Fixed values are preserved by
     `a₀`, so `a₀ (main x) = σ (main x) = α x` before `R` by `hσ`. [L8.6g] (with this `hfix`)
     and [R24] give `(stageSetup …).Valid`. `WFit` gives `β < ownerVal c = α v`, with
     `queryGraph` at `fitVal β`.
   - Set `a := a₀` updated at `qry x ↦ β x`. Only the query block reads `qry` variables, and it
     holds by `queryGraph = queryAtoms`.

**Uses:** L8.2d, L8.6a, L8.6c, L8.6g, N5.4, [R24].
**Lean:** `stage_fit`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** L.
**Testable:** no.

### L8.6i Restore `K`   (paper: txt:1306-1311)
**Fidelity:** as in paper. Labels read `ι` (R-3).
**Statement.** `stage_restore`: from the fitted realization `a` of L8.6h and
`expand H (m+1) = some G'`, there are `g'`, `b'` with `StageInv … (m+1) G' g' b'`.
**Proof.** [R22] `stage_succ` gives `G'.roles = G.roles ++ (h :: q(Q) ++ f(K))`. Set:
- `g'` on `G.roles` to `a ∘ main`;
- `g' h = α R`;
- `g'` on `q x` to `a (qry x)`;
- `g'` on `f x` to `α x`.

This is well defined by [R11] `roles_nodup`. Set `b' := a ∘ lab`.
1. `lim` atoms: from `Γ(G)`, from `α R`, from the query block, and from `α`.
2. `lt` chain on `G'.roles` (graph real body):
   - inside `G`: from `Γ(G)`;
   - `last G < h`: budget atom `main · < top`;
   - `h <` first query value, and query chain: from `queryAtoms` (`T` precedes `Q`
     contiguously);
   - last query value `< α v`: L8.6h;
   - `K` chain: [N5.4], since `α` increases along `H`.
3. Structural atoms by [R22]:
   - old atoms hold by `Γ(G)`;
   - `q`-images: `g' ∘ q = a ∘ qryVar` on the variables of structural query atoms, which lie
     in `D ∪ {T} ∪ Q` by [R23], with `q = f_m` on `D`. For `x ∈ D`,
     `qryVar x = refVar (χ x) = main (f_m x)`, since `find?` returns `x` by injectivity of
     `χ` [R16] [V-fix: citation added];
   - `f`-images: `g' ∘ f = α` on `D`, with `f = id` below `R`, where the values are fixed at
     `α`.
4. Invariant clauses:
   - 2: values `< α T`;
   - 3: by construction;
   - 4 and 5: fixed;
   - 6: `eq` atoms;
   - 7: the `lab` block;
   - 8: budget atom with `top = α R`.

**Uses:** L8.6d, L8.6e, L8.6h, N5.4, [R11], [R16], [R22], [R23]. [V-fix] R16 added.
**Lean:** `stage_restore`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** L (about 600 LOC).
**Testable:** no.

### L8.6j One stage   (paper: txt:1264-1311)
**Fidelity:** as in paper.
**Statement.** `stage_step`: `StageInv m` and `expand H (m+1) = some G'` give
`∃ g' b'', StageInv (m+1) G'`.
**Proof.** Apply [L8.6f], then [L8.6h], then [L8.6i]. The fixed values match because
`stageSigma α g b' … = stageSigma α α b …` on fixed variables, by clauses 4 and 5. This
equation is the hypothesis `hσ` of L8.6h, and composed with L8.6h's fixed-value clause it is
the hypothesis `hfixed` of L8.6i. [V-fix] Checked with a real proof term over the sorry'd
leaves: `vglue_stage_step` in `scratch/blueprint/U5-verify/vglue_tail.lean`.
**Uses:** L8.6f, L8.6h, L8.6i.
**Lean:** `stage_step`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.6 `W_{<n} ⇒ D_{<n}`   (paper: txt:1250-1323)
**Fidelity:** simplified (S-4, S-6). The stage machinery is written once for an arbitrary
label.

S-6 formalization order:
1. First prove L8.6d–j for the label-free instance (`V = Role`, `Λ = Γ(H)|P`, `ν = eν = id`,
   `Fix = ∅`). It yields `DCore` through D8.1a.
2. Then add the `lab` block, the bindings and `Fix`.

**Statement.** `dLab_of_wFit I n (hW : WFit I.toPrims n) : DLab I.toPrims n`.
**Proof.** Use [L8.6a] `dLab_iff`. Fix `DLabHyps` and `k`, `H'`.
1. [L8.6a] `roleSets_eq` gives `rs`.
2. [L8.6e] gives `StageInv 0`.
3. Induction on `m < k` with [L8.6j]. `H[m+1]` exists by U1 `expand_isSome`.
4. At `m = k` (`G = H'`), the invariant clauses are the conclusion of `DLab`:
   - `iota = id` (spine real body);
   - clause 8 is the moving clause;
   - clause 4 is the pre-root clause.

The marker identity (22) is the label clause with `ν` the chart of the marked host, owner and
frame.
**Uses:** L8.6a, L8.6e, L8.6j; U1 `expand_isSome`.
**Lean:** `dLab_of_wFit`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** M.
**Testable:** no.

### D8.1a Label-free core   (paper: txt:1185-1189)
**Fidelity:** new (spine D8.1a; S-6).
**Statement.** `dCore_of_dLab P n : DLab P n → DCore P n`.
**Proof.** Verified in scratch as `glue_dCore_of_dLab`; two side conditions are left sorry.
1. From `AllowedInput n H`, `rootData H = some rd` by U1 `rootData_of_ordinary`.
2. Build `DLabHyps` with `E = H`, `cap = none`, `V = Role`, `Λ = ofBase (Γ(H)|_{rolesBefore H T})`,
   `ν = eν = id`, `b = α`, `Fix = ⊥`. Its fields:
   - `pre`: `T' = T` and `map id = id`;
   - `holds`: `Λ ⊆ Γ(H)`, with N5.4 `holds_ofBase`;
   - `below`: the variables of `Λ` are before `T` [N5.4].
3. Apply `DLab` and keep its first two conclusions.

**Uses:** L8.6a, N5.4; U1 `rootData_of_ordinary`.
**Lean:** `dCore_of_dLab`. Planned file `Descent/Ordinary.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.7a Iterated capture of a block   (paper: txt:1329-1338)
**Fidelity:** as in paper.
**Statement.** `special_copies`: assume
- `Elem s Wv` and `L < s`;
- frame values `< s`;
- a witness `β₀` with frame agreement, `D` holding, and new values in `[s, Wv)`.

Then for every `N` there are `βs : ℕ → W → Ordinal` such that:
- each `βs i` (`i < N`) agrees with the frame, satisfies `D`, and has new values in `(L, s)`;
- copy `i` is entirely below copy `j` on new variables for `i < j < N`.

**Proof.** Induction on `N`, carrying the floor `L_i`, with `L_0 = L` and
`L_{i+1} := max(L_i, new values of βs i) < s`.
1. `β₀` witnesses `BlockAbove D fr L_i Wv`, since its new values are `≥ s > L_i`.
2. [N5.3] `blockAbove_capture` with `Elem s Wv`, floor `L_i < s` and frame `< s` gives copy
   `i`.
3. `L_{i+1} < s` because finite maxima stay below `s`.

**Uses:** N5.3.
**Lean:** `special_copies`. Planned file `Descent/Special.lean`.
**Difficulty:** M.
**Testable:** no.

### L8.7 Special descent   (paper: txt:1325-1346)
**Fidelity:** as in paper. In ordinal form the limited label clause is automatic: the conclusion
keeps `P(H,e)` and introduces only fresh roles in `(L, s)`.
**Statement.** `specialDesc I : SpecialDesc I.toPrims` (spine).
**Proof.** Fix `H`, `H'`, `k`, `α`, `sd`, `e`, `L`.
1. [R5]: `e` is an entry, `T` is inside `e`, and the last column of `e`'s height is
   `[(a, ∅)]`.
2. `s := α (slot e)` and `Wv := α T`. [L8.2] `owner_path_elem_config` gives `Elem s Wv`.
3. Original block: `β₀ := α ∘ blockMap e`. It realizes
   `posBlock (specialKey H e) (entrySel H e)`:
   - [R18] puts `posBlock (entryKey H e)` in `Γ(H)`;
   - [N5.6] `posBlock_prefix` applies, since `specialKey`'s columns are `entryKey`'s columns
     with the last one dropped;
   - frame agreement is [R18], second clause;
   - new values: owner `s`, inner values `> s` and `< Wv`, since `C`'s roles are before `T`
     [N5.4], [R12];
   - frame values `< s` [R19], and `≤ L` by hypothesis.
4. [R27] `special_graph` gives `N`, `cm`. [L8.7a] gives copies `βs`.
5. Define `γ`:
   - `γ = α` on `prefixRoles H e`;
   - `γ (cm i w) = βs i w` for new `w`. This is unique by [R11].
6. `IsConfig H' γ`:
   - prefix atoms hold by `α`;
   - copy atoms are `a'.map (cm i)` with `γ ∘ cm i = βs i` on the variables of `posBlock`
     (frame roles are in the prefix);
   - `lt` chain: `α(last prefix) ≤ L < βs 0 owner`; inside a copy, the `freeBlock` chain;
     between copies, the windows increase;
   - `lim` from the blocks.
7. Conclusion: `γ = α` on the prefix, and the other roles lie in `(L, s)`.

**Uses:** L8.2, L8.7a, N5.4, N5.6, [R5], [R11], [R12], [R18], [R19], [R27].
**Lean:** `specialDesc` (spine). Planned file `Descent/Special.lean`.
**Difficulty:** L (about 500 LOC).
**Testable:** no.

### L8.8a (23) from a failure   (paper: txt:1353-1356)
**Fidelity:** as in paper.
**Statement.** `failure_floor`: assume `pk.Valid`, `L < u` and `¬ TargetAbove L`. Then there is
`Ls` with `L ≤ Ls`, `Ls < u`, low values `< Ls`, and `¬ BlockAbove (posBlock tgtKey tgtSel) frv Ls u`.
**Proof.** Spine `factorization` (L7.3), contrapositive of its last clause.
**Uses:** spine `factorization`.
**Lean:** `failure_floor`. Planned file `Descent/Strict.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.8b Case 1: the whole target ends first   (paper: txt:1357-1363)
**Fidelity:** as in paper.
**Statement.** `case_wholeEnds`: admitted, valid, (23) at `Ls`, and `firstDiff = wholeEnds` give
`False`.
**Proof.**
1. [R28]: the columns of `tgtKey` are the first `|tgtKey.cols|` columns of `srcKey`, a proper
   prefix.
2. [N5.6] `posBlock_prefix`: `posBlock tgtKey sel ⊆ posBlock srcKey sel` in atoms, and the roles
   of `tgtKey` are a prefix of those of `srcKey`.
3. Let `z := roleUnder a.heightPath (ord ⟨[], |tgtKey.cols|⟩)`, the first omitted source vertex.
   It is in `F` by [R12], with [R14] `relKey_roles`.
4. Define `β := frv` on frame variables, `β owner = u`, and `β (inner r) = α_F (blockMap a (inner r))`.
5. `freeBlock tgtKey` holds at `β`:
   - its atoms are `freeBlock srcKey` atoms, which map into `Γ(F)` by [R18] and hold at `α_F`
     [N5.8];
   - `β` agrees with `α_F ∘ blockMap a` on their variables:
     - owner and inner by definition;
     - host: Valid clause 2;
     - `ord q`, `cur q` for false labels `q < r`: Valid clause 3 (`take r`), and [R18] frame
       clause.
6. Heads at `u`: Valid clause 5.
7. Bounds:
   - new values `> Ls`: `u > Ls`, and inner values `> u` [N5.4];
   - all values `< α_F z`: inner roles of the prefix are before `z` by [R12] and step 2;
     `u < α_F z`; frame values are low, hence `< u`.
8. [L8.2] `owner_path_elem_config` gives `Elem u (α_F z)`. [N5.3] `blockAbove_capture` gives
   `BlockAbove … Ls u`, contradicting (23).

**Uses:** L8.2, N5.3, N5.4, N5.6, N5.8, [R12], [R14], [R18], [R28].
**Lean:** `case_wholeEnds`. Planned file `Descent/Strict.lean`.
**Difficulty:** M (about 300 LOC).
**Testable:** no.

### L8.8c Readmission by a second capture   (paper: txt:1375-1381, 1459-1470)
**Fidelity:** repaired (G-003). The readmitted packet is constructed, and all six Valid clauses
are proved.
**Statement.** `readmit_capture`. Data and hypotheses:
- `pk` is valid, with (23) at `Ls`;
- an admitted `rk'` with the same `E` and `b`;
- a chart `srcChart'` with:
  - injectivity on `rk'.F.roles`;
  - `srcChart' (ord a'.col) = pk.host` and `srcChart' (slot a') = pk.owner`;
  - frame agreement below the printed host;
  - prefix roles map to low names;
  - every other role (neither prefix nor the slot `a'`) maps to a name that is neither low nor
    the owner;
- a configuration `γ` of `rk'.F` with:
  - `γ = asg ∘ srcChart'` on the prefix;
  - `γ (slot a') = u`;
  - `γ < W`, where `Elem u W`.

Conclusion: there is a packet `pk'` such that:
- `pk'.rk = rk'` and `pk'.Valid`;
- the host value is `ρ`;
- the owner value `w` satisfies `Ls < w < u`;
- `¬ pk'.TargetAbove Ls`.

**Proof.**
1. **Diagram** over `Option Name`, with `none` the floor:
   - `Γ(rk'.F)` through `some ∘ srcChart'`;
   - target heads `edge owner host o` and `edge owner host v` at `tgtFrame.reps[tgtSel]`;
   - `lt none (some owner)`.

   Fixed: the floor and every name other than the owner and the fresh internal names, at
   `asg`.
2. **Witness below `W`:** `γ` on the source names, `u` on the owner, `asg` elsewhere.
   - Graph atoms by `hγ`.
   - Heads by Valid clause 5.
   - `Ls < u`.
   - Bounds: the fixed names are low (`< u`), and `γ < W`.
3. **`I.capture` along `Elem u W`** (fixed values `< u`). The witness `a` has every value `< u`
   and the owner value `w > Ls`.
4. **`pk'`:** `rk'`, `tgtChart`, `srcChart'`, `aux`, and `asg' := a ∘ some`. Then `asg' = asg`
   on every fixed name, hence on all low names. Validity:
   - (1) injectivity: `pk`, and the hypothesis;
   - (2) and (3): hypotheses;
   - (4) the target prefix and `aux` are unchanged (N5.8 and [R20] `holds_congr`); `Γ(F')` is
     captured;
   - (5) captured heads;
   - (6) `lowNames'` consists of `pk`'s low names (target prefix, prefix names by hypothesis,
     `aux`), with values `< Ls < w`.
5. **Failure:** `TargetAbove Ls` at `pk'` gives `BlockAbove … Ls w` [N5.3(d)]. With `w ≤ u`,
   [N5.3(c)] gives `BlockAbove … Ls u`, contradicting (23). The target frame names and values
   are the same.

**Uses:** N5.3, N5.8, [R20].
**Lean:** `readmit_capture`. Planned file `Descent/Strict.lean`.
**Difficulty:** L (about 500 LOC).
**Testable:** no.

### L8.8d Case 2: a proper child forest ends first   (paper: txt:1364-1381)
**Fidelity:** repaired (G-003). The readmission goes through L8.8c, and the U3 data are
[R29].
**Statement.** `case_childEnds`: assume `DLab n`, `SpecialDesc`, `pk` admitted and valid with
size `n`, (23) at `Ls`, and `firstDiff = childEnds π`. Then
`∃ pk', Fails n pk' Ls ∧ failPair pk' < failPair pk`.
**Proof.**
1. [R29] gives `ChildData`:
   - `F₁` in L with roles a prefix of `F`'s roles, and `Γ(F₁) ⊆ Γ(F)`;
   - stopping column `z := ord sd₁.col` inside `a`;
   - `F₂ = F₁[k]`, with `P(F₂,a) = P(F,a)` and an admitted record with `F₂`;
   - either ordinary with `Q = []` and the root inside `a`, or special with owner entry `e`
     strictly inside `a`.
2. `α₁ := α_F` is a configuration of `F₁` [N5.4 `config_of_sub`, N5.8]. `W := α_F z`, and
   `Elem u W` by [L8.2].
3. **Ordinary branch.** `DLab` with `E = F₁`, `cap = none`, the trivial label as in D8.1a, and
   the empty query, so no `IsStd`. This gives `γ` with:
   - `γ < W`;
   - `γ = α₁` before the root, which includes `P(F,a)` and `slot a` by [R12], since the root
     is inside `a`.
4. **Special branch.** `SpecialDesc` with `L₁ := max α₁` over `prefixRoles F₁ e`, which is
   `< α₁ (slot e)` [N5.4]. Then:
   - `γ = α₁` on `P(F₁,e) ⊇ P(F,a) ∪ {slot a}`;
   - other values are `< α₁ (slot e) < W`, since `slot e` is before `z` ([R5], `z` inside
     `e`).
5. **`srcChart'`:** `srcChart` on `P(F,a)`, `owner` on `slot a`, and
   `Name.role N₀ x` otherwise, with `N₀ := tagBound (lowNames ++ [owner])` [N5.5].
   - The roles of `F₂` are the prefix, the slot and roles inside `a`: [R13] together with
     Admitted (`truncAfter`).
   - Injectivity: `srcChart` on `F`'s roles, plus the fresh tag.
   - Frame: `frameOf a` lies in the prefix [R19].
6. [L8.8c] gives `pk'` with `Fails n pk' Ls`: the size is unchanged since `E` and `b` are. Its
   pair is `(ρ, w)` with `w < u`, which is lexicographically smaller.

**Uses:** L8.2, L8.8c, N5.4, N5.5, N5.8, [R5], [R12], [R13], [R19], [R29]; `DLab`,
`SpecialDesc`.
**Lean:** `case_childEnds`. Planned file `Descent/Strict.lean`.
**Difficulty:** L (about 500 LOC).
**Testable:** no.

### L8.8e Root position   (paper: txt:1454-1455)
**Fidelity:** as in paper ("every visible external parent has ordinary value at most ρ").
**Statement.** `root_position`: under V, if `T` is inside an entry `e` of `H`, then one of:
- `R` is inside `e`;
- `R = e.col`;
- `R` is before `ord e.col`.

**Proof.**
1. `R = resolve` of `sd.r` on `T`'s stack [R3].
2. The stack of a column inside `e` consists of internal columns, `e.col`, and `e.col`'s own
   stack. By `resolve_spec` [R11], `e.col`'s own stack consists of columns before `e.col` in
   reading order.

**Uses:** [R3], [R11].
**Lean:** `root_position`. Planned file `Descent/Strict.lean`.
**Difficulty:** M.
**Testable:** yes (syntactic, once U1 bodies exist).

### L8.8f Case 3: a parent differs or an existing column ends   (paper: txt:1382-1470)
**Fidelity:** repaired (G-003). The labelled premise (24)–(25) is an explicit diagram `Λ`. Both
readmissions are explicit: `p ≤ ρ` directly, and `p > ρ` through L8.8c. The U3/U2 data are
[R30].
**Statement.** `case_cap`: assume `DLab n`, `pk` admitted and valid with size `n`, (23) at `Ls`,
and `firstDiff = capAt c k p`. Then `∃ pk' L', Fails n pk' L' ∧ failPair pk' < failPair pk`.

**Proof.** [R30] gives `CapData`: the repaired cap `H := w.H` and `sd`, `rd`. Write
`a' := moveAddr w.moves b`, `α := asg' ∘ nmH`, `W := α T` and `p := α R`.

Facts used below:
- `α` is a configuration of `H`;
- `asg' = asg` on old names;
- `nm = tgtChart` on `P(E,b)`, and `nm (slot b) = owner`;
- the `E`-prefix graph holds at `asg' ∘ nm`, below `W`;
- `compat`;
- the marked-entry facts;
- `u < W`;
- the readmission clause.

Two derived equalities:
- `nmH (slot a') = owner`, by `compat`, `marked_slot` and `nm_owner`;
- `nmH (ord a'.col) = host`, by `compat`, `marked_host`, `nm_tgt` and Valid clause 2.

1. **Step.** By [R7] and [R17], `cofinal_bound` (spine T3.8, with `IsStd E` and `InL H`) gives
   `k ≥ 1` and `H' = H[k]` with `E < H'`. The readmission clause makes
   `rk' := (E, b, H'.truncAfter a', a', repair w.moves)` admitted.
2. **Label.** `V := Option Name`, `ν x := some (nmH x)`, `eν y := some (nm y)`,
   `b (some y) := asg' y`, `b none := Ls`. `Λ` consists of:
   - (i) the `E`-prefix graph through `eν`;
   - (ii) `noB tgtKey tgtSel (tgtFrame.map some) (some owner) none`;
   - (iii) `lt none (some owner)`;
   - (iv) `lt (some x) none` for `x ∈ lowNames`;
   - (v) `aux.map some`.

   This is (24)–(25):
   - (i) at `b`: `ePrefix_holds`;
   - (ii): (23), with `asg' = asg` on the frame names and the owner, and N5.4 `toFr_map`;
   - (iii) and (iv): (23);
   - (v): N5.8 and [R20].

   `Λ` values are `< W`: `ePrefix_below`, and low values `< u < W`.
3. **`DLabHyps`** with `Fix = ⊥`:
   - `query`: `IsStd E`, and sizes `≤ n − 2` by `qsize`;
   - `bind`: `b ∘ ν = α` by definition;
   - `origin`: `compat`;
   - `pre`: (i).

   `DLab` gives `γ` and `b'` with:
   - `γ` a configuration of `H'`, with `γ < W`;
   - `Λ` holding at `b'`;
   - `b' (ν x) = γ x` on `P_H`;
   - pre-root `γ = α`;
   - the moving clause (since `k ≥ 1`).
4. **Split** by [L8.8e] on `R` relative to `a'` (`T` is inside `a'` by `stop_inside`). If `R` is
   `a'.col` or before it, then `p ≤ ρ` [N5.4]. If `R` is inside `a'`, then `p > u > ρ`.
5. **Case `p ≤ ρ`.** Put `ρ' := γ (ord a'.col)`, `u' := γ (slot a')` and `L' := b' none`.
   - `ord a'.col` is not before `R`, and `¬ Fix`, so the moving clause gives `ρ' < p ≤ ρ`.
   - New packet `pk'`:
     - `rk'`, `tgtChart`;
     - `srcChart' := nmH` on `P_H` (`rolesBefore H T`) and `Name.role N₀ x` elsewhere, with
       `N₀` fresh for the names of `Λ` and `nmH(H.roles)` [N5.5];
     - `aux`;
     - `asg''` equal to `γ` on fresh names and to `b' ∘ some` elsewhere. This is consistent
       because `b' ∘ ν = γ` on `P_H`.
   - Valid:
     - (1) `nmH_inj`, and freshness;
     - (2) `srcChart' (ord a'.col) = host`;
     - (3) `marked_frame`, with the frame roles before `slot a'`, inside `P_H` [R19];
     - (4) target prefix: (i) restricted to `P(E,b)` (`pre_sub`); `Γ(F')` at
       `asg'' ∘ srcChart' = γ` ([R13], [R21], [L8.6e] `persist_prefix`); `aux`: (v);
     - (5) target heads: they are the edges of `U_b` in (i), at `u'` and `ρ'`. [V-fix] Spelled
       out: `slot b = χ (slot a') ∈ ePrefix` by `marked_slot` and [R16], since `slot a'` is
       before `T`. The frame roles of `b` are in `prefixRoles E b ⊆ ePrefix` (`pre_sub`). So
       both edges of `U_b` in `graph E` lie in (i). Through `eν = some ∘ nm` they read
       `owner` (`nm_owner`), `host` (`nm_tgt`, Valid clause 2) and the pair
       `tgtFrame.reps[tgtSel]`, which is `rep 0 b.col tgtSel` mapped by `tgtChart`
       ([R10] `reps0_length`, `nm_tgt`). At `b'` these values are
       `b' (some owner) = b' (ν (slot a')) = γ (slot a') = u'` and, in the same way, `ρ'`;
     - (6) low names: `P(F',a')` names are in `P(E,b)`'s names (`marked_prefix`, `nm_tgt`), and
       (iv) and (iii) give `< L' < u'`.
   - Failure: (ii) at `b'` says `¬ BlockAbove … L' u'`, so `¬ TargetAbove L'` [N5.3(d)], with
     `L' < u'` by (iii).
   - `failPair pk' = (ρ', u') < (ρ, u)`, since `ρ' < ρ`.
6. **Case `p > ρ`.** `R` is inside `a'`, so `P(H,a') ∪ {slot a'}` is before `R` [R12], and
   `γ = α` there.
   - Take `srcChart'` to be `nmH` on `P(H,a')`, `owner` on `slot a'`, and fresh elsewhere.
   - [L8.8c] applies with:
     - `γ` restricted to `F' = H'.truncAfter a'` ([R21], [N5.4]);
     - `W = α T`, and `Elem u W` by [L8.2] `owner_path_elem_config` on `H`, with `T` inside
       `a'`;
     - `γ = asg ∘ srcChart'` on the prefix (`asg' = asg` on low names);
     - `γ (slot a') = u`.
   - The new pair is `(ρ, w)` with `w < u`.

**Uses:** L8.2, L8.6e, L8.8c, L8.8e, N5.3, N5.4, N5.5, N5.8, [R7], [R12], [R13], [R17], [R19],
[R10], [R16], [R20], [R21], [R30]; spine `cofinal_bound`, `DLab`. [V-fix] R10 and R16 added.
**Lean:** `case_cap`. Planned file `Descent/Strict.lean`.
**Difficulty:** L (about 1500 LOC; the largest node of the unit).
**Testable:** no.

### L8.8g Least failure   (paper: txt:1349-1352, 1472-1474)
**Fidelity:** simplified. `WellFoundedLT (Ordinal ×ₗ Ordinal)` (Mathlib `Data/Prod/Lex`)
replaces bounded Separation.
**Statement.** `least_failure`: assume every failure has a failure with a lexicographically
smaller `failPair`. Then `SStrict P n`.
**Proof.** Verified in scratch as `glue_least_failure`.
1. `WellFoundedLT.induction` on `x : Ordinal ×ₗ Ordinal` proves:
   `∀ pk L, Fails pk L → failPair pk = x → False`.
2. Unfold `SStrict` and use `by_contra`.

**Uses:** D8.1b.
**Lean:** `least_failure`. Planned file `Descent/Strict.lean`.
**Difficulty:** S.
**Testable:** no.

### L8.8 `D_{<n} ⇒ S_n`   (paper: txt:1348-1474)
**Fidelity:** repaired (G-003).
**Statement.** `sStrict_of_dLab I n (hD : DLab I.toPrims n) : SStrict I.toPrims n`.
**Proof.** Verified in scratch as `glue_sStrict_of_dLab`.
1. Apply [L8.8g]. For a failure, [L8.8a] gives `Ls`.
2. Case on `firstDiff`:
   - `wholeEnds`: [L8.8b];
   - `childEnds`: [L8.8d] with `specialDesc I` [L8.7];
   - `capAt`: [L8.8f].

**Uses:** L8.7, L8.8a, L8.8b, L8.8d, L8.8f, L8.8g.
**Lean:** `sStrict_of_dLab`. Planned file `Descent/Strict.lean`.
**Difficulty:** S.
**Testable:** no.

### T9.1b Deletion   (paper: txt:1482-1483)
**Fidelity:** as in paper.
**Statement.** `deletion_config`: if `stepKind A = deletion`, `A' = A[k]` and `α` is a
configuration of `A`, then `α` is a configuration of `A'` and `cfgMax A' α < cfgMax A α`.
**Proof.**
1. U1 `expand_deletion` gives `A' = .node A.cols.dropLast`. [R6] says the last column is
   empty.
2. `A.roles = A'.roles ++ [ord ⟨[], |A.cols|−1⟩]` (`rolesCols` real body).
3. `graph A' ⊆ graph A` (graph real body: the same addresses and entries). [N5.4]
   `config_of_sub` applies.
4. The last role has the largest value [N5.4], and that value is positive (a limit).
   [N5.4] `cfgMax_lt` concludes.

**Uses:** N5.4, [R6]; U1 `expand_deletion`.
**Lean:** `deletion_config`. Planned file `Descent/Final.lean`.
**Difficulty:** M.
**Testable:** yes (syntactic part).

### T9.1c Special case of (27)   (paper: txt:1482-1489)
**Fidelity:** as in paper.
**Statement.** `descent_special`: `InL A`, `stepKind A = special`, a configuration `α` and
`A' = A[k]` give `γ` with `cfgMax A' γ < cfgMax A α`.
**Proof.**
1. U1 `stopData_of_stepKind` and `ownerEntry_of_special` give `sd` and `e`.
2. Apply [L8.7] with `L := max α` over `prefixRoles A e`. Then `L < α (slot e)` [N5.4]; the
   prefix is nonempty since `ord e.col` is in it.
3. Every role of `A'` has `γ < α (slot e) ≤ cfgMax A α`. The prefix has `γ = α`. Use
   [N5.4] `cfgMax_lt`.

**Uses:** L8.7, N5.4, [R5]; U1 `stopData_of_stepKind`, `ownerEntry_of_special`.
**Lean:** `descent_special`. Planned file `Descent/Final.lean`.
**Difficulty:** S.
**Testable:** no.

### T9.1d Ordinary case of (27)   (paper: txt:1480-1481, 1488)
**Fidelity:** as in paper.
**Statement.** `descent_ordinary`: `IsStd A`, `stepKind A = ordinary`, a configuration `α` and
`A' = A[k]` give `γ` with `cfgMax A' γ < cfgMax A α`.
**Proof.** Verified in scratch as `glue_descent_ordinary`.
1. Take `n := 1 + max` of the query sizes.
2. [D8.1] `dCore_all I n` gives `γ` with `γ < α T`.
3. `α T ≤ cfgMax A α`, with `T ∈ A.roles` by [R4]. `0 < α T`, since it is a limit [N5.4].

**Uses:** D8.1, N5.4, [R4].
**Lean:** `descent_ordinary`. Planned file `Descent/Final.lean`.
**Difficulty:** S.
**Testable:** no.

### T9.1 Strict descent (27)   (paper: txt:1477-1490)
**Fidelity:** as in paper (G-001: nonempty inputs).
**Statement.** `strictDescent I : StrictDescent I.toPrims` (spine).
**Proof.** Verified in scratch as `glue_strictDescent`.
1. `std_inL` gives V and I.
2. U1 `stepKind_isSome` (using `A ≠ ∅`) gives the step kind.
3. Case split: [T9.1b], [T9.1c] or [T9.1d].

**Uses:** T9.1b, T9.1c, T9.1d; U1 `stepKind_isSome`; U2 `std_inL`.
**Lean:** `strictDescent` (spine). Planned file `Descent/Final.lean`.
**Difficulty:** S.
**Testable:** no.

### N5.1a Configurations of standard expressions   (paper: txt:1489-1490)
**Fidelity:** as in paper.
**Statement.** `std_configured`: `FinalHyps Conf`, `IsStd A` and `A ≠ ∅` give `∃ θ, Conf A θ`.
**Proof.** Verified in scratch as `glue_std_configured`. Induction on `IsStd`.
1. Seed case: the `seed` field.
2. `expand e n = some e'`:
   - if `e = ∅`, then `e' = ∅` by `Scan.expand_empty`, a contradiction;
   - otherwise use the induction hypothesis and the `descent` field.

**Uses:** none (the spine definition `FinalHyps`, §c.13).
**Lean:** `std_configured`. Planned file `Descent/Abstract.lean`.
**Difficulty:** S.
**Testable:** no.

### N5.1b/N5.1c Accessibility   (paper: txt:1491-1504; S-2)
**Fidelity:** simplified (S-2, accessibility form, codex simpl. 2).

**Choice and justification.** I chose accessibility over `g(B) = min{σ(A) : A ∈ Std, A ≥ B}`:
1. It needs no infimum over a class indexed by expressions and configurations (`sInf` plus an
   attainment lemma).
2. The induction measure is the configuration maximum `θ` itself (`WellFoundedLT Ordinal`).
3. It uses exactly the `FinalHyps` fields, plus `IsStd.expand`.
4. The whole proof is about 30 lines. It was checked in scratch with real terms (`glue2.lean`).

**Statement.**
- `acc_of_conf`: assume `FinalHyps Conf`. For all `θ` and `A` with `IsStd A`, `A ≠ ∅` and
  `Conf A θ`, every `B : Std` with `B.1 ≤ A` is `Acc Std.lt`.
- `acc_empty`: `B.1 = ∅` gives `Acc Std.lt B`.

**Proof.**
1. `acc_empty`: nothing is below `∅`. If `D < ∅`, then `D ≠ ∅` by irreflexivity, so `∅ < D`
   (`empty_least`), contradicting asymmetry.
2. `acc_of_conf`: `WellFoundedLT.induction` on `θ`. For `C < B ≤ A`:
   - if `C = ∅`, use step 1;
   - otherwise `C < A`, and `cofinal` (with `closure A`) gives `A' = A[n]` with `C ≤ A'`;
   - `A' ≠ ∅`, since `C ≤ ∅` would force `C = ∅`;
   - `IsStd A'` holds by `IsStd.expand`;
   - `descent` gives `θ' < θ` with `Conf A' θ'`;
   - the induction hypothesis gives `Acc C`.

**Uses:** none (the spine definition `FinalHyps`, §c.13).
**Lean:** `acc_of_conf`, `acc_empty`. Planned file `Descent/Abstract.lean`.
**Difficulty:** S.
**Testable:** no.

### N5.1 The S-5 abstract final theorem   (paper: txt:1491-1504)
**Fidelity:** simplified (S-2, S-5).
**Statement.** These are spine-declared:
- `abstract_wellOrder : FinalHyps Conf → IsWellOrder Std Std.lt`;
- `abstract_implies_main : (hyp → ∃ Conf, FinalHyps Conf) → MainTheorem`.

**Proof.** Both verified in scratch as `glue_abstract_wellOrder` and
`glue_abstract_implies_main`.
1. `IsWellOrder` extends `IsWellFounded` and `Std.Trichotomous` (`Mathlib/Order/RelClasses`).
2. Trichotomy: `Subtype.ext (le_antisymm (not_lt.mp hba) (not_lt.mp hab))`, using the
   `LinearOrder Forest` instance (U1).
3. Well-foundedness: for each `B`, use N5.1c if `B.1 = ∅`; otherwise use N5.1a and then N5.1b
   with `A = B.1`.
4. `abstract_implies_main h hM := (h hM).elim fun _ hC => abstract_wellOrder hC`.

The field `FinalHyps.order` is not used; see proposed simplification PS-2.
**Uses:** N5.1a, N5.1b, N5.1c.
**Lean:** `FinalHyps`, `abstract_wellOrder`, `abstract_implies_main`. Planned file
`Descent/Abstract.lean`.
**Difficulty:** S.
**Testable:** no.

### T9.1a Assembly   (paper: txt:1477-1490)
**Fidelity:** new (spine T9.1a, S-5).
**Statement.** `finalHyps I hM : FinalHyps (Configured I.toPrims)` (spine).
**Proof.** Verified in scratch as `glue_finalHyps`. The fields:
- `order := inferInstance`;
- `empty_least := Forest.empty_lt`;
- `closure := Closure.std_inL`;
- `cofinal` from `Closure.cofinal`, dropping `E' < E`;
- `seed m` from `seed_config I m (hM (m−1))`, with `θ := cfgMax`;
- `descent` from `strictDescent I`: rewrite `θ = cfgMax A α` and repackage `γ`.

**Uses:** L6.7, T9.1; U1 `empty_lt`; U2 `std_inL`, `cofinal`.
**Lean:** `finalHyps` (spine). Planned file `Descent/Final.lean`.
**Difficulty:** S.
**Testable:** no.

### R9.2 Ordinal interpretation σ   (paper: txt:1505-1512)
**Fidelity:** as in paper.
**Statement.** `sigma P E` is `0` if `E = ∅`, and otherwise
`sInf {o | ∃ θ, Configured P E θ ∧ o = θ + 1}`.

`sigma_lt`: assume `StrictDescent P`, `IsStd E`, `E ≠ ∅`, `∃ θ, Configured P E θ` and
`E[k] = E'`. Then `sigma P E' < sigma P E`. This includes `E' = ∅`.
**Proof.**
1. The set is nonempty, so `sInf` is attained (`csInf_mem` on `Ordinal`). This gives `α` with
   `σ E = cfgMax E α + 1`.
2. If `E' = ∅`: `0 < σ E`.
3. Otherwise `StrictDescent` gives `γ` with `cfgMax E' γ < cfgMax E α`. Then
   `σ E' ≤ cfgMax E' γ + 1` (`csInf_le'`), which is `< cfgMax E α + 1`.

**Uses:** T9.1 (only through the hypothesis `StrictDescent`).
**Lean:** `sigma`, `sigma_lt`. Planned file `Descent/Final.lean`.
**Difficulty:** S.
**Testable:** no.

### Proof plan for `BTBMS.MainTheorem`
1. `Main.lean` (root, not a unit):
   ```lean
   theorem mainTheorem : MainTheorem.{u} :=
     Descent.abstract_implies_main (fun hM => ⟨_, Descent.finalHyps Hier.jInterface hM⟩)
   theorem paperTheorem : PaperTheorem.{u} := MainTheorem.paper mainTheorem
   ```
   This exact term typechecks against the spine and U5 signatures (`glue_main` in
   `scratch/blueprint/U5/glue.lean`).
2. Obligations behind it:
   - `abstract_implies_main` and `abstract_wellOrder` [N5.1, proved in scratch];
   - `finalHyps` [T9.1a, proved in scratch from its leaves];
   - leaves of `finalHyps`:
     - U1: the order instance and `empty_lt`;
     - U2: `std_inL` and `cofinal`;
     - U5: `seed_config` [L6.7] and `strictDescent` [T9.1];
     - U4: `jInterface`.
   - `strictDescent` rests on `deletion_config`, `specialDesc` and `dCore_all`.
   - `dCore_all` rests on the cycle (18): L8.5, L8.6, L8.8.
3. Formalization order inside U5:
   1. N5.2–N5.8, L8.2a–d, L6.7;
   2. N5.1 (already complete modulo leaves);
   3. L8.7, T9.1b–d;
   4. L8.3, L8.4;
   5. L8.6 label-free, then labels (S-6);
   6. L8.5;
   7. L8.8.

---

## Requires

Facts from other units that the spine does not already provide. Each was declared as a stub in
`blueprint/lean/U5.lean` under `Descent.Req`. **Integration:** `Descent.Req` is deleted. The last
column names the node that now provides each fact; a stub that no owner node stated was moved,
verbatim, into the owner's Lean file as a new node (U1 Part J, U2 D3.1d, U3 D6.1c, D7.1b, L6.2e,
L6.2f, D7.2d, L7.6b, L4.3d, L7.5d), except R24, which is the U5 node L8.5h. Citations `[R<n>]` in
this unit resolve through that column.

| # | Stub | Needed by | Owner | Exact statement (summary of the Lean stub) | Matches | Provider (integration) |
|---|---|---|---|---|---|---|
| R1 | `Req.roleUnder` (def) | L8.2b, L8.8b, R12 | U1 | `ord c ↦ ord ⟨π ++ c.path, c.col⟩`; `slot e ↦ slot ⟨⟨π ++ e.col.path, e.col.col⟩, e.idx⟩` (real body given) | new; SCR-1 | spine `Role.under` (§c.2; vocabulary of U1 D1.2a); SCR-1 applied, stub removed |
| R2 | `Req.blockMap` (def) | L8.3–L8.5, L8.7, L8.8b | U3 | `host ↦ ord e.col`; `ord q`/`cur q ↦ e.col.reps0[q]` components; `owner ↦ slot e`; `inner r ↦ roleUnder e.heightPath r` (real body given) | new; SCR-1 | spine `Packet.blockMap` (§c.9; vocabulary of U3 D7.1), with U3's body (equal to the stub's by U3 D7.1b `reps0_getElem?`); SCR-1 applied, stub removed |
| R3 | `rootData_col` | L8.5f, L8.6b, L8.6c, L8.8e | U1 | `stopData H = sd`, `rootData H = rd` ⇒ `sd.col.resolve 0 sd.r = some rd.col ∧ rd.col.num 0 = sd.r ∧ closingSlot sd ∈ H.entryAddrs ∧ H.entryAt (closingSlot sd) = some (sd.r, ∅)` | D1.6 (branch data) | U1 D1.6d `Scan.rootData_col` |
| R4 | `stopData_col_mem` | L8.2d, T9.1d | U1 | `stopData H = sd ⇒ ord sd.col ∈ H.roles` | D1.6 | U1 D1.6d `Scan.stopData_col_mem` |
| R5 | `ownerEntry_spec` | L8.7, L8.8d, T9.1c | U1 | special, `ownerEntry = e` ⇒ `e` entry, `T` inside `e`, `e`'s height ends with the column `[(e.col.num 0, ∅)]` | D1.6 (`ownerEntry_of_special` extended) | U1 D1.6d `Scan.ownerEntry_mem` |
| R6 | `lastCol_of_deletion` | T9.1b | U1 | `stepKind E = deletion ⇒ E.cols.getLast? = some []` | D1.6 | U1 D1.6b `Scan.stepKind_deletion_iff` (forward direction) |
| R7 | `lastCol_of_ordinary` | L8.8f | U1 | `stepKind E = ordinary ⇒ E.cols.getLast? ≠ some []` | D1.6 | U1 D1.6d `Scan.lastCol_of_ordinary` |
| R8 | `firstParent_host` | L8.2a | U1 | V, I, `e` entry with height `h ≠ ∅` ⇒ the first entry of `h`'s first column has parent `e.col.num 0` | D1.3 | U1 D1.3b `Scan.firstParent_host` |
| R9 | `rep_host` | L8.2a, L6.7a | U1 | `e.heightPath <+: c.path ⇒ c.rep 0 (e.col.num 0) = some (ord e.col, slot e)` | D1.2a | U3 D7.1a `rep_inside` (second conjunct) |
| R10 | `reps0_take`, `reps0_length` | L8.5f | U1 | `d.resolve 0 (c.num 0) = some c ⇒ d.reps0.take (c.num 0) = c.reps0`; `c.reps0.length = c.num 0` (every number below the printed number is visible) | D1.2a | U3 D7.1b `reps0_take`, `reps0_length` |
| R11 | `roles_nodup`, `resolve_spec` | L8.2c, L8.6i, L8.7, L8.8e | U1 | `E.roles.Nodup`; the spine's `resolve_spec`† | spine `roles_nodup`†, `resolve_spec`† | U1 D1.2b `Tree.roles_nodup`, `ColAddr.resolve_spec` |
| R12 | `roles_entry` | L8.2b, L8.4, L8.5f, L8.7, L8.8b–f | U1 | `e` entry ⇒ `E.roles = prefixRoles E e ++ slot e :: (heightRoles.map (roleUnder e.heightPath) ++ post)`, with no role of `post` inside `e` | new (D1.2a) | U1 D1.2e `Tree.roles_entry` |
| R13 | `truncAfter_roles` | L8.8d, L8.8f | U1 | `(E.truncAfter e).roles = prefixRoles E e ++ slot e :: heightRoles.map (roleUnder e.heightPath)` | spine `truncAfter_roles`† | U1 D1.2e `Tree.truncAfter_roles_under` |
| R14 | `relKey_roles`, `relKey_eq_empty` | L8.4, L8.8b | U1 | `(relKey a B).roles = B.roles`; `relKey a B = ∅ ↔ B = ∅` | D1.4 | U1 D1.4b `relKey_roles`, `relKey_eq_empty` |
| R15 | `trace_spec` | L8.5g, L8.5 | U1 | the trace starts at `(0,0)`; consecutive states move by the three comparison rules; all states have `i ≤ cursor` and `j ≤ |qry|`; the last state is `(cursor, j)` with `cursor < |src| ⇒ j = |qry|` | D2.1/L2.5 (word library) | U1 L2.5d `Scan.trace_spec` |
| R16 | `origin_prefix` | L8.6a, L8.6f, L8.6g | U2 | `χ(T)` is defined; `χ` is injective; every pre-stop role `x` has `χ x = some y` with `y ∈ ePrefix ∧ y ∈ E.roles` | spine `origin_spec`† | U2 D3.1d `Closure.anchorOrigin_prefix` (the `ePrefix` form follows by unfolding U3 D6.1c `ePrefix` at the `T'` it supplies) |
| R17 | `admCap_lt` | L8.8f | U2 | `E < w.H` for every `w : AdmCap E` | new (D3.1a; needed for `cofinal_bound`) | U2 D3.1d `Closure.lt_admCap` |
| R18 | `graph_block` | L8.4, L8.5d–f, L8.7, L8.8b | U3 | V, I, `e` entry ⇒ every atom of `posBlock (entryKey E e) (entrySel E e)` mapped by `blockMap e` is in `graph E`, and `blockMap e` agrees with `frameOf e` on frame variables | new (D7.1); SCR-1 | U3 D7.1a `posBlock_heads_graph` (first conjunct; `entryKey`, `entrySel` unfold to its key and selector) and U3 D7.1b `blockMap_frame` (second conjunct) |
| R19 | `frameOf_mem_prefix` | N5.8, L8.4, L8.7, L8.8d,f | U3 | `ord e.col` and all `e.col.reps0` roles are in `prefixRoles E e` | D7.1 | U3 D7.1b `frameOf_mem_prefix` |
| R20 | `holds_congr`, `holds_map` | L8.8c, L8.8f, N5.3 | U3 | the truth of a diagram depends only on the values of its variables; `(D.map f).Holds P a ↔ D.Holds P (a ∘ f)` | N3.1 (`amalgamate`†, `holds_map`†) | U4 N4.1a `Hier.Diagram.holds_congr`; U3 N3.1 `Hier.Diagram.holds_map` |
| R21 | `graph_truncAfter` | L8.8f | U3 | `graph (E.truncAfter e) ⊆ graph E` | D6.1 | U3 D6.1a `graph_truncAfter` (for `e ∈ E.entryAddrs`; otherwise `truncAfter` is the identity by its body, U1 D1.2c) |
| R22 | `stage_zero`, `stage_succ` | L8.6e–i | U3 | see the Lean stubs: `H[0].roles = P`, `graph H[0] ⊆ graph H`, `f_0 = id` on `D`; `H[m+1].roles = H[m].roles ++ (f(R) :: q(Q) ++ f(K))`, `q(T) = f(R)`, `q = f_m` on `D`, `f = id` below `R`; structural atoms of `H[m+1]` are old, or `q`-images of structural `queryAtoms`, or `f`-images of `retAtoms` (atoms in `D` involving `K`). [V-fix] With this `retAtoms`, both directions hold on the bounded sample (`test_u5.py`). The previous `retAtoms` (involving `R` or `K`) made the converse fail on `elem A_prev R` | spine `occurrence_map_identity`† (L6.2), stage form | U3 L6.2e `stage_zero`, `stage_succ` |
| R23 | `queryAtoms_struct_vars` | L8.6i | U3 | the structural `queryAtoms` read only `D ∪ {T} ∪ Q` (txt:941) | D6.1 | U3 L6.2e `queryAtoms_struct_vars` |
| R24 | `valid_iff` | L8.5, L8.6h | U3 | `S.Valid P ↔ SetupClauses P S` | D7.2b; SCR-2 | U5 L8.5h `valid_iff` (new U5 node; the spine body of `Valid` is U3's `ValidDef`) |
| R25 | `scanRecord_tgtHeight` | L8.5e | U3 | `j < |Q| ⇒ (S.scanRecord i j).tgtHeight = Q_j.2` | D4.1/D7.2b | U3 D7.2d `scanRecord_tgtHeight` |
| R26 | `fit_of_block` | L8.5e, L8.5f | U3 | a posBlock realization of query entry `j` at the fitted frame above `L ≥ Lmax j β` extends `Fitted j β` to `Fitted (j+1) β'`, with the entry values among the block's new values | L7.6 (its target-advance step, txt:1160-1162) | U3 L7.6b `fit_of_block` (`queryKey`, `querySel` unfolded) |
| R27 | `special_graph` | L8.7 | U3 | special `H`, `H' = H[k]` ⇒ `∃ N cm`: `H'.roles = prefixRoles H e ++ ⋃_{i<N} cm i (owner :: inner roles of specialKey)`; `cm i` sends frame variables to `frameOf e`; every structural atom of `H'` lies in `graph H` with all variables in the prefix, or is `a'.map (cm i)` with `a' ∈ posBlock (specialKey H e) (entrySel H e)` | new (special counterpart of L6.2) | U3 L6.2f `special_graph` |
| R28 | `firstDiff_wholeEnds` | L8.8b | U3 | `firstDiff = wholeEnds ⇒ |tgtKey.cols| < |srcKey.cols| ∧ tgtKey.cols = srcKey.cols.take |tgtKey.cols|` | L4.2 (classifier spec) | U3 L4.2 `firstDiff_spec` (first conjunct), with `List.prefix_iff_eq_take` |
| R29 | `ChildData`, `childEnds_package` | L8.8d | U3 | the fields of `ChildData` (Lean): `F₁` in L with prefix roles and subgraph; stopping column inside `a`; `F₂ = F₁[k]`; ordinary with `Q = []` and root inside `a`, or special with owner entry strictly inside `a`; `P(F₂,a) = P(F,a)`; the record `(E, b, F₂, a, kind')` admitted | spine `reduce_childEnds`† (L4.3) | U3 L4.3d `ChildData`, `childEnds_package` |
| R30 | `CapData`, `cap_package` | L8.8f | U3, U2 | the fields of `CapData` (Lean): repaired cap `w`; `(7)` sizes `+2 ≤ n`; charts `nm` (E-prefix) and `nmH` (`H`) with `nm = tgtChart` on `P(E,b)`, `nm(U_b) = owner`, `compat`, injectivity; `asg'` extends `asg` on old names; `Γ(H)` at `asg' ∘ nmH`; the E-prefix graph at `asg' ∘ nm` below `W`; marked entry: membership, origins of slot and host, prefix into `P(E,b)`, whole frame (txt:1418-1421); `T` inside `a'`; `u < W`; readmission of the repair record for every `H[k] > E` | `firstDiff_cap`† (L4.2), `repair`† (L3.1), `joint_cap`† (L7.4), `joint_repair`† (L7.5), `repair_output`† and `query_size_bound`† (L4.3) | U3 L7.5d `CapData`, `cap_package` |
| R31 | `weaklyMahlo_regular`, `weaklyMahlo_stationary` | L6.7, L6.7b | U4 | `IsWeaklyMahlo n κ ⇒ ℵ₀ < κ ∧ κ.IsRegular`; `IsWeaklyMahlo (n+1) κ ⇒ StationaryIn κ {μ.ord ∣ IsWeaklyMahlo n μ}` (definitional unfolding) | D6.4 helpers (`IsWeaklyMahlo.uncountable_regular`, `.stationary_pred`) | U4 D6.4 `IsWeaklyMahlo.uncountable_regular`, `IsWeaklyMahlo.stationary_pred` (identical statements) |

**Observed in the concurrent drafts** (read after drafting; nothing here relies on them):
- `blueprint/lean/U3.lean` declares:
  - `Hier.Diagram.holds_congr`, which matches R20;
  - `stageRoles` and the decomposition `H[n].roles = rs.P ++ ⋃ stageRoles`, which matches the
    first clause of R22;
  - `reduce_childEnds`, `joint_cap`, `joint_repair`, `repair_output` and `query_size_bound`,
    which are the components of R29 and R30.
- It has no counterpart of `blockMap` (SCR-1).
- `blueprint/lean/U1.lean` declares `resolve_spec` and `truncAfter_roles` (R11, R13).

**G-003 (shared with U3): the packet closure U5 needs.**
- U5 itself constructs every readmitted packet and proves all six `SourcePacket.Valid` clauses
  (real spine body): L8.8c for Case 2 and Case 3 with `p > ρ`, and L8.8f step 5 for Case 3
  with `p ≤ ρ`.
- From U3, U5 needs exactly:
  - the admission of the new **record**: `ChildData.admitted` and `CapData.readmit`;
  - the joint realizations of the reduced and capped contexts: the remaining fields of
    `ChildData` and `CapData`.
- No closure of `SourcePacket.Valid` itself is required from U3.

---

## Spine change requests

### SCR-1: add `Role.under` and `Packet.blockMap` with real bodies, and their two contracts
**Status: applied at integration** (spine §i.6). `Packet.blockMap` takes U3's body (the draft's
`blkRole`), which equals the proposed body by U3 D7.1b `reps0_getElem?`; the contracts are U1 D1.2e
`roles_entry` and U3 D7.1a `posBlock_heads_graph` with D7.1b `blockMap_frame`.
- **Item.** Spine §c.2 (occurrences) and §c.9 (blocks). The spine has `freeBlock`, `posBlock`
  and `frameOf`, but nothing relates the block variables of an entry to the roles of
  `Γ(E)`.
- **Missing case.** Every use of "the complete internal graph of B interpreted at this frame"
  (txt:1028-1030) needs that map. In U5 these are L8.3–L8.5, L8.7 and L8.8 Case 1; in U3,
  L7.4 and L7.6.
- **Proposed replacement.** Add:
  - `Role.under (π) : Role → Role` (U1, real body as `Req.roleUnder`);
  - `Packet.blockMap (e) : BlkVar → Role` (U3, real body as `Req.blockMap`);
  - U1 contract `Tree.roles_entry` ([R12]);
  - U3 contract `Packet.graph_block` ([R18]).

  The body and both directions of the correspondence were tested on 2199 standard
  expressions: the forward claim, and the converse "every structural atom touching `e` is a
  block image" (`scratch/blueprint/U5/blocktest.lean`).
- **Consumers affected.** U1 (one def, one lemma), U3 (one def, one lemma; their L7.4 and L7.6
  can use them), U5.
- **Local workaround.** `Descent.Req.roleUnder` and `Descent.Req.blockMap`, marked SCR-1.

### SCR-2: fix the body of `ScanSetup.Valid` as `SetupClauses`
**Status: superseded at integration** (spine §i.3). The body is U3's `ValidDef` (U3's SCR2, from the
owner of the definition); the exact characterization U5 needs is the new node L8.5h `valid_iff`.
The helpers `setupBank` … `setupEPrefix` stay U5 definitions.
- **Item.** `ScanSetup.Valid` (spine §c.11; "body: U3").
- **Missing case.** U5 must both use S4 and S5 as named facts (L8.5) and prove `Valid` for a
  setup it constructs (L8.6g–h). A sorry body makes both impossible without an exact
  characterization.
- **Proposed replacement.**
  - Make the body exactly `SetupClauses` (U5.lean, L8.5a), so `valid_iff` is `Iff.rfl`.
  - Move `setupBank`, `setupPreRoot`, `setupBankGraph`, `setupBankVal`, `setupPosVal` and
    `setupEPrefix` into `Packet.ScanSetup` as real-bodied helpers.
  - The clauses transcribe the spine's S1–S6 literally. S6 is stated as pairwise
    disjointness of the named images.
- **Consumers affected.** U3 (L7.6 `scan_packet` is proved from these clauses), U5.
- **Local workaround.** `SetupClauses` plus the stub `Req.valid_iff` ([R24]).

No FIRM statement was found wrong. In particular, `DLab`'s `Fix` bound, which ranges only over
`Λ.vars`, is sufficient: L8.6a `nu_mem_vars` shows that every `ν x` lies in `Λ.vars`.

---

## Proposed simplifications (flagged, not applied)

- **PS-1 (U3, L7.6).** State `scan_packet`'s last clause as "`TargetAbove` ⇒ the hypotheses of
  `fit_of_block`" and let `fit_of_block` [R26] do the fitting. Then the three advancing cases
  of L8.5 share one lemma. The converse block correspondence (tested, SCR-1) makes
  `fit_of_block` a direct consequence of `graph_block` and `localStruct_vars`.
- **PS-2 (spine, FinalHyps).** The field `order` is unused: `abstract_wellOrder` gets
  trichotomy from the `LinearOrder Forest` instance (`glue2.lean`). It could be dropped, or
  kept as documentation.
- **PS-3 (L8.6).** The fixed floor `η` and the per-stage fresh reference charts of txt:1259-1270
  are unnecessary in ordinal form. The `lt` atoms carry the order, and the reference chart
  values never change. This is already reflected in L8.6d (fidelity "simplified (S-4)"). The
  flag is for the reconciler, to confirm that no other unit relies on `η`.
- **PS-4 (L8.8f).** In Case 3 with `p ≤ ρ`, `Fix = ∅` suffices: DLab's pre-root clause already
  keeps the allowed pre-root data. This simplifies the paper's "allowed pre-root data and finite
  codes are fixed" (txt:1423).
- **PS-5 (R9.2).** `sigma` is not used by `MainTheorem`. It can be formalized last, or
  dropped.

---

## Open problems

| ID | Node | Issue | Severity |
|---|---|---|---|
| OP-1 | L8.8f / R30 | **Integration:** `CapData`/`cap_package` are now U3 node L7.5d, whose plan names a U3 or U2 source for every field (the two fields in question: `marked_frame` from L7.5 `joint_repair` and L7.5a `frame_repair`; `compat` and `nmH_inj` from the definition of `capRole` and value separation). Remains to be confirmed when L7.5d is proved. Original issue: The `CapData` interface is my proposal for what L4.2 + L3.1 + L7.4 + L7.5 + L4.3 must jointly supply. Two fields rest on paper passages that are only sketched: `marked_frame`, whole-frame survival through repairs (txt:1418-1421, "induction through the containers"); and `compat`/`nmH_inj`, an injective chart of the repaired cap compatible with `χ`. U3 must confirm each field is provable as stated. | major |
| OP-2 | L8.6 / R22 | **Integration:** U3's `qMapDef`/`fMapDef` are now the spine bodies of `qMap`/`fMap`, and the stage form is U3 node L6.2e. Open: re-run `test_u5.py`'s stage check against these bodies (`#eval!`). Original issue: `stage_succ` fixes the stage form of the occurrence-map identity: appended roles `h :: q(Q) ++ f(K)`, `f = id` below `R`, and the structural-atom classification. The role-prefix part is tested (2199 expressions, `m ≤ 3`). [V-fix] The whole stage form is now tested in Python. The test uses a port of `stopData`/`rootData` written from spine §c.5 and the explicit `q`/`f` of txt:948-955 (3073 ordinary inputs, `m ≤ 3`): 9219 role cases, 576,318 forward and 111,093 converse atom cases, 0 failures. Still open for U3: its `qMap`/`fMap` bodies must be these maps. | major |
| OP-3 | L8.6i / R23 | "Query edges read only `D ∪ {T} ∪ Q`" (txt:941) is claimed for structural atoms only. `lt (last of P, T)` may read a consumed role; it is handled through the roles list, not through `q`. [V-fix] Tested: 10,856 structural query atoms read only `D ∪ {T} ∪ Q`, and the 174 query atoms that read a consumed role are all non-structural. | minor (tested) |
| OP-4 | L8.3 / R10 | `two_candidates` now takes "the frame is complete" as a hypothesis (`hnew`). Its one use (L8.5f) discharges it with `reps0_length` [R10]. `reps0_length` is claimed unconditionally, from the tiling of `resolveAux`'s ranges; U1 should confirm it. [V-fix] Closed. The ranges `[start, start + c_k]` at each level and `[start, start + col)` at the own level tile `[base, num base c)`, so every smaller number resolves. Tested on 42,985 columns. | closed |
| OP-5 | L8.5g / R15 | The exact form of `trace_spec` (indices vs. `ReachesGT`) is my proposal. U1 may prefer a different packaging of the trace facts. [V-fix] The content was tested exhaustively on all 14,641 source/query word pairs over `{0,1,2}` of length `≤ 4`. | minor (tested) |
| OP-6 | L8.7 / R27 | **Integration:** stated as U3 node L6.2f with the tested choice `cm i = blockMap ⟨e.col, e.idx + i⟩`, `N = n + ε`. Original issue: `special_graph` is new (the paper states no occurrence identity for special outputs). Its `N = n + ε` and its copy maps must match U1's `paperOp_special`†. [V-fix] Tested with `cm i = blockMap ⟨e.col, e.idx + i⟩` and `N = n + ε` on 696 special inputs, `n ≤ 3`: 2784 role cases and 94,462 structural atoms, 0 failures. | minor (tested) |

---

## Files

- `/home/dev/ggg/btbms-formalization/blueprint/U5-descent-main.md` (this file).
- `/home/dev/ggg/btbms-formalization/blueprint/lean/U5.lean` (signatures; typechecks).
- Scratch (tests and wiring checks):
  - `scratch/blueprint/U5/check.lean`: the deliverable typecheck;
  - `glue.lean`, `glue2.lean`, `glue3.lean`: real proof terms for the wiring;
  - `seedtest.lean`, `stagetest.lean`, `chaintest.lean`, `blocktest.lean`: bounded `#eval`
    tests.
