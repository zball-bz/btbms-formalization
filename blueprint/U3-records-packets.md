# U3 records-packets — blueprint

**Task:** blueprint, unit U3. **Sections:** §4 (txt:646-733), §6.1 (txt:921-970), §7
(txt:1016-1170). **Lean companion:** `blueprint/lean/U3.lean`. It is appended after
`blueprint/lean/Spine.lean` and typechecks with 0 errors. The only warnings are
`declaration uses 'sorry'` (84 in the U3 region **[changed in verification:** was 79; five
declarations added**]**). The command and the log are in §T.

**Inputs read:**
- `blueprint/00-spine.md` and `Spine.lean`;
- the paper §1–§4, §6.1, §7, §8.1–§8.5 (consumers);
- ledger G-003, R-3, S-1…S-6, D-1…D-3;
- claude-review C-05, codex-review X-04 and §4/§6/§7 inventory;
- codex-crosscheck-1 Q2.

## Overview

U3 makes the finite bookkeeping of §4, §6.1 and §7 exact. It does this in four parts.

1. **Graph and occurrence maps (§6.1).** `graph E` (spine) is decomposed by *ownership*: each
   non-order atom is owned by one role. A configuration is then checked role by role. The query
   map `q_m` and the retained map `f_m` get real bodies built from three address-relocation
   functions and an explicit head address `h_m` (L6.2a). The occurrence-map identity (L6.2)
   becomes a list equality for the roles of `H[n]` plus a per-role transport of owned atoms.
   Deletion and special steps get the same form (L6.2b, L6.2c). `ι = id` is kept separate from
   `f_m` (D6.3, L6.2d).
2. **Frames and blocks (§7.1).** D7.1a proves that the spine's `freeBlock` and `posBlock`, read
   through `blockMap e`, are exactly the atoms of `Γ` around an entry `e`. This is the bridge
   used in every packet argument. N3.1 is the amalgamation and packing toolkit.
3. **Records (§4, G-003).** The admitted class is the spine's `SrcRecord.Admitted`. D4.1a adds
   the explicit first-difference classifier and its specification. L4.2 is split into the
   κ-transfer (L4.2a), word facts (L4.2b), the path transfer for each record kind (L4.2c) and
   cap legality (L4.2d). L4.3 is split into confined operations (L4.3a), repairs outside the
   marked height (L4.3c), the monotonicity (6) (L4.3b) and the four spine contracts.
4. **Packets (§7, G-003).** Factorization (L7.3) is almost trivial in ordinal form; SCR1 fixes
   a missing hypothesis. Joint cap (L7.4) and joint repair (L7.5) give an explicit chart `κ`
   and configuration `α`. The class of admitted valid packets is closed under:
   - the §7.3 extension (L7.6a, explicit `scanPacket`);
   - Case 2 readmission (L7.5b, `readmitHeight`);
   - Case 3 readmission (L7.5c, `readmitRepair`).

   Each constructor has real bodies and fresh tags (D7.2c).

**R-3 checklist** (where each identification is made explicit):
- *occurrence identity*: roles are addresses. Every map between occurrences is a named function:
  - `transColumn`, `transEntry`, `transCols`;
  - `qMapDef`, `fMapDef`;
  - `specialCopy`;
  - `anchorD`, `capRole`;
  - `toH`, `Role.under`.
- *stack lookup*: `rep_inside`, `rep_visible` (D7.1a), `rep_stage` (L6.2a), and U2's rep clause
  of `origin_spec` (R10).
- *ι versus f*: `iota = id` (D6.3, L6.2d) versus `fMapDef` (L6.2a). L6.2 part (ii) is the only
  place old pre-stop roles are read.
- *charts*: `Name.role tag r` with `freshTag` (D7.2c). Each constructor fixes its charts by an
  explicit `if` on a role list.
- *frames*: `frameOf` (spine), `frame_repair` (L7.5a), and the frame clause of `scanPacket_spec`
  (L7.6a).

**Bounded evidence** (§T): every finite node whose test was feasible was run on bounded
instances, with 0 failures:
- L6.2 parts (i)–(iv), L6.2b, L6.2c: 8,992 standard expressions, 31,621 cases;
- D7.1a: 38,754 entries;
- `rep_visible`: 273,040 instances.

**[Changed in verification.]** The cap and child branches of L4.2/L4.3 *are* reached by
reachable records. The smallest instance found is the standard
`E = [[], [(0, [[(1,∅),(0,∅)]])], [(1, [[(2,∅)]]), (1,∅)]]` (size 11, seed `L_3`, 23 operations).
Its stopping column is outer column 2 (`t = 2`, `r = 1`, `Q = [(1, [[(2,∅)]])]`). At raw-scan
state `(0,0)` it has `y_0 = h_2([[(2,∅)]]) = [[((true,0),∅)]]` and
`x_0 = h_1([[(1,∅),(0,∅)]]) = [[((true,0),∅), ((false,0),∅)]]`, so the target column ends
first: a `capAt` difference. The drafter's generator stopped at breadth-first depth 11 and missed
it. These branches were tested on bounded instances; see §T, last paragraph.

---

## Conventions used below

- Paper `E[n]` is `expand E n = some E'`. Under `E ≠ ∅ ∧ V ∧ I` this equals `Scan.paperOp E n`
  (`expand_eq_paperOp`, D1.6a).
- `x <_E y` is `Before E x y`: `x` strictly precedes `y` in `E.roles`.
- "**Owned atoms of `z`**" means `ownedBy (graph E) z`. The owner is defined by `atomOwner`:
  - `lim x ↦ x`;
  - `elem y x ↦ x`;
  - `edge s c o ↦ s`.
- For a record `rk`, write:
  - `t := rk.b.col.num 0` and `r := rk.a.col.num 0`;
  - `B := rk.tgtHeight` and `A' := rk.srcHeight`.
- For a packet `pk`, write:
  - `u := pk.asg pk.owner` and `ρ := pk.asg pk.host`;
  - "low" for the names in `pk.lowNames`.
- Requires are numbered **R1–R19** (section "Requires"; **[changed in verification:** R18, R19 added**]**). Stubs are in `U3.lean`
  `namespace Packet.Stubs` (deleted at integration; see Requires). **SCR***n* are spine-change requests.

---

# Part A — §6.1: the graph, configurations, occurrence maps

### D6.1 Graph Γ(E), configurations, role sets   (paper: txt:922-943)
**Fidelity:** as in paper, with bodies from the spine. Two clarifications are explicit:
- the strict reading order is encoded by consecutive `lt` atoms;
- duplicated edges are kept (they are harmless).

**Statement.** These are spine definitions with real bodies, unchanged.
- `graph E` has:
  - `lim` on every role;
  - `lt` on consecutive roles of `E.roles`;
  - `elem (A_c) (A_{c'})` for consecutive columns of one forest;
  - for every entry `e = (p, ·)` of column `c` with `c.rep 0 p = some (o, v)`, the atoms
    `edge (U_e) (A_c) o` and `edge (U_e) (A_c) v`.
- `IsConfig P E α :⇔ BaseHolds P (graph E) α`.
- `cfgMax E α = (E.roles.map α).foldr max 0`, and `Configured P E θ :⇔ ∃ α, IsConfig ∧ cfgMax = θ`.
- `rolesBefore`, `prefixRoles` (= `P(E,e)`), `restrictTo`, `prefixGraph`.
- `roleSets H`:
  - `R`, `T`, `N`, as in txt:935;
  - `Q` = the roles strictly between `T` and `N`;
  - `K` = the roles strictly between `R` and `T`, minus the slots and heights of the root entries
    of index `< rd.cursor`;
  - `D = rolesBefore R ++ [R] ++ K`;
  - `P = rolesBefore T`.

**Proof.** Definitions only.

**Uses:** D1.2 (`roles`, `rep`, `colAddrs`, `entryAddrs`), D1.6 (`stopData`, `rootData`).

**Lean:** `Packet.graph`, `IsConfig`, `cfgMax`, `Configured`, `rolesBefore`, `prefixRoles`,
`restrictTo`, `prefixGraph`, `RoleSets`, `roleSets` (Spine.lean §c.8). Planned file
`Packet/Graph.lean`.

**Difficulty:** S. The bodies are given.

**Testable:** yes. `graph` is computable. The spine checked `L_3`, and `test_blocks.py`
recomputes it (§T).

### D6.1a Ownership, reading order, truncation and prefix lemmas   (paper: new)
**Fidelity:** new (R-3). This is infrastructure that lets every configuration argument proceed
role by role.

**Statement.** For every forest `E`:
1. `graph_atom_cases`: every `a ∈ graph E` is either `lt x y` with `x`, `y` consecutive in
   `E.roles`, or has `atomOwner a = some z` with `z ∈ E.roles`.
2. `graph_lt_iff`: `lt x y ∈ graph E ↔ ∃ i, E.roles[i]? = some x ∧ E.roles[i+1]? = some y`.
3. `graph_vars_roles`: every variable of every atom of `graph E` is in `E.roles`.
4. `isConfig_before`: `IsConfig P E α → x <_E y → α x < α y`.

   **[Changed in verification.]** 4b. `before_of_restrict`: let `m ≤ |E.roles|` and
   `S = E.roles.take m`. If `restrictTo (graph E) S` holds at `α` and `x <_E y` with
   `x, y ∈ S`, then `α x < α y`. This is the form used when only a prefix of `Γ(E)` is
   realized (L7.6a step 8(b): S2 realizes only `restrictTo (graph E) P_E`, and
   `P_E = rolesBefore E T_E` is a `take` of `E.roles`).
5. `le_cfgMax`, `cfgMax_lt`:
   - `x ∈ E.roles → α x ≤ cfgMax E α`;
   - `0 < θ → (∀ x ∈ E.roles, α x < θ) → cfgMax E α < θ`.
6. `graph_truncAfter`: for `e ∈ t.entryAddrs`,
   `a ∈ graph (t.truncAfter e) ↔ a ∈ restrictTo (graph t) (t.truncAfter e).roles`.
7. `prefixGraph_setHeight`: for `e ∈ t.entryAddrs`:
   - `prefixRoles (t.setHeight e h) e = prefixRoles t e`;
   - the two `prefixGraph`s have the same members.
8. **[Changed in verification.]** `graph_truncClear`: for `e ∈ t.entryAddrs`, with
   `t₀ := (t.truncAfter e).setHeight e ∅`,
   `a ∈ graph t₀ ↔ a ∈ restrictTo (graph t) t₀.roles`. This is truncation at a slot: it keeps
   `U_e` but not its height. L7.4 step 6 needs it, because the reindexed internal cap `S_A` is
   of this form and is not a `truncAfter`.

**Proof.**
1. Items 1–2: unfold `graph`. It is a concatenation of four lists:
   - the `lim` part, whose owner is the role itself;
   - the `zip` part: an `lt` atom of `rs.zip rs.tail`, which gives consecutive indices
     (`List.mem_zip`, `List.getElem?_tail`);
   - the `elem` part, owned by its second column, a role by `colAddrs ⊆ roles`;
   - the `flatMap` part, an `edge` owned by `.slot e` with `e ∈ entryAddrs`.
2. Item 3:
   - `lim` and `lt` atoms: their variables are roles by construction.
   - `elem` atoms: `colAt ⟨c.path, c.col+1⟩ = some _` gives the role.
   - `edge` atoms: `c.rep 0 p = some (o, v)`. The address `resolve 0 c p` is a column of `E`
     whenever `c` is, because the visible stack consists of existing columns (`resolveAux`
     computation). The container entry exists since it lies on `c.path`.
3. Item 4: induction on `j − i`, using item 2 and `lt x y ∈ graph E` (each holds under `α`).
   **[Changed in verification.]** Item 4b: the same induction. Every consecutive pair of
   `E.roles` inside the prefix `S` has both variables in `S`, so its `lt` atom (item 2) lies in
   `restrictTo (graph E) S`.
4. Item 5: `List.foldr` with `max` (Mathlib `List.foldr_max_le`, or by induction).
5. Item 6:
   - by U1 `truncAfter_roles`†, `(t.truncAfter e).roles` is a prefix `t.roles.take m`;
   - `lt` atoms are consecutive pairs of a prefix (item 2);
   - `elem` and `edge` atoms of retained roles are unchanged: same addresses, and same labels
     by R1 (`truncAfter_spec`, `entryAt` of retained entries);
   - the only removed atoms read a removed role. These are excluded on both sides: on the
     right by `restrictTo`, on the left by item 3.
6. Item 7:
   - `setHeight` changes only the subtree of `e` (R2);
   - `prefixRoles` is `takeWhile (· != .slot e)`, and every role before `U_e` lies outside that
     subtree;
   - the atoms are compared role by role as in item 6.
7. **[Changed in verification.]** Item 8:
   - by U1 `truncAfter_roles`† and R2, `t₀.roles` is `t.roles` up to and including `U_e`, a
     prefix of `t.roles`;
   - the label of `e` is unchanged (R2, last clause), and every other retained entry keeps its
     label (item 6). So the two edges of `U_e` and all other owned atoms of retained roles are
     unchanged;
   - the rest is the argument of item 6.

**Uses:** D6.1, R1, R2, U1 `truncAfter_roles`†.

**Lean:** `atomOwner`, `ownedBy`, `Before`, `graph_atom_cases`, `graph_lt_iff`,
`graph_vars_roles`, `isConfig_before`, `before_of_restrict`, `le_cfgMax`, `cfgMax_lt`,
`graph_truncAfter`, `prefixGraph_setHeight`, `graph_truncClear`. Planned file
`Packet/Graph.lean`. **[Changed in verification:** `before_of_restrict`, `graph_truncClear`
added.**]**

**Difficulty:** M. List reasoning over the four parts of `graph`, about 300 LOC.

**Testable:** yes (finite). Items 1–3 and 6–7 can be checked by `#eval`/`decide` on
enumerated forests once U1's `truncAfter` and `setHeight` have bodies.

### D6.1c Syntactic helpers of ordinary and special steps   (paper: new)

**Fidelity:** new (moved from U5 N5.7 at integration, unchanged, so that the U3 statements L6.2e,
L6.2f and L7.5d, requested by U5, can be written in U3; U5 reads these names through
`open Packet`).

**Statement.** These are definitions with real bodies:
- `isStruct` is true exactly on `elem` and `edge` atoms.
- `entrySel E e` is the parent of `e` (`0` if `e` is not an entry).
- `entryKey E e = relKey (e.col.num 0) (height of e)`.
- `ePrefix E cap sd` is `rolesBefore E T'` for `T' = anchorOrigin E cap (ord sd.col)`, and `[]` if
  that is `none`.
- `queryAtoms H rs` is the restriction of `Γ(H)` to `P ++ [T] ++ Q`, filtered to atoms with a
  variable in `T :: Q`. This is `ScanSetup.queryGraph` verbatim, with `preStop = rs.P` and
  `queryRoles = rs.Q`.
- `retAtoms H rs` is the restriction of `Γ(H)` to `D`, filtered to structural atoms with a variable
  in `K`. Atoms reading only `R` and pre-root roles are excluded: the only such structural atom is
  the old pair `elem A_prev R`, whose `f`-image is not an atom of `Γ(H[m+1])` (U5 verification
  F4). The root-to-next-column pair `elem R A_next` involves `K` (txt:961-962) and is kept.
- `specialKey H e = relKey (e.col.num 0) (.node (height of e).cols.dropLast)`, the key of the
  copies `(p, C)` of a special step.

**Proof.** Definitions.

**Uses:** D6.1, D3.1a.

**Lean:** `Packet.isStruct`, `Packet.entrySel`, `Packet.entryKey`, `Packet.ePrefix`,
`Packet.queryAtoms`, `Packet.retAtoms`, `Packet.specialKey`. Planned file `Packet/Graph.lean`.

**Difficulty:** S (definitions only).

**Testable:** yes (all computable).

### D6.3 Persistent map ι_m   (paper: txt:965-968)
**Fidelity:** as in paper.

**Statement.** `iota H n = id` (spine, real body). On `P` it is the identity onto the original
pre-stop occurrences of `H[n]`: L6.2 part (i) shows that `rs.P` is a prefix of `H[n].roles`.
It generally differs from `fMap H n n`. Example: `fMap H n n R = .ord h_n ≠ R` for `n ≥ 2`,
by L6.2a. Old labels must read `iota`, never `fMap` (txt:967-968, 1310). U5's `DLab` does so.

**Proof.** Definition. The identity property is L6.2 (i)–(ii) together with L6.2d.

**Uses:** L6.2, L6.2d.

**Lean:** `Packet.iota` (spine). Planned file `Packet/OccurrenceMaps.lean`.

**Difficulty:** S.

**Testable:** yes. It is covered by part (ii) in `test_stage_roles.py`.

### L6.2a Stage addresses, relocations and the explicit maps q_m, f_m   (paper: new; makes txt:944-964 explicit)
**Fidelity:** new (R-3). It gives the bodies owed by U3 for the spine's `qMap` and `fMap`
(SCR2).

**Statement.**

*Definitions with real bodies:*
- `relocCol c c' f d` and `transColumn c c' f`. They move the subtree of column `c` (the
  column, its slots, and everything in its entries' heights) to column `c'`. A slot of `c` with
  index `i` goes to index `f i`. Every other address is unchanged.
- `relocEntryCol src dst` and `transEntry src dst`. They move the subtree of entry `src`
  (`U_src` and the roles under `src.heightPath`) to `dst`.
- `relocCols π π' lo lo'` and `transCols`. They move the columns `x ≥ lo` of the forest at `π`,
  with their content, to the columns `x − lo + lo'` of the forest at `π'`.
- `nextHead sd rd qLen rootLen h`. Write `j = rd.layer` (the depth of the root forest),
  `i = rd.idx`, `ℓ = sd.depth`, `π_ℓ = sd.col.path`, `c_ℓ = sd.col.col`, and
  `tail = π_ℓ.drop (j+1)`. Then:
  - owner root (`rd.owner`):
    `⟨h.path ++ (h.col, qLen + (rootLen − cursor) − 1) :: tail, c_ℓ⟩`. The hole lies inside
    the last restored root entry, at depth `ℓ − j − 1` (txt:128).
  - body root with `j = ℓ`: `⟨h.path, h.col + (c_ℓ − i)⟩`. The copied columns of `F[i+1:]`
    follow `h`, and the stopping column is their last.
  - body root with `j < ℓ`: let `π_ℓ[j] = (c_j, i_j)`. The result is
    `⟨h.path ++ (h.col + (c_j − i), i_j) :: tail, c_ℓ⟩`.
- `headAddr sd rd qLen rootLen m`: `h_1 = sd.col`, and `h_{m+1} = nextHead … h_m`.
- `fMapDef H _n m x`:
  - `m = 0`: `x`.
  - Otherwise, with `h = h_m`:
    - `R ↦ .ord h`;
    - roles inside root entries of index `≥ cursor` (`inRootSuffix`) go by
      `transColumn rd.col h (i ↦ |Q| + (i − cursor))`;
    - in the body case, the remaining roles go by `transCols rd.col.path h.path (i+1) (h.col+1)`;
    - all other roles are fixed.
- `qMapDef H n m x`:
  - `m = 0`: `x`.
  - Otherwise:
    - `T ↦ .ord h_m`;
    - query-region roles (`inQueryRegion`) go by `transColumn sd.col h_m id`;
    - every other role goes to `fMapDef H n (m−1) x`.
- `stageRoles H n rs m = qMap m T :: (rs.Q.map (qMap m) ++ rs.K.map (fMap m))`.

*Lemmas:*
1. `roles_map`: `(t.map f).roles = t.roles`.
2. `roles_replaceAt`: if `(routeCols F)[ℓ]? = some ⟨π, c⟩`, then
   `(replaceAt r d Z ℓ F).roles = rolesBefore F (.ord ⟨π,c⟩) ++ Z.roles.map (transCols [] π 0 c)`.
3. `rep_stage` (stack transport). Assume `H ≠ ∅`, V, I, `stepKind H = some .ordinary`,
   `roleSets H = some rs`, `stopData H = some sd`, `rootData H = some rd`,
   `expand H n = some H'`, and `1 ≤ m ≤ n`. Put `d := sd.t − sd.r`.
   - For every query slot `U_e ∈ rs.Q` with parent `p`, `qMap m U_e = U_{e'}`, where:
     - `qMap m A_{e.col} = A_{e'.col}`;
     - `H'` has parent `shiftVal r ((m−1)d) p` at `e'`;
     - `e'.col.rep 0 (shiftVal r ((m−1)d) p) = (e.col.rep 0 p).map (qMap m × qMap m)`.
   - For retained slots in `rs.K`, the same holds with `fMap m` and shift `m·d`.

**Proof.**
1. `roles_map`: mutual induction on the tree, alongside `Tree.map` and `rolesF`/`rolesCols`/
   `rolesCol`. Roles never read labels.
2. `roles_replaceAt`: induction on `ℓ`, unfolding the locked `replaceAt`.
   - Case `0`: `cols.dropLast` keeps the roles of the columns before `c`, by item 1, since
     `mapCol` keeps the shape. The roles of `Z.cols` are then numbered from column `c`, which
     is exactly `transCols [] π 0 c`.
   - Case `k+1`: `mapLast` keeps every column and entry except the last entry of the last
     column (item 1). Recursion into that entry's height adds the step
     `(|cols|−1, |col|−1)` to `π`. `routeColsAux` produces the same step.
3. `rep_stage`:
   1. Reduce to `paperOp` (D1.6a `expand_eq_paperOp`).
   2. Unfold the output by R16 (U1's `paperOp_ordinary`†).
   3. For the address of the copy of `e`: by the definitions, `qMap m` (resp. `fMap m`) relocates
      `e` into stage `m`'s head column (query copy at the same index; `U`-copy at
      `|Q| + (i − cursor)`), or into the copy of `F[i+1:]` at `h_m.col + 1 + (x − i − 1)`.
      Stage `m` is loop index `k = m` (txt:125-131). Its query part is `T_{r,(m−1)d}(Q)`, and
      its retained part is shifted by `T_{r,md}` (U-heights, and `A_{r,md,…}` on `F[i+1:]`).
      `U` entries keep their outer parent, but that parent is `< r` by V, so
      `shiftVal r (md) p = p`.
   4. Printed numbers: `num` of the stage-`m` copy of a column of number `y ≥ r` is
      `y + (m−1)d` (query) or `y + md` (retained). This is computed from `ColAddr.num` and the
      `nextHead` formulas, using `h_1.num = t` and `h_{m+1}.num = h_m.num + d`.
   5. Resolution: `resolveAux` on the copied stack returns, for a shifted number, the copy of
      the old column. It returns the same column for numbers `< r`.
      - The containers above `R`'s forest are common to `R` and `T`. Pre-root columns keep
        their address (`fMap = id` below `R`).
      - For a containing column `q < r` of `T`, its container entry also contains `R` (see
        L7.6a step 7 for the argument). So its slot precedes `R` and is fixed.
   6. Containers: a copied column's containers inside the copy are the copies of the old
      containers (`relocCol` commutes with `ColAddr.container` on prefixes, by
      `List.isPrefixOf` arithmetic). Hence `rep` maps to the mapped pair.

**Uses:** D1.2, D1.5, D1.6a (`expand_eq_paperOp`), R16, D6.1.

**Lean:** `relocCol`, `transColumn`, `relocEntryCol`, `transEntry`, `relocCols`, `transCols`,
`nextHead`, `headAddr`, `rootLenOf`, `inQueryRegion`, `inRootSuffix`, `fMapDef`, `qMapDef`,
`qMap_eq_def`, `fMap_eq_def`, `stageRoles`, `roles_replaceAt`, `rep_stage`.
Planned file `Packet/OccurrenceMaps.lean`.
**Integration note:** At integration, SCR2: the definitions from `relocCol` to `qMapDef` moved verbatim into `Spine.lean` §c.8 and the spine's `qMap`/`fMap` are defined by them, so the bridges hold by `rfl`; `roles_map` moved to U1 D1.4b as `Tree.roles_map`.

**Difficulty:** M. The bodies are given; `roles_replaceAt` is about 150 LOC; `rep_stage` is
about 350 LOC of address arithmetic.

**Testable:** yes, and tested. `test_stage_roles.py` implements these formulas verbatim and
checks L6.2 part (i) on every case (§T).

### L6.2 Occurrence-map identity   (paper: txt:944-964)
**Fidelity:** repaired (R-3). The paper's "after n stages this is exactly Γ(E[n])" becomes:
- an explicit reading order;
- per-role transport of owned atoms, with the stage maps of L6.2a.

Order atoms are handled through the reading order (D6.1a item 2), not by maps. A map cannot
carry them, because consecutive old roles need not stay consecutive.

**Statement** (`occurrence_map_identity`; refines the spine's †). Let `H ≠ ∅`, `CondV H`,
`CondI H`, `stepKind H = some .ordinary`, `roleSets H = some rs`, `expand H n = some H'`.
Then:
1. (i) `H'.roles = rs.P ++ stageRoles 1 ++ … ++ stageRoles n`.
2. (ii) For `z ∈ rs.P`: `ownedBy (graph H') z` and `ownedBy (graph H) z` have the same members.
3. (iii) For `1 ≤ m ≤ n` and `x ∈ T :: Q`:
   `a ∈ ownedBy (graph H') (qMap m x) ↔ ∃ a₀ ∈ ownedBy (graph H) x, a = a₀.map (qMap m)`.
4. (iv) For `1 ≤ m ≤ n` and `x ∈ K`: the same with `fMap m`.

Moreover, `owned_reads`. **[Changed in verification:** it now assumes `InL H`.**]** Let `InL H`,
`stepKind H = some .ordinary` and `roleSets H = some rs`. Then:
- atoms owned by `T :: Q` read only `D ∪ {T} ∪ Q`;
- atoms owned by `K` read only `D` (txt:940-943).

Without `InL H` the statement is false: V alone does not keep the owner's active root entry
unconsumed. Counterexample: `H = [[], [(0, H₁)]]` with `H₁ = [[(1,∅)], [(2,J), (1,∅)]]` and
`J = [[(3, [[(4,∅)]])]]`.
- V, I, H and S hold, and A fails.
- The step is ordinary with `t = 3`, `r = 1` and an owner root.
- The scan consumes the only root entry (cursor `1` = root length), so `K = []`.
- The `T`-owned pair `elem A_⟨[(1,0)],0⟩ T` and the query edge of `U_⟨⟨[(1,0)],1⟩,0⟩` both read
  `A_⟨[(1,0)],0⟩ ∉ D ∪ {T} ∪ Q`.

Every consumer (U5 L8.6) has `InL H`.

Consequences, used by U5 in L8.6:
- (i) and `roles_nodup` (U1) make the maps injective on their domains and the stage blocks
  pairwise disjoint;
- (i) and D6.1a items 1–2 give the order atoms of `Γ(H')`;
- (ii)–(iv) cover every owned atom, because by (i) every role of `H'` is in `P` or is a stage
  image.

**Proof.**
1. Replace `expand` by `paperOp` (D1.6a `expand_eq_paperOp`). By R16 (`paperOp_ordinary`†)
   `H' = replaceAt 0 0 Z_1 ℓ H`, where `Z_{n+1} = ∅` and `Z_m` is built from head `m` and
   `Z_{m+1}` (txt:125-131).
2. (i): by `roles_replaceAt` (L6.2a) with `r = d = 0`, `H'.roles = rs.P ++ (Z_1.roles placed at
   sd.col)`. Then induct on `m` from `n` down to `1`, using:
   - head `m` = (`T_{r,(m−1)d}(Q)` ⌢ `U` with heights `T_{r,md}`);
   - in the body case, followed by `replaceAt r (md) Z_{m+1} (ℓ−j) (F[i+1:])`;
   - in the owner case, `replaceAt r (md) Z_{m+1} (ℓ−j−1)` in the last restored height.

   Apply `roles_map` and `roles_replaceAt` to each part. The roles of `Z_m` placed at `h_m` are
   `stageRoles m ++ (roles of Z_{m+1} placed at h_{m+1})`. Here the placement address `h_{m+1}`
   is the position of the hole, which is `nextHead h_m` by L6.2a. The order inside a stage
   matches `stageRoles`:
   - head column role, then its entries (`Q`-copy, then `U`-copy with their heights);
   - then the copied columns, in the body case;
   - the hole is the last position of the copied route, so `Z_{m+1}` follows every role of
     stage `m`.

   This order is the reading order of `K` itself. The `U`-entries come first, then the
   `F[i+1:]` content before `T`; `T` is the last role before `Q, N`, by R4.
3. (ii): a role `z ∈ P` keeps its address (step 2).
   - `lim z`: present on both sides.
   - `elem y z`: `z`'s predecessor column in its forest is the same, and still exists.
   - Edges of a slot `z`: the label is the same, since `shiftVal 0 0 = id`. The `rep` is the
     same, because `rep` depends only on the address (spine) and, for numbers `< z`'s column
     number, the stack consists of `P`-roles (`rep_visible`, D7.1a).
4. (iii)–(iv), owned atoms of a copy `z' = qMap m x` (resp. `fMap m x`):
   - `lim`: by (i).
   - `edge`: by `rep_stage` (L6.2a). The parent and both representatives of the copy are the
     mapped ones.
   - `elem y' z'`: by (i), the predecessor column of `z'` in its forest is the image of `x`'s
     predecessor. There are four cases:
     - `x ∈ Q` or `x ∈ K` internal: copied forests.
     - `x` = the first column of `F[i+1:]`: its predecessor is `R`, and `fMap m R = h_m`. This
       is the root-to-next-column pair.
     - `x = T` (`h_m`): if `T` has a predecessor `a` in its forest, the predecessor of `h_m` is
       `qMap m a = fMap (m−1) a`. This is the entering pair (txt:961-963). Otherwise neither
       has one.
     - The last stage `m = n` has no hole, so no `elem` pair is owned by `h_{n+1}`.
   - No other pairs exist: removed consumed sibling heights create no pair, since there is no
     `elem` between sibling height forests (D6.1).
5. `owned_reads`. Query edges read the stack of a column in `T :: Q`. Retained edges read the
   stack of a column in `K`. Numbers on these stacks resolve to `D ∪ {T} ∪ Q`, resp. `D`:
   - a consumed root entry is closed; its slot and height are off the stack after it.
     **[Changed in verification.]** The owner's active entry `u` cannot be consumed, which is
     where `InL H` is used. By the definedness part of capping (txt:233-236, U1 `barrier`†/R8 at
     the closing entry), the complete query `Z = ν(y_0,…,y_{|Q|−1})` satisfies `Z < B_R(u)`.
     U1 `cursor_nu` gives `rd.cursor = cursor (rootKeys) Z`; R7 then gives cursor `≤ u`, and
     consumed entries are those of index `< cursor` (spine `roleSets`). In the body case no root
     entry is active (R5);
   - sibling heights are invisible;
   - `Q`, `N` come after `T`.

**Uses:** L6.2a, D6.1, D6.1a, D7.1a (`rep_visible`), D1.6a, R4, R5, R7, R8, R16, U1
`roles_nodup`†, U1 `cursor_nu` (D2.1/L2.1). **[Changed in verification:** R7, R8, `cursor_nu`
added for `owned_reads`.**]**

**Lean:** `occurrence_map_identity`, `owned_reads`. Planned file `Packet/OccurrenceMaps.lean`.

**Difficulty:** L. The structural induction over the nested hole carries addresses at every
depth, about 1,200 LOC.

**Testable:** yes, and tested. `test_stage_roles.py` (§T): all standard expressions reachable
from `L_1…L_4` by ≤ 9 operations with parameters ≤ 3 and size ≤ 30 (8,992); every ordinary
case with `n ≤ 3` (30,172: 1,004 owner roots, 4,963 body roots in the stopping forest, 1,576
deeper body roots). Parts (i)–(iv): 0 failures. **[Changed in verification.]** The same script
was rerun with generation depth ≤ 40 and size ≤ 20: 92,700 expressions and 295,668 ordinary
cases (4,601 owner, 62,359 body/same forest, 6,957 body/deeper), with 0 failures. The
`owned_reads` counterexample is raw (A fails), so it lies outside these runs.

### L6.2b Graph of a deletion step   (paper: new; txt:96-97)
**Fidelity:** new (it supplies U5's T9.1a deletion case).

**Statement** (`graph_deletion`). If `stepKind E = some .deletion` and `expand E n = some E'`,
then:
- `E'.roles = E.roles.dropLast`;
- `a ∈ graph E' ↔ a ∈ restrictTo (graph E) E'.roles`.

**Proof.**
1. By `expand_deletion` (D1.6a), `E' = .node E.cols.dropLast`. The last column is empty, so its
   only role is its ordinary role, the last of `E.roles` (`rolesCols` unfolding).
2. Graph: the argument of D6.1a item 6, with the removed role being the last.

**Uses:** D1.6a, D6.1a.

**Lean:** `graph_deletion`. Planned file `Packet/OccurrenceMaps.lean`.

**Difficulty:** S.

**Testable:** yes, and tested. The roles part was checked on 246 deletion cases (§T).

### L6.2c Graph of a special step   (paper: new; txt:105-109, 1325-1340)
**Fidelity:** new (it supplies U5's L8.7 the output graph of a special step).

**Statement** (`graph_special`). Let `H ≠ ∅`, V, I, `stepKind H = some .special`,
`stopData H = some sd`, `sd.ownerEntry = some e`, and `expand H n = some H'`. Put
`ε = 1` if `e.idx = 0`, else `0` (`P = ∅`, txt:107). Put
`C := specialRoles H sd e`, the roles from `U_e` up to, but excluding, `T`. Then:
- `H'.roles = prefixRoles H e ++ concat_{x<n+ε} C.map (specialCopy e x)`;
- the owned atoms of `z ∈ prefixRoles H e` are unchanged;
- for `x < n+ε` and `y ∈ C`, the owned atoms of `specialCopy e x y` are the
  `specialCopy e x`-images of those of `y`.

**Proof.**
1. Reduce to `paperOp` (D1.6a). R17 (`paperOp_special`†) gives the output: `e`'s column
   `P ⌢ [(p, C ⌢ [[(a,∅)]])]` is replaced by `P ⌢ [(p,C)]^{n+ε}`, and nothing follows on the
   route.
2. Roles: `roles_map`, `rolesCol` unfolding. Copy `x` sits at index `e.idx + x`, which is
   `specialCopy`.
3. Owned atoms of a copy:
   - its heads have the same parent `p` and the same external `rep`
     (`rep_inside`, `rep_visible`; the external part of the stack is unchanged);
   - internal `(true,0)` reads give `(A_{e.col}, U_{copy})` (`rep_inside` part 2);
   - internal pairs are as in the original;
   - there is no pair between copies, since they are siblings (D6.1).

**Uses:** D1.6a, R17, L6.2a (`roles_map`, `transColumn`), D7.1a.

**Lean:** `specialRoles`, `specialCopy`, `graph_special`. Planned file
`Packet/OccurrenceMaps.lean`.

**Difficulty:** M (about 300 LOC).

**Testable:** yes, and tested: 1,203 special cases with `n ≤ 3`, all three parts, 0 failures
(§T).

### L6.2d Pre-stop prefixes are unchanged (`graph_prefix`)   (paper: txt:965-966)
**Fidelity:** as in paper (spine-named †).

**Statement** (`graph_prefix`). Under the hypotheses of L6.2, for every `x ∈ rs.P`:
- `rolesBefore H' x = rolesBefore H x`;
- `restrictTo (graph H') (rolesBefore H x)` and `restrictTo (graph H) (rolesBefore H x)` have
  the same members.

Consumers:
- U5 L8.6, where the transported old labels read `ι_k = id`;
- L7.5c, where `prefixRoles (Hk.truncAfter bm) bm = prefixRoles w.H bm`.

**Proof.**
1. Roles: by L6.2 (i), `rs.P` is a prefix of `H'.roles`, and `x ∈ rs.P`.
2. Atoms: by D6.1a item 1, split into order atoms and owned atoms.
   - Order atoms: D6.1a item 2, on a common prefix.
   - Owned atoms: L6.2 (ii). Every variable of an atom owned by a `P`-role lies in `P`, by
     D6.1a item 3 and the reading order of owners.

**Uses:** L6.2, D6.1a.

**Lean:** `graph_prefix`. Planned file `Packet/OccurrenceMaps.lean`.

**Difficulty:** S.

**Testable:** yes. It is implied by the tested parts (i)–(ii).

### L6.2e Stage form of the occurrence-map identity   (paper: txt:944-964)

**Fidelity:** new (requested by U5 R22, R23 at integration; the stage-by-stage form of L6.2 that
U5 L8.6 uses; formerly stubs `Req.stage_zero`, `Req.stage_succ`, `Req.queryAtoms_struct_vars`).

**Statement.** Let `H ∈ L` with `roleSets H = some rs`; write `q = qMap H (m+1) (m+1)` and
`f = fMap H (m+1) (m+1)`.
1. `stage_zero`: if `expand H 0 = some G`, then `G.roles = rs.P`, `graph G ⊆ graph H`, and
   `fMap H 0 0` is the identity on `rs.D`.
2. `stage_succ`: if `expand H m = some G` and `expand H (m+1) = some G'`, then
   `G'.roles = G.roles ++ (f(R) :: q(Q) ++ f(K))`; `q(T) = f(R)`; `q = fMap H m m` on `rs.D`; `f`
   is the identity on the roles before `R`; and every structural atom of `graph G'` lies in
   `graph G`, or is the `q`-image of a structural atom of `queryAtoms H rs`, or the `f`-image of an
   atom of `retAtoms H rs` (D6.1c).
3. `queryAtoms_struct_vars`: every structural atom of `queryAtoms H rs` reads only
   `rs.D ∪ {T} ∪ rs.Q`.

**Proof.**
1. *Setting.* `roleSets H = some rs` gives `stopData H` and `rootData H` (spine body), hence
   `stepKind H = some .ordinary` (spine body of `rootData`), and `H ≠ ∅`; `InL H` gives V and I.
   So L6.2 applies to `H` at every `n` with `expand H n = some _`.
2. *Item 1.* L6.2 (first clause) at `n = 0`: `H[0].roles = rs.P` (the stage list is empty).
   Every atom of `Γ(H[0])` is an order atom between consecutive roles of `rs.P`, which are
   consecutive in `H.roles` (`rs.P` is a prefix, spine body of `roleSets`), or is owned by a role of
   `rs.P` (D6.1a `graph_atom_cases`), and L6.2 (second clause) identifies the owned atoms with those
   of `Γ(H)`; so `graph H[0] ⊆ graph H` (D6.1a `graph_lt_iff`). `fMapDef H _ 0 = id` (spine body,
   SCR2).
3. *Item 2, roles.* L6.2 (first clause) at `n = m` and `n = m + 1`. The bodies `qMapDef H n k` and
   `fMapDef H n k` do not read `n` (spine body; L6.2a), so `stageRoles H (m+1) rs k =
   stageRoles H m rs k` for `k ≤ m`, and `H[m+1].roles = H[m].roles ++ stageRoles H (m+1) rs (m+1)`,
   which is `q(T) :: (q(Q) ++ f(K))` (L6.2a `stageRoles`). Both bodies send their head role to
   `ord h_{m+1}` at stage `m + 1`, so `q(T) = f(R)`.
4. *Item 2, maps.* For `x ∈ rs.D`: `x ∉ {T} ∪ Q` (`D` lies before `T`, spine body of `roleSets`),
   so the last branch of `qMapDef` gives `q x = fMapDef H _ m x`. For `x` before `R`: `x ≠ R`, `x`
   is not in a root entry and not in a column after the root (reading order; D6.1a), so every branch
   of `fMapDef` returns `x`.
5. *Item 2, atoms.* Let `a ∈ graph H[m+1]` be structural. Structural atoms are owned (D6.1a
   `atomOwner`); let `z` be the owner. If `z` is a role of `H[m]`, the owned atoms of `z` in
   `H[m+1]` and in `H[m]` agree: for `z ∈ rs.P` both are those of `Γ(H)` (L6.2, second clause), and
   for a stage `k ≤ m` both are the images of the same old atoms under the same maps (L6.2, third and
   fourth clauses, with step 3). If `z = q(x)` with `x ∈ {T} ∪ Q`, L6.2 (third clause) gives
   `a = a₀.map q` with `a₀` owned by `x` in `Γ(H)`; by L6.2 `owned_reads` (which needs `InL H`)
   `a₀` reads only `D ∪ {T} ∪ Q`, so `a₀` lies in `P ∪ {T} ∪ Q` (`D ⊆ P`) and involves `x`: it is in
   `queryAtoms H rs` (D6.1c). If `z = f(x)` with `x ∈ K`, L6.2 (fourth clause) gives `a = a₀.map f`
   with `a₀` owned by `x`, reading only `D` (`owned_reads`), structural and involving `x ∈ K`: it is
   in `retAtoms H rs`.
6. *Item 3.* A structural atom of `queryAtoms H rs` has all variables in `P ∪ {T} ∪ Q` and involves
   `T` or `Q`. If its owner is in `{T} ∪ Q`, L6.2 `owned_reads` gives the claim. Otherwise its owner
   is in `P`. An atom owned by a role `z` of `P` reads `z`, the column of `z` and, for an edge, the
   representatives of a visible number of `z`'s column (spine body of `graph`), and all of these are
   at or before `z` in reading order (D7.1b `frameOf_mem_prefix`, D1.2e item 3); `T` and the roles of
   `Q` come after every role of `P`. So this case does not occur.

**Uses:** D1.2e, D6.1, D6.1a, D6.1c, D7.1b, L6.2, L6.2a.

**Lean:** `Packet.stage_zero`, `Packet.stage_succ`, `Packet.queryAtoms_struct_vars`. Planned file
`Packet/OccurrenceMaps.lean`.

**Difficulty:** M (about 350 LOC given L6.2).

**Testable:** yes. U5's verifier tested items 1 and 2 against an explicit model of `q_m`, `f_m`
(`scratch/blueprint/U5-verify/test_u5.py 40 4000`: 9,219 role cases, 576,318 forward and 111,093
converse atom cases, with the corrected `retAtoms`) and item 3 (10,856 structural query atoms).
Re-running the same test with the spine bodies of `qMap`/`fMap` (real since integration) is open.

### L6.2f Block form of the graph of a special step   (paper: txt:105-109, 1325-1340)

**Fidelity:** new (requested by U5 R27 at integration; the special counterpart of L6.2e; formerly
the stub `Req.special_graph`).

**Statement.** `special_graph`: let `H ∈ L` have a special step, `stopData H = some sd`,
`sd.ownerEntry = some e` and `expand H k = some H'`. There are `N` and maps `cm i : BlkVar → Role`
such that:
- `H'.roles = P(H,e) ++` the concatenation over `i < N` of `cm i` applied to
  `owner :: (specialKey H e).roles.map inner`;
- every `cm i` agrees with `frameOf e` on the frame variables;
- every structural atom of `graph H'` lies in `graph H` with all its variables in `P(H,e)`, or is
  `a'.map (cm i)` for some `i < N` and `a' ∈ posBlock (specialKey H e) (entrySel H e)`.

**Proof.**
1. Take `N = k + ε` with `ε = 1` iff `e.idx = 0`, and `cm i = blockMap ⟨e.col, e.idx + i⟩` (spine
   §c.9). U5's verifier tested exactly this choice.
2. *Roles.* L6.2c `graph_special` gives `H'.roles = P(H,e) ++` the concatenation over `x < k + ε`
   of `(specialRoles H sd e).map (specialCopy e x)`. `specialRoles H sd e` is `U_e` followed by the
   roles of `e`'s height before the stopping column; the stopping column is the last column of that
   height (D1.6d `ownerEntry_mem`), so by D1.2e item 1 these are `U_e` and the roles of the height
   without its last column, placed under `e.heightPath`. By D1.4b `relKey_roles` the latter are
   `(specialKey H e).roles.map (Role.under e.heightPath)`. `specialCopy e x` (L6.2c, through L6.2a
   `transColumn`) moves entry `e` to `⟨e.col, e.idx + x⟩`, and on these roles it agrees with
   `blockMap ⟨e.col, e.idx + x⟩` applied to `owner` resp. `inner r` (spine bodies; D7.1a:
   `relRole ∘ Role.under = id`).
3. *Frames.* All copies lie in column `e.col`, and `frameOf` depends only on the column (spine
   body), so D7.1b `blockMap_frame` gives the agreement.
4. *Atoms.* L6.2c (second and third clauses): the atoms owned by roles of `P(H,e)` are those of
   `Γ(H)`, whose variables lie in `P(H,e)` (D6.1a `graph_vars_roles` with D7.1b
   `frameOf_mem_prefix` for the representatives); the atoms owned by a copied role are the
   `specialCopy`-images of the atoms owned by the original role in `Γ(H)`. The atoms owned by `U_e`
   and by the roles of the shortened height are the `blockMap e`-images of
   `posBlock (relKey (e.col.num 0) (height)) (entrySel H e)` restricted to the shortened height
   (D7.1a `graph_owned_block` and `freeBlock_graph` with `takeCols`); removing the last column
   `[(a, ∅)]` removes exactly its own atoms, which leaves the images of
   `posBlock (specialKey H e) (entrySel H e)`. Transport by `specialCopy e x` gives the `cm x`-images.

**Uses:** D1.2e, D1.4b, D1.6d, D6.1a, D6.1c, D7.1, D7.1a, D7.1b, L6.2a, L6.2c.

**Lean:** `Packet.special_graph`. Planned file `Packet/OccurrenceMaps.lean`.

**Difficulty:** M (about 250 LOC).

**Testable:** yes. Tested by U5's verifier as R27 with `cm i = blockMap ⟨e.col, e.idx+i⟩` and
`N = n + ε` on 696 special inputs (2,784 role cases, 94,462 structural atoms, 0 failures).

### D6.1b Graph transport along the surviving-role map of an anchor   (paper: new; txt:1107-1110, 1416-1421)
**Fidelity:** new (R-3). This is the one place where `Γ(anchor E cap)` is compared with `Γ(E)`.

**Statement** (`graph_origin`). Let `InL E` and `cap : Option (AdmCap E)`. Write
`χ := anchorOrigin E cap`, `χ̂ := anchorD E cap` (the totalized `χ`), and
`Rng := originRange E cap`.
1. For every atom `a` with an owner:
   - `(∃ a₀ ∈ graph (anchor E cap), every variable of a₀ has a χ-origin, and a = a₀.map χ̂)`
   - holds iff `a ∈ graph E` and every variable of `a` is in `Rng`.
2. If `x <_{anchor} y` and both have origins, then `χ̂ x <_E χ̂ y`.

**Proof.**
1. For `cap = none`, `χ = some` and everything is the identity.
2. For `cap = some w`, use R10 (`origin_spec`). Its clauses: injective; the closing slot is the
   only role without an origin; ordinary roles go to ordinary roles; labels and `ord e.col` are
   preserved for slots; printed numbers are preserved; `rep` commutes with `χ̂`; order is
   preserved.
   - `lim`: R10 injectivity and range.
   - `elem (A_c) (A_{c+1})`: consecutive columns of one forest. The forest survives, since
     moves delete only entries. Its consecutive columns have consecutive origins: R10 maps
     `ord` to `ord` with the same printed number, and in one forest consecutive columns have
     consecutive numbers. In the converse direction, two consecutive columns of `E` in `Rng`
     are images of consecutive columns, by injectivity and the same number argument.
   - `edge (U_e)(A_{e.col}) o`/`v`: the label of `e` equals that of its origin, and `rep`
     commutes (R10). Both directions follow.
   - Item 2 is R10's order clause.

**Uses:** R10, D6.1, D6.1a.

**Lean:** `anchorD`, `originRange`, `graph_origin`. Planned file `Packet/Graph.lean` (imports
`Closure`).
**Integration note:** At integration, SCR2: `anchorD` moved verbatim into `Spine.lean` §c.11, because the spine body of `ScanSetup.Valid` uses it.

**Difficulty:** M (about 300 LOC, given R10).

**Testable:** yes for literal caps (no moves) with the scripts of §T. With moves, it needs U2's
`applyMove` body.

---

# Part B — §7.1: names, frames, blocks

### D7.1 Names, charts, frames, blocks, Cert_B, No_B   (paper: txt:1017-1044)
**Fidelity:** simplified (S-4). Certificates are in ordinal form. `Cert_B(z; ρ, c⃗, L)` in `J_u`
is `BlockAbove P (posBlock K sel) fr L u`, and `No_B` is `Atom.noReal` (spine §c.7
translation table).

**Statement.** These are spine definitions with real bodies:
- `Name := role tag r | aux k`;
- `Frame V := {host, reps}`, `Frame.map`, and `frameOf e := ⟨A_{e.col}, e.col.reps0⟩`.
  `reps0` lists `rep 0 e.col q` for every `q < e.col.num 0`; every such `q` resolves, since the
  visible numbers of a column form the interval `0…num−1` (`resolveAux`);
- `BlkVar := host | ord q | cur q | owner | inner r` and `Frame.toFr`;
- `freeBlock K`, `posBlock K sel`, and `noB K sel fr u L := Atom.noReal (posBlock K sel) fr.toFr u L`.

A **chart** is a map `Role → Name`, injective on the relevant role list. "Different charts overlap
only on explicitly shared names" is realized by the constructors of D7.2c/L7.5b/L7.5c/L7.6a. Each
of them names every role by an explicit `if` on a role list, with fresh tags elsewhere.

**Proof.** Definitions only.

**Uses:** D1.2, N4.1 (U4: `BaseAtom`, `Atom`, `BlockAbove`).

**Lean:** `Packet.Name`, `Frame`, `Frame.map`, `frameOf`, `BlkVar`, `Frame.toFr`, `freeBlock`,
`posBlock`, `noB` (spine §c.9); `Hier.Atom.noReal` (U4). Planned file `Packet/Names.lean`.

**Difficulty:** S.

**Testable:** yes. `freeBlock` is computable and is checked in D7.1a.

### D7.1a Frames and blocks read inside a tree   (paper: new; txt:1028-1032, 1087-1092, 1235-1237)
**Fidelity:** new (R-3). It is the bridge between block problems and graphs: "equal relative keys
give the same free problem" (txt:1235-1237).

**Statement.** Let `e` be an entry with host `a := e.col.num 0`, and let `d` be a column with
`e.heightPath <+: d.path`.
1. `rep_inside`:
   - (a) `d.rep 0 q = e.col.rep 0 q` for `q < a`;
   - (b) `d.rep 0 a = some (A_{e.col}, U_e)`;
   - (c) for `w ≥ 1`, `d.rep 0 (a + w) = ((relCol e d).rep 1 w).map (Role.under e.heightPath)²`;
   - (d) `d.num 0 = a + (relCol e d).num 1`.
2. `rep_visible`: if `c.resolve 0 (o.num 0) = some o`, then `o.rep 0 q = c.rep 0 q` for every
   `q < o.num 0`.
3. Define `blockMap e`:
   - `host ↦ A_{e.col}`;
   - `ord q ↦ (e.col.rep 0 q).1` and `cur q ↦ (e.col.rep 0 q).2`;
   - `owner ↦ U_e`;
   - `inner r ↦ Role.under e.heightPath r`.

   Let `X := F.heightAt e`, `sel :=` the parent of `e`, and let `F` satisfy V with
   `e ∈ F.entryAddrs`.
   - `freeBlock_graph`: for every `m`, every atom of
     `freeBlock (relKey a (takeCols X m))` mapped by `blockMap e` is in `graph F`.
   - `posBlock_heads_graph`: the same for `posBlock (relKey a X) sel`.
4. `graph_owned_block`: every atom of `graph F` owned by `U_e`, or by a role under
   `e.heightPath`, is `a₀.map (blockMap e)` for some `a₀ ∈ posBlock (relKey a X) sel`.

**Proof.**
1. Item 1 (a), (b), (d): unfold `resolveAux` and `container`. `d.path = e.heightPath ++ ρ`, and
   the levels of `e.heightPath` are scanned first (computation on `List.drop`/`take`).
2. Item 1 (c): `resolveAux` started at `start = a + 1` on the relative path equals the relative
   `resolveAux` with base `1`, shifted by `a` (induction on `ρ`).
3. Item 2:
   - (a) The numbers `< o.num 0` on `o`'s stack are a prefix of `c`'s stack (`resolveAux`).
   - (b) Container agreement. Suppose `q` contains `o`. Since `o` is on `c`'s stack, the
     container entry of `q` on `o`'s path is on `c`'s path. Suppose instead that `q` does not
     contain `o` and `q < o.num`. Then `q` does not contain `c`: otherwise `o`, being visible
     from `c` with a larger number, would lie inside `q`'s container.
4. Item 3 and item 4, by cases on the atoms:
   - `lim` atoms and the strict chain: `U_e` is immediately followed by the roles of `X` in
     reading order (`rolesCol`). The chain `owner, r_1, r_2, …` of `freeBlock` maps to
     consecutive roles. `takeCols X m` gives an initial segment of these roles.
   - `elem`: consecutive internal columns.
   - Edges with label `(false, q)`, `q < a`: by item 1 (a), `frameOf e` gives
     `(ord q, cur q) ↦ e.col.rep 0 q = d.rep 0 q`.
   - Edges with label `(true, 0)`: by item 1 (b), `(host, owner)`.
   - Edges with label `(true, v+1)`: by item 1 (c) with `w = v+1`. `relKey a` turns the parent
     `a+w` into `(true, w)`.
   - The two added atoms of `posBlock`: `U_e`'s own heads, with the parent `sel < a` read on
     `e.col`'s stack.
   - Item 4: `graph_atom_cases` (D6.1a) and the same case list read backwards.

**Uses:** D1.2, D7.1, D6.1, D6.1a.

**Lean:** `relRole`, `relCol`, `rep_inside`, `rep_visible`, `takeCols`, `freeBlock_graph`,
`posBlock_heads_graph`, `graph_owned_block`. Planned file `Packet/Names.lean` (section Frames).
**Integration note:** At integration, SCR-1 of U5: the draft's U3 definitions `underRole` and `blkRole` became the spine definitions `Role.under` (§c.2) and `Packet.blockMap` (§c.9), with the same bodies, and this unit's text now uses the spine names.

**Difficulty:** M (about 400 LOC).

**Testable:** yes, and tested:
- `test_blocks.py`: for every entry of 3,502 standard expressions (38,754 entries), the image of
  `posBlock` equals the union of the owned atoms; the chain is consecutive; `rep_inside` (a),
  (b) hold;
- `rep_visible`: 273,040 instances.

0 failures (§T).

### D7.1b Frames of nested columns; frames in the prefix   (paper: new; txt:1024-1032)

**Fidelity:** new (requested by U5 R10, R18 (second conjunct) and R19 at integration; formerly the
stubs `Req.reps0_take`, `Req.reps0_length`, `Req.graph_block`, `Req.frameOf_mem_prefix`).

**Statement.**
1. `blockMap_frame`: `(frameOf e).toFr w = some x → blockMap e w = x`.
2. `reps0_length`: `c.reps0.length = c.num 0`; `reps0_getElem?`: `c.reps0[q]? = c.rep 0 q`.
3. `reps0_take`: `d.resolve 0 (c.num 0) = some c → d.reps0.take (c.num 0) = c.reps0`.
4. `frameOf_mem_prefix`: for `e ∈ E.entryAddrs`, `A_{e.col} ∈ P(E,e)`, and both components of every
   pair of `e.col.reps0` lie in `P(E,e)`.

The first conjunct of U5's R18 (`graph_block`: the attached positive block, mapped by `blockMap e`,
lies in `Γ(E)`) is D7.1a `posBlock_heads_graph`; `entryKey` and `entrySel` (D6.1c) unfold to its
key and selector.

**Proof.**
1. *Item 2.* `c.reps0 = (List.range (c.num 0)).filterMap (c.rep 0)` (spine). For `q < c.num 0`,
   `c.resolve 0 q` is `some` (D1.2b `resolve_isSome_iff`), so `c.rep 0 q` is `some` (spine body of
   `rep`), and `filterMap` keeps every element: length `c.num 0`, and `c.reps0[q]? = c.rep 0 q`. For
   `q ≥ c.num 0` both sides are `none` (`resolve_isSome_iff`).
2. *Item 1.* `toFr host = some A_{e.col} = blockMap e host`. `toFr (ord q) =
   ((frameOf e).reps[q]?).map Prod.fst = (e.col.rep 0 q).map Prod.fst` by item 2, and
   `blockMap e (ord q)` is its `getD`, which is `x` when it is `some x`; `cur q` likewise with
   `Prod.snd`; `toFr` is `none` on `owner` and `inner` (spine `Frame.toFr`).
3. *Item 3.* `c.num 0 < d.num 0` (D1.2b `resolve_lt`). By item 2 the left side is the list of
   `d.rep 0 q` for `q < c.num 0` and the right side the list of `c.rep 0 q`; D7.1a `rep_visible`
   (with its `c := d`, `o := c`) gives `c.rep 0 q = d.rep 0 q` for every `q < c.num 0`.
4. *Item 4.* `A_{e.col} ∈ P(E,e)` is D1.2e item 3. Every pair of `e.col.reps0` is
   `e.col.rep 0 q = (A_o, x)` with `q < e.col.num 0` and `o = e.col.resolve 0 q`, so
   `e.col.OnStack o` (D1.2b `resolve_spec`); `x = U_{e'}` if `o.container e.col = some e'`, so
   `e'.Contains e.col` (D1.2b `contains_iff_container`), and `x = A_o` otherwise. D1.2e item 3
   places `A_o` and `U_{e'}` in `P(E,e)`.

**Uses:** D1.2b, D1.2e, D7.1, D7.1a.

**Lean:** `Packet.blockMap_frame`, `Packet.reps0_length`, `Packet.reps0_getElem?`,
`Packet.reps0_take`, `Packet.frameOf_mem_prefix`. Planned file `Packet/Names.lean`.

**Difficulty:** S (about 120 LOC).

**Testable:** yes. U5's verifier tested `reps0_length` (42,985 columns), `reps0_take` (234,078
pairs), `graph_block` (964,959 cases) and frames in the prefix (60,894 entries) before integration.

### N3.1 Finite-name amalgamation and packing   (paper: new; S-6; txt:1061-1065, 1074-1078, 1115-1117)
**Fidelity:** simplified (S-6). The paper's "finite packing" becomes ordinal facts.

**Statement.**
1. `BaseAtom.holds_map`, `baseHolds_map`, `Diagram.holds_map`:
   `(D.map f).Holds P a ↔ D.Holds P (a ∘ f)`.
2. `Diagram.holds_append`.
3. `Diagram.holds_congr`: the truth of `D` depends only on the values of `D.vars`.
4. `Diagram.amalgamate`: `D₁` at `a₁` and `D₂` at `a₂`, with `a₁ = a₂` on shared variables, give
   `D₁ ++ D₂` at the glued assignment.
5. `pack_below`: if `IsLim u`, `L < u` and `l` is a finite list of values `< u`, then some `β`
   has `L ≤ β < u` and `l < β`.

**Proof.**
1. Item 1, `base`: by cases on `BaseAtom`. `noReal`:
   `((fr x).map f).map a = (fr x).map (a ∘ f)` (`Option.map_map`).
2. Item 2: `List.forall_mem_append`.
3. Item 3:
   - `base` atoms read only their `vars`.
   - For `noReal D fr u L`: its `vars` are `u`, `L` and `(baseVars D).filterMap fr`. A witness
     `β` for `BlockAbove` can be modified outside `baseVars D` to meet the frame equations for
     the other assignment, since `BaseHolds P D β` reads only `baseVars D`. Hence the
     `BlockAbove` instance is equivalent.
4. Item 4: items 2 and 3, using `if x ∈ D₁.vars`.
5. Item 5: put `β := max(L, (l.foldr max 0) + 1)`. `Order.IsSuccLimit u` gives `x + 1 < u` for
   `x < u` (`Order.IsSuccLimit.succ_lt`, `Ordinal.add_one_eq_succ`).

**Uses:** N4.1 (U4 grammar).

**Lean:** `Hier.BaseAtom.holds_map`, `Hier.baseHolds_map`, `Hier.Diagram.holds_append`,
`Hier.Diagram.holds_map`, `Hier.Diagram.amalgamate`, `Packet.pack_below`. Planned file
`Packet/Names.lean` (section Amalgamation).
**Integration note:** At integration: the congruence lemma of item 3 is U4 N4.1a `Hier.Diagram.holds_congr`, and U3's duplicate is removed; the other `Hier.*` names, which the draft had placed by mistake under `Packet.Hier.*`, are now declared as `BTBMS.Hier.*`.

**Difficulty:** S.

**Testable:** no (ordinal semantics over an abstract `Prims`).

---

# Part C — §4: records

### D4.1 Scan, descendant and repair records   (paper: txt:646-663)
**Fidelity:** repaired (G-003). Records are explicit finite structures with constructors carrying
anchor, indices and move list. The original target address `b` and the current source address
`a` are distinct fields (X-04).

**Statement.** These are spine definitions:
- `RecKind E := scan cap i j | desc cap i j | repair ms`;
- `SrcRecord := {E, b, F, a, kind}`;
- accessors `tgtHeight`, `srcHeight`, `tgtKey = relKey t B`, `srcKey = relKey r A'`, and
  `tgtSel` (the parent of `b`).

Correspondence with txt:650-658:
- item 1 (scan) is `scan cap i j`:
  - "names an ordinary input H" is `cap`, with `H = anchor E cap`;
  - "its complete terminal query" is the stop data of `H`;
  - "its actual source index" is `i`, with query index `j`;
- item 2 (descendant) is `desc`;
- item 3 (repair) is `repair ms`. "Each move records the old and new address, common parent,
  retained later entry, and deleted closed blocks": the `Move` fields and U2's
  `RepairList`/`moveAddr`.

**Proof.** Definitions.

**Uses:** D3.1a (U2: `AdmCap`, `Move`).

**Lean:** `Packet.RecKind`, `SrcRecord`, `SrcRecord.tgtHeight`, `srcHeight`, `tgtKey`, `srcKey`,
`tgtSel` (spine §c.10). Planned file `Packet/Records.lean`.

**Difficulty:** S.

**Testable:** yes (finite data).

### D4.1a Admission and the first-difference classifier   (paper: txt:646-663, 1357-1382; spine-new)
**Fidelity:** repaired (G-003).
- Admission is the spine's real-bodied `SrcRecord.Admitted`. It has the common clauses:
  standard `E`; `b`, `a` entries; `InL F`; `F` truncated after `a`; strictness.
- The kind clauses are `AnchorAt` (ordinary anchor, origin of the query slot, `ReachesGT`,
  closedness), `anchorSrc`, and the `truncAfter`/`setHeight` equations. For repair records they
  are `RepairList` and `moveAddr`.
- U3 adds the classifier body and its specification.

**Statement.**
1. Classifier (`firstDiffDef`, real body; SCR2 makes it the spine's `firstDiff`).
   - The walker `fdForest t π top`, `fdCols`, `fdCol` compares `tgtKey` with `srcKey` exactly in
     the order of `Tree.cmp`: labels, then heights, then the rest of the column; columns
     lexicographically.
   - It tracks the absolute address `π` in `E`, starting at `b.heightPath`. On entering entry
     `k` of column `ci` it appends `(ci, k)`.
   - It returns:
     - `wholeEnds` when the outer target column list ends first;
     - `childEnds π` when an inner target forest ends first;
     - `capAt ⟨π,ci⟩ k (labelAbs t l)` when the target column `ci` ends at `k` while the source
       has an entry with label `l`, or when the target label at `k` is smaller than the source
       label `l`. Here `labelAbs t (false,q) = q` and `labelAbs t (true,v) = t + v` (spine
       §c.10).
   - `stop` (target larger) and `same` default to `wholeEnds`. Admission excludes them (item 2).
2. `firstDiff_spec`. If `rk.Admitted`, with `cutBefore` as in `U3.lean` (the containing
   structure along a path, earlier columns, and optionally the first `k` entries):
   - `wholeEnds` ⇒ `tgtKey.cols` is a proper prefix of `srcKey.cols`.
   - `childEnds π` ⇒ `π = b.heightPath ++ ρ` with `ρ ≠ []`. The forests `X` (target) and `Y`
     (source) at `ρ` exist, and `|X.cols| < |Y.cols|`. The two keys agree on
     `cutBefore ρ |X.cols| none`.
   - `capAt c k p` ⇒ `c.path = b.heightPath ++ ρ`. The keys agree on
     `cutBefore ρ c.col (some k)`, and column `⟨ρ, c.col⟩` exists in `tgtKey`. Then either the
     target has no entry `k` and the source entry `k` has label `l` with `p = labelAbs t l`, or
     both have entry `k` with `l₁ < l₂` and `p = labelAbs t l₂`.

**Proof** (of item 2).
1. Strictness `tgtKey < srcKey` (Admitted) means `Tree.cmp keyLabelCmp tgtKey srcKey = .lt`
   (`Key.instLinearOrder`).
2. Mutual induction on `tgtKey` following `fdForest`/`fdCols`/`fdCol`. Each `same` result
   corresponds to an `.eq` comparison of the processed parts (unfold `Tree.cmp`, `cmpCols`,
   `cmpCol`, `Ordering.then`). Each `diff` result corresponds to the first `.lt` decision,
   which is the stated case. A `.gt` decision (`stop`) would make `cmp = .gt`, contradicting
   step 1. `same` overall would give `.eq`, also contradicting step 1.
3. The invariant "the parts processed so far agree" is exactly the equality of `cutBefore` at
   the current position (unfold `cutBefore`).

**Uses:** D4.1, D1.4 (`Key.instLinearOrder`, U1 proofs).

**Lean:**
- spine: `SrcRecord.AnchorAt`, `SrcRecord.anchorSrc`, `SrcRecord.Admitted`,
  `SrcRecord.FirstDiff`;
- U3: `labelAbs`, `FDStep`, `fdForest`, `fdCols`, `fdCol`, `firstDiffDef`,
  `firstDiff_eq_def` (SCR2), `cutBefore`, `firstDiff_spec`.

Planned file `Packet/Records.lean`.

**Integration note:** SCR2 applied: the definitions from labelAbs to firstDiffDef moved verbatim
into `Spine.lean` §c.10, and the spine's `SrcRecord.firstDiff` is `firstDiffDef`. The spine text now
writes the type as `Packet.SrcRecord.FirstDiff`.

**Difficulty:** M. `firstDiff_spec` is about 300 LOC of mutual induction.

**Testable:** yes. The walker was unit-tested on constructed keys in all three classes and run on
every reachable scan record (§T).

### D4.1b Basic facts about admitted records   (paper: new; txt:650, 655, 1054-1057)
**Fidelity:** new.

**Statement.** If `rk.Admitted`:
1. `admitted_hosts`: `r ≤ t`, with `r = t` for repair records and `r < t` for scan and
   descendant records.
2. `admitted_src_ne`: `srcHeight ≠ ∅`.

**Proof.**
1. Scan and descendant records:
   - `a = ⟨rd.col, i⟩` and `rd.col.num 0 = sd.r` (R5);
   - `b` is the origin of `⟨sd.col, j⟩`, with `b.col.num 0 = sd.t`: R4 for `cap = none`, and
     R15 (`origin` preserves `num`) otherwise;
   - `sd.r < sd.t` by V on the closing entry (R4: the closing entry `(r, ∅)` is an entry of
     column `sd.col`).
2. Repair records: `a = moveAddr ms b`, and R19 (`moveAddr_num`) gives
   `(moveAddr ms b).col.num 0 = b.col.num 0`. **[Changed in verification:** R12 assumes an
   `AdmCap` and its moves; an admitted repair record carries only a `RepairList`. A move rewrites
   only entry indices, and `ColAddr.num` reads only column indices.**]**
3. Item 2: `relKey r ∅ = ∅` (map of `.node []`), and `∅` is least
   (`Forest.empty_lt`-style for keys: `Tree.cmp` with an empty column list). So
   `tgtKey < srcKey` forces `srcKey ≠ ∅`.

**Uses:** D4.1a, R4, R5, R15, R19.

**Lean:** `admitted_hosts`, `admitted_src_ne`. Planned file `Packet/Records.lean`.

**Difficulty:** S.

**Testable:** yes (finite).

### L4.2a The label map κ and key transfer   (paper: txt:667-670)
**Fidelity:** new (split from L4.2's proof). This is the paper's "κ map": "the common relative
prefix shifts internal numbers by t − r and fixes parents below r".

**Statement.** Put `kappa r t (false, q) = (false, q)` if `q < r`, else `(false, q + (t−r))`.
Put `kappa r t (true, v) = (true, v)`.
1. `kappa_cmp`: for `r ≤ t`, `keyLabelCmp (κ x) (κ y) = keyLabelCmp x y`. So κ is an order
   embedding of labels.
2. `keyCmp_map`: every label map preserving `keyLabelCmp` preserves `keyCmp` on keys.
3. `relKey_kappa`: if `r ≤ t`, `r ≤ s` and `relKey r X = relKey t Y`, then
   `(relKey s X).map κ = relKey (s + (t−r)) Y`.
4. `relKey_kappa_low`: if `s ≤ r`, then `(relKey s X).map κ = relKey s X`.

**Proof.**
1. Item 1: case split on the two labels (four cases), using `q < r ≤ q'` ⇒ `q < q' + (t−r)`.
2. Item 2: mutual induction on keys along `Tree.cmp`/`cmpCols`/`cmpCol` and
   `Tree.map`/`mapCols`/`mapCol`. U1 proves the special case behind `relKey_lt_iff`; reuse its
   proof if U1 states the general form.
3. Item 3: mutual induction on `X` and `Y` simultaneously (the equal `relKey`s force equal
   shapes). At a label `qx` of `X` and `qy` of `Y`, `relKey r`/`relKey t` equality gives one of
   two cases:
   - `qx < r`, `qy < t`, `qx = qy`;
   - `qx ≥ r`, `qy ≥ t`, `qx − r = qy − t`.

   Then compute both sides at threshold `s` (three subcases: `qx < r`, `r ≤ qx < s`, `qx ≥ s`).
4. Item 4: every false label of `relKey s X` has value `< s ≤ r`, so κ fixes it; true labels are
   fixed.

**Uses:** D1.4.

**Lean:** `Packet.kappa`, `kappa_cmp`, `keyCmp_map`, `relKey_kappa`, `relKey_kappa_low`. Planned file
`Packet/FirstDifference.lean`.

**Difficulty:** S (about 150 LOC).

**Testable:** yes (random keys; `decide` on small instances).

### L4.2b Scan word facts for caps, moves and descendants   (paper: txt:675-676, 680-681, 289-293)
**Fidelity:** new (split from L4.2's proof).

**Statement.** Over `List (WithTop Key)`:
1. `capped_block_resp`: suppose the query `W` contains no `⊤` and `|ppre| = |pre|`. Then the
   response of the key list `pre ++ blk ++ [⊤]`, with parents `ppre ++ replicate (|blk|+1) p`,
   equals the response of `pre ++ [⊤]` with parents `ppre ++ [p]`. This is "a capped same-parent
   block answers like one capped entry".
2. `cursor_raise`: if `cursor (pre ++ [x]) W ≤ |pre|` and `x ≤ x'`, then
   `cursor (pre ++ x' :: post) W = cursor (pre ++ [x]) W`. This is "raise an unconsumed key and
   restore unread later entries".

`cappedAt ks u := ks.take u ++ [⊤]`.

**Proof.**
1. Item 1: induction on `pre` and `W` along `Scan.cursor`'s equations. While in `pre`, both scans
   take identical steps. At the block, the first scan stays inside `[|pre|, |pre|+|blk|]`,
   because `⊤ ≤ y` fails for `y ≠ ⊤`, so `⊤` is never passed. The second scan stays at `|pre|`.
   Both parent lists give `p` there. If the scan stops in `pre`, the cursors coincide.
2. Item 2: induction along `cursor`. Up to index `|pre|` both scans are identical. At `|pre|` the
   first scan never advances the source (hypothesis), so every remaining query letter `y`
   satisfies `y < x` (if `x ≤ y` the source cursor would advance). Then `y < x ≤ x'`, so the
   query is exhausted at `|pre|` in both.

**Uses:** D2.1 (`Scan.cursor`).

**Lean:** `cappedAt`, `capped_block_resp`, `cursor_raise`. Planned file
`Packet/FirstDifference.lean`.

**Difficulty:** S (about 120 LOC).

**Testable:** yes (finite words).

### L4.2c Path transfer: the new parent is on the target's actual cut chain   (paper: txt:667-681)
**Fidelity:** new. This splits L4.2's proof into explicit phases. It repairs the compressed
argument (C-06-style; X-04).

**Statement** (`firstDiff_path`). If `rk.Admitted` and `firstDiff rk = capAt c k p`, then
`Path E (actualKeys E) c W x p`, where `W = cutQuery (actualKeys E c) k` and
`x = cutStart E c k`. Here `cutStart` is the start vertex of `CondAK`:
- `c.num 0 − 1` if `k = 0`;
- the parent of entry `k−1` otherwise.

**Proof.** Notation:
- `ρ_`, `l` and the column `c = ⟨b.heightPath ++ ρ_, j⟩` from D4.1a item 2;
- `c' := ⟨a.heightPath ++ ρ_, j⟩`, the corresponding source column of `F`;
- `p' := labelAbs r l`, the source parent of entry `⟨c',k⟩`;
- `σ y := y` for `y < r`, and `σ y := y + (t−r)` for `y ≥ r`;
- `ks_X := actualKeys X`.

0. **Source test.** `InL F` (Admitted) gives `CondA F` at `c'`, entry `k`. So there is a
   `Path F ks_F c' W' x' p'` with `W' = cutQuery (ks_F c') k` and `x' = cutStart F c' k`.
   Turn the `ReflTransGen` into a list of edges `x' = y_0 → … → y_L = p'` (Mathlib
   `List.relationReflTransGen_of_exists_chain` or induction). The vertices strictly decrease
   (V in `F`).
1. **Queries.**
   - For `e < k`: `ks_E c [e] = (ks_F c' [e]).map κ`. This is L4.2a item 3, with
     `s = c'.num 0 ≥ r + 1` and the equality of relative keys of the entries `e`, from the
     `cutBefore` equality (D4.1a item 2); `c.num 0 = c'.num 0 + (t − r)` by `rep_inside`
     item (d) on both sides.
   - Hence `W = W'.map κ`, by R9 (`nu_map`) with L4.2a item 1.
   - `x = σ x'`: for `k = 0` by the `num` relation; for `k > 0` because the parent label of
     entry `k−1` is common, and `labelAbs t = σ ∘ labelAbs r` on labels whose false values are
     `< r`.
2. **Internal edges** (all `y_s > r` up to the step considered). By induction on `s`, the target
   chain from `x` at `W` reaches `σ y_s`. Let `o'` be the column that `y_s` resolves to on
   `c'`'s stack. It is internal to `A'` (`rep_inside` item (c)). Its target twin is
   `o := relocEntryCol a b o'`, and `σ y_s` resolves to `o` on `c`'s stack.
   - (a) `o'` is not a containing column of `c'`. Then all of its entries lie in the common part
     (`cutBefore` keeps the earlier columns of every containing forest). Their keys satisfy
     `ks_E o = (ks_F o').map κ` (L4.2a item 3). By U1 `trace_map`† (L2.5 (1)) with κ, the
     cursors coincide. The responses correspond under `σ`, since the labels are common.
   - (b) `o'` contains `c'`, with active entry `u`.
     - Source barrier: R8 in `F` at `(c', k)`.
     - Target barrier: R8 in `E` at `(c, k)`. It applies because the target chain reaches
       `σ y_s` by the induction hypothesis, and `E` is in L by `std_inL`.
     - These give `W' < B^F_{o'}(u)` and `W < B^E_o(u)`.
     - R7 then gives `cursor = cursor (cappedAt · u)` on both sides.
     - The capped lists correspond under κ, with `⊤ ↦ ⊤`: entries `< u` are common.
     - `trace_map` gives equal cursors `≤ u`.
     - The responses are the parents of the entry at the cursor. These are common labels: for
       a cursor `< u` an earlier entry; for a cursor `= u` the containing entry's label, which
       lies in the common part.
3. **Case `p' ≥ r`.** Every `y_s ≥ p' ≥ r`, so step 2 applies to every edge.
   - If `p' > r`: the target chain reaches `σ p' = p`.
   - If `p' = r`: the last edge enters `r`, and its target twin enters `σ r = t = labelAbs t
     (true, 0) = p`.
4. **Case `p' < r`.** Let `s*` be the first index with `y_{s*} ≤ r`.
   - (a) `y_{s*} < r` (a direct exit). The exit edge's label is false and common, so the target
     chain reaches `y_{s*}` (step 2's argument, last edge).
   - (b) `y_{s*} = r`. The target chain reaches `t` (step 3's last-edge argument). Then:
     - Repair records: `r = t`, nothing to do.
     - Scan and descendant records over `H := anchor E cap`, with `T_H` (`T_E := χ̂ T_H`) and
       root `R_H` of number `r`:
       - (b1) R8 in `E` at `(c, k)` at the vertex `t`, where `b.col` contains `c` with active
         entry `b`, gives `W < B^E_{b.col}(b.idx)`. Also `B^E_{b.col}(b.idx) ≤ Z :=
         B^E_{b.col}(|Q|−1)`: U1 `cutQuery_lt_succ`; `b.idx < |Q|` by R15/R4. The query
         prefixes of `b.col` in `E` and of `T_H` in `H` coincide (R15).
       - (b2) In `H` (∈ L) the decorated system `capKeys H (routeCols H)` satisfies `CondAK`
         (U1 `capping_iff`†). Its response at `T_H` against `Z` is `r`: the capped last key
         `⊤` is never consumed, and the first `|Q|` keys are consumed by the scan boundary
         lemma `cursor_spec`. `path_nesting` (L2.2) with `W ≤ Z` turns this edge into a
         decorated `g_W`-path `t ⇝ r` on `T_H`'s stack.
       - (b3) Transfer this path to `E`, edge by edge, at a vertex `y` between `r` and `t`,
         with `o_H` its column and `o_E = χ̂ o_H`:
         - if `o_H` is a route column of `H`, the `E`-chain reads `o_E` with an active entry,
           so R8 and R7 give the `cappedAt` cursor. Capped-`H` and capped-`E` responses
           coincide by L4.2b item 1, using R13 (fixed form: each move replaces a same-parent
           block ending at the active entry) **[changed in verification:** R12 dropped here; it
           concerns a marked entry `b` of a record, not the anchor's moves**]**. With no moves the
           lists are equal;
         - otherwise `o_H` is closed, and its entries are unchanged (R10 labels;
           `capKeys` changes only route columns), so the responses coincide.
         - **[Changed in verification.]** At `y = t` itself, `o_H = T_H` and `o_E = b.col`.
           Here the decorated `H`-list `[y_0,…,y_{|Q|−1}, ⊤]` and the capped `E`-list
           `cappedAt (ks_E b.col) j` with `j = b.idx < |Q|` are not related by L4.2b item 1.
           Instead, apply R7 on both sides. Both lists have the same first `j+1` keys (R15), so
           (b1) gives `W < cutQuery · (j+1)` on both sides. Both cursors therefore equal the
           cursor of the common list `[y_0,…,y_{j−1}, ⊤]`, and the responses agree.

         Since `g_W`-chains are deterministic, the `E`-chain from `t` passes through `r`.
     - (c) **Low part.** From the first vertex `≤ r` on, the source and target chains coincide.
       At every column `o` with number `≤ r` on the common stack below and at `r`, the source
       response (`F` at `W'`) equals the target response (`E` at `W`):
       - `κ` fixes the keys of `o` (L4.2a item 4), so `W = W'.map κ` produces the same
         comparison signs (`trace_map`).
       - `F` versus `H`, when `o` contains `a` with active entry `u_a`:
         - this includes `R_H`, with `u_a = i`;
         - R8 in `F` gives the cursor `≤ u_a`;
         - **[Changed in verification.]** For scan and descendant records alike, `F`'s key
           at `u_a` is `≤ H`'s. For `o = R_H` this is `A' ≤ A_i` (equality for scan records).
           For a proper container of `R_H`, `F`'s height of the active entry is `H`'s height
           truncated after `a` (a safe prefix, D1.9 `truncAfter_safePrefix`, hence `≤` by
           `word_lt_iff`), with `A'` placed at `a` (monotone, L4.3a step 5);
         - by L4.2b item 2 (`cursor_raise`, with `pre` = the common keys before `u_a`) the
           cursor equals `H`'s, restoring later entries. R7 alone does not suffice for proper
           containers, because their keys at `u_a` differ even for scan records;
       - `H` versus `E`, for caps: as in (b3). The `E`-barrier for route columns of `H` comes
         from R8 at `(c, k)`. The `E`-chain reads them with the active entry on `b`'s route,
         which is the same entry that contains `a`: if `o` contains both `R_H` and `T_H`, its
         containing entries coincide (R5: `rd.col.path <+: sd.col.path`).
         **[Changed in verification.]** In the owner case, `R_H` itself is a route column of
         `H` whose active entry (the last one) is not `a`'s entry `i`. Chain the equalities
         there as follows:
         - the actual `H`-cursor is `≤ i` (previous bullet);
         - it equals the decorated `H`-cursor (`cursor_raise` with `x` the actual last key and
           `x' = ⊤`);
         - it equals the capped `E`-cursor (L4.2b item 1);
         - it equals the actual `E`-cursor (R7 with the `E`-barrier R8).
       - Repair records: `F = applyMoves (E.truncAfter b) ms` with `a`'s height replaced.
         - F-barrier ⇒ capped `F`;
         - L4.2b item 1 ⇒ capped `E`. **[Changed in verification:** the same-parent block
           comes from the record's own `RepairList` (U2 `RepairStepOK`: entries `i…j` share
           the parent of `j`, and `j` is `b` or contains it), not from R12/R13. Those are
           facts about an `AdmCap`, which a repair record does not carry.**]**;
         - E-barrier ⇒ actual `E`.
5. **Conclusion.** The target chain reaches `p = σ p'`, or `p = p'` when `p' < r`. The `Path`
   is the concatenation of the transferred edges (`Relation.ReflTransGen.trans`).

**Uses:** D4.1a, D7.1a (`rep_inside`), L4.2a, L4.2b, L2.1 (`cursor_spec`), L2.2
(`path_nesting`), L2.4 (`capping_iff`†), L2.5 (`trace_map`†), D2.1 (`cutQuery_lt_succ`),
T3.2 (`std_inL`), D1.9 (`truncAfter_safePrefix`), L4.3a (step 5), U2 D3.1a (`RepairList`
body `RepairStepOK`), R4, R5, R7, R8, R9, R10, R12, R13, R15. **[Changed in verification:** D1.9,
L4.3a and `RepairStepOK` added.**]**

**Lean:** `firstDiff_path`. Planned file `Packet/FirstDifference.lean`, possibly split into
`Packet/PathTransfer.lean`.
**Integration note:** At integration, U3's `cutStart` was an exact duplicate of U1 D2.2a `Scan.cutStart`; it is removed and `Scan.cutStart` is used, as U1's SCR-1 asked.

**Difficulty:** XL. There are three record kinds and two anchor kinds, and four phases with
simultaneous chain induction, about 2,500 LOC.

**Testable:** yes, and tested. **[Changed in verification.]** The claim "no reachable `capAt`" was
wrong; see the Overview. Every first difference was checked, with 0 failures:
- scan and descendant records over `E` and over admissible caps (size ≤ 20): 1,384 `capAt`
  differences. Of these, 361 cross the source host (step 4(b)) and 1,023 are internal;
- admitted repair records (size ≤ 17): 50,878 `capAt` differences. Of these, 29,962 cross the
  host, 4,324 exit directly (step 4(a)), and 1,344 have a low part with moves.

The step 4(b3) branch with a *moved* cap anchor was not reached.

### L4.2d Legality of the first-difference cap   (paper: txt:682-686)
**Fidelity:** new (split from L4.2's proof).

**Statement** (`cap_legal`). Let `IsStd E`, `c ∈ E.colAddrs`, `c.path ≠ []`,
`IsUpward E c k p`, and let `p` be on the actual cut chain (the conclusion of L4.2c). Then
`K := litCap E c k p` satisfies:
- `CondV K`, `CondI K`, `CondS K`;
- decorated A: `CondAK K (capKeys K (routeCols K))`;
- `stepKind K = some .ordinary`.

**Proof.**
1. `E` is in L and satisfies P: T3.2 `std_inL`, `std_condP`.
2. R11 gives the shape of `K`:
   - roles: a prefix of `E.roles`, then `⟨c,k⟩`;
   - entries other than `⟨c,k⟩` keep `E`'s labels. Entries that do not contain `c` also keep
     their heights; containers of `c` do not. **[Changed in verification:** the R11 stub had
     claimed equal heights for all entries.**]**
   - `stopData K` has column `c`, `r = p`, and `Q` = the first `k` entries.
3. V:
   - retained entries: as in `E`, since the stacks are unchanged (`rep` depends only on the
     address);
   - the closing entry: `p` is a `Path` vertex on `c`'s stack, so it resolves (unfold `Edge`).
     Responses are parents of entries visible from `c` (V in `E` with `rep_visible`, D7.1a).
4. I:
   - retained columns: as in `E`;
   - column `c`, if `k = 0`: `c.path ≠ []`, so `c` is a column of a nonempty height. By I in
     `E` it has an entry `0` with parent `≥` its host number. `IsUpward` with `k = 0 < |col|`
     gives `p >` that parent;
   - `K`'s containers are nonempty.
5. Ordinary (R6):
   - the route stops at `(p, ∅)`, since containers are last entries (R11);
   - not special: either `Q ≠ []` (`k > 0`), or `k = 0` and `p >` the first parent `≥` the
     direct owner number, so `p ≠ sd.t − |F_ℓ|`;
   - the root `p` resolves (step 3).
6. S: U2 `upward_condS`†, since `E` satisfies V, I, H, P and `K` satisfies V and I.
7. Decorated A, for each column `o` of `K` and entry index `e`:
   - (a) Retained test, `e` not the closing entry. Its query `cutQuery (capKeys K o) e` uses
     only the keys of entries `< e`, none of which is a capped last key. So it equals `E`'s
     query.
   - Its chain in `E` (A in `E`) reads route columns of `K` (the containing columns of `c`).
     These are containing columns of `o`, with the same active entry: a retained `o` precedes
     the cut, so a route column visible from `o` contains `o`.
   - R8 in `E` at `(o, e)` and R7 make the capped `K`-responses equal to the actual
     `E`-responses. So the `E`-path is a decorated `K`-path.
   - (b) The closing entry `⟨c,k⟩`: its query is `W` (the first `k` keys are `E`'s), and its
     start is `cutStart E c k`. The `E`-path of the hypothesis transfers by the argument of
     step 7(a), applied with R8 at `(c, k)`.

**Uses:** T3.2, L3.1 (`upward_condS`†), R6, R7, R8, R11, D7.1a.

**Lean:** `cap_legal`. Planned file `Packet/FirstDifference.lean`.

**Difficulty:** L (about 700 LOC, mainly step 7).

**Testable:** yes, and tested. **[Changed in verification.]** Tested directly on its
hypotheses: every standard `E` of size ≤ 20 (parameters ≤ 3), every column `c` with
`c.path ≠ []`, every cut `k` and parent `p` with `IsUpward` and `p` on the actual cut chain.
That is 695,585 caps, all with V, I, S, decorated A and an ordinary step. It was also checked at
every `capAt` difference of the record tests (L4.2c). 0 failures.

### L4.2 First-difference lemma   (paper: txt:664-686)
**Fidelity:** repaired (G-003). The difference is computed by an explicit classifier (D4.1a).
The proof is split into L4.2a–d, one phase per record kind.

**Statement** (`firstDiff_cap`; the spine's †, consumer U5 L8.8 Case 3). If `rk.Admitted` and
`firstDiff rk = capAt c k p`, then, with `K := litCap E c k p`:
- `b.heightPath <+: c.path` and `c ∈ E.colAddrs`;
- `IsUpward E c k p`;
- `CondV K`, `CondI K`, `CondS K`, and decorated A;
- `stepKind K = some .ordinary`;
- `Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (cutStart E c k) p`.

The cap's "closing parent is on the target's actual complete-cut chain" (txt:666).

**Proof.**
1. `c.path = b.heightPath ++ ρ`, and the column exists in `tgtKey`, hence in `B` (`relKey`
   keeps the shape): D4.1a item 2.
2. `IsUpward`: in D4.1a's two subcases, either `k = |col|`, or `l₁ < l₂`.
   - `labelAbs t` is strictly increasing on labels whose false values are `< t`.
   - `l₂`'s false values are `< r ≤ t`, since the source is normalized at `r` (D4.1b).
   - `labelAbs t l₁` is the target's parent at `k`, since the target is normalized at `t`.
3. The path: L4.2c.
4. Legality: L4.2d, with `c.path ≠ []` from step 1 and `IsStd E` from Admitted.

**Uses:** D4.1a, D4.1b, L4.2c, L4.2d.

**Lean:** `firstDiff_cap`. Planned file `Packet/FirstDifference.lean`.

**Difficulty:** S given L4.2c and L4.2d (L overall, with them).

**Testable:** see L4.2c.

### L4.3a Confined operations and safe prefixes inside the marked height   (paper: txt:688-695; X-04)
**Fidelity:** repaired (G-003 boundary case X-04). "Confined" requires survival of the marked
occurrence.

**Statement.**
- `Confined F a :⇔` the stopping column has `a.heightPath` as a path prefix, and, for a special
  step, so does the owner entry's column.
- `expand_confined`: if `InL F`, `a ∈ F.entryAddrs`, `F.truncAfter a = F`, `Confined F a` and
  `expand F k = some F'`, then `F' = F.setHeight a A''` with `A'' < F.heightAt a`.
- `safePrefix_inside`: if `µ(F.setHeight a ∅) ≤ k`, then
  `safePrefix F k = F.setHeight a A''` with `A'' ≤ F.heightAt a`.

**Proof** (`expand_confined`).
1. Show the step is not a deletion: `F`'s last outer column contains `a`'s outermost container.
   `stepKind_isSome` (D1.6a) then gives ordinary or special.
2. Show `a` is on the route of `F`:
   - `F.truncAfter a = F`, so each container of `a` is the last entry of the last column (R1);
   - the route follows last entries (`stopData`, R4).
3. Ordinary (R16): `F' = replaceAt 0 0 Z ℓ F`.
   - `shiftVal 0 0 = id`, so the labels are unchanged.
   - The replaced route column has `a.heightPath` as a prefix (Confined).
   - Unfold `replaceAt` along `a.heightPath`: only the last entry's height changes (induction on
     the path, as in `roles_replaceAt`). So `F' = F.setHeight a A''`.
4. Special (R17): the replaced column is the owner entry's column, which lies under
   `a.heightPath` (Confined). Same structural induction.
5. `A'' < A'`:
   - `expand_lt` (T3.2) gives `F' < F`;
   - `F' = F.setHeight a A''` and `F = F.setHeight a A'` (R2);
   - `setHeight` at the last route entry preserves and reflects the order, by unfolding
     `Tree.cmp` along the path: equal prefixes compare `.eq`, the last entries share the label,
     and nothing follows.

**Proof** (`safePrefix_inside`).
1. `word F = word (F.setHeight a ∅) ++ wordAt (d+1) A'`, where `d` is `a`'s depth, because
   `a`'s height is the last part of `F` (`wordCol` unfolding).
2. `word_safePrefix` and `word_injective` (C1.8, D1.9): the forest whose word is the first `k`
   atoms is `F.setHeight a A''`, where `A''` has the word `(wordAt (d+1) A').take (k − µ₀)`.
   Such a decoding exists by D1.9.
3. A prefix word is `≤`, so `A'' ≤ A'` (`word_lt_iff`).

**Uses:** D1.6a, R1, R2, R4, R16, R17, T3.2 (`expand_lt`), C1.8, D1.9.

**Lean:** `Confined`, `expand_confined`, `safePrefix_inside`. Planned file
`Packet/SourceReduction.lean`.

**Difficulty:** M (about 400 LOC).

**Testable:** yes (finite). Enumerate `F`, `a` on the route and `k`; check the `setHeight` shape
of the output.

### L4.3c Repairs take place outside the marked internal height   (paper: txt:697-698)
**Fidelity:** new (split from L4.3).

**Statement** (`repair_moves_outside`). If `rk.Admitted`, `firstDiff rk = capAt c k p`, and
`w : AdmCap E` with `(w.col, w.cut, w.par) = (c, k, p)`, then no move of `w.moves` has
`b.heightPath` as a prefix of its column path.

**Proof.**
1. Suppose a move `m` has `b.heightPath <+: m.col.path`. Take the first such move in
   `w.moves`, at index `idx`, and let `X := applyMoves K (w.moves.take idx)` with
   `K := litCap E c k p`. **[Changed in verification.]** Every earlier move is outside `B`. By R13
   its retained entry `j` is active and contains the current stopping column, which lies inside
   `B`. So its column is `b`'s current column (then `j` is `b`'s current entry) or a strict
   container, and entries `i…j` share a parent. Hence the earlier moves form a
   `RepairList K b (w.moves.take idx)` (U2 `RepairStepOK`), and R19 (`repairList_height`) gives
   `X.heightAt b_idx = K.heightAt b`, with `b_idx := moveAddr (w.moves.take idx) b`. Inside
   `B`, `X` therefore equals `K`. The proof does not depend on the order of the moves.
2. R13 (fixed form): in `X`, entries `m.i < m.j` of `m.col` share a parent `q`, `H_i < C`, and
   entry `m.j` contains the stopping column of `X`. By step 1 this is `c` relocated inside an
   unchanged `B`.
3. *Internal cap = reindexed safe source prefix.* Let `S_A` be `A'` cut after the source entry
   `⟨c',k⟩`, with that entry's height cleared (a safe prefix: L4.3a `safePrefix_inside`). By the
   `cutBefore` equality and the closing label, `relKey t (K.heightAt b) = relKey r S_A` (D4.1a
   item 2; `p = labelAbs t l` corresponds to `l`).
4. `F.setHeight a S_A` is in L (`inL_safePrefix`, T3.2), so `CondH` holds at every column of
   `S_A`.
5. `EntryLe` on two entries of one column inside a height corresponds to `EntryLe` on their
   `relKey` images:
   - parents are compared through the monotone label map;
   - heights by `relKey_lt_iff` (D1.4).

   Equal `relKey`s therefore transfer `CondH` to every column of `K` inside `B`. In particular
   `(q, H_i) ≥ (q, C)` in `m.col`, so `H_i ≥ C`. This contradicts step 2.

**Uses:** D4.1a, L4.3a, T3.2, D1.4, R11, R13, R19, U2 D3.1a (`RepairStepOK`).
**[Changed in verification:** R19 replaces R12, which assumes the conclusion `hout`.**]**

**Lean:** `repair_moves_outside`. Planned file `Packet/SourceReduction.lean`.

**Difficulty:** M (about 300 LOC).

**Testable:** yes, and tested. **[Changed in verification.]** A Python model implemented U2's
inside-out repair. At every `capAt` difference of the record tests (1,384 at size ≤ 20, 262 of
them with at least one move), no move lay inside `B`; 0 failures.

### L4.3b The marked old height increases along repairs, (6)   (paper: txt:699-704)
**Fidelity:** new (split from L4.3; "the interval fact identifies the prefixes").
**[Changed in verification:** the statement gains item 1, the literal-cap form of the repaired
cap. The proof is rewritten: the drafted induction used "C caps X_j" without carrying it as an
invariant, which is false as stated once an inner move has relocated the cap. The repaired proof
no longer needs moves to be applied inner-first (old OP3).**]**

**Statement** (`marked_height_mono`). Assume the hypotheses of L4.3c. Write `c.path =
b.heightPath ++ ρ` (D4.1a item 2), `ms := w.moves`, `bm := moveAddr ms b` and
`c' := ⟨bm.heightPath ++ ρ, c.col⟩`. Then:
1. `w.H = litCap E c' k p`, `IsUpward E c' k p`, and `bm.col.num 0 = b.col.num 0`;
2. `bm ∈ E.entryAddrs`;
3. `B ≤ E.heightAt bm`, that is `B = B^{(0)} ≤ … ≤ B^{(m)} = B_good`.

**Proof.** Put `K := litCap E c k p`, `X_q := applyMoves K (ms.take q)`,
`b_q := moveAddr (ms.take q) b`, `c_q := ⟨b_q.heightPath ++ ρ, c.col⟩` and
`B^{(q)} := E.heightAt b_q`. Induct on `q ≤ |ms|` with the invariant:
- (I1) `X_q = litCap E c_q k p` and `IsUpward E c_q k p`;
- (I2) `b_q ∈ E.entryAddrs`;
- (I3) `B ≤ B^{(q)}`.

By L4.3c no move lies inside `B`, so R18 applies to `w` and `b` at every `q`. Steps:
1. (I1) at every `q` is R18 (`applyMoves_litCap_addr`, the address form of U2 L3.1h). It
   rests on the U2 interval fact L3.1f. (I2) follows: `b_q` is on `c_q`'s path and
   `litCap E c_q k p` keeps every entry on that path (spine §c.6, `litCap`). Item 1 is (I1) at
   `q = |ms|`, together with R19 (`moveAddr_num`).
2. Base `q = 0`: `b_0 = b` and `c_0 = c`.
3. Step `q → q+1`. Let `m = ms[q]` be at column `m.col`, moving entry `j` to index `i`.
   - By R13 (fixed form), in `X_q`: `j` is the last entry of `m.col` and contains the stopping
     column `c_q`; `i < j`; entries `i…j` share a parent; and `H_i < C`, where `H_i`, `C` are
     the heights of entries `i`, `j` of `m.col` in `X_q`.
   - By L4.3c, `m.col` is `b_q`'s column or a strict container of it.
   - Let `X_i`, `X_j` be the heights in `E` of entries `i`, `j` of `m.col`.
   - By (I1), `X_q = litCap E c_q k p`:
     - entry `i` is closed (it does not contain `c_q`), so `H_i = X_i` (R11, fixed form);
     - `C` is the literal cap of `X_j` at the relative position of `c_q` inside `X_j`. In
       relative terms, `C = litCap X_j c_rel k p`, upward by (I1).
4. Facts:
   - `X_j ≤ X_i`: `CondH E` (T3.2 `std_inL`) along the same-parent run `i…j` (transitivity of
     `≤`);
   - `X_i < C`: step 3.
5. *Interval fact.* U2 L3.1f (`interval_cap`) with `X := X_j`, `Y := X_i` gives
   `litCap X_i c_rel k p = litCap X_j c_rel k p`. So `X_i` and `X_j` have the same word before
   the cut position `π := capPos X_j c_rel k` (U2 L3.1c `word_litCap`).
   - The marked address `b_q` lies inside `X_j`, and the cut lies inside the marked height, so
     every atom before the marked height's internal atoms comes before `π`.
   - Hence `X_i` has an entry at the same relative address with the same label, and that entry
     is `b_{q+1}`.
   - `B^{(q)}`, `B^{(q+1)}` are the heights of `X_j`, `X_i` at that relative address.
6. *Monotonicity.* Suppose `B^{(q)} > B^{(q+1)}`. The words of `X_j` and `X_i` agree up to the
   marked height (step 5). Inside it, either:
   - their first differing atom lies inside both heights and is larger in `X_j`; or
   - `w(B^{(q+1)})` is a proper prefix of `w(B^{(q)})`. Then the next atom of `X_j` is internal
     to `B^{(q)}`, with depth coordinate `≥ 2(d+1)` for `d` the depth of `b_q`'s column. The
     next atom of `X_i` is an outer continuation, with depth coordinate `≤ 2d+1`, or absent.

   Either way `w(X_j) > w(X_i)`, which contradicts `X_j ≤ X_i` (C1.8 `word_lt_iff`; txt:700-703).
   So `B^{(q)} ≤ B^{(q+1)}`, and (I3) at `q+1` follows from (I3) at `q`.

**Uses:** L4.3c, T3.2 (`std_inL`), C1.8 (`word_lt_iff`), R11, R13, R18, R19, U2 L3.1c
(`word_litCap`), U2 L3.1f (`interval_cap`).

**Lean:** `marked_height_mono`. Planned file `Packet/SourceReduction.lean`.

**Difficulty:** M (about 400 LOC; word arithmetic).

**Testable:** yes, and tested. **[Changed in verification.]** Items 1–3 were checked for every
repaired admissible cap of every standard expression of size ≤ 20 (parameters ≤ 3), and every
marked entry `b` on the cap's path with no move inside `B`. That is 942,009 pairs; 25,286 have
moves, and 12,844 have `B_good > B`. 0 failures.

### L4.3 Source reduction lemma, (6), (7)   (paper: txt:687-730)
**Fidelity:** repaired (G-003, X-04). The three bullets of txt:688-695 become four contracts with
explicit records.

**Statement.**
1. `reduce_confined` (bullet 1; consumers U5 L8.8 Case 2 and W). Suppose:
   - `rk.Admitted`;
   - `A'' ≤ srcHeight`;
   - `InL (F.setHeight a A'')`;
   - `tgtKey < relKey r A''`.

   Then the record `{rk with F := F.setHeight a A'', kind := kind.toDesc}` is admitted. Here
   `toDesc` turns `scan` into `desc` and keeps the other kinds. A safe prefix inside `A'` and a
   confined operation produce such an `A''`, by L4.3a.
2. `repair_output` (bullet 2; consumer U5 Case 3). Let `w` be an admissible cap with
   `(col, cut, par) = (c, k, p)` for `firstDiff rk = capAt c k p`, and let
   `expand w.H n = some Hk` with `E < Hk`. Put `bm := moveAddr w.moves b`. Then:
   - `bm ∈ Hk.entryAddrs` and `Hk.truncAfter bm = Hk`;
   - `B_good := E.heightAt bm < Hk.heightAt bm =: B'`, and `B < B'`;
   - the repair record `{E, b, F := Hk.truncAfter bm, a := bm, repair w.moves}` is admitted.
3. `repair_output_exists`: some `n ≥ 1` and `Hk` have `expand w.H n = some Hk` and `E < Hk`.
4. `query_size_bound` (7): if `stopData w.H = some sd`, then:
   - `|sd.Q| = k`;
   - every query slot `j` has origin `⟨c, j⟩` inside `B` (`b.heightPath <+: c.path`), with the
     same height;
   - every `J ∈ sd.Q` has `J.size + 2 ≤ B.size`.
5. `reduce_childEnds` (bullet 3; consumer U5 Case 2). If `firstDiff rk = childEnds π`, there is
   `A₁` with:
   - `F₁ := F.setHeight a A₁` in L, `A₁ ≤ A'`, and `tgtKey < relKey r A₁`;
   - `Confined F₁ a`;
   - the step of `F₁` is special, or ordinary with `Q = []` and root column inside `A₁`;
   - for some `k` and `A₂`: `expand F₁ k = some (F.setHeight a A₂)`,
     `tgtKey < relKey r A₂ < relKey r A'` (`A₂ < A'`), and the record with
     `F := F.setHeight a A₂` and `toDesc` is admitted.

**Proof.**
1. *`reduce_confined`*:
   1. Common clauses:
      - `IsStd E` and `b ∈ E` are unchanged;
      - `a ∈ (F.setHeight a A'').entryAddrs` (R2);
      - in L (hypothesis);
      - truncated: R2, last clause, from `F.truncAfter a = F`;
      - strict (hypothesis; `srcKey` of the new record is `relKey r A''` by R2's `heightAt`).
   2. Scan becomes descendant:
      - `AnchorAt` and `anchorSrc` are unchanged;
      - `(F.setHeight a A'').setHeight a (H.heightAt a) = F.setHeight a (H.heightAt a)`
        (R2 idempotence) `= (H.truncAfter a).setHeight a (H.heightAt a) = H.truncAfter a`
        (R2 identity clause, with R1 `heightAt`);
      - `A'' ≤ A' = H.heightAt a`.
   3. Descendant stays descendant: the same equation, from the old descendant clause, and
      `A'' ≤ A' ≤ H.heightAt a`.
   4. Repair stays repair: `(F.setHeight a A'').setHeight a B = F.setHeight a B` (R2).
2. *`repair_output`*:
   1. Moves are outside `B` (L4.3c).
   2. Show `w.H` is ordinary with stopping column inside `bm`'s height. **[Changed in
      verification:** the facts now come from L4.3b item 1, `w.H = litCap E c' k p` with
      `c' = ⟨bm.heightPath ++ ρ, c.col⟩` and `IsUpward E c' k p`.**]**
      - `stopData w.H` has column `c'`, `r = p` and `Q` = the first `k` entries (R11 applied to
        `litCap E c' k p`; R15). `c'` lies inside `bm`'s height;
      - not special, by the argument of L4.2d step 5. It applies to `c'` because `IsUpward E c'
        k p` and `c'.path ≠ []`;
      - `w.H.truncAfter bm = w.H`: `litCap E c' k p` removes all context after the path of `c'`
        (spine §c.6), and `bm` is on that path.
   3. `expand_confined` (L4.3a) with `a := bm`: `Hk = w.H.setHeight bm B'`. Hence
      `Hk.truncAfter bm = Hk` and `bm ∈ Hk`.
   4. *Agreement with `E` before `bm`.* **[Changed in verification.]** By L4.3b item 1,
      `w.H = litCap E c' k p`. Since `bm` is on the path of `c'`, this equals
      `(E.truncAfter bm).setHeight bm B_cap'`, with `B_cap'` the relative literal cap of
      `B_good` (spine §c.6, `litCap`; R11 fixed form for the entries off the path). So
      `Hk = (E.truncAfter bm).setHeight bm B'` (R2 idempotence).
   5. *Comparison.* `E.truncAfter bm ≤ E` (a safe prefix, `truncAfter_safePrefix`; prefix words
      are `≤`). With the `setHeight` monotonicity of L4.3a step 5:
      - `B' ≤ B_good` would give `Hk ≤ E.truncAfter bm ≤ E`;
      - so `E < Hk` forces `B' > B_good`;
      - and `B_good ≥ B` by L4.3b.
   6. *Admission:*
      - `IsStd E`, `b ∈ E`;
      - `bm ∈ Hk.truncAfter bm` (R1);
      - in L: `inL_expand` from `w.inL`, then `inL_safePrefix` with `truncAfter_safePrefix`;
      - truncated: R1;
      - strict: `relKey t B < relKey t B'` by `relKey_lt_iff`, since `bm`'s host number is `t`
        (R19 `moveAddr_num`).
   7. Repair clauses: `RepairList (E.truncAfter b) b ms` (R12), and `a = bm` by definition.
      Finally
      ```
      (Hk.truncAfter bm).setHeight bm B
        = (applyMoves (E.truncAfter b) ms).setHeight bm X .setHeight bm B   (R12 last clause, R2)
        = applyMoves (E.truncAfter b) ms                                    (R12 heightAt clause, R2)
      ```
3. *`repair_output_exists`*:
   1. `E < w.H`. **[Changed in verification.]** By L4.3b item 1, `w.H = litCap E c' k p` with
      `IsUpward E c' k p`, and U2 L3.1c (`lt_litCap`) gives `E < litCap E c' k p`.
   2. `w.H`'s last outer column contains `bm`'s outermost container, so it is nonempty.
   3. `cofinal_bound` (T3.8) with `B := E` (standard) and `E := w.H` (in L) gives `n ≥ 1` with
      `E < (w.H)[n]`.
4. *`query_size_bound`*:
   1. R15 gives `|sd.Q| = w.cut = k`, the origins, and the equal heights. `b.heightPath <+:
      c.path` comes from D4.1a.
   2. `B.size ≥ J.size + 2`: `B.roles` (relative) contains `A_c`, `U_{⟨c,j⟩}` and the relocated
      roles of `J`, pairwise distinct (U1 `roles_nodup`†, `rolesCol` unfolding).
5. *`reduce_childEnds`*:
   1. D4.1a item 2 gives `ρ ≠ []`, `X`, `Y`, `m := |X.cols| < |Y.cols|`, and the common part.
   2. Let `e₀` be the entry of `A'` at relative path `ρ` (`ρ = ρ₀ ++ [(c₀, i₀)]`), with host
      number `a₀`. Column `m` of `Y` has a first entry with parent `p₀ ≥ a₀` (I in `F`).
   3. `A₁` := `A'` cut through that first entry, with its height cleared.
      - It is a safe prefix (`truncAfter_safePrefix`, then L4.3a `safePrefix_inside`), so it
        is in L (`inL_safePrefix`) and `A₁ ≤ A'`.
      - `tgtKey < relKey r A₁`: the common part agrees, and `A₁`'s forest at `ρ` has the extra
        column (unfold `Tree.cmp`).
   4. Route of `F₁` (R4): column `⟨a.heightPath ++ ρ, m⟩`, `Q = []`, `r = p₀`. It is Confined:
      `ρ ≠ []`, so `e₀` is an entry of `A₁` itself.
   5. Case `p₀ > a₀`:
      - not special; ordinary (R6); the root is column `p₀ − a₀ − 1 < m` of the same forest
        (V), inside `A₁`;
      - take `k = 1`. R16 gives the output forest at `ρ`: the first `m` columns unchanged, then
        the nonempty head (all root entries, since the cursor is `0` for an empty query; the
        root column is nonempty by I), then copies;
      - so `tgtKey < relKey r A₂` (the target forest ends first), and `A₂ < A₁` (`expand_lt`);
      - `F.setHeight a A₂` by `expand_confined`.
   6. Case `p₀ = a₀`: special (R6 negation).
      - Let `N'` be the number of target entries of column `⟨ρ₀, c₀⟩` from index `i₀` on, and
        take `k := N' + 1`.
      - R17: the source column becomes `i₀` common entries followed by `k + ε ≥ N' + 1` copies
        of `(p_{e₀}, C)`, with `relKey C = relKey X`.
      - The target entries after `i₀` are `≤ (p, X)` (CondH in `E`). The comparison is decided
        strictly in the source's favour at the first smaller target entry, or when the target
        column ends. That happens within `N' + 1` copies.
      - So `tgtKey < relKey r A₂`, and `A₂ < A₁` (`expand_lt`).
   7. Admission: `reduce_confined` (part 1) with `A₂ ≤ A'` and `InL` (`inL_expand`).

**Uses:** L4.3a, L4.3b, L4.3c, D4.1a, D4.1b, L4.2d, T3.2 (`std_inL`, `inL_expand`,
`inL_safePrefix`, `expand_lt`), T3.8 (`cofinal_bound`), D1.4 (`relKey_lt_iff`), D1.9
(`truncAfter_safePrefix`), U2 L3.1c (`lt_litCap`), R1, R2, R4, R6, R11, R12, R15, R16, R17, R19.
**[Changed in verification:** `lt_litCap`, R11, R19 added.**]**

**Lean:** `RecKind.toDesc`, `reduce_confined`, `repair_output`, `repair_output_exists`,
`query_size_bound`, `reduce_childEnds`. Planned file `Packet/SourceReduction.lean`.

**Difficulty:** L (about 1,200 LOC).

**Testable:** yes, and tested. **[Changed in verification.]** All results had 0 failures:
- `repair_output`, `repair_output_exists` and `query_size_bound`: 942,009 (cap, marked entry)
  pairs (L4.3b), and at every `capAt` difference of the record tests;
- `reduce_childEnds`: 2,063 `childEnds` differences of reachable scan and descendant records
  (size ≤ 20), and 52,906 synthetic entry pairs of standard expressions (471 ordinary,
  52,435 special);
- `expand_confined` (L4.3a): 462,693 confined steps.

---

### L4.3d The data of §8.5 Case 2   (paper: txt:1364-1368)

**Fidelity:** new (requested by U5 R29 at integration; the structure `ChildData` moved here from
U5 `Req.ChildData`, unchanged).

**Statement.** `childEnds_package`: for a packet `pk` with `pk.rk.Admitted` and
`firstDiff pk.rk = childEnds π`, there is `ChildData pk`, whose fields are: a forest `F₁ ∈ L` whose
roles are a prefix of `F.roles` and whose graph is contained in `Γ(F)`; stop data `sd₁` of `F₁`
whose column lies inside the marked entry `a`; `expand F₁ k = some F₂`; either an ordinary step with
`Q = []` whose root lies inside `a`, or a special step whose owner entry lies strictly inside `a`;
`P(F₂, a) = P(F, a)`; and the admitted record `(E, b, F₂, a, kind')`.

**Proof.**
1. L4.3 `reduce_childEnds` gives `A₁` with `F₁ := F.setHeight a A₁ ∈ L`, `Confined F₁ a`
   (L4.3a), the branch, `k` and `A₂` with `expand F₁ k = some (F.setHeight a A₂)`, and the admitted
   record with `F := F.setHeight a A₂` and `kind := rk.kind.toDesc`. Put `F₂ := F.setHeight a A₂` and
   `kind' := rk.kind.toDesc`; `sd₁` is the stop data of `Confined`.
2. *Roles and graph of `F₁`.* By the construction in the proof of L4.3 (`reduce_childEnds`, step 3),
   `A₁` is `A'` cut through the first entry `e₁` of the extra column, with the height of `e₁`
   cleared. Since `F.truncAfter a = F` (admission), `F₁ = (F.truncAfter e₁').setHeight e₁' ∅` for the
   address `e₁'` of `e₁` in `F`. D6.1a item 8 `graph_truncClear` gives `graph F₁ ⊆ graph F`. D1.2e
   item 2 and D1.2c `truncAfter_roles` give `F₁.roles = P(F, e₁') ++ [U_{e₁'}]`, a prefix of
   `F.roles` (D1.2e item 1).
3. *Positions.* `Confined F₁ a` gives `a.heightPath <+: sd₁.col.path`, which is `A_{sd₁.col}.inEntry a`
   (spine `Role.inEntry`). In the ordinary branch `a.heightPath <+: rd.col.path` gives
   `A_{rd.col}.inEntry a`. In the special branch `Confined` gives the owner entry `e` with
   `a.heightPath <+: e.col.path`, so `U_e.inEntry a`, and `e ≠ a` because the column of `e` lies
   strictly inside the height of `a`.
4. *Prefix.* D6.1a `prefixGraph_setHeight` (first clause) for `F.setHeight a A₂`.

If a formalizer of L4.3 exposes `A₁` only through the statement of `reduce_childEnds`, step 2
needs that statement strengthened by `F₁.roles <+: F.roles` and `graph F₁ ⊆ graph F`; both hold
for the construction of its proof.

**Uses:** D1.2c, D1.2e, D6.1a, L4.3, L4.3a.

**Lean:** `Packet.ChildData`, `Packet.childEnds_package`. Planned file
`Packet/SourceReduction.lean`.

**Difficulty:** M (about 200 LOC).

**Testable:** yes. U3's verifier tested the construction on 2,063 `childEnds` records (T3) and
52,906 child pairs (T4(c)).

# Part D — §7: packets

### D7.2 Source packet   (paper: txt:1045-1065)
**Fidelity:** repaired (G-003). A packet is a finite structure: a record, two charts, an
auxiliary diagram over names in the fixed grammar `Hier.Atom`, and one assignment. "One joint
certificate `w_low ∈ J_u`" is the ordinal condition "every low name `< u`" (S-4).

**Statement.** These are spine definitions:
- `SourcePacket := {rk, tgtChart, srcChart, aux, asg}`;
- `host`, `owner`, `tgtFrame`, `srcFrame`, `lowNames`, `joint`.

Correspondence with the six paper clauses:
1. the target-prefix chart: `tgtChart` on `prefixRoles E b`;
2. the source context: `srcChart` on `F.roles`;
3. the auxiliary diagram: `aux : Diagram Name`, any atoms of the grammar. This includes
   `noReal`, which is "bounded labels";
4. the shared assignment: `asg`;
5. both target heads: Valid clause 5;
6. the low certificate: Valid clause 6.

**Proof.** Definitions.

**Uses:** D4.1, D7.1, N4.1.

**Lean:** `Packet.SourcePacket` and its namespace (spine §c.11). Planned file
`Packet/Packets.lean`.

**Difficulty:** S.

**Testable:** no (semantic).

### D7.2a Validity and the target conclusion   (paper: txt:1045-1065, 1173-1180; spine-new)
**Fidelity:** repaired (G-003). The spine's FIRM `Valid` and `TargetAbove` are used unchanged. The
deliberate weakenings justified in spine §c.11 are accepted: extra overlaps are allowed, and `aux`
is opaque.

**Statement.** `SourcePacket.Valid P` and `SourcePacket.TargetAbove P L` (spine, real bodies).
For U3 the relevant consequences are:
- `IsLim u`, which needs `a ∈ F.entryAddrs` (see SCR1);
- `ρ < u`, from the `lt` chain of `graph F` through `srcChart`;
- frames below `r` share names.

**Proof.** Definitions.

**Uses:** D7.2.

**Lean:** `SourcePacket.Valid`, `SourcePacket.TargetAbove` (spine). Planned file
`Packet/Packets.lean`.

**Difficulty:** S.

**Testable:** no.

### D7.2c Fresh names   (paper: txt:1018-1021, 1074)
**Fidelity:** new.

**Statement.**
- `tagOf`, and `freshTag ns := (max tag in ns) + 1`.
- `freshTag_fresh`: `Name.role (freshTag ns) r ∉ ns`.
- `SourcePacket.usedNames := lowNames ++ [owner]`.

**Proof.** `List.foldr max` is above every element, so `tagOf (role (freshTag ns) r) > tagOf n`
for every `n ∈ ns` (`List.le_max`-style induction).

**Uses:** D7.1.

**Lean:** `tagOf`, `freshTag`, `freshTag_fresh`, `SourcePacket.usedNames`. Planned file
`Packet/Packets.lean`.

**Difficulty:** S.

**Testable:** yes (`decide` on small lists).

### L7.3 Factorization lemma   (paper: txt:1068-1081)
**Fidelity:** simplified (S-4), and repaired (SCR1). In ordinal form, "every positive target
certificate in `J_u` above `L*` is compatible with all unchanged low resources" is literally
`TargetAbove L`. The stage `β` and the history packing become `pack_below`.

**Statement** (the spine's `factorization`, with the hypothesis `ha` added by SCR1 at integration;
the draft's name for this form was `factorization_mem`).
Suppose:
- `pk.Valid P`;
- `pk.rk.a ∈ pk.rk.F.entryAddrs`;
- `L < u`.

Then some `L*` has `L ≤ L* < u` and `lowNames < L*`, and
`BlockAbove P (posBlock tgtKey tgtSel) (tgtFrame values) L* u → TargetAbove L`.

**Proof.**
1. `IsLim u`:
   - `lim (U_a) ∈ graph F` (D6.1, `a ∈ F.entryAddrs`);
   - its `srcChart` image is in `joint` (`Diagram.ofBase`, `List.mem_map`);
   - Valid clause 4 with N3.1 `holds_append`/`holds_map`.
2. `pack_below` (N3.1) with the list `lowNames.map asg` (Valid clause 6) gives `L*`.
3. Unfold `BlockAbove`. Its witness `β`:
   - agrees with the frame;
   - has new variables `> L* ≥ L`, hence `>` every low value;
   - has every variable `< u`;
   - satisfies `posBlock`.

   These are the four `TargetAbove` clauses.

**Uses:** D6.1, D7.2a, N3.1.

**Lean:** `factorization` (spine). Planned file `Packet/Factorization.lean`.
**Integration note:** At integration SCR1 is applied: the spine statement carries the hypothesis `ha : pk.rk.a ∈ pk.rk.F.entryAddrs`, which was the workaround `factorization_mem`; that duplicate is removed. Consumers cite `factorization`.

**Difficulty:** S (about 80 LOC).

**Testable:** no.

### L7.3b Target blocks are block realizations   (paper: txt:1079-1080)
**Fidelity:** new (the converse direction used for (26)).

**Statement** (`targetAbove_blockAbove`). `TargetAbove P L` implies
`BlockAbove P (posBlock tgtKey tgtSel) (tgtFrame values) L u`.

**Proof.** Unfold both definitions. The same witness works: the frame clause, the new variables
`> L`, all `< u`, `BaseHolds`.

**Uses:** D7.2a.

**Lean:** `targetAbove_blockAbove`. Planned file `Packet/Factorization.lean`.

**Difficulty:** S.

**Testable:** no.

### L7.3a The failure label at the raised floor, (23)   (paper: txt:1079-1081, 1352-1355)
**Fidelity:** simplified (S-4).

**Statement** (`factorization_noB`). Under the hypotheses of L7.3, suppose `TargetAbove L`
fails. Let the name `ℓ` differ from `owner` and from every frame name read by `posBlock`. Then
`noB tgtKey tgtSel tgtFrame owner ℓ` holds at `Function.update asg ℓ L*`, with `L*` as in L7.3.

**Proof.**
1. Take `L*` from L7.3. By contraposition, `¬ BlockAbove … L* u`.
2. Unfold `noB` and `Atom.Holds (noReal …)`:
   - the updated assignment has `L ↦ L*`;
   - the owner is unchanged (`ℓ ≠ owner`);
   - the frame values read by `posBlock` are unchanged (`hℓf`);
   - frame values outside `baseVars` do not affect `BlockAbove`, by the argument of N3.1
     item 3.

**Uses:** L7.3, N3.1.

**Lean:** `factorization_noB`. Planned file `Packet/Factorization.lean`.

**Difficulty:** S.

**Testable:** no.

### L7.4 Joint cap lemma   (paper: txt:1082-1099)
**Fidelity:** simplified (S-4).
- "Joint certificate in `J_W`" becomes "every value `< W`".
- "Already true bounded label with checking data in `J_{u+ω}`" becomes "its variables are
  `≤ u < W`".
- κ maps into existing names. The spine's informal "extension to fresh names" is not needed:
  REFINABLE, refined here.

**Statement** (`joint_cap`; the spine's †, consumer U5 L8.8 Case 3). Let `pk` be admitted and
valid, with `firstDiff = capAt c k p`, `K := litCap E c k p`, and `κ := capChart pk`. That is:
- `κ y = tgtChart y` on `P(E,b)`;
- `κ y = srcChart (transEntry b a y)` otherwise.

Then:
- (a) `IsConfig P K (asg ∘ κ)`;
- (b) `κ = tgtChart` on `P(E,b)`, and `κ U_b = owner`;
- (c) on the other roles of `K`, `κ` is the source chart of the corresponding source role;
- (d) `u < W < C`, where `W := asg (κ A_c)` and `C := asg (κ U_{⟨c,k⟩})`;
- (e) every value on `rolesBefore K A_c` is `< W`, and every low value is `< W`;
- (f) `restrictTo (graph E) (rolesBefore E A_c)` holds through `κ`. This is the E-prefix part
  of U5's label (deleted blocks included).

**Proof.**
1. R11: `K.roles` is a prefix of `E.roles` followed by `⟨c,k⟩`. Partition it into:
   - (A) `P(E,b)`;
   - (B) `U_b` together with the internal roles before the cut;
   - (C) `U_{⟨c,k⟩}`.
2. `transEntry b a` maps (B) ∪ (C) injectively into `F.roles`, onto the corresponding source
   roles. The shapes agree by the `cutBefore` equality (D4.1a), and the source has entry `k`.
3. Atoms owned by (A): these are the atoms of `prefixGraph E b`, because every variable of an
   atom owned by an (A)-role lies in (A) (D6.1a items 1, 3). They hold via `tgtChart` (Valid
   clause 4).
4. Order atoms (D6.1a item 2), consecutive in `K.roles`:
   - inside (A): step 3;
   - `(last of A, U_b)`: a low value `< u` (clause 6);
   - inside (B) ∪ (C): consecutive source roles, which hold via `srcChart` (`graph F`).
5. Atoms owned by `U_b`:
   - `lim`: `lim U_a` in `graph F`;
   - the heads: `edge(U_b, A_{b.col}, O/P(sel))` ↦ `(owner, host, tgtFrame.reps[sel])` by
     clause 2 (host) and `frameOf` (spine), hence clause 5.
6. Atoms owned by the internal roles and by (C), following txt:1087-1092:
   - By D7.1a `graph_owned_block` applied to `K` at `b`, each is a `freeBlock(relKey t
     (K.heightAt b))`-atom read through `blockMap b`.
   - `relKey t (K.heightAt b) = relKey r S_A` (L4.3c step 3). So it is the same free block as the
     source's. **[Changed in verification.]** Let `e'` be the absolute source entry `⟨c'', k⟩`,
     with `c''` the source column corresponding to `c`. Then
     `F.setHeight a S_A = (F.truncAfter e').setHeight e' ∅` (R1, R2, `F.truncAfter a = F`). This
     forest satisfies V: its entries are entries of `F` at the same addresses with the same
     labels (R1, R2), and `resolve` depends only on the address. D7.1a `freeBlock_graph` applied to it
     at `a`, with `m = |S_A.cols|` (so `takeCols S_A m = S_A`), puts the `blockMap a`-images in
     its graph. D6.1a item 8 then shows that these are atoms of `graph F`. (Item 6 does not
     apply: `S_A` clears the height of `e'`, so it is not a `truncAfter`.) They hold via
     `srcChart` by Valid clause 4.
   - It remains that `asg ∘ κ ∘ blockMap b = asg ∘ srcChart ∘ blockMap a` on the block variables:
     - `inner r`: `transEntry b a (Role.under b r) = Role.under a r`;
     - `owner`: (b);
     - `host`: clause 2;
     - `ord q`, `cur q` with `q < r`: these are the only frame entries read, because the false
       labels of the common part are `< r` (D4.1a; source normalized at `r`). Clause 3 gives
       `srcFrame.reps.take r = tgtFrame.reps.take r`.
7. (d), (e):
   - D6.1a `isConfig_before` on the `srcChart` part: `U_a <_F A_{c'} <_F U_{⟨c',k⟩}`, and the
     internal roles before `A_c` map before `A_{c'}`;
   - (A)-values and the low values are `< u` (clause 6).
8. (f): `rolesBefore E A_c = rolesBefore K A_c` (R11), and the restricted atoms coincide (D6.1a
   item 6 applied with `truncAfter`; `K` agrees with `E` before the cut). Use steps 3–6.

**Uses:** D4.1a, D6.1a (items 1–4, 6, 8), D7.1a, L4.3c (step 3), N3.1, R1, R2, R11, D7.2a.

**Lean:** `capChart`, `joint_cap`. Planned file `Packet/JointCap.lean`.

**Difficulty:** L (about 600 LOC).

**Testable:** no (semantic). The syntactic core (step 6) is D7.1a, which is tested.

### L7.5a The external frame survives repairs   (paper: txt:1102-1105, 1416-1421)
**Fidelity:** new (split; "induction through the containers proves this also for unused external
representatives").

**Statement** (`frame_repair`). Let `IsStd E`, `w : AdmCap E`, `b ∈ E.entryAddrs` with
`b.heightPath <+: w.col.path`, and moves outside `B`. Put `bm := moveAddr w.moves b`. Then:
- `(frameOf bm).map (capRole w) = frameOf b`;
- `capRole w U_bm = U_b`;
- `capRole w` maps `prefixRoles w.H bm` into `prefixRoles E b`, injectively.

**Proof.**
1. `reps0 bm.col` has length `bm.col.num 0 = b.col.num 0` (R12).
2. For each `q`, R10's rep clause (at the column `bm.col`, whose origin is `b.col` by R10's label
   clause) gives `χ̂ ∘ rep_H(bm.col, q) = rep_E(b.col, q)`. This is where "deleted blocks are
   closed siblings" is used: U2 proves it inside `origin_spec`.
3. Slot: R12 together with R10 (the moved entry's origin is the retained later entry).
4. Prefix and injectivity: R10's order and injectivity clauses.

**Uses:** R10, R12.

**Lean:** `capRole`, `frame_repair`. Planned file `Packet/JointRepair.lean`.

**Difficulty:** M (about 200 LOC, given R10).

**Testable:** yes, once U2 has the bodies of `applyMove`/`origin` (finite).

### L7.5 Joint repair lemma   (paper: txt:1100-1117)
**Fidelity:** simplified (S-4). "Repack in `J_u` and raise the floor" becomes "the values are
unchanged, so every bound persists".

**Statement** (`joint_repair`; the spine's †). Under the hypotheses of L7.4, let `w : AdmCap E`
with `(col, cut, par) = (c, k, p)`. Put `α := asg ∘ κ ∘ capRole w` and `bm := moveAddr w.moves b`.
Then:
- (a) `IsConfig P w.H α`;
- (b) `α U_bm = u` and `α A_{bm.col} = ρ`;
- (c) `(frameOf bm).map (κ ∘ capRole w) = tgtFrame`;
- (d) on `P(w.H, bm)`, `κ ∘ capRole w = tgtChart ∘ capRole w` ("the repaired prefix has an
  injective chart into the old target prefix", with injectivity from L7.5a);
- (e) at the stop data of `w.H`: `α T = W` and `α N = C`, and every value before `T` is `< W`;
- (f) `κ y = κ (capRole w x)` whenever `anchorOrigin E (some w) x = some y`. This is the
  `eν ∘ χ = ν` premise of U5's `DLab`, with `eν := κ` and `ν := κ ∘ capRole w`.

Deleted blocks stay realized: they are in `P(E,b)`, so they lie in `prefixGraph E b`, which
holds via `tgtChart` (Valid clause 4) and via `κ` (L7.4 (f)).

**Proof.**
1. Moves are outside `B` (L4.3c).
2. Every atom of `graph w.H` maps under `capRole w` to an atom of `graph K`, or, for order
   atoms, to an order-related pair:
   - (a) atoms without the closing slot: D6.1b item 1 into `graph E`, all of whose variables
     precede the cut. These are atoms of `graph K` (R11; `K` agrees with `E` before the cut);
   - (b) atoms with the closing slot: `lim`, and its two edges
     `edge(N_H, T_H, O/P(p))` ↦ `edge(⟨c,k⟩, A_c, O/P_K(p))` (R10 rep clause, R15);
   - (c) order atoms: D6.1b item 2. The closing slot is last in both orders (R4, R11).
3. (a) follows from step 2 and L7.4 (a), with D6.1a items 1–2 and `isConfig_before`.
4. (b), (c), (d): L7.5a, together with L7.4 (b) and κ = `tgtChart` on `P(E,b)`.
5. (e): R15 gives `χ̂ T_H = A_c`, and `capRole` of the closing slot is `⟨c,k⟩`. Use L7.4 (d),
   (e), and R10's order clause.
6. (f): `capRole w x = y` (definition of `getD`).

**Uses:** L7.4, L7.5a, L4.3c, D6.1b, D6.1a, R4, R10, R11, R15.

**Lean:** `joint_repair`. Planned file `Packet/JointRepair.lean`.

**Difficulty:** M (about 350 LOC).

**Testable:** no (semantic). Step 2 is finite and testable with U2's bodies.

### L7.5b Readmission after a confined source reduction (§8.5 Case 2)   (paper: txt:1118-1120, 1364-1381)
**Fidelity:** new. This is the G-003 closure lemma. The paper's "it is an admitted packet at
`(ρ, w)`" becomes a constructor with checkable hypotheses.

**Statement.** Define `readmitHeight pk F' kind' δ` (real body):
- the record is `{pk.rk with F := F', kind := kind'}`;
- `tgtChart`, `aux` are unchanged;
- `srcChart` is the old chart on `prefixRoles F a` and `role tg x` elsewhere, with
  `tg := freshTag pk.usedNames`;
- the assignment is `δ` on tag `tg` and the old one elsewhere.

`readmit_height`. Suppose:
- `pk` is admitted and valid;
- the record with `F' := F.setHeight a A''` and `kind'` is admitted (from L4.3);
- `graph F'` holds at "old values on `prefixRoles F a`, `δ` elsewhere";
- both target heads hold at `δ U_a` with the old host and frame values;
- every old low value is `< δ U_a`.

Then the new packet is admitted and valid, and:
- its owner value is `δ U_a`;
- host, `tgtFrame`, `lowNames`, low values, `tgtKey` and `tgtSel` are unchanged.

**Proof.**
1. `prefixRoles F' a = prefixRoles F a` (D6.1a item 7).
2. `freshTag_fresh` (D7.2c): the new names avoid `usedNames`. So the new assignment equals the
   old one on every used name.
3. Clause 1:
   - `tgtChart` is unchanged;
   - the new `srcChart` is injective: the old chart on the prefix, `Name.role tg` (injective in
     `r`) elsewhere, and the two ranges are disjoint (step 2).
4. Clause 2: `A_{a.col} ∈ prefixRoles F a`, so the host name is unchanged.
5. Clause 3: frame roles of `a` are in the prefix (D7.1a: reps are numbers `< r` on `a.col`'s
   stack, before `U_a`), so `srcFrame` is unchanged.
6. Clause 4, by N3.1 `holds_append`, `holds_map`, `holds_congr`:
   - the `prefixGraph E b` part reads low names only;
   - the `graph F'` part is the hypothesis, since `asg' ∘ srcChart'` is the stated valuation;
   - `aux` vars are low.
7. Clause 5: hypothesis.
8. Clause 6: the low names are unchanged (steps 1, 4), and the values come from the hypothesis.

**Uses:** D6.1a, D7.1a, D7.2a, D7.2c, N3.1, L4.3 (supplies `hadm'`).

**Lean:** `readmitHeight`, `readmit_height`. Planned file `Packet/Readmission.lean` (new; after
`JointRepair.lean`).

**Difficulty:** M (about 300 LOC).

**Testable:** no.

### L7.5c Readmission after the repaired-cap descent (§8.5 Case 3)   (paper: txt:1120-1124, 1400-1470)
**Fidelity:** new (the G-003 closure lemma for Case 3, both root positions `p ≤ ρ` and `p > ρ`).

**Statement.** Define `readmitRepair pk w Hk γ b'` (real body):
- the record is `{E, b, F := Hk.truncAfter bm, a := bm, repair w.moves}`;
- `tgtChart`, `aux` are unchanged;
- `srcChart` is `tgtChart ∘ capRole w` on `prefixRoles (Hk.truncAfter bm) bm`, and fresh
  `role tg x` elsewhere. This is "the source prefix is the surviving restriction of the original
  target prefix, while the full latter remains auxiliary";
- the assignment is `γ` on tag `tg` and `b'` on every other name.

`readmit_repair`. Suppose:
- `pk` is admitted and valid, with `firstDiff = capAt c k p`;
- `w` has `(c, k, p)`, `expand w.H n = some Hk`, and `E < Hk`;
- (src) `graph (Hk.truncAfter bm)` holds at `γ`;
- (share) `γ x = b' (tgtChart (capRole w x))` on `prefixRoles w.H bm`. This is (24), and the
  sharing check `γ(ι_k(ℓ(v))) = a'_{χ(v)}` of txt:1443;
- (tgt) `prefixGraph E b` holds via `tgtChart` at `b'`;
- (aux) `aux` holds at `b'`;
- (heads) both target heads at `γ U_bm`, with `b'` on host and frame;
- (low) every old low name has `b'`-value `< γ U_bm`.

Then the new packet is admitted and valid. Also:
- its owner value is `γ U_bm`;
- the host name and `tgtFrame` are unchanged;
- the low values are `b'`;
- `tgtKey`, `tgtSel`, `E` and `b` are unchanged.

**Proof.**
1. Admission: L4.3 `repair_output`.
2. `prefixRoles (Hk.truncAfter bm) bm = prefixRoles w.H bm`:
   - L6.2d applied to `w.H`, since `U_bm` precedes `T` (the stopping column lies inside `bm`'s
     height: L4.3 part 2, step 2);
   - R1.
3. Clause 1: `tgtChart ∘ capRole w` is injective on the prefix (L7.5a, with Valid clause 1 on
   `P(E,b)`). Fresh names are disjoint (D7.2c).
4. Clause 2: `capRole w A_{bm.col} = A_{b.col}` (L7.5a frame host), so the host name is
   unchanged.
5. Clause 3: `srcFrame' = (frameOf bm).map (tgtChart ∘ capRole w) = tgtFrame` (L7.5a). This is
   the whole frame, as `r = t`.
6. Clause 4:
   - the `prefixGraph E b` part: (tgt), since every name there has a tag `≠ tg`;
   - `graph (Hk.truncAfter bm)` through the new `srcChart` at the new assignment is `γ`: by
     (share) on the prefix, by definition elsewhere. Then (src);
   - `aux`: (aux).
7. Clause 5: (heads); the owner name `role tg U_bm` has value `γ U_bm`.
8. Clause 6: `srcChart'(P(F_k, bm)) ⊆ tgtChart(P(E,b))` (L7.5a), so `lowNames' ⊆ old lowNames`
   as sets. Then (low).

**Uses:** L4.3, L6.2d, L7.5a, D6.1a, D7.2c, N3.1, R1.

**Lean:** `readmitRepair`, `readmit_repair`. Planned file `Packet/Readmission.lean`.

**Difficulty:** M (about 350 LOC).

**Testable:** no.

### L7.5d The data of §8.5 Case 3   (paper: txt:1382-1424)

**Fidelity:** new (requested by U5 R30 at integration; the structure `CapData` moved here from U5
`Req.CapData`, unchanged; this closes U5's open problem OP-1 at the level of the plan).

**Statement.** `cap_package`: for a packet `pk` with `pk.rk.Admitted`, `pk.Valid P` and
`firstDiff pk.rk = capAt c k p`, there is `CapData P pk` (fields as in the Lean structure): the
repaired cap `w` with ordinary stop and root data; (7); charts `nm` of the `E`-prefix and `nmH` of
`Γ(w.H)`; an assignment `asg'`; the realized graphs; the marked entry `bm = moveAddr w.moves b` with
its origins, prefix and whole frame; `T` inside `bm`; `u < W`; and readmission of the repair
records for every `H[k] > E`.

**Proof.** Write `κ = capChart pk` (L7.4) and `bm = moveAddr w.moves b`. Field by field:
1. `w`: L4.2 `firstDiff_cap` gives `IsUpward E c k p` and V, I, S and decorated A of `litCap E c k p`;
   L3.1 `repair` (with `InL E`, `CondP E` from T3.2 `std_inL`, `std_condP`) gives `w : AdmCap E` with
   `w.col = c`, `w.cut = k`, `w.par = p`, `stopData w.H = some sd` with `sd.r = p` and
   `sd.Q` the first `k` entries, and `w.H = litCap E c' k p`.
2. `ordinary`, `stop`, `root`: not a deletion (the last outer column of a literal cap is nonempty,
   D3.1e item 1); not special: `specialStop` reads `depth`, `|Q|`, `r`, `col.col` and `t`
   (spine body), which agree for `litCap E c k p` and `w.H` (D3.1d `admCap_query`; `moveAddr` keeps
   numbers, D3.1e item 5), and `litCap E c k p` is ordinary (L4.2 `firstDiff_cap`); the root is
   visible by V of `w.H` (`w.inL`; D1.6c `resolve_root_of_condV`). So `stepKind w.H = some .ordinary`
   (D1.6b `stepKind_ordinary_iff`) and `rootData w.H` is `some` (spine contract
   `rootData_of_ordinary`).
3. `qsize`: L4.3 `query_size_bound`.
4. `nm := κ`, `nmH := κ ∘ capRole w`, `asg' := pk.asg`. `nm_tgt`, `nm_owner`: L7.4 `joint_cap`.
   `asg_old`: trivial.
5. `pre_sub`: `ePrefix E (some w) sd = rolesBefore E A_c` (D6.1c body, with `χ (A_{sd.col}) = A_c`
   from D3.1d `admCap_query`), and `P(E,b) ⊆ rolesBefore E A_c` because `b` contains `c` (D1.2e
   item 1: the roles of `b`'s height, in particular `A_c`, follow `U_b`).
6. `nm_inj`, `nmH_inj`: on `P(E,b)` `κ = tgtChart` is injective (Valid clause 1); on the internal
   roles `κ = srcChart ∘ transEntry b a` is injective (Valid clause 1, `transEntry` injective,
   L6.2a); the two images are disjoint because their values are separated: low names have values
   `< asg u` (Valid clause 6) and internal source names values `> asg u` (they follow `U_a` in the
   `lt` chain of `Γ(F)`, Valid clause 4; D6.1a `isConfig_before`); `κ (U_b) = owner` has value
   `asg u`. `capRole w` is injective on `w.H.roles` (D3.1d item 1; the closing slot goes to
   `U_{⟨c,k⟩}`, which is not an origin).
7. `compat`: `nmH x = κ ((w.origin x).getD _) = κ y = nm y` when `w.origin x = some y` (definition of
   `capRole`).
8. `config`: L7.5 `joint_repair` (first conjunct). `ePrefix_holds`: L7.4 `joint_cap` (last
   conjunct) with N3.1 `baseHolds_map`. `ePrefix_below`: L7.4 `joint_cap`
   (`∀ y ∈ rolesBefore K (A_c), asg (κ y) < asg (κ A_c)`), with
   `rolesBefore E A_c = rolesBefore K A_c` (D3.1e item 1, roles clause) and
   `nmH (A_{sd.col}) = κ A_c` (step 5).
9. `marked_mem`, `marked_slot`, `marked_host`, `marked_prefix`, `marked_frame`: L4.3c gives that no
   move lies inside the height of `b`; then D3.1e item 2 (`moves_spec`) and D1.2f
   `setHeight_basic` give `bm ∈ w.H.entryAddrs`; L7.5a `frame_repair` gives
   `capRole w (U_bm) = U_b`, `(frameOf bm).map (capRole w) = frameOf b` (whose host component is
   `marked_host`) and the prefix map; since `U_bm` and `A_{bm.col}` are not the closing slot,
   `capRole` is `w.origin` there (D3.1d item 1). `marked_frame` is the frame clause of L7.5
   `joint_repair`.
10. `stop_inside`: `sd.col = c'`, and D3.1e item 4 (`applyMoves_litCap_addr`) writes `c'` as
    `bm.heightPath ++ …`.
11. `owner_lt`: L7.4 `joint_cap` (`asg u < asg (κ A_c)`).
12. `readmit`: L4.3 `repair_output` (last conjunct), for every `k`, `H'` with `expand w.H k = some H'`
    and `E < H'`.

**Uses:** D1.2e, D1.2f, D1.6b, D1.6c, D3.1d, D3.1e, D6.1a, D6.1c, L3.1, L4.2, L4.3, L4.3c, L6.2a,
L7.4, L7.5, L7.5a, N3.1, T3.2.

**Lean:** `Packet.CapData`, `Packet.cap_package`. Planned file `Packet/JointRepair.lean`.

**Difficulty:** M (assembly, about 300 LOC); its cost is carried by L4.2, L7.4 and L7.5.

**Testable:** no (semantic).

### D7.2b Scan setup and its validity (§7.3 hypotheses)   (paper: txt:1127-1137, 1183-1185, 1295-1303; spine-new)
**Fidelity:** repaired (G-003). The body of the spine's `ScanSetup.Valid` is supplied by
`ValidDef` (SCR2).

**Statement.** With the spine's `ScanSetup` fields and the helpers `chi` (`χ̂`), `TE`, `PE`, `R`,
`preRoot`, `rootLen`, `bankRoles` (the roles of root entries `0…c`), `qVal`, `bankVal` and
`bankGraph`, `ValidDef P` is the conjunction of:
- **S1.**
  - `IsStd E`, `InL H`, `stepKind H = some .ordinary`, `stopData H = some sd`,
    `rootData H = some rd`;
  - `rd.cursor < rootLen` (the bank is not exhausted);
  - root entry `c` is not the container of `sd.col` (closed endpoint).
- **S2.** `ePre` is injective on `PE`; `restrictTo (graph E) PE` holds through `ePre`; every
  value `asg (ePre y) < ρ`.
- **S3.** `aux` holds, and its values are `< ρ`.
- **S4.** `queryGraph` holds at `qVal`:
  - `Q` through `qNm`;
  - `T ↦ ρ`;
  - `P⁻` through `ePre ∘ χ̂`.
- **S5.** `bankGraph` holds at `bankVal`. `bankGraph` is the atoms of `Γ(H)` inside
  `preRoot ∪ {R} ∪ bank` that involve `R` or the bank. `bankVal` is:
  - `R ↦ ρ`, the same new role and not `ePre (χ̂ R)`;
  - the bank through `bankNm`;
  - `preRoot` through `ePre ∘ χ̂`.
- **S6.** `qNm` and `bankNm` are injective, and their images are pairwise disjoint and disjoint
  from `ePre(PE)`, `stopNm` and `aux.vars`.

`valid_iff_def : S.Valid P ↔ S.ValidDef P` (SCR2).

**Proof.** Definitions.

**Uses:** D6.1, D6.1b (`anchorD`), D7.2.

**Lean:** `ScanSetup.chi`, `TE`, `PE`, `R`, `preRoot`, `rootLen`, `bankRoles`, `qVal`, `bankVal`,
`bankGraph`, `ScanSetup.ValidDef`, `ScanSetup.valid_iff_def`; spine: `ScanSetup`, `H`,
`preStop`, `queryRoles`, `queryGraph`, `baseVal`, `fitVal`, `ownerVal`, `entryRoles`,
`fittedRoles`, `Fitted`, `Lmax`, `Cmax`, `HeadsAt`, `scanRecord`. Planned file
`Packet/ScanPackets.lean`.
**Integration note:** SCR2 applied: every definition of this list before valid_iff_def moved
verbatim into `Spine.lean` §c.11, the spine's Valid is `S.ValidDef P`, and valid_iff_def holds by
`Iff.rfl`.

**Difficulty:** S.

**Testable:** no (semantic).

### D7.2d Targets of scan records   (paper: txt:650-652)

**Fidelity:** new (requested by U5 R25 at integration; formerly the stub
`Req.scanRecord_tgtHeight`).

**Statement.** `scanRecord_tgtHeight`: for `S.Valid P` and `j < |S.sd.Q|`, the target height of
`S.scanRecord i j` is the height of query entry `j`, `((S.sd.Q[j]?).map Prod.snd).getD ∅`.

**Proof.**
1. S1 of `S.Valid` (spine body `ValidDef`, D7.2b): `IsStd S.E`, `InL S.H` and
   `stopData S.H = some S.sd`.
2. `cap = none`: `S.H = S.E` and `anchorOrigin = some`, so the target is `b = ⟨sd.col, j⟩` (spine
   `scanRecord`); D1.6d `stopData_roles` gives `S.E.colAt sd.col = some (Q ++ [(r, ∅)])`, so the
   height of entry `j < |Q|` is that of `Q[j]` (spine bodies of `entryAt`, `heightAt`).
3. `cap = some w`: D3.1d `admCap_query` (with `InL S.E` from T3.2 `std_inL`) gives
   `χ (U_{⟨sd.col, j⟩}) = U_{⟨w.col, j⟩}` and `sd.Q[j]? = (S.E.colAt w.col)[j]?`; so
   `b = ⟨w.col, j⟩` and its height in `S.E` is that of `Q[j]`.

**Uses:** D1.6d, D3.1d, D7.2b, T3.2.

**Lean:** `Packet.scanRecord_tgtHeight`. Planned file `Packet/ScanPackets.lean`.

**Difficulty:** S.

**Testable:** yes (decidable on bounded setups; not run at integration).

### L7.6a The explicit packet at a scan state and the fitting extension   (paper: txt:1138-1167)
**Fidelity:** repaired (G-003). The paper's "the next source-greater comparison has a complete
source packet" becomes an explicit packet, `scanPacket`.

**Statement.** Definitions with real bodies:
- `fitTag := freshTag usedNames`, where `usedNames` = `ePre(PE)`, `stopNm`, `bankNm(bank)` and
  `aux.vars`;
- `cE` is the `E`-copy of the stopping column;
- `toH := transColumn cE sd.col id`;
- `pkTgtChart`: `ePre` on `PE`, `stopNm` on `TE`, and `role fitTag (toH y)` otherwise (the
  fitted query entries);
- `pkSrcChart`: `ePre ∘ χ̂` on `preRoot`, `stopNm` on `R`, and `bankNm` otherwise;
- `pkAsg β`: `β` on tag `fitTag`, `S.asg` elsewhere;
- `scanPacket i j β := {scanRecord i j, pkTgtChart, pkSrcChart, aux, pkAsg β}`;
- `extendFit j β γ`:
  - on entry `j`'s slot: `γ owner`;
  - on its height: `γ (inner (relRole …))`;
  - elsewhere: `β`.

`scanPacket_spec`. Suppose:
- `S.Valid P`;
- `ReachesGT (rootKeys H rd) (queryKeys sd) i j`;
- `Fitted P j β`;
- `Lmax j β < u_i`;
- `HeadsAt P j i β`.

Then `pk := scanPacket i j β` has `pk.rk = scanRecord i j`, `pk.rk.Admitted`, `pk.Valid P`, and
owner value `u_i`. Moreover, let `L ≥ Lmax j β`, and let `γ` satisfy the four `TargetAbove`
clauses for `pk` at `L`. Then `extendFit j β γ` fits entry `j`, equals `β` on the earlier fitted
roles, and has its new values in `(L, u_i)`.

**Proof.**
1. `valid_iff_def` gives S1–S6.
2. Indices:
   - `i ≤ c`, by R3 and R5 (`cursor` is the final source cursor);
   - `i < rootLen` and `j < |Q|`, from `ReachesGT`;
   - entry `i` is closed: in the owner case the active entry is the last one (R5) and `c` is
     not it (S1), so `i ≤ c < rootLen − 1`.
3. Record facts:
   - `b` has origin `⟨cE, j⟩` (R15, or the identity), `b.col.num 0 = sd.t` and
     `E.heightAt b = Q[j].2` (R4, R15). Hence `tgtKey = y_j`.
   - `srcKey = x_i` (R1 `heightAt`).
   - `ReachesGT` gives `tgtKey < srcKey`.
   - The scan clauses of `Admitted`: `AnchorAt` from S1, the origin, `ReachesGT` and step 2;
     `F = H.truncAfter a` by definition.
   - Common clauses: `InL F` (`truncAfter_safePrefix`, `inL_safePrefix`), and truncation (R1).
4. Role lists:
   - `F.roles = preRoot ++ [R] ++ bank_{≤i}` (U1 `truncAfter_roles`†);
   - `P(E,b) = PE ++ [TE] ++ fittedE` (R4 applied in `E`'s column `cE`);
   - `toH` is a bijection from `fittedE` onto `fittedRoles j` (R15: equal query entries).
5. Clause 1:
   - S2 gives injectivity on `PE`; the values separate `stopNm` from `ePre(PE)`;
   - `freshTag_fresh` and the injectivity of `toH`;
   - R10 makes `χ̂` injective, and order preservation puts `χ̂(preRoot)` inside `PE`;
   - S6 for the bank.
6. Clause 2: `tgtChart TE = stopNm = srcChart R`.
7. Clause 3: for `q < r`:
   - `rep_H(rd.col, q) = rep_H(sd.col, q)` (D7.1a `rep_visible`, `R` visible from `T`, R5);
   - R10 rep clause: `χ̂ ∘ rep_H(sd.col, q) = rep_E(cE, q)`;
   - both are in `preRoot`/`PE`, where the charts are `ePre ∘ χ̂`/`ePre`.
8. Clause 4:
   - (a) `prefixGraph E b`:
     - atoms inside `PE`: S2;
     - owned atoms involving `TE` or `fittedE`: D6.1b item 1, converse direction. All their
       variables have origins (R10 rep clause), so they are `χ̂`-images of `queryGraph`-atoms
       inside `preStop ∪ {T} ∪ fittedRoles j`. These hold at `fitVal β = pkAsg β ∘ pkTgtChart ∘
       χ̂⁻¹` (hfit);
     - order atoms: `(pred TE, TE)` from S2's bound; inside the fitted region they are
       consecutive in `H`, by `toH`.
   - (b) `graph F = restrictTo (graph H) F.roles` (D6.1a item 6):
     - `preRoot` atoms by D6.1b item 1 (forward), then S2. Order atoms by D6.1b item 2 and the
       strict increase along `PE`. **[Changed in verification:** that increase is D6.1a item 4b
       (`before_of_restrict`), applied to the S2 part `restrictTo (graph E) PE` with
       `PE = E.roles.take |PE|`. Item 4 needs the whole `Γ(E)`, which S2 does not give.**]**;
     - atoms involving `R`/bank by S5.
   - (c) `aux`: S3. Its names are not tagged `fitTag`.
9. Clause 5: `tgtFrame.reps[tgtSel] = tgtChart² (rep_E(cE, p_j))`, and the values equal
   `fitVal β (rep_H(sd.col, p_j))` (R10). Then use `HeadsAt`.
10. Clause 6:
    - `PE` and `aux` values are `< ρ`; `ρ < u_i` by the `R → … → U_i` chain in S5
      (`isConfig_before`-style);
    - fitted values `≤ Lmax < u_i`;
    - `prefixRoles F a = preRoot ++ [R] ++ bank_{<i}`, whose values are `< u_i` by the S5 chain.
11. Owner value: `pkSrcChart U_{⟨rd.col,i⟩} = bankNm …`, which is not tagged `fitTag`.
12. Extension. `Fitted P (j+1) (extendFit j β γ)`:
    - atoms inside `preStop ∪ {T} ∪ fitted_j`: hfit;
    - atoms owned by entry `j`'s roles: D7.1a `graph_owned_block` at `⟨sd.col, j⟩` in `H`
      writes them as `posBlock (relKey t Q[j].2) p_j`-atoms through `blockMap`. This is
      `posBlock tgtKey tgtSel` (step 3). So they hold at `γ`.
    - The valuations agree: `fitVal (extendFit…) ∘ blockMap ⟨sd.col,j⟩ = γ` on the block
      variables:
      - owner and inner by definition (`relRole ∘ Role.under = id`);
      - host `T ↦ ρ` by `γ`'s frame clause;
      - `ord q`, `cur q`: reps on `T`'s stack are in `P⁻` (`q < t`), where `fitVal = baseVal`,
        which equals the frame value by step 7.
    - Order atom `(pred U_j, U_j)`: the value is `≤ Lmax ≤ L < γ owner`.
    - Bounds: `γ`'s new variables are in `(L, u_i)`.

**Uses:** D7.2b, D7.1a, D6.1a, D6.1b, D7.2c, D4.1a, N3.1, T3.2 (`inL_safePrefix`), D1.9
(`truncAfter_safePrefix`), U1 `truncAfter_roles`†, R1, R3, R4, R5, R10, R15.

**Lean:** `ScanSetup.usedNames`, `fitTag`, `cE`, `toH`, `pkTgtChart`, `pkSrcChart`, `pkAsg`,
`scanPacket`, `extendFit`, `scanPacket_spec`. Planned file `Packet/ScanPackets.lean`.

**Difficulty:** L (about 900 LOC).

**Testable:** no (semantic). Steps 2–4 and 7 are finite and checkable.

### L7.6 Complete packets at a scan (17)   (paper: txt:1126-1167)
**Fidelity:** repaired (G-003).

**Statement** (`scan_packet`, FIRM in the spine; consumer U5 L8.5). Exactly as in `Spine.lean`.
Its hypothesis `h17b` (`Lmax ≤ Cmax`) is not needed for the conclusion. It is harmless and
belongs to U5's W-invariant.

**Proof.**
1. Take `pk := scanPacket i j β` (L7.6a).
2. Given `TargetAbove P L`, obtain its witness `γ` and apply the extension part of L7.6a with
   `β' := extendFit j β γ`.

**Uses:** L7.6a.

**Lean:** `Packet.scan_packet` (spine). Planned file `Packet/ScanPackets.lean`.

**Difficulty:** S given L7.6a.

**Testable:** no.

---

### L7.6b Fitting one query entry from a block   (paper: txt:1160-1162)

**Fidelity:** new (requested by U5 R26 at integration; the target-advance step inside L7.6a,
isolated as U5's PS-1 proposed; formerly the stub `Req.fit_of_block`).

**Statement.** `fit_of_block`: let `S.Valid P`, `j < |S.sd.Q|`, `S.Fitted P j β` and
`S.Lmax j β ≤ L`. Write `K_j = (queryKeys S.sd)[j]` and `p_j` for the parent of query entry `j`
(both with the defaults of the Lean text). Let `βb` realize `posBlock K_j p_j`, agree with
`S.fitVal β` on the frame of `⟨sd.col, j⟩`, and give every new variable a value `> L`. Then some
`β'` has `S.Fitted P (j+1) β'`, agrees with `β` on `S.fittedRoles j`, and gives every role of
entry `j` the value of some new block variable.

**Proof.**
1. Put `β' = S.extendFit j β βb` (L7.6a): on the roles of entry `j`, the slot goes to
   `βb owner` and every other role `x` to `βb (inner (relRole (heightPath ⟨sd.col, j⟩) x))`; `β`
   elsewhere.
2. The roles of `fittedRoles j` are not roles of entry `j` (different entries; spine `Role.inEntry`),
   so `β'` agrees with `β` there.
3. New values: `lim owner` and `lim (inner r)` for every `r ∈ K_j.roles` are atoms of
   `freeBlock K_j` (spine body), so these variables lie in `baseVars (posBlock K_j p_j)` and have
   `toFr = none`. Every role of entry `j` other than its slot is `Role.under (heightPath) r` for some
   `r` in the roles of its height (D1.2e item 1), which are `K_j.roles` (D1.4b `relKey_roles`).
4. `Fitted P (j+1) β'`. The atoms of the restricted query graph for `j + 1` are those for `j` plus
   the atoms involving entry `j`. The latter are exactly the `blockMap ⟨sd.col, j⟩`-images of
   `posBlock (relKey t Q[j].2) p_j` (D7.1a `posBlock_heads_graph` for one inclusion,
   `graph_owned_block` for the other), and `relKey t Q[j].2 = K_j` because `queryKeys` normalizes
   at `t = sd.col.num 0` (spine `queryKeys`; D1.6d `stopData_roles`). Their truth at `fitVal β'` is
   the truth of the block atoms at `fitVal β' ∘ blockMap ⟨sd.col, j⟩` (N3.1 `baseHolds_map`), and
   this assignment equals `βb` on every block variable: on frame variables by the frame hypothesis
   and D7.1b `blockMap_frame`, on `owner` and `inner` by step 1 and `relRole ∘ Role.under = id`
   (D7.1a). Conclude with N4.1b `baseHolds_congr`.

**Uses:** D1.2e, D1.4b, D1.6d, D7.1, D7.1a, D7.1b, D7.2b, L7.6a, N3.1, N4.1b.

**Lean:** `Packet.fit_of_block`. Planned file `Packet/ScanPackets.lean`.

**Difficulty:** M (about 200 LOC; the computation of L7.6a step 8).

**Testable:** no (semantic).

## Requires

Facts from other units that the spine does not already provide in the needed form. Each has a
stub in `U3.lean` `namespace Packet.Stubs` (R1–R15, R18, R19), or is described here (R16, R17).
**Integration:** `namespace Packet.Stubs` is deleted. Each row's last column names the node that
now provides the fact; a stub that no owner node stated was moved, verbatim, into the owner's Lean
file as a new node (U1 Part J, U2 D3.1d and D3.1e). Citations `R<n>` in this unit resolve through
that column.
**[Changed in verification:** R11 and R13 corrected; R18 and R19 added.**]**
"Matches" names the node believed to provide it.

| ID | needed_by | owner | statement (exact form: stub) | matches | provider (integration) |
|---|---|---|---|---|---|
| R1 | D6.1a, L4.3, L7.5c, L7.6a | U1 | `truncAfter_spec`: for `e ∈ t.entryAddrs`, truncation is idempotent, keeps `e`, its height and entry, and `prefixRoles (t.truncAfter e) e = prefixRoles t e` | D1.9 / D1.2a (`truncAfter`) | U1 D1.2f `Tree.truncAfter_spec` (stub moved) |
| R2 | D6.1a, L4.3, L4.3a | U1 | `setHeight_basic`: `e` stays an entry; `heightAt e = some h`; idempotence `setHeight∘setHeight = setHeight`; `setHeight e (heightAt e) = id`; truncation after `e` is preserved; the label of `e` is unchanged | D1.2a (`setHeight`) | U1 D1.2f `Tree.setHeight_basic` (stub moved) |
| R3 | L7.6a, L4.2c | U1 | `trace_fst_le_cursor`: `(i,j) ∈ trace src qry → i ≤ cursor src qry` | D2.1 | U1 L2.5a `Scan.trace_fst_le_cursor` (stub removed) |
| R4 | L6.2, L4.3, L7.6a, D4.1b | U1 | `stopData_spec`: `sd.t = sd.col.num 0`; `sd.depth = |sd.col.path|`; `colAt sd.col = Q ++ [(r,∅)]`; `entryAt closingSlot = (r,∅)`; `E.truncAfter closingSlot = E`; `E.roles = rolesBefore T ++ T :: (qs ++ [N])` with `qs` in the query region | D1.6 | U1 D1.6d `Scan.stopData_roles` (stub moved) |
| R5 | L6.2, L4.2c, L7.6a, D4.1b | U1 | `rootData_spec`: `resolve sd.r = rd.col`; `rd.col.num 0 = sd.r`; `rd.layer = |rd.col.path|`; `rd.col.path <+: sd.col.path`; `rd.cursor = cursor (rootKeys) (queryKeys)`; `owner ↔ container`; an active root entry is the last one | D1.6 | U1 D1.6d `Scan.rootData_path` (stub moved) |
| R6 | L4.2d, L4.3 | U1 | `stepKind_ordinary_iff` (`E ≠ ∅`, V, I): ordinary iff stop data exists, not `(0 < depth ∧ Q = [] ∧ r + col+1 = t)`, and the root resolves | D1.6a | U1 D1.6d `Scan.stepKind_ordinary_iff_unfold` (stub moved) |
| R7 | L4.2c, L4.2d | U1 | `cursor_cappedAt`: for a reduced, `⊤`-free `W < cutQuery ks (u+1)`, `cursor ks W ≤ u` and `cursor ks W = cursor (ks.take u ++ [⊤]) W` | L2.1, L2.5 (2) | U1 L2.1d `Scan.cursor_cappedAt` (stub moved; `cappedAt ks u` unfolded to `ks.take u ++ [⊤]`) |
| R8 | L4.2c, L4.2d | U1 | `cut_barrier_read`: for `E` in L, a vertex `y` of the cut path of `(c,k)` resolving to `o`, with `o.container c = some e`: `cutQuery (ks c) k < cutQuery (ks o) (e.idx+1)` | L2.3a (`cut_barrier`†) | U1 L2.3c `Scan.cut_barrier_read` (stub moved) |
| R9 | L4.2c | U1 | `nu_map`: `nu (l.map f) = (nu l).map f` for strictly monotone `f` | D2.1 (S-6 word library) | U1 D2.1a `Scan.nu_map` (stub removed) |
| R10 | D6.1b, L7.5a, L7.5, L7.6a, L4.2c | U2 | `origin_spec` (refines †): χ is injective on `w.H.roles`; it is `none` exactly on the closing slot; its values are roles of `E`; `ord ↦ ord` with equal `num`; for slots, equal labels and `χ(ord e.col) = ord (χ e).col`; `rep` commutes for `q < num`; reading order is preserved | D3.1a (`origin_spec`†) | U2 D3.1d `Closure.origin_spec_full` (stub moved; `Before` written out, `anchorD` is spine §c.11) |
| R11 | L4.2d, L7.4, L7.5, L4.3b, L4.3c | U2 | **[Changed in verification.]** `litCap_spec`: `K.roles = E.roles.take m ++ [U_{⟨c,k⟩}]`; every entry `e ≠ ⟨c,k⟩` keeps `E`'s *label*; every entry `e ≠ ⟨c,k⟩` that does not contain `c` (`¬ e.heightPath <+: c.path`) keeps `E`'s label and height; `entryAt ⟨c,k⟩ = (p,∅)`; for `c.path ≠ []`, I, V: `stopData K` has column `c`, `r = p`, and `Q = first k entries`. (The drafted stub claimed equal `entryAt` for every `e ≠ ⟨c,k⟩`. That is false for the containers of `c`, whose heights are truncated: in `L_2 = [[], [(0, [[(1,∅)]])]]`, with `c` the inner column, `k = 1` and `p = 1`, the outer entry's height becomes `[[(1,∅),(1,∅)]]`.) | D3.1 (`litCap`) | U2 D3.1e `Closure.litCap_spec` (stub moved) |
| R12 | L4.3, L7.5a | U2 | `moves_spec` (moves outside `B`): `RepairList (E.truncAfter b) b ms`; `moveAddr` preserves `num`; `applyMoves` commutes with `setHeight` at `b`; heights are carried; `w.H = (applyMoves (E.truncAfter b) ms).setHeight bm (w.H.heightAt bm)` | D3.1a, L3.1 (`repair`†) | U2 D3.1e `Closure.moves_spec` (stub moved) |
| R13 | L4.3b, L4.3c | U2 | **[Changed in verification.]** `moves_violate`: for every `idx < |w.moves|`, with `X := applyMoves (litCap E w.col w.cut w.par) (w.moves.take idx)` and `m := w.moves[idx]`: `m.col` is a column of `X`, `j = m.j` is its last entry, and `j` contains the stopping column of `X`; `m.i < m.j`; entries `i…j` share a parent `q`; and `H_i < C` (heights of entries `i`, `j` in `X`). This is the content of U2's `MoveOK` (U2.lean, `MovesValidBody`). The drafted stub quantified an arbitrary `X` unrelated to `w`, which made it useless for L4.3b/L4.3c. Move order is not assumed. | L3.1, D3.1a (`MoveOK`) | U2 D3.1e `Closure.moves_violate` (stub moved) |
| R14 | U5 (Case 3), L4.2 | U2 | `repair_exists` (refines `repair`†): an upward literal cap with V, I, S and decorated A gives `w : AdmCap E` with the same column, cut and parent | L3.1 (`repair`†) | U2 L3.1 `Closure.repair`, with T3.2 `std_inL`, `std_condP` for `InL E`, `CondP E` (stub removed; `repair` needs no S of the cap and concludes more) |
| R15 | L4.2c, L4.3, L7.5, L7.6a, D4.1b | U2 | `admCap_query`: for `stopData w.H = some sd`: `sd.t = w.col.num 0`, `sd.r = w.par`, `|Q| = w.cut`, `χ T = A_{w.col}`, query slots have origins `⟨w.col, j⟩` with equal entries | D3.1a | U2 D3.1d `Closure.admCap_query` (stub moved) |
| R16 | L6.2, L6.2a, L4.3a, L4.3 | U1 | `paperOp_ordinary`† in this form: `paperOp H n = some (replaceAt 0 0 Z_1 ℓ H)`, with `Z_{n+1} = ∅`. Body root: `Z_k = head_k :: (replaceAt r (k·d) Z_{k+1} (ℓ−j) (F[i+1:])).cols`. Owner root: `Z_k = [head'_k]`, where the last restored height is `replaceAt r (k·d) Z_{k+1} (ℓ−j−1)`. Here `head_k = T_{r,(k−1)d}(Q) ++ U` with heights `T_{r,kd}`, `d = t − r`, and `(j,i)` = `(rd.layer, rd.idx)` | D1.6a (`paperOp_ordinary`†) | U1 D1.6b `Scan.paperOp_ordinary`, with the spine bodies `ordZ`, `ordLoop`, `ordStep` (SCR-2 of U1) |
| R17 | L6.2c, L4.3a, L4.3 | U1 | `paperOp_special`† in this form: the output replaces `e`'s column `P ⌢ [(p, C ⌢ [[(a,∅)]])]` by `P ⌢ [(p,C)]^{n+ε}` (`ε = 1` iff `P = []`) and changes nothing else | D1.6a (`paperOp_special`†) | U1 D1.6b `Scan.paperOp_special` |
| R18 | L4.3b, L4.3 | U2 | **[New in verification.]** `applyMoves_litCap_addr`: for `CondH E`, `w : AdmCap E`, `b` with `b.heightPath <+: w.col.path` and no move inside `B`, and every `q ≤ |w.moves|`: with `b_q := moveAddr (w.moves.take q) b` and `c_q := ⟨b_q.heightPath ++ w.col.path.drop |b.heightPath|, w.col.col⟩`, `IsUpward E c_q w.cut w.par`, `applyMoves (litCap E w.col w.cut w.par) (w.moves.take q) = litCap E c_q w.cut w.par`, and `c_q`'s first `w.cut` entries in `E` equal `w.col`'s. This is U2 L3.1h (`applyMoves_litCap`) applied to the prefix `w.moves.take q` (MovesValid is prefix-closed by its body), with the relocated column named explicitly. U2's proof (L3.1h step 3) builds exactly this `c_{s+1}`. | L3.1h (`applyMoves_litCap`) | U2 D3.1e `Closure.applyMoves_litCap_addr` (stub moved) |
| R19 | D4.1b, L4.3, L4.3b, L4.3c | U2 | **[New in verification.]** (a) `moveAddr_num`: `(moveAddr ms b).col.num 0 = b.col.num 0` for all `ms`, `b` (a move rewrites only entry indices; `ColAddr.num` reads only column indices). (b) `repairList_height`: `RepairList K b ms → (applyMoves K ms).heightAt (moveAddr ms b) = K.heightAt b`. Unlike R12, neither assumes an `AdmCap` or that the moves avoid `B`. | D3.1a (`moveAddr`, `RepairList`, `applyMove`) | U2 D3.1e `Closure.moveAddr_num`, `Closure.repairList_height` (stubs moved) |

Facts used as the spine already provides them (no request):
- U1: `expand_eq_paperOp`, `expand_deletion`, `stepKind_isSome`, `truncAfter_safePrefix`,
  `word_lt_iff`, `word_injective`, `word_safePrefix`, `cutQuery_lt_succ`, `cursor_spec`,
  `path_nesting`, `capping_iff`†, `trace_map`†, `relKey_lt_iff`, `roles_nodup`†,
  `truncAfter_roles`†.
- U2: `std_inL`, `std_condP`, `inL_expand`, `inL_safePrefix`, `expand_lt`, `cofinal_bound`,
  `upward_condS`†; and, from U2's own blueprint, L3.1c `lt_litCap`/`word_litCap`, L3.1f
  `interval_cap`, D3.1a `RepairStepOK` **[changed in verification:** added; used by L4.2c,
  L4.3, L4.3b, L4.3c**]**.

**Provided to U5** (consumers named in spine §d, plus new):
- `factorization` (spine, SCR1 applied), `factorization_noB`, `targetAbove_blockAbove`;
- `joint_cap`, `joint_repair`;
- `readmit_height`, `readmit_repair`;
- `firstDiff_cap`, `firstDiff_spec`;
- `reduce_confined`, `reduce_childEnds`, `repair_output`, `repair_output_exists`,
  `query_size_bound`;
- `scan_packet`, `scanPacket_spec`;
- `occurrence_map_identity`, `owned_reads`, `graph_prefix`, `graph_deletion`, `graph_special`;
- D6.1a, D7.1a.

U5's Case 2 must call `readmit_height` with `kind' := rk.kind.toDesc`. Its Case 3 must call
`repair_exists` (R14), then `joint_cap`, `joint_repair`, `repair_output_exists`, its own
`DLab`, and finally `readmit_repair`.

---

## Spine change requests

### SCR1 — `Packet.factorization` is false as stated (FIRM statement)

**Status: applied at integration** (spine §i.4).
- **Item:** `theorem factorization` (Spine.lean §c.11). Its only hypotheses are `pk.Valid P` and
  `L < asg owner`.
- **Counterexample.** Take any `P` with `Elem ≡ Edge ≡ True`, and:
  - `E := seed 1 = [[], [(0, ∅)]]` with roles `A_0, A_1, U_{⟨1,0⟩}`, and
    `b := ⟨⟨[],1⟩,0⟩`, so that `tgtSel = 0` and `prefixRoles E b = [A_0, A_1]`;
  - `F := ∅` and `a := ⟨⟨[],0⟩,0⟩`. This `a` is not an entry, and `Admitted` is not assumed;
  - `tgtChart := A_0 ↦ aux 2, A_1 ↦ aux 0`;
  - `srcChart := ord ⟨[],0⟩ ↦ aux 0, slot a ↦ aux 1`;
  - `aux := []`;
  - `asg (aux 2) = ω·2`, `asg (aux 0) = ω·3`, `asg (aux 1) = ω·3 + 1`.

  Every Valid clause holds:
  - injective on `[A_0, A_1]` and on `F.roles = []`;
  - host `aux 0` on both sides;
  - `take 0`;
  - the joint is `lim, lim, lt, elem`, which hold;
  - the heads hold since `Edge ≡ True`;
  - the low names `aux 2`, `aux 0` are `< ω·3+1`.

  With `L = 0` the conclusion needs `ω·3 < L* < ω·3 + 1`, which is impossible.
- **Cause:** `IsLim u` comes only from `lim U_a ∈ graph F`, which needs `a ∈ F.entryAddrs`.
- **Proposed replacement:** add the hypothesis `(ha : pk.rk.a ∈ pk.rk.F.entryAddrs)` (implied by
  `pk.rk.Admitted`). This is `Packet.factorization_mem` in `U3.lean`.
- **Consumers affected:** U5 L8.4 (`sStrict_zero`) and L8.8 ((23)). Both have `Admitted`, so no
  proof changes.
- **Local workaround:** `factorization_mem`, marked `SPINE-CHANGE: SCR1`.

### SCR2 — fill-ins for the `body: U3` declarations (bookkeeping)

**Status: applied at integration** (spine §i.3); the type name in spine §c.10 is corrected to
`Packet.SrcRecord.FirstDiff`.
- **Items:** `qMap`, `fMap`, `SrcRecord.firstDiff`, `ScanSetup.Valid` (sorry bodies in
  Spine.lean).
- **Request:** at T-018 replace the bodies by `qMapDef`, `fMapDef`, `firstDiffDef` and
  `ScanSetup.ValidDef` from `U3.lean`. The bridges `qMap_eq_def`, `fMap_eq_def`,
  `firstDiff_eq_def` and `ScanSetup.valid_iff_def` become `rfl`/`Iff.rfl`.
- **Documentation fix:** spine §c.10 names the type `Packet.FirstDiff`, but the Lean name is
  `Packet.SrcRecord.FirstDiff`.
- **Consumers:** none change. They use the spine names.

No other FIRM item needed a change. `scan_packet`, `Valid`, `TargetAbove`, `Admitted`,
`ScanSetup` and `RoleSets` were each checked against the constructions of L7.5b, L7.5c and
L7.6a.

---

## Proposed simplifications (flagged, not applied)

- **PS1 — refuted in verification [changed in verification].** The drafted proposal said that
  every closed source-greater raw-scan state of an ordinary standard expression (or of an
  admissible cap) has a whole-target first difference, so that only Case 1 of §8.5 would be
  reachable. This is false. Counterexample: the standard
  `E = [[], [(0, [[(1,∅),(0,∅)]])], [(1, [[(2,∅)]]), (1,∅)]]` (seed `L_3`, parameters
  `1,2,1,0,0,2,1,1,1,0,0,1,0,2,1,0,0,1,0,0,1,1,1`) at state `(0,0)` has a `capAt` difference,
  with the target column ending at cut `1` and absolute parent `0`. Among the standard
  expressions of size ≤ 20 with parameters ≤ 2 (no depth limit on the generation), there are:
  - over `E` itself: 3,896 scan records, of which 121 are `capAt` and 88 `childEnds`;
  - over admissible caps: 23,111 scan records, of which 154 are `capAt` and 463 `childEnds`.

  The drafted counts came from a breadth-first generation cut at depth 11 (resp. 8), which
  misses these expressions. Cases 2 and 3 of §8.5, descendant and repair records, and caps as
  `DLab` inputs all stay on the critical path. Do not pursue PS1.
- **PS2.** `Valid` is invariant under injective renaming of names that preserves `asg`. A general
  `valid_rename` lemma would let L7.5b, L7.5c and L7.6a assume convenient fresh names, instead of
  carrying `freshTag` disjointness in each proof.
- **PS3.** In ordinal form `factorization_mem` is a one-step corollary of `pack_below`. U5 could
  inline it, but keeping it costs nothing.

---

## Open problems

| node | issue | severity |
|---|---|---|
| L4.2c | **[Changed in verification.]** The paper's proof (txt:667-681) is compressed; this plan supplies the phases. They were checked against instances, with 0 failures: 1,384 `capAt` differences of scan and descendant records (361 crossing the host, step 4(b)), and 50,878 of admitted repair records (29,962 via host, 4,324 direct exits, 1,344 with moves in the low part). Still unexercised: step 4(b3) with a *moved* cap anchor, i.e. the decorated `H`-path transferred through route columns that carry a deleted same-parent block. Moved-cap anchors gave only 2 `capAt` differences, both internal. Its argument (R7, R8, L4.2b item 1, R13) is the same one that was tested for repair records. | minor |
| L4.2, L4.3 | **OP2 — resolved in verification [changed].** `capAt` and `childEnds` differences do occur among reachable records (PS1, refuted). The cap and child branches of L4.2c, L4.2d, L4.3, L4.3b and L4.3c were tested with a Python model of U2's repair (see the "Testable" lines). | — |
| L4.3b, L4.3c | **OP3 — resolved in verification [changed].** The repaired proofs of L4.3b (invariant `X_q = litCap E c_q k p`, R18) and L4.3c (R19 on the moves before the first one inside `B`) do not depend on the order of the moves. U2's `MoveOK` does not fix an order. | — |
| L7.3 | **SCR1 — closed at integration:** the spine's `factorization` now carries `ha`. | — |
| D7.2b | **OP5 (coordination, unchanged):** U5's L8.6 must build a `ScanSetup` satisfying S5 exactly; since integration U5 proves `Valid` through L8.5h `valid_iff`. The bank's root is the new stopping name, and its pre-root goes through `ePre ∘ χ̂` (txt:1131-1137, 1295-1303). This is a coordination point, not a gap. | minor |
| R4–R6, R16, R17 | **OP6 — closed at integration:** U1's bodies are the spine bodies (SCR-2 of U1), and R4–R6 are U1 D1.6d in exactly the stub forms; R16, R17 are U1 D1.6b `paperOp_ordinary`, `paperOp_special`. | — |

---

## §T Typecheck and bounded test record

**Typecheck** (from the repository root):
```
mkdir -p scratch/blueprint/U3 && { grep -h '^import ' blueprint/lean/U3.lean; cat blueprint/lean/Spine.lean; grep -v '^import ' blueprint/lean/U3.lean; } > scratch/blueprint/U3/check.lean && (cd lean && PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake env lean ../scratch/blueprint/U3/check.lean)
```
Result: 0 errors; only `declaration uses 'sorry'` warnings. The log is
`scratch/blueprint/U3/typecheck.log`.

**Bounded tests** (`scratch/blueprint/U3/`). Each script recomputes roles, `rep` and `graph` from
the spine's definitions. The operation is the existing port `checks/claude/btbm.py` (`FS`), used
read-only.

| script | checks | instances | failures |
|---|---|---|---|
| `test_stage_roles.py … 9 30` | L6.2 (i)–(iv) with `headAddr`/`qMapDef`/`fMapDef` verbatim; L6.2c; L6.2b roles | 8,992 standard expressions; 30,172 ordinary cases (`n ≤ 3`: 1,004 owner, 4,963 body/same forest, 1,576 body/deeper); 1,203 special; 246 deletion | 0 |
| `test_blocks.py … 8 26` | D7.1a: `posBlock` through `blockMap` = owned atoms; chain consecutive; `rep_inside` (a), (b) | 3,502 expressions, 38,754 entries | 0 |
| inline `rep_visible` check | D7.1a item 2 | 273,040 | 0 |
| `test_firstdiff.py` (BFS 11/40; BFS 8/60 with `n ≤ 5`; random) | walker; L4.2c path and L4.2d legality at `capAt` | 73,988 + 112,111 + 4,379 expressions; 4,120 + 876 + 25 records, all `wholeEnds` | 0 (cap branch not reached) |
| `test_firstdiff_caps.py … 7 24` | same, for scan records over literal admissible caps (in L, no moves) | 12,577 caps; 45 records, all `wholeEnds` | 0 (cap branch not reached) |

**[Changed in verification.]** The last two rows used breadth-first generation cut at depth 11
(resp. 8). That cut is why no `capAt` or `childEnds` record appeared (see PS1). The verification
scripts in `scratch/blueprint/U3-verify/` reach and test these branches:
- `t3_records.py` covers scan and descendant records over `E` and over repaired admissible caps,
  for all standard expressions of size ≤ 20 with parameters ≤ 2 (no depth limit; 58,309
  expressions; 0 failures);
- `t4_synthetic.py` tests L4.2d, L4.3b, L4.3, the child construction, L4.3a and admitted repair
  records (0 failures).

The exact commands and counts are in `blueprint/verification/U3.md`.
