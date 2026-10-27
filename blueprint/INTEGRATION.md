# Blueprint integration report

**Task:** T-016, integration step. **Date:** 2026-10-27.

**Inputs:** the spine (`blueprint/00-spine.md`, `blueprint/lean/Spine.lean`), the five verified
units (`blueprint/U1-syntax-scans.md` … `blueprint/U5-descent-main.md` with
`blueprint/lean/U1.lean` … `U5.lean`), the verification notes in `blueprint/verification/`, and
the mechanical integration report (no duplicates, no unresolved uses, three unmatched Requires,
seven Lean-name clashes, no cycles, no uncovered paper node, eleven spine-change requests). The
locked statement (`lean/BTBMS/{Syntax,Expansion,Mahlo,Statement}.lean`) is untouched.

**Result.**
- The integrated check, run exactly as the task gives it, has **0 errors**:
  ```
  mkdir -p scratch/blueprint/all && { grep -h '^import ' blueprint/lean/U*.lean; cat blueprint/lean/Spine.lean; for f in blueprint/lean/U1.lean blueprint/lean/U2.lean blueprint/lean/U3.lean blueprint/lean/U4.lean blueprint/lean/U5.lean; do grep -v '^import ' $f; done; } > scratch/blueprint/all/check.lean && (cd lean && PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake env lean ../scratch/blueprint/all/check.lean)
  ```
  Exit code 0; 661 diagnostics, all ``declaration uses `sorry` ``; no axiom. Log:
  `scratch/blueprint/all/typecheck.log`. Before integration the same command failed with two
  errors (`Scan.ordZ` and `Scan.gwordAt` declared twice, by U1 and by U2's stubs).
- Every bridge between a spine name and a moved body holds by `rfl`/`Iff.rfl`, and the moved
  bodies evaluate: `scratch/blueprint/all/rfl_check.lean` (18 `example`s, plus `#eval!` of
  `expand (seed 2) n = paperOp (seed 2) n` for `n < 5`, `true`, and `stepKind (seed 3)`,
  `some special`; log `rfl_check.log`). The blueprint files keep `sorry` for these proofs, as the
  rules require.
- The node graph has **302 nodes** (U1 60, U2 86, U3 46, U4 51, U5 59), all 61 ledger nodes
  covered, every `Uses` entry resolved to a node, **no cycle**, and no Lean name claimed by two
  nodes. Scripts: `scratch/blueprint/all/{parse_nodes,analyze,metrics,gen_tables}.py`.

---

## 1. What changed

### 1.1 Spine-change requests applied

| Request | From | What was done |
|---|---|---|
| SCR-1 | U1 | Registered U1's shared definitions as FIRM types with U1 bodies (spine §i.1): `EntryAddr.Contains`, `ColAddr.OnStack`, `Tree.lastStep?`, `Scan.IsRoutePath`, `Scan.cutStart`, `Scan.AAt`, `Scan.CutBound`, `Scan.ReturnBound`, `Scan.specialStop`, `Scan.ordStep`, `Scan.ordLoop`, `Scan.ordZ`, `Scan.specialOut`, `Scan.ordinaryOut`, `Scan.Hole.put`, `Scan.Noninc`, `Scan.nuStep`, `Scan.qcursor`, `Scan.GAtom`, `Scan.gword` (and `Scan.gwordAt`, SCR-U2-1), plus the theorems the verifier added (`nu_map` …). Spine §c.10's `x(c,k)` is now `Scan.cutStart E c k`. |
| SCR-2 | U1 | Moved U1's bodies verbatim into `Spine.lean` (`truncAux` … `setHeightBody` in §c.2, `spF` … `safePrefixBody` in §c.4, `stopF` … `paperOpBody` in §c.5, the latter placed after `queryKeys`) and defined the seven spine names by them (spine §i.2). |
| SCR-3 | U1 | Note only (`#eval!` while the order instances have `sorry` proof fields); nothing to apply. |
| SCR-U2-1 | U2 | U2's stubs `Scan.ordZ`, `Scan.gwordAt` deleted (they caused the two errors); U1's declarations registered (spine §i.1); the stub-placement rule restated (spine §i.5, §h.2). |
| SCR-U2-2 | U2 | Moved U2's bodies of `profile`, `litCap`, `applyMove`, `MovesValid`, `RepairList`, `moveAddr`, `AdmCap.origin` and their helpers into `Spine.lean` §c.6; `moveAddr` now precedes `RepairList`, whose body uses it (spine §i.3). |
| SCR1 | U3 | `Packet.factorization` gains `(ha : pk.rk.a ∈ pk.rk.F.entryAddrs)`; the FIRM statement was false (U3's counterexample, confirmed by its verifier). Consumers U5 L8.4, L8.8 assume `Admitted`, which contains `ha`. U3's workaround `factorization_mem` is removed (spine §i.4). |
| SCR2 | U3 | Moved `qMapDef`, `fMapDef` and helpers (§c.8), `firstDiffDef` and the walker (§c.10, with `namespace SrcRecord` closed around them), `anchorD` and `ScanSetup.ValidDef` with its helpers (§c.11) into `Spine.lean`; the four spine bodies are defined by them. Spine text: the type is `Packet.SrcRecord.FirstDiff`. |
| SCR-1 | U5 | Added `Role.under` (§c.2, owner U1) and `Packet.blockMap` (§c.9, owner U3) with real bodies. `blockMap` takes U3's body (its former `blkRole`), which equals U5's proposal by U3 D7.1b `reps0_getElem?`. The contracts are U1 D1.2e `Tree.roles_entry` and U3 D7.1a `posBlock_heads_graph` with D7.1b `blockMap_frame` (spine §i.6). |
| SCR-2 | U5 | Superseded, not applied as proposed: U3's SCR2 makes the owner's `ScanSetup.ValidDef` the body of `ScanSetup.Valid`; U5's need (an exact characterization usable in both directions) is met by the new U5 node L8.5h `valid_iff : S.Valid P ↔ SetupClauses P S`, with a clause-by-clause proof plan. Both U3 and U5 are served; no statement changed. |

The deferred request (SCR-U4-1) is in §2.1.

### 1.2 Unmatched Requires (the three of the mechanical report)

| Requires | Needed by | Resolution |
|---|---|---|
| U5 R1 `Role.under` (owner U1) | L8.2b, L8.8b, R12 | Spine definition `Role.under` (§c.2, vocabulary of U1 D1.2a; SCR-1 of U5). Its lemmas are the new U1 node **D1.2e**. |
| U5 R2 `Packet.blockMap` (owner U3) | L8.3–L8.5, L8.7, L8.8b | Spine definition `Packet.blockMap` (§c.9, vocabulary of U3 D7.1). Its lemmas are U3 D7.1a and the new U3 node **D7.1b**. |
| U5 R27 `special_graph` (owner U3) | L8.7 | New U3 node **L6.2f** `Packet.special_graph`, with `N = n + ε` and `cm i = blockMap ⟨e.col, e.idx + i⟩` (the choice U5's verifier tested), proved from U3 L6.2c. |

### 1.3 All Requires and stubs

The mechanical report matched the other Requires rows to nodes through their "Matches" column, but
several matched nodes did not state the fact (U1 verification V-09, U3 verification F15). Every
row was therefore rechecked against the owner's declarations, and every stub was resolved:
- **removed** where the owner states the same fact (or a stronger one);
- **moved** verbatim into the owner's Lean file as a declaration of a new owner node, with a
  precise statement, a proof plan citing the owner's nodes, `**Fidelity:** new (requested by …)`,
  difficulty and test status;
- the only stub that stays in its consumer is U5's `valid_iff` (R24), because it mentions U5's
  own `SetupClauses`; it is the U5 node L8.5h.

No stub remains in any unit file. Each unit's Requires table now has a final column naming the
provider, so the local citations `R<n>`, `REQ-U1-<n>` resolve to node IDs.

| Unit, request | Provider (node, Lean) | Action |
|---|---|---|
| U2 REQ-U1-1 | U1 D1.6 `Scan.ordZ` (spine body), D1.6b `paperOp_ordinary` | stub removed |
| U2 REQ-U1-2 | U1 N1.2, C1.8a (`gwordAt`, `gword_map`, `gword_lt_iff`, …) | stub removed |
| U2 REQ-U1-3 | U1 D1.6b `stopData_spec`, D1.2d `mem_routeCols_iff`; converse U1 D1.6d `stopData_of_route` | converse new |
| U2 REQ-U1-4, 5, 15 | U1 D1.6b | already stated |
| U2 REQ-U1-6, 8 | U1 D1.5a | already stated |
| U2 REQ-U1-7 | U1 D1.5a `Hole.fill_eq_put`; second form U1 D1.5b `shift_replaceAt` | second form new |
| U2 REQ-U1-9 | U1 D1.2b, D1.3a | already stated |
| U2 REQ-U1-10 | U1 L2.5, L2.5c | already stated |
| U2 REQ-U1-11, 12 | U1 L2.3, L2.4 | already stated |
| U2 REQ-U1-13, 16, 17 | U1 D2.1a, N1.3, L2.1/L2.1a | already stated |
| U2 REQ-U1-14 | U1 D1.9; decoding U1 D1.9b `routeCols_of_word_snoc` | decoding new |
| U2 REQ-U1-18 | U1 N1.4 `wordAt_add`, `wordAt_map` | new |
| U3 R1, R2 | U1 D1.2f `Tree.truncAfter_spec`, `Tree.setHeight_basic` | moved |
| U3 R3 | U1 L2.5a `Scan.trace_fst_le_cursor` | removed |
| U3 R4, R5, R6 | U1 D1.6d `stopData_roles`, `rootData_path`, `stepKind_ordinary_iff_unfold` | moved |
| U3 R7 | U1 L2.1d `Scan.cursor_cappedAt` (`cappedAt` unfolded) | moved |
| U3 R8 | U1 L2.3c `Scan.cut_barrier_read` | moved |
| U3 R9 | U1 D2.1a `Scan.nu_map` | removed |
| U3 R10, R15 | U2 D3.1d `origin_spec_full` (`Before` written out), `admCap_query` | moved |
| U3 R11, R12, R13, R18, R19 | U2 D3.1e `litCap_spec`, `moves_spec`, `moves_violate`, `applyMoves_litCap_addr`, `moveAddr_num`, `repairList_height` | moved |
| U3 R14 | U2 L3.1 `repair` with T3.2 `std_inL`, `std_condP` | removed |
| U3 R16, R17 | U1 D1.6b `paperOp_ordinary`, `paperOp_special` (with the spine bodies) | described only; matched |
| U5 R3, R4, R5, R7 | U1 D1.6d `rootData_col`, `stopData_col_mem`, `ownerEntry_mem`, `lastCol_of_ordinary` | moved |
| U5 R6 | U1 D1.6b `stepKind_deletion_iff` | removed |
| U5 R8 | U1 D1.3b `firstParent_host` | moved |
| U5 R9 | U3 D7.1a `rep_inside` (second conjunct) | removed |
| U5 R10 | U3 D7.1b `reps0_take`, `reps0_length` | moved |
| U5 R11 | U1 D1.2b `roles_nodup`, `resolve_spec` | removed |
| U5 R12, R13 | U1 D1.2e `roles_entry`, `truncAfter_roles_under` | moved |
| U5 R14 | U1 D1.4b `relKey_roles`, `relKey_eq_empty` (with `Tree.roles_map`, moved from U3) | moved |
| U5 R15 | U1 L2.5d `trace_spec` | moved |
| U5 R16, R17 | U2 D3.1d `anchorOrigin_prefix` (stated without `ePrefix`), `lt_admCap` | moved |
| U5 R18 | U3 D7.1a `posBlock_heads_graph`; U3 D7.1b `blockMap_frame` | split: removed + moved |
| U5 R19 | U3 D7.1b `frameOf_mem_prefix` | moved |
| U5 R20 | U4 N4.1a `Hier.Diagram.holds_congr`; U3 N3.1 `Hier.Diagram.holds_map` | removed |
| U5 R21 | U3 D6.1a `graph_truncAfter` (non-entry case by the body, U1 D1.2c) | removed |
| U5 R22, R23 | U3 L6.2e `stage_zero`, `stage_succ`, `queryAtoms_struct_vars` | moved |
| U5 R24 | U5 L8.5h `valid_iff` | became a U5 node |
| U5 R25 | U3 D7.2d `scanRecord_tgtHeight` | moved |
| U5 R26 | U3 L7.6b `fit_of_block` (`queryKey`, `querySel` unfolded) | moved |
| U5 R27 | U3 L6.2f `special_graph` | moved |
| U5 R28 | U3 L4.2 `firstDiff_spec` with `List.prefix_iff_eq_take` | removed |
| U5 R29 | U3 L4.3d `ChildData`, `childEnds_package` | moved |
| U5 R30 | U3 L7.5d `CapData`, `cap_package` | moved |
| U5 R31 | U4 D6.4 `IsWeaklyMahlo.uncountable_regular`, `.stationary_pred` | removed (identical) |

To state the moved U3 nodes, U5's seven syntactic helpers (`isStruct`, `entrySel`, `entryKey`,
`ePrefix`, `queryAtoms`, `retAtoms`, `specialKey`; node N5.7) moved to U3 as node **D6.1c**, same
bodies, namespace `Packet`; U5 reads them through `open Packet`, so no U5 statement changed.

### 1.4 New nodes (22)

| Unit | Nodes |
|---|---|
| U1 (11) | D1.2e, D1.2f, D1.3b, D1.4b, D1.5b, D1.6d, D1.9b, N1.4, L2.1d, L2.3c, L2.5d (Part J of the U1 doc) |
| U2 (2) | D3.1d, D3.1e |
| U3 (8) | D6.1c (moved from U5 N5.7), D7.1b, L6.2e, L6.2f, L4.3d, L7.5d, D7.2d, L7.6b |
| U5 (1) | L8.5h |

U5's N5.7 is no longer a U5 node (it is U3 D6.1c). Each new node has a statement, a proof plan
citing node IDs, `**Fidelity:** new (requested by …)`, a Lean signature that typechecks in the
integrated check, a difficulty and a test status.

### 1.5 Lean-name clashes and duplicates

The seven clashes of the mechanical report:

| Clash | Resolution |
|---|---|
| `ColAddr.num`, `ColAddr.resolve`: D1.2a and D1.2 | D1.2 is the paper node; its Lean line now says "no declaration of its own" and points to D1.2a (definitions) and D1.2b (lemmas). |
| `Scan.cursor_nu`: L2.1c and L2.1 | Owned by L2.1c, which states and proves it; removed from L2.1's Lean line. |
| `Closure.expand_lt`: T3.2x and T3.2 | Owned by T3.2; T3.2x's Lean line no longer names it. |
| `Hier.Diagram.holds_congr`: N3.1 and N4.1a | A real duplicate declaration (U3 had `BTBMS.Packet.Hier.Diagram.holds_congr`). U4's N4.1a is kept; U3's copy is deleted and N3.1 cites N4.1a (verification V-U4-16). |
| `Hier.jCapture`: L5.9a and L5.9 | L5.9 is an umbrella; its Lean line now says "no declaration of its own". |
| `Hier.jTransport`: L5.9b and L5.9 | As above. |

Further duplicates found at integration and removed (the owner's declaration is kept):
- U3 `Packet.cutStart` (= U1 `Scan.cutStart`, D2.2a);
- U3 `factorization_mem` (= the spine `factorization` after SCR1);
- U5 `le_cfgMax`, `cfgMax_lt` (= U3 D6.1a), `baseHolds_map` (= U3 N3.1), `baseHolds_congr`
  (= U4 N4.1b);
- U3 `roles_map` moved to U1 D1.4b as `Tree.roles_map`.

U3's N3.1 lemmas were declared under `BTBMS.Packet.Hier.*` by mistake; they are now
`BTBMS.Hier.*` (with `_root_`). `Closure.kappa` (U2 T3.2h) and `Packet.kappa` (U3 L4.2a) are
different maps in different namespaces; the doc Lean lines now qualify them.

### 1.6 Cycles

None. One apparent cycle shows up if definition names count as dependencies: D8.1 bundles the
FIRM real-bodied definitions `SStrict`, `WFit`, `DCore`, `DLab` (spine §c.12, no proof obligation)
with the induction (18) (`sStrict_all` …, which uses L8.8), while L8.8d and L8.8f take `DLab` as a
hypothesis type. Only the induction theorem of D8.1 depends on L8.8, and L8.8d, L8.8f depend only
on the definitions, so there is no proof cycle. The graph below counts as dependencies only cited
node IDs, the Requires aliases, and theorem names; definition names carry no edge.

### 1.7 Uncovered paper nodes

None: all 61 ledger nodes are nodes of the final graph.

### 1.8 Files changed

- `blueprint/00-spine.md`: §c.2 (`Role.under`), §c.9 (`blockMap`), §c.10 (type name,
  `Scan.cutStart`), §c.11 (`factorization` hypothesis), §h.2, header, and the new §i.
- `blueprint/lean/Spine.lean`: the moved bodies (U1, U2, U3), `Role.under`, `Packet.blockMap`,
  the `factorization` hypothesis, header. The only remaining `sorry` body is `Hier.jInterface`.
- `blueprint/lean/U1.lean` … `U5.lean`: moved bodies removed (bridges kept), stubs removed or
  moved, duplicates removed, the new declarations of §1.4.
- `blueprint/U1-syntax-scans.md` … `U5-descent-main.md`: the new nodes, the Requires provider
  columns, the Lean-line fixes, `**Integration note:**` lines where a definition moved, and the
  status of each spine-change request and of the open problems it affects.
- `blueprint/verification/*` is unchanged.

---
## 2. What remains open

### 2.1 Spine-change request deferred to root

**SCR-U4-1 (U4): make the reflection hierarchy P-U4-1 the body of `Hier.jInterface`.**
- *Status:* not applied. It is a fidelity decision, not a correctness question: the agreed S-4
  says to instantiate the interface "with the J-hierarchy", and U4's verifier left it open
  (V-U4-14). No statement and no consumer depends on the choice: U3 uses only the grammar, U5
  only `Interface` fields and `isLim_ord`, and `Main.lean` only the name `jInterface`. Both
  `jInst` (Part B) and `Refl.interface` (Part C) typecheck against the FIRM `Interface`.
- *Recommendation:* adopt P-U4-1 for the main-theorem route, with the user's sign-off, and keep
  Part B as an optional fidelity track.
  - It replaces about 18k–37k LOC by about 2.5k–5k, and the longest U4 chain from 15 nodes (49
    weighted units, through the XL node L5.5c and eight L nodes) to 11 nodes.
  - It removes R-1, R-4 and R-6 and needs no CU vendoring (R-5).
  - Its mathematics passed adversarial verification (N4.4 items 6–7, N4.7 step 4).
  - The cost is fidelity: the formal proof would no longer certify §5 itself; `MainTheorem` is
    unchanged.
  - If root applies it: set the body of `jInterface` to `Hier.Refl.interface`, and update the
    spine texts listed in the request (docstring, §b row N4.2, §c.7 soundness paragraph, §d U4,
    §e module list, §g R-1/R-4/R-6).

### 2.2 Mathematical gaps carried over from verification (not closed here)

| Item | Node | Issue | Severity | Recommendation |
|---|---|---|---|---|
| OP-U2-1 | T3.8lo | The invariant for the previous-phase root response (step 3) is not written; the statement passed 647 bounded caps. | major | Write the invariant before formalizing T3.8l; until then T3.8lo is the riskiest U2 node. |
| OP-U2-2 | T3.8li, T3.2q | The decorated variant of `head_path` that the projection needs is unstated; it must restrict the query (74 bounded failures for arbitrary reduced `W`, 0 for cut queries). | major | State it for cut queries of `a` (the tested form) and re-verify T3.8li against it. |
| OP-U4-1 / V-U4-15 | L5.5c, L5.5d, L5.8b | Part B's coding layer (canonical order, compatible Σ₁ Skolem functions, coded satisfaction) is at sketch level. | major if Part B is chosen | Moot under the §2.1 recommendation; otherwise design the coding layer first. |
| F13 (U3) | L4.2c | Step 4(b3) with a moved cap anchor was never reached by a bounded instance. | minor | Build a targeted instance when testing L4.2c. |
| OP-U2-3, O5, OP-U2-5…7 | T3.2m, T3.2o, T3.2r, T3.8li–ls, T3.2k | Existential positions untested; no statement-level test of `condP_ord`/`condA_ord`; Q-material handled uniformly; one compressed I step. | minor | As in the U2 doc. |
| OP-U4-3…5 | N4.7, N4.9, C5.3c | Universe lifts, a B/Gödel-operation bridge, CU toolchain. | minor | As in the U4 doc. |

### 2.3 Items created or changed by the integration

| Item | Node | Issue | Recommendation |
|---|---|---|---|
| I-1 | L7.5d (was U5 OP-1) | Every field of `CapData` now has a named U3 or U2 source; `nm_inj`/`nmH_inj` rest on value separation, `marked_frame` on L7.5 and L7.5a. | Confirm field by field when L7.5d is proved; it is on the weighted critical path. |
| I-2 | L6.2e (was U5 OP-2) | U5's verifier tested the stage form against its own model of `q_m`/`f_m`; since integration the spine bodies of `qMap`/`fMap` are U3's. | Re-run `scratch/blueprint/U5-verify/test_u5.py`'s stage check against the spine bodies with `#eval!`. |
| I-3 | L4.3d | Step 2 uses the construction inside L4.3's proof of `reduce_childEnds` (a truncate-and-clear of the source height). | If L4.3's formalizer exposes `A₁` only through the statement, strengthen `reduce_childEnds` by `F₁.roles <+: F.roles` and `graph F₁ ⊆ graph F`. |
| I-4 | D1.2e (items 2–3), D1.2f, D1.3b, D1.4b, D1.5b, D1.6d (items 4–8), D1.9b, N1.4, D3.1d (items 3–4), D7.2d | New statements not yet bounded-tested (the others were tested under their stub names by the verifiers). | Test them now: the bodies they mention are real since SCR-2, SCR-U2-2 and SCR2. |
| I-5 | L7.5b, L7.5c vs U5 L8.8c, L8.8f | U3 provides `readmit_height`/`readmit_repair` (closure of the packet class), but U5 constructs the readmitted packets itself and proves the six Valid clauses again; L7.5b, L7.5c are not on any chain to the main theorem. | Decide at formalization time which side keeps the readmission proof; drop the other. |
| I-6 | U5 N5.5 vs U3 D7.2c | Two fresh-name schemes (`tagBound`, `freshTag`). | Harmless; unify if convenient. |
| I-7 | U1 SCR-3 | `#eval!` is needed while the order instances have `sorry` proof fields. | Prove D1.1 and D1.4 early (they are on layer 1–2). |

The flagged simplifications of every unit (U1 P-1…P-6, U2 PS-U2-1…4, U3 PS2, PS3, U4 P-U4-2,
U5 PS-1…PS-5) are unchanged and not applied. U3's PS1 stays refuted.

---

## 3. Node list per unit

Columns: kind (from the ledger for the 61 paper nodes, otherwise from the node's declarations),
fidelity (from the node's `**Fidelity:**` line), difficulty (S, M, L, XL from `**Difficulty:**`),
layer (§5), and `Uses` resolved to node IDs: cited IDs, the Requires aliases through the
provider columns, and cited theorem names; definition names carry no edge (§1.6). Nodes marked
*(new)* were added at integration.

### U1 syntax-scans (`blueprint/U1-syntax-scans.md`) — 60 nodes

| ID | Title | Kind | Fidelity | Diff. | Layer | Uses |
|---|---|---|---|---|---|---|
| D1.1a | Lawful comparators on trees | lemma | new | M | 0 | — |
| D1.1 | Forests, columns, entries; syntax order | def | as-paper | S | 1 | D1.1a |
| D1.4a | Key labels and relabelling | def | new | S | 0 | — |
| D1.4 | Relative key h_a | def | as-paper | S | 2 | D1.1, D1.1a, D1.4a |
| D1.2a | Address types | structure | new | S | 0 | — |
| D1.2b | Stacks, containment, accessors, roles | def | new | M | 1 | D1.2a |
| D1.2 | Column numbering, visibility, occurrences | def | as-paper | S | 2 | D1.2a, D1.2b |
| D1.2c | `truncAfter` and `setHeight` | def | new | M | 2 | D1.2b |
| D1.2d | The terminal last-column, last-entry route | def | new | S | 2 | D1.2b |
| D1.3 | Conditions V, I, H | def | as-paper | S | 2 | D1.1, D1.2a |
| D1.3a | V as a numeric bound | lemma | new | S | 3 | D1.2b, D1.3 |
| D2.1a | The ν library | def | new | M | 0 | — |
| D2.1 | ν reduction; boundaries strictly increase | def | as-paper | S | 1 | D2.1a |
| L2.1a | Cursor bookkeeping | lemma | new | S | 0 | — |
| L2.5a | Trace bookkeeping | lemma | new | S | 1 | L2.1a |
| L2.1b | Exhaustion is lexicographic comparison | lemma | new | M | 1 | D2.1a, L2.1a |
| L2.1c | Query reduction | lemma | new | S | 1 | D2.1a |
| L2.1 | Scan boundary lemma | lemma | as-paper | S | 2 | D2.1, D2.1a, L2.1a, L2.1b, L2.1c |
| L2.3b | Word observation | lemma | as-paper | S | 1 | D2.1a |
| L2.5 | Exact trace facts (1)–(3) | lemma | as-paper | M | 2 | L2.5a |
| L2.5b | The generic cursor is the locked `scanCount` | lemma | new | S | 3 | D1.1a, D1.4, D1.4a |
| N1.2 | The generic compact word | def | new | S | 0 | — |
| N1.3 | List order lemmas | lemma | new | S | 0 | — |
| C1.8a | The generic word is an order embedding | fact | new | M | 1 | D1.1a, N1.2 |
| C1.8 | The compact word is injective and order-preserving | fact | as-paper | S | 2 | C1.8a, D1.1, N1.2, N1.3 |
| D1.9a | Safe-prefix bookkeeping | def | new | M | 3 | D1.2c |
| D1.9 | Safe prefix | def | as-paper | S | 4 | C1.8, D1.2c, D1.9a |
| L2.5c | The sign criterion | lemma | as-paper | S | 3 | C1.8a, D1.1a, D1.4, D1.4a, N1.2, N1.3 |
| D1.5 | Shifts T_{r,d} and replacement A_{r,d,ℓ,Z} | def | as-paper | S | 0 | — |
| D1.5a | Shift and hole laws | def | new | M | 3 | D1.2d, D1.5, N1.2 |
| D1.6 | The fundamental operation E[n] | def | repaired | M | 3 | D1.2a, D1.4, D1.5, D2.1 |
| D1.6b | Branch data specifications | lemma | new | L | 4 | D1.2b, D1.2d, D1.3, D1.5a, D1.6 |
| D1.6c | Agreement sub-lemmas | lemma | new | L | 5 | D1.2b, D1.2d, D1.3, D1.5a, D1.6, D1.6b, L2.1a, L2.5b |
| D1.6a | The agreement lemma and branch contracts | lemma | repaired | S | 6 | D1.6b, D1.6c |
| D1.7a | Seeds and generation witnesses | lemma | new | S | 0 | — |
| D1.7 | Seeds L_m, Std, generation witness | def | as-paper | S | 1 | D1.7a |
| D2.2 | g_W, ancestors, condition A | def | as-paper | S | 3 | D1.2a, D1.4, D2.1 |
| D2.2a | Responses, edges and paths | def | new | S | 4 | D1.2b, D1.3a, D2.2 |
| D2.3 | Owner return, condition S, class L | def | as-paper | S | 3 | D1.2a, D1.4 |
| D2.3a | Owner-return lemmas | lemma | new | S | 2 | D1.2b |
| L2.2a | The path-nesting induction | lemma | repaired | M | 5 | D1.2b, D1.3a, D2.1, D2.1a, D2.2a, L2.1, L2.1a |
| L2.2 | Path nesting lemma | lemma | repaired | S | 6 | L2.2a |
| L2.3a | The barrier's joint predicates | lemma | repaired | M | 5 | D1.2b, D2.1, D2.1a, D2.2a, D2.3a, L2.1, L2.3b |
| L2.3 | Barrier lemma | lemma | repaired | S | 6 | D1.2b, D2.2a, L2.3a |
| L2.4b | Capped responses, route visibility, forward paths | lemma | new | M | 6 | D1.2b, D1.2d, D2.2a, L2.1, L2.3a, L2.5, L2.5a |
| L2.4a | Reverse capping by first divergence | lemma | repaired | M | 7 | D2.2a, L2.3a, L2.4b |
| L2.4 | Capping lemma | lemma | repaired | S | 8 | L2.3a, L2.4a, L2.4b |
| L2.4c | Every operation is defined on V, I, A, S | lemma | repaired | S | 7 | D1.2b, D1.6a, D1.6b, D2.1, D2.2a, D2.3a, L2.1, L2.3, L2.5 |
| N1.1 | Decidable mirrors and test generators | def | new | M | 5 | D1.3, D2.2, D2.2a, D2.3 |
| D1.2e *(new)* | Roles of an entry, and the stack before it | lemma | new | M | 3 | D1.2a, D1.2b, D1.2c |
| D1.2f *(new)* | Truncation and height replacement: basic laws | lemma | new | M | 4 | D1.2b, D1.2c, D1.2e |
| D1.3b *(new)* | First parents of nonempty heights | lemma | new | S | 4 | D1.2a, D1.2b, D1.3, D1.3a |
| D1.4b *(new)* | Shape of relative keys | lemma | new | S | 3 | D1.4 |
| D1.5b *(new)* | Shifts commute with unshifted placement | lemma | new | S | 4 | D1.5, D1.5a |
| D1.6d *(new)* | Branch data in the forms used by U3 and U5 | lemma | new | M | 5 | D1.2b, D1.2c, D1.2d, D1.2e, D1.6, D1.6b |
| D1.9b *(new)* | One-atom extensions of a word | lemma | new | M | 5 | C1.8, D1.2d, D1.9, D1.9a |
| N1.4 *(new)* | Depth shift and relabelling of the compact word | lemma | new | S | 3 | C1.8 |
| L2.1d *(new)* | Cursor below a boundary, with the key raised to `⊤` | lemma | new | S | 3 | L2.1, L2.1a, L2.5, L2.5a |
| L2.3c *(new)* | The cut barrier read at a containing column | lemma | new | S | 7 | D1.2b, D2.1a, L2.3 |
| L2.5d *(new)* | Trace specification | lemma | new | S | 2 | D2.1, L2.5a |

### U2 closure-cofinality (`blueprint/U2-closure-cofinality.md`) — 86 nodes

| ID | Title | Kind | Fidelity | Diff. | Layer | Uses |
|---|---|---|---|---|---|---|
| D3.1 | Profile, condition P, literal and upward caps | def | as-paper | S | 0 | — |
| D3.1b | Tower keys | def | new | S | 0 | — |
| D3.1c | Cap positions and local suffixes | def | new | S | 1 | D3.1 |
| D3.1a | Moves, repair lists, admissible caps, origin map | def | repaired | M | 9 | D3.1, T3.8c |
| T3.2b | Word fact: two first-change positions | theorem | simplified | S | 0 | — |
| L3.4 | Word criterion | lemma | simplified | S | 0 | — |
| L3.7 | Delayed-change lemma | lemma | simplified | S | 0 | — |
| T3.2p | Reset identity and head cursor | theorem | simplified | S | 3 | D2.1, D2.1a, L2.1, L2.1a |
| L3.1c | Word of a literal cap | lemma | new | M | 3 | C1.8, D3.1, D3.1c |
| N2.1 | Literal caps from words | lemma | new | M | 6 | C1.8, D1.9, D1.9b, D3.1c, L3.1c |
| L3.1b | Pure towers | lemma | repaired | M | 2 | D1.1, D1.2a, D3.1, D3.1b |
| L3.1a | `V ∧ I ∧ H ∧ P ⇒ S` | lemma | repaired | S | 3 | L3.1b |
| L3.1d | Γ bound for V,I-legal upward caps | lemma | repaired | M | 4 | L3.1b, L3.1c |
| L3.1e | S for upward caps (`upward_condS`†) | lemma | repaired | M | 5 | D1.4, L3.1a, L3.1b, L3.1c, L3.1d |
| L3.1f | Interval fact | lemma | as-paper | S | 7 | C1.8, L3.1c, N2.1 |
| L3.1g | A legal move keeps decorated responses | lemma | as-paper | M | 10 | D3.1a |
| L3.1h | Legal moves keep literal caps | lemma | as-paper | M | 10 | D3.1a, L3.1c, L3.1f |
| L3.1 | Profile and repair lemma (`repair`†) | lemma | repaired | L | 11 | L2.4, L3.1e, L3.1g, L3.1h, T3.8c |
| D3.1d *(new)* | The surviving-role map: full specification | lemma | new | M | 12 | D1.1, D1.1a, D1.2b, D1.6b, D1.6d, D3.1, D3.1a, D3.1e, L3.1c |
| D3.1e *(new)* | Literal caps and moves: address facts | lemma | new | M | 11 | D1.2c, D1.2d, D1.2f, D1.6b, D1.6d, D3.1, D3.1a, L3.1f, L3.1h |
| D3.3 | Kernel `F_E` and context `C_E` | def | simplified | S | 0 | — |
| D3.3a | Iterate identity | lemma | as-paper | M | 7 | D1.5, D1.5a, D1.5b, D1.6, D1.6a, D3.3 |
| D3.3b | Words of kernels and contexts | lemma | as-paper | M | 5 | C1.8, D1.5, D1.5a, D1.5b, D1.6, D3.3, N1.4 |
| D3.3c | Success, covering, kernel conjugacy | def | new | S | 5 | D1.5, D1.5a, D1.5b, D3.3, T3.2h |
| L3.5 | Filling identity (1), cancellation (2), root restriction | identity | simplified | M | 6 | D1.5, D1.5a, D1.5b, D1.9, D3.1c, D3.3, D3.3b |
| T3.2h | Shift and normalization identities | theorem | as-paper | S | 3 | C1.8, D2.1 |
| T3.2i | Phase classification of ordinary outputs | theorem | repaired | L | 8 | D1.5, D3.3, D3.3a, L3.5, T3.2h |
| T3.2l | Changed continuations decrease | theorem | as-paper | S | 8 | D1.6, D3.3a, D3.3b |
| T3.2j | Body columns lie in the root subtree | theorem | as-paper | M | 7 | D1.2a, D1.2b, D1.3a, D2.2, L2.2 |
| T3.2c | Safe prefixes keep V, I, H | theorem | as-paper | S | 6 | D1.9, D1.9b |
| T3.2d | Safe prefixes keep S | theorem | as-paper | M | 7 | C1.8, T3.2b, T3.2c |
| T3.2e | Safe prefixes keep A | theorem | as-paper | M | 9 | L2.3, L2.4, L2.5, T3.2c, T3.2d |
| T3.2f | Safe prefixes keep P | theorem | as-paper | M | 7 | L3.1b, T3.2c |
| T3.2g | Deletions and zero-parameter ordinary steps are safe prefixes | theorem | as-paper | S | 8 | C1.8, D1.6a, D1.9, D3.3a, D3.3b |
| T3.2k | Ordinary outputs satisfy V and I | theorem | as-paper | M | 9 | D1.2a, T3.2i, T3.2j |
| T3.2x | Ordinary outputs satisfy H | theorem | as-paper | M | 9 | T3.2h, T3.2i, T3.2l |
| T3.2m | Owner returns of ordinary outputs have old origins | theorem | as-paper | L | 9 | T3.2b, T3.2h, T3.2i, T3.2l |
| T3.2n | Ordinary outputs satisfy S | theorem | as-paper | S | 10 | C1.8, T3.2b, T3.2h, T3.2m |
| T3.2o | Ordinary steps preserve P | theorem | as-paper | L | 10 | L3.1b, T3.2f, T3.2i, T3.2m |
| T3.2q | Paths through heads | theorem | as-paper | L | 9 | L2.1, L2.2, L2.5, T3.2h, T3.2i, T3.2p |
| T3.2r | Ordinary outputs satisfy A | theorem | as-paper | XL | 11 | L2.3, L2.4, T3.2i, T3.2k, T3.2n, T3.2p, T3.2q |
| T3.2s | Special outputs satisfy V, I, H | theorem | as-paper | S | 7 | D1.6a |
| T3.2t | Special outputs satisfy S, and P when present | theorem | as-paper | M | 8 | L3.1b, T3.2b, T3.2d, T3.2f |
| T3.2u | Special outputs satisfy A | theorem | as-paper | M | 9 | L2.4, T3.2s, T3.2t |
| T3.2v | Seeds; T3.2w the empty forest | theorem | as-paper | S | 4 | L3.1a |
| T3.2 | Closure theorem | theorem | repaired | S | 12 | D1.6a, D1.7, D3.3a, D3.3b, T3.2c, T3.2d, T3.2e, T3.2f, T3.2g, T3.2k, T3.2l, T3.2n, T3.2o, T3.2r, T3.2s, T3.2t, T3.2u, T3.2v, T3.2x |
| T3.2a | The Lean `IsStd` is the paper's Std | theorem | repaired | S | 13 | D1.6a, D1.7, T3.2 |
| T3.8n | Cofinality predicates | theorem | new | S | 6 | D3.3c |
| T3.8a | An empty last column is least | theorem | as-paper | S | 0 | — |
| T3.8b | Approximants strictly increase | theorem | as-paper | S | 8 | D1.5, D1.6a, D3.3a, D3.3b, L3.4 |
| T3.8c | Caps are ordinary, their data and zero approximant | theorem | as-paper | S | 8 | D1.6, D1.6a, D3.3a, D3.3b, L3.1c |
| N2.2 | Local suffix decomposition and fill | lemma | new | M | 9 | C1.8, D1.9, D3.3b, L3.1c, T3.8c |
| T3.8d | Between `E[1]` and `E`, `E` is a cap of the target | theorem | as-paper | M | 9 | C1.8, D3.3a, D3.3b, L2.4, N2.1, T3.8c |
| T3.8e | Special steps cover | theorem | as-paper | M | 9 | D1.6a, D3.1c, T3.8b |
| T3.8f | Covering is kernel success | theorem | as-paper | M | 10 | C1.8, D3.3a, D3.3b, L2.4, L3.4, N2.2, T3.8c |
| L3.4f | Full one-column cuts succeed | lemma | as-paper | S | 10 | D3.3, L2.4, N2.2, T3.8c |
| T3.8h | Caps above a covered old target | theorem | as-paper | S | 9 | L2.4, T3.8b |
| T3.8g | Kernel success gives cofinality | theorem | as-paper | S | 13 | D1.1, D1.6a, L2.4, T3.2, T3.8a, T3.8b, T3.8d, T3.8e, T3.8f |
| L3.6a | Reversed repairs compare suffixes | lemma | as-paper | S | 10 | C1.8, L3.1f, N2.2 |
| L3.6b | Success transfers backward through one move | lemma | as-paper | L | 11 | L2.4, L2.5, L3.1e, L3.4, L3.5, L3.6a, N2.2 |
| L3.6 | Cap completion lemma | lemma | as-paper | S | 12 | L3.1, L3.1c, L3.1g, L3.1h, L3.6b, T3.8b, T3.8c, T3.8f |
| T3.8i | Seeds | theorem | as-paper | S | 11 | L3.4f, T3.8f |
| T3.8j | Safe prefixes of a covered target | theorem | as-paper | S | 13 | D1.9, D1.9b, L3.1c, L3.4f, T3.2, T3.8c, T3.8f, T3.8h |
| T3.8k | Special outputs | theorem | as-paper | M | 13 | L3.1c, L3.4f, T3.2, T3.8f, T3.8h |
| T3.8l | The ordinary induction step | theorem | as-paper | M | 14 | L3.1c, L3.4f, L3.6, T3.8b, T3.8c, T3.8f, T3.8h, T3.8la, T3.8lb, T3.8lc, T3.8ld, T3.8le, T3.8lf, T3.8lg, T3.8lh, T3.8li, T3.8lj, T3.8lk, T3.8ll, T3.8lm, T3.8ln, T3.8lo, T3.8lp, T3.8lq, T3.8lr, T3.8ls |
| T3.8la | Cut locations | theorem | as-paper | M | 9 | D3.3a, D3.3b, L3.1c, T3.2i |
| T3.8lb | Old terminal cap of a head-query cut | theorem | as-paper | M | 11 | T3.2i, T3.2q, T3.8li |
| T3.8lc | Head-query cuts succeed | theorem | as-paper | M | 13 | D3.3c, L2.5, L3.4, L3.6, T3.2h, T3.2i, T3.8f, T3.8lb |
| T3.8ld | The seam | theorem | as-paper | L | 9 | D3.3a, D3.3c, T3.2h, T3.2i, T3.2p |
| T3.8le | No smaller closing parent at the seam | theorem | as-paper | M | 10 | L2.3, T3.2p, T3.2q |
| T3.8lf | Restored-suffix cuts have `ρ < r` | theorem | as-paper | S | 9 | T3.2i |
| T3.8lg | The old root cap of a restored-suffix cut | theorem | as-paper | M | 10 | T3.2e, T3.2p, T3.8lf |
| T3.8lh | Restored-suffix cuts succeed | theorem | as-paper | L | 11 | D3.3b, L2.1, L3.5, L3.7, N2.2, T3.2h, T3.2i, T3.2l, T3.2p, T3.8lg |
| T3.8li | Projection to an old cap | theorem | as-paper | XL | 10 | L2.3, T3.2e, T3.2h, T3.2i, T3.2q, T3.8ln |
| T3.8lj | Proper current root `ρ > s_φ` | theorem | as-paper | M | 9 | D3.3c, L2.4, L3.4, T3.2h, T3.2i, T3.2l, T3.8c |
| T3.8lk | Current head root `ρ = s_φ` | theorem | as-paper | M | 10 | T3.2h, T3.2i, T3.2p, T3.8lj, T3.8ll, T3.8ln |
| T3.8ll | Wins at once | theorem | as-paper | S | 1 | D3.3 |
| T3.8lm | Sign independence | theorem | as-paper | S | 4 | T3.2h |
| T3.8ln | Parent dichotomy for phase material | theorem | as-paper | S | 9 | T3.2i |
| T3.8lo | The response at a previous-phase root | theorem | as-paper | L | 10 | T3.2q, T3.8lm, T3.8ln |
| T3.8lp | Previous-phase root `r < ρ < s_φ` | theorem | as-paper | S | 11 | T3.8c, T3.8ll, T3.8ln, T3.8lo |
| T3.8lq | Fixed roots: the cursors agree | theorem | as-paper | M | 9 | L2.4, L3.1e, T3.2h, T3.2i |
| T3.8lr | Closed side targets | theorem | as-paper | M | 10 | L3.5, N2.2, T3.2h, T3.2i, T3.8lq |
| T3.8ls | Direct body targets | theorem | as-paper | L | 10 | D3.3b, L3.5, L3.7, N2.2, T3.2h, T3.2i, T3.2l, T3.8lq |
| T3.8m | Kernel success for standard targets | theorem | as-paper | S | 15 | D1.6a, D1.7, T3.2, T3.2g, T3.8g, T3.8i, T3.8j, T3.8k, T3.8l |
| T3.8 | Cofinality theorem | theorem | as-paper | S | 16 | T3.2, T3.8g, T3.8m |

### U3 records-packets (`blueprint/U3-records-packets.md`) — 46 nodes

| ID | Title | Kind | Fidelity | Diff. | Layer | Uses |
|---|---|---|---|---|---|---|
| D6.1 | Graph Γ(E), configurations, role sets | def | as-paper | S | 4 | D1.2, D1.6 |
| D6.1a | Ownership, reading order, truncation and prefix lemmas | def | new | M | 5 | D1.2c, D1.2f, D6.1 |
| D6.1c *(new)* | Syntactic helpers of ordinary and special steps | def | new | S | 10 | D3.1a, D6.1 |
| D6.3 | Persistent map ι_m | def | as-paper | S | 10 | L6.2, L6.2d |
| L6.2a | Stage addresses, relocations and the explicit maps q_m, f_m | lemma | new | M | 7 | D1.2, D1.5, D1.6a, D1.6b, D6.1 |
| L6.2 | Occurrence-map identity | lemma | repaired | L | 8 | D1.2b, D1.6a, D1.6b, D1.6d, D2.1, D6.1, D6.1a, D7.1a, L2.1, L2.1d, L2.3c, L6.2a |
| L6.2b | Graph of a deletion step | lemma | new | S | 7 | D1.6a, D6.1a |
| L6.2c | Graph of a special step | lemma | new | M | 8 | D1.4b, D1.6a, D1.6b, D7.1a, L6.2a |
| L6.2d | Pre-stop prefixes are unchanged (`graph_prefix`) | lemma | as-paper | S | 9 | D6.1a, L6.2 |
| L6.2e *(new)* | Stage form of the occurrence-map identity | lemma | new | M | 11 | D1.2e, D6.1, D6.1a, D6.1c, D7.1b, L6.2, L6.2a |
| L6.2f *(new)* | Block form of the graph of a special step | lemma | new | M | 11 | D1.2e, D1.4b, D1.6d, D6.1a, D6.1c, D7.1, D7.1a, D7.1b, L6.2a, L6.2c |
| D6.1b | Graph transport along the surviving-role map of an anchor | def | new | M | 13 | D3.1d, D6.1, D6.1a |
| D7.1 | Names, charts, frames, blocks, Cert_B, No_B | def | simplified | S | 3 | D1.2, N4.1 |
| D7.1a | Frames and blocks read inside a tree | def | new | M | 6 | D1.2, D6.1, D6.1a, D7.1 |
| D7.1b *(new)* | Frames of nested columns; frames in the prefix | lemma | new | S | 7 | D1.2b, D1.2e, D7.1, D7.1a |
| N3.1 | Finite-name amalgamation and packing | lemma | simplified | S | 1 | N4.1 |
| D4.1 | Scan, descendant and repair records | def | repaired | S | 10 | D3.1a |
| D4.1a | Admission and the first-difference classifier | def | repaired | M | 11 | D1.4, D4.1 |
| D4.1b | Basic facts about admitted records | lemma | new | S | 13 | D1.6d, D3.1d, D3.1e, D4.1a |
| L4.2a | The label map κ and key transfer | lemma | new | S | 3 | D1.4 |
| L4.2b | Scan word facts for caps, moves and descendants | lemma | new | S | 2 | D2.1 |
| L4.2c | Path transfer: the new parent is on the target's actual cut chain | lemma | new | XL | 14 | D1.6d, D1.9, D2.1, D2.1a, D3.1a, D3.1d, D3.1e, D4.1a, D7.1a, L2.1, L2.1d, L2.2, L2.3c, L2.4, L2.5, L4.2a, L4.2b, L4.3a, T3.2 |
| L4.2d | Legality of the first-difference cap | lemma | new | L | 13 | D1.6d, D3.1e, D7.1a, L2.1d, L2.3c, L3.1, T3.2 |
| L4.2 | First-difference lemma | lemma | repaired | S | 15 | D4.1a, D4.1b, L4.2c, L4.2d |
| L4.3a | Confined operations and safe prefixes inside the marked height | lemma | repaired | M | 13 | C1.8, D1.2f, D1.6a, D1.6b, D1.6d, D1.9, T3.2 |
| L4.3c | Repairs take place outside the marked internal height | lemma | new | M | 14 | D1.4, D3.1a, D3.1e, D4.1a, L4.3a, T3.2 |
| L4.3b | The marked old height increases along repairs, (6) | lemma | new | M | 15 | C1.8, D3.1e, L3.1c, L3.1f, L4.3c, T3.2 |
| L4.3 | Source reduction lemma, (6), (7) | lemma | repaired | L | 17 | D1.2f, D1.4, D1.6b, D1.6d, D1.9, D3.1d, D3.1e, D4.1a, D4.1b, L3.1c, L4.2d, L4.3a, L4.3b, L4.3c, T3.2, T3.8 |
| L4.3d *(new)* | The data of §8.5 Case 2 | lemma | new | M | 18 | D1.2c, D1.2e, D6.1a, L4.3, L4.3a |
| D7.2 | Source packet | def | repaired | S | 11 | D4.1, D7.1, N4.1 |
| D7.2a | Validity and the target conclusion | def | repaired | S | 12 | D7.2 |
| D7.2c | Fresh names | def | new | S | 4 | D7.1 |
| L7.3 | Factorization lemma | lemma | repaired | S | 13 | D6.1, D7.2a, N3.1 |
| L7.3b | Target blocks are block realizations | lemma | new | S | 13 | D7.2a |
| L7.3a | The failure label at the raised floor, (23) | lemma | simplified | S | 14 | L7.3, N3.1 |
| L7.4 | Joint cap lemma | lemma | simplified | L | 15 | D1.2f, D3.1e, D4.1a, D6.1a, D7.1a, D7.2a, L4.3c, N3.1 |
| L7.5a | The external frame survives repairs | lemma | new | M | 13 | D3.1d, D3.1e |
| L7.5 | Joint repair lemma | lemma | simplified | M | 16 | D1.6d, D3.1d, D3.1e, D6.1a, D6.1b, L4.3c, L7.4, L7.5a |
| L7.5b | Readmission after a confined source reduction (§8.5 Case 2) | lemma | new | M | 18 | D6.1a, D7.1a, D7.2a, D7.2c, L4.3, N3.1 |
| L7.5c | Readmission after the repaired-cap descent (§8.5 Case 3) | lemma | new | M | 18 | D1.2f, D6.1a, D7.2c, L4.3, L6.2d, L7.5a, N3.1 |
| L7.5d *(new)* | The data of §8.5 Case 3 | lemma | new | M | 18 | D1.2e, D1.2f, D1.6b, D1.6c, D3.1d, D3.1e, D6.1a, D6.1c, L3.1, L4.2, L4.3, L4.3c, L6.2a, L7.4, L7.5, L7.5a, N3.1, T3.2 |
| D7.2b | Scan setup and its validity (§7.3 hypotheses) | structure | repaired | S | 14 | D6.1, D6.1b, D7.2 |
| D7.2d *(new)* | Targets of scan records | lemma | new | S | 15 | D1.6d, D3.1d, D7.2b, T3.2 |
| L7.6a | The explicit packet at a scan state and the fitting extension | lemma | repaired | L | 15 | D1.2c, D1.2f, D1.6d, D1.9, D3.1d, D4.1a, D6.1a, D6.1b, D7.1a, D7.2b, D7.2c, L2.5a, N3.1, T3.2 |
| L7.6 | Complete packets at a scan (17) | lemma | repaired | S | 16 | L7.6a |
| L7.6b *(new)* | Fitting one query entry from a block | lemma | new | M | 16 | D1.2e, D1.4b, D1.6d, D7.1, D7.1a, D7.1b, D7.2b, L7.6a, N3.1, N4.1b |

### U4 hierarchy (`blueprint/U4-hierarchy.md`) — 51 nodes

| ID | Title | Kind | Fidelity | Diff. | Layer | Uses |
|---|---|---|---|---|---|---|
| F5.1a | Limit coordinates | fact | new | S | 0 | — |
| F5.1 | (8): `v < u`, `Lim(u)` ⇒ `v + ω ≤ u` | fact | as-paper | S | 1 | F5.1a |
| D6.4 | Finite Mahlo hierarchy and its helpers | def | simplified | S | 1 | F5.1a |
| N4.1 | Diagram grammar and interface | def | new | S | 0 | — |
| N4.1b | Base-level congruence: values and frames | lemma | new | S | 1 | N4.1 |
| N4.1a | Congruence and locality of diagram truth | lemma | new | M | 2 | N4.1, N4.1b |
| C5.3b | Formulas of set theory, Δ₀ and Σ₁, absoluteness | fact | as-paper | M | 0 | — |
| D5.2 | The basis B, `S(X)` and `J` | def | as-paper | M | 0 | — |
| D5.2a | Bounded graphs of the basis operations and of `S` | lemma | as-paper | M | 1 | C5.3b, D5.2 |
| C5.3a | Transitivity and closure of the levels | fact | as-paper | M | 1 | D5.2 |
| C5.3c | Truth tables of fixed formulas | fact | as-paper | L | 2 | C5.3a, C5.3b, D5.2 |
| C5.3d | The uniform bounded table verifier | fact | as-paper | L | 3 | C5.3a, C5.3b, C5.3c |
| C5.3e | `S(T)` inside closed levels | fact | as-paper | L | 3 | C5.3a, C5.3c |
| C5.3 | Truth tables, bounded verifier, `S(T)` inside closed levels | fact | as-paper | L | 4 | C5.3a, C5.3b, C5.3c, C5.3d, C5.3e |
| C5.4 | (9) Heights and sizes | fact | as-paper | L | 3 | C5.3a, C5.3c, D5.2 |
| L5.5a | Histories: the bounded check and uniqueness | lemma | as-paper | M | 2 | C5.3b, D5.2, D5.2a |
| L5.5b | The history budget | lemma | as-paper | L | 4 | C5.3a, C5.3b, C5.3c, C5.4, F5.1a, L5.5a |
| L5.5g | `ξ ↦ J_ξ` is globally single-valued Σ₁ | lemma | as-paper | M | 5 | C5.3a, C5.3b, F5.1, L5.5a, L5.5b |
| L5.5c | The canonical well-order `<_J` | lemma | as-paper | XL | 5 | C5.3a, C5.3b, C5.3c, D5.2, F5.1, L5.5a, L5.5b |
| L5.5f | The canonical Σ₁ hull (definition) | lemma | as-paper | S | 1 | C5.3b, D5.2 |
| L5.5d | Compatible canonical Σ₁ Skolem functions | lemma | as-paper | L | 6 | C5.3a, C5.3b, C5.3d, D5.2, L5.5c, L5.5f |
| L5.5e | Hulls: elementarity, monotonicity, continuity, size, compatibility | lemma | as-paper | L | 7 | C5.3a, C5.3b, D5.2, L5.5d, L5.5f |
| L5.5 | History and hull lemma | lemma | as-paper | XL | 8 | L5.5a, L5.5b, L5.5c, L5.5d, L5.5e, L5.5f, L5.5g |
| L5.6a | Collapse of a Σ₁ substructure | lemma | as-paper | M | 1 | C5.3b, D5.2 |
| L5.6 | Condensation | lemma | as-paper | XL | 5 | C5.3a, C5.3b, C5.4, D5.2, D5.2a, F5.1, L5.5a, L5.5b, L5.6a |
| D5.7 | Control edges (10) and the J primitives | def | as-paper | S | 2 | C5.3b, D5.2, L5.5f |
| D5.7a | Edges give `J_a ≺ J_b`; repair of G-004 | lemma | repaired | M | 8 | C5.3a, C5.3b, C5.4, D5.7, L5.5e, L5.5f, L5.5g |
| D5.7b | Environment restriction | lemma | as-paper | S | 8 | C5.3a, C5.3b, C5.4, D5.7, L5.5e |
| D5.7c | Environment extension | lemma | as-paper | S | 8 | C5.3b, D5.7, L5.5e |
| D5.7d | The control collapse | lemma | as-paper | M | 8 | C5.3a, C5.4, D5.7, L5.5e, L5.6, L5.6a |
| L5.8b | `JElem`, `JEdge` are Δ₀ in a history parameter | lemma | as-paper | L | 8 | C5.3b, C5.3d, D5.7, L5.5a, L5.5d, L5.5e |
| L5.8c | Block problems are Δ₀ in their parameters | lemma | as-paper | L | 9 | C5.3b, C5.4, L5.8b, N4.1b |
| L5.8d | (16) The negative label is Δ₀ | lemma | as-paper | S | 10 | L5.8c |
| L5.8a | Certificate lemma, ordinal form | lemma | simplified | L | 11 | C5.3a, C5.3b, C5.4, F5.1, L5.5a, L5.5b, L5.5g, L5.8b, L5.8c, L5.8d, N4.1a |
| L5.8 | Certificate lemma | lemma | simplified | XL | 12 | L5.8a, L5.8b, L5.8c, L5.8d |
| L5.9a | Capture | lemma | simplified | S | 12 | C5.4, D5.7, L5.8a |
| L5.9b | Control transport | lemma | simplified | M | 13 | D5.7, D5.7d, L5.5e, L5.6, L5.8a, L5.9a, N4.1a |
| L5.9 | Capture and transport | lemma | simplified | S | 14 | L5.9a, L5.9b |
| L6.5 | (13) `J_κ ≺₁ J_w` | lemma | simplified | M | 8 | C5.3a, C5.3b, C5.4, D5.2, D6.4, L5.5e, L5.6, L5.6a |
| L6.6a | Hulls meet `J_κ` boundedly | lemma | simplified | M | 8 | C5.3a, C5.4, D5.2, D6.4, F5.1a, L5.5e |
| L6.6 | (14) The club of reflection points | lemma | simplified | M | 9 | C5.3a, D5.2, D6.4, F5.1a, L5.5e, L6.5, L6.6a |
| N4.2 | The J instance of the interface | def | new | S | 14 | C5.3a, C5.3b, D5.7, D5.7a, D5.7b, D5.7c, L5.9a, L5.9b, L6.5, L6.6 |
| N4.3 | The language `{<, Elem, Edge}` and the structures `M(ν, Q)` | def | new | S | 1 | N4.1 |
| N4.4 | Translation of the grammar into first-order formulas | lemma | new | L | 3 | N4.1, N4.1a, N4.1b, N4.3 |
| N4.5 | The recursive definition of `Elem` and `Edge` | def | new | M | 4 | N4.1a, N4.4 |
| N4.6 | The structural laws, capture and transport | lemma | new | M | 5 | N4.1a, N4.5 |
| N4.7 | Hulls and condensation in `M_w` | lemma | new | L | 6 | N4.1a, N4.3, N4.4, N4.5, N4.6 |
| N4.8 | Transfer through a collapsed hull | lemma | new | M | 7 | N4.1a, N4.4, N4.7 |
| N4.9a | (13) for the reflection hierarchy | lemma | new | M | 8 | D6.4, F5.1a, N4.1a, N4.5, N4.7, N4.8 |
| N4.9b | (14) for the reflection hierarchy | lemma | new | M | 9 | D6.4, F5.1a, N4.1a, N4.5, N4.7, N4.8, N4.9a |
| N4.10 | The reflection instance | def | new | S | 10 | N4.6, N4.9a, N4.9b |

### U5 descent-main (`blueprint/U5-descent-main.md`) — 59 nodes

| ID | Title | Kind | Fidelity | Diff. | Layer | Uses |
|---|---|---|---|---|---|---|
| N5.2 | Elementarity chains | lemma | new | S | 0 | — |
| N5.3 | Block problems: floor encoding, capture, monotonicity | lemma | new | M | 7 | N5.4 |
| N5.4 | Order facts of configurations and maxima | lemma | new | S | 6 | D6.1a, F5.1a, N3.1, N4.1b |
| N5.5 | Fresh names | lemma | new | S | 0 | — |
| N5.6 | Prefix monotonicity of free blocks | lemma | new | M | 0 | — |
| N5.8 | Projections of packet validity | lemma | new | S | 8 | D7.1b, N5.4 |
| L6.7a | Seed syntax | lemma | as-paper | M | 7 | D7.1a |
| L6.7b | Descending Mahlo chain | lemma | simplified | M | 2 | D6.4 |
| L6.7c | Seed values | lemma | as-paper | S | 8 | L6.7a |
| L6.7 | Seed lemma | lemma | simplified | S | 9 | D6.4, L6.7a, L6.7b, L6.7c, N5.4 |
| D8.1 | `S_n`, `W_{<n}`, `D_{<n}` and the induction (18) | def | as-paper | S | 21 | D8.1a, L8.4, L8.5, L8.6, L8.8 |
| D8.1b | Failures and the host-owner pair | def | new | S | 0 | — |
| L8.2a | Local steps of Γ(E) | lemma | as-paper | M | 7 | D1.3b, D7.1a |
| L8.2b | Owner-path chain | lemma | as-paper | M | 8 | D1.2e, L8.2a, N5.2 |
| L8.2c | Variables of local atoms | lemma | new | M | 8 | D1.2b, D7.1a, D7.1b |
| L8.2 | (19) Owner-path elementarity | lemma | as-paper | S | 9 | L8.2b, N5.2, N5.4 |
| L8.2d | Route elementarity | lemma | as-paper | M | 8 | D1.6d, L8.2a, N5.2 |
| L8.3 | Two-candidate fact | lemma | as-paper | M | 8 | N5.3, N5.4, N5.6 |
| L8.4 | Base `S_0` | lemma | as-paper | M | 14 | D1.2e, D1.4b, L7.3, L8.2, N5.3, N5.4, N5.8 |
| L8.5a | Setup notation | lemma | repaired | S | 11 | D6.1c |
| L8.5h *(new)* | `ScanSetup.Valid` written out | lemma | new | S | 15 | D3.1d, D6.1c, D7.2b, L8.5a, N3.1, N4.1b, T3.2 |
| L8.5b | Scan invariant and its start | lemma | as-paper | S | 12 | L8.5a, N5.4 |
| L8.5c | Source advance | lemma | as-paper | S | 12 | L8.5a, N5.4 |
| L8.5d | Target heads at the source owner | lemma | as-paper | M | 12 | D7.1a, D7.1b, L8.2, L8.2c, L8.5a |
| L8.5e | Strict comparison `x_i > y_j` | lemma | as-paper | M | 17 | D7.1a, D7.1b, D7.2d, L7.6, L7.6b, L8.2c, L8.5d, N5.4 |
| L8.5f | Equal comparison `x_i = y_j` | lemma | as-paper | L | 17 | D1.2e, D1.6d, D7.1a, D7.1b, L7.6b, L8.2, L8.2c, L8.3, L8.5d, N5.4, N5.6 |
| L8.5g | Along the trace | lemma | as-paper | M | 18 | L2.5d, L8.5b, L8.5c, L8.5e, L8.5f |
| L8.5 | `S_{<n} ⇒ W_{<n}` | lemma | as-paper | M | 19 | L2.5d, L8.5b, L8.5g, L8.5h |
| L8.6a | `DLab` unfolded | lemma | as-paper | S | 13 | D3.1d, D6.1c, N5.4 |
| L8.6b | (20) Control edge | lemma | as-paper | S | 6 | D1.6d |
| L8.6c | First retained role | lemma | as-paper | M | 9 | D1.6d, L8.2d |
| L8.6d | The stage problem | lemma | simplified | S | 11 | D6.1c |
| L8.6e | Stage invariant and stage zero | lemma | simplified | M | 14 | L6.2e, L8.6a, N5.4 |
| L8.6f | Control transport of the stage | lemma | simplified | L | 15 | L6.2e, L8.6a, L8.6b, L8.6d, L8.6e, N5.4 |
| L8.6g | Scan setup of the closed-owner case | lemma | repaired | L | 13 | D3.1d, L6.2e, L8.5a, L8.6d |
| L8.6h | Fit before `K` | lemma | as-paper | L | 16 | L8.2d, L8.5h, L8.6a, L8.6c, L8.6g, N5.4 |
| L8.6i | Restore `K` | lemma | as-paper | L | 17 | D1.2b, D3.1d, L6.2e, L8.6d, L8.6e, L8.6h, N5.4 |
| L8.6j | One stage | lemma | as-paper | S | 18 | L8.6f, L8.6h, L8.6i |
| L8.6 | `W_{<n} ⇒ D_{<n}` | lemma | simplified | M | 19 | L8.6a, L8.6e, L8.6j |
| D8.1a | Label-free core | lemma | new | S | 14 | D1.6a, L8.6a, N5.4 |
| L8.7a | Iterated capture of a block | lemma | as-paper | M | 8 | N5.3 |
| L8.7 | Special descent | lemma | as-paper | L | 12 | D1.2b, D1.2e, D1.6d, D7.1a, D7.1b, L6.2f, L8.2, L8.7a, N5.4, N5.6 |
| L8.8a | (23) from a failure | lemma | as-paper | S | 14 | L7.3 |
| L8.8b | Case 1: the whole target ends first | lemma | as-paper | M | 16 | D1.2e, D1.4b, D7.1a, D7.1b, L4.2, L8.2, N5.3, N5.4, N5.6, N5.8 |
| L8.8c | Readmission by a second capture | lemma | repaired | L | 9 | N3.1, N4.1a, N5.3, N5.8 |
| L8.8d | Case 2: a proper child forest ends first | lemma | repaired | L | 19 | D1.2e, D1.6d, D7.1b, L4.3d, L8.2, L8.8c, N5.4, N5.5, N5.8 |
| L8.8e | Root position | lemma | as-paper | M | 6 | D1.2b, D1.6d |
| L8.8f | Case 3: a parent differs or an existing column ends | lemma | repaired | L | 19 | D1.2e, D1.6d, D3.1d, D6.1a, D7.1b, L7.5d, L8.2, L8.6e, L8.8c, L8.8e, N3.1, N4.1a, N5.3, N5.4, N5.5, N5.8, T3.8 |
| L8.8g | Least failure | lemma | simplified | S | 1 | D8.1b |
| L8.8 | `D_{<n} ⇒ S_n` | lemma | repaired | S | 20 | L8.7, L8.8a, L8.8b, L8.8d, L8.8f, L8.8g |
| T9.1b | Deletion | theorem | as-paper | M | 7 | D1.6a, D1.6b, N5.4 |
| T9.1c | Special case of (27) | theorem | as-paper | S | 13 | D1.6a, D1.6d, L8.7, N5.4 |
| T9.1d | Ordinary case of (27) | theorem | as-paper | S | 22 | D1.6d, D8.1, N5.4 |
| T9.1 | Strict descent (27) | theorem | as-paper | S | 23 | D1.6a, T3.2, T9.1b, T9.1c, T9.1d |
| N5.1a | Configurations of standard expressions | lemma | as-paper | S | 0 | — |
| N5.1b/N5.1c | Accessibility | lemma | simplified | S | 0 | — |
| N5.1 | The S-5 abstract final theorem | theorem | simplified | S | 1 | N5.1a, N5.1b/N5.1c |
| T9.1a | Assembly | theorem | new | S | 24 | D1.1, L6.7, T3.2, T3.8, T9.1 |
| R9.2 | Ordinal interpretation σ | remark | as-paper | S | 24 | T9.1 |

---

## 4. Critical path

The longest dependency chain ending at the main theorem has **25 nodes** plus the root
`MainTheorem` (`Main.lean`), whose term uses N5.1, T9.1a and N4.2. It runs from the address types
through the agreement lemma (G-001), the repair lemma, cofinality T3.8, the source reduction L4.3
and the Case 2 data L4.3d, to the least-failure argument L8.8, the induction (18) (D8.1), strict
descent and the assembly.

| # | Node | Unit | Title | Diff. |
|---|---|---|---|---|
| 1 | D1.2a | U1 | Address types | S |
| 2 | D1.2b | U1 | Stacks, containment, accessors, roles | M |
| 3 | D1.2d | U1 | The terminal last-column, last-entry route | S |
| 4 | D1.5a | U1 | Shift and hole laws | M |
| 5 | D1.6b | U1 | Branch data specifications | L |
| 6 | D1.6c | U1 | Agreement sub-lemmas | L |
| 7 | D1.6a | U1 | The agreement lemma and branch contracts | S |
| 8 | D3.3a | U2 | Iterate identity | M |
| 9 | T3.8c | U2 | Caps are ordinary, their data and zero approximant | S |
| 10 | D3.1a | U2 | Moves, repair lists, admissible caps, origin map | M |
| 11 | L3.1g | U2 | A legal move keeps decorated responses | M |
| 12 | L3.1 | U2 | Profile and repair lemma (`repair`†) | L |
| 13 | L3.6 | U2 | Cap completion lemma | S |
| 14 | T3.8lc | U2 | Head-query cuts succeed | M |
| 15 | T3.8l | U2 | The ordinary induction step | M |
| 16 | T3.8m | U2 | Kernel success for standard targets | S |
| 17 | T3.8 | U2 | Cofinality theorem | S |
| 18 | L4.3 | U3 | Source reduction lemma, (6), (7) | L |
| 19 | L4.3d | U3 | The data of §8.5 Case 2 | M |
| 20 | L8.8d | U5 | Case 2: a proper child forest ends first | L |
| 21 | L8.8 | U5 | `D_{<n} ⇒ S_n` | S |
| 22 | D8.1 | U5 | `S_n`, `W_{<n}`, `D_{<n}` and the induction (18) | S |
| 23 | T9.1d | U5 | Ordinary case of (27) | S |
| 24 | T9.1 | U5 | Strict descent (27) | S |
| 25 | T9.1a | U5 | Assembly | S |
| 26 | MainTheorem | root (`Main.lean`) | `std_isWellOrder := abstract_implies_main (fun hM => ⟨_, finalHyps jInterface hM⟩)` | S |

Weighted by difficulty (S = 1, M = 2, L = 4, XL = 8), the heaviest chain weighs **57** of the
graph's 581 units. It shares its first eight nodes with the chain above and then runs through
closure T3.2 (with the XL node T3.2r) and the path transfer L4.2c (XL) to Case 3 (L7.5d, L8.8f):

| # | Node | Unit | Title | Diff. |
|---|---|---|---|---|
| 1 | D1.2a | U1 | Address types | S |
| 2 | D1.2b | U1 | Stacks, containment, accessors, roles | M |
| 3 | D1.2d | U1 | The terminal last-column, last-entry route | S |
| 4 | D1.5a | U1 | Shift and hole laws | M |
| 5 | D1.6b | U1 | Branch data specifications | L |
| 6 | D1.6c | U1 | Agreement sub-lemmas | L |
| 7 | D1.6a | U1 | The agreement lemma and branch contracts | S |
| 8 | D3.3a | U2 | Iterate identity | M |
| 9 | T3.2i | U2 | Phase classification of ordinary outputs | L |
| 10 | T3.2m | U2 | Owner returns of ordinary outputs have old origins | L |
| 11 | T3.2n | U2 | Ordinary outputs satisfy S | S |
| 12 | T3.2r | U2 | Ordinary outputs satisfy A | XL |
| 13 | T3.2 | U2 | Closure theorem | S |
| 14 | L4.3a | U3 | Confined operations and safe prefixes inside the marked height | M |
| 15 | L4.2c | U3 | Path transfer: the new parent is on the target's actual cut chain | XL |
| 16 | L4.2 | U3 | First-difference lemma | S |
| 17 | L7.5d | U3 | The data of §8.5 Case 3 | M |
| 18 | L8.8f | U5 | Case 3: a parent differs or an existing column ends | L |
| 19 | L8.8 | U5 | `D_{<n} ⇒ S_n` | S |
| 20 | D8.1 | U5 | `S_n`, `W_{<n}`, `D_{<n}` and the induction (18) | S |
| 21 | T9.1d | U5 | Ordinary case of (27) | S |
| 22 | T9.1 | U5 | Strict descent (27) | S |
| 23 | T9.1a | U5 | Assembly | S |

The hierarchy instance is a separate branch into `MainTheorem`. Under Part B (J-hierarchy) its
longest chain is 15 nodes, D5.2 → C5.3a → C5.3c → C5.4 → L5.5b → L5.5c (XL) → L5.5d → L5.5e →
L5.8b → L5.8c → L5.8d → L5.8a → L5.9a → L5.9b → N4.2, weight 49; under Part C (P-U4-1) it is 11
nodes, N4.1 → N4.1b → N4.1a → N4.4 → N4.5 → N4.6 → N4.7 → N4.8 → N4.9a → N4.9b → N4.10. Neither is
longer than the U1–U5 chain, but Part B's weight is close to the weighted critical path.

---

## 5. Width of the graph

Every node's dependencies are stated: each dependency is a node with a Lean declaration that
typechecks in the integrated check (with `sorry` proofs), or an umbrella node whose sub-nodes
have them. So all 302 nodes can be formalized independently and at once, each against the
`sorry`-proved statements of its dependencies; this is the full width.

If dependencies are to be proved before their users, the layers give the schedule. Layer 0 holds
the nodes with no dependency; a node in layer `k` depends only on nodes in layers below `k`
(`k` is one more than the largest layer of its dependencies).

| Layer | Nodes | U1 | U2 | U3 | U4 | U5 | Cumulative |
|---|---|---|---|---|---|---|---|
| 0 | 26 | 9 | 7 | 0 | 4 | 6 | 26 |
| 1 | 22 | 9 | 2 | 1 | 8 | 2 | 48 |
| 2 | 17 | 10 | 1 | 1 | 4 | 1 | 65 |
| 3 | 22 | 12 | 4 | 2 | 4 | 0 | 87 |
| 4 | 14 | 6 | 3 | 2 | 3 | 0 | 101 |
| 5 | 14 | 6 | 3 | 1 | 4 | 0 | 115 |
| 6 | 14 | 4 | 4 | 1 | 2 | 3 | 129 |
| 7 | 18 | 3 | 6 | 3 | 2 | 4 | 147 |
| 8 | 25 | 1 | 6 | 2 | 9 | 7 | 172 |
| 9 | 25 | 0 | 17 | 1 | 3 | 4 | 197 |
| 10 | 19 | 0 | 14 | 3 | 2 | 0 | 216 |
| 11 | 15 | 0 | 8 | 4 | 1 | 2 | 231 |
| 12 | 10 | 0 | 3 | 1 | 2 | 4 | 241 |
| 13 | 16 | 0 | 5 | 7 | 1 | 3 | 257 |
| 14 | 11 | 0 | 1 | 4 | 2 | 4 | 268 |
| 15 | 8 | 0 | 1 | 5 | 0 | 2 | 276 |
| 16 | 6 | 0 | 1 | 3 | 0 | 2 | 282 |
| 17 | 4 | 0 | 0 | 1 | 0 | 3 | 286 |
| 18 | 6 | 0 | 0 | 4 | 0 | 2 | 292 |
| 19 | 4 | 0 | 0 | 0 | 0 | 4 | 296 |
| 20 | 1 | 0 | 0 | 0 | 0 | 1 | 297 |
| 21 | 1 | 0 | 0 | 0 | 0 | 1 | 298 |
| 22 | 1 | 0 | 0 | 0 | 0 | 1 | 299 |
| 23 | 1 | 0 | 0 | 0 | 0 | 1 | 300 |
| 24 | 2 | 0 | 0 | 0 | 0 | 2 | 302 |

- Layers 0–3 (87 nodes, mostly U1 and U4) can start at once.
- U2's cofinality block makes layers 8–11 the widest (25, 25, 19, 15 nodes).
- From layer 15 on, at most 8 nodes per layer are available. Layers 17–19 hold the convergence
  of U3's packet lemmas and U5's three steps of (18) (L8.5, L8.6, L8.8d, L8.8f); the last five
  layers are the single chain L8.8 → D8.1 → T9.1d → T9.1 → T9.1a (with R9.2 beside T9.1a).
  N5.1 (S-5) depends on nothing but the spine and sits in layer 1.

Nodes on no chain to the main theorem: C5.3, C5.3e, D2.3, D6.3, L2.4c, L2.5c, L5.5, L5.8, L5.9, L6.2b, L6.2d, L7.3a, L7.3b, L7.5b, L7.5c, N1.1, N4.10, N4.3, N4.4, N4.5, N4.6, N4.7, N4.8, N4.9a, N4.9b, R9.2, T3.2a, T3.8n. These are umbrella nodes whose sub-nodes are used
directly (C5.3, L5.5, L5.8, L5.9), definition nodes reached only through definitions (D2.3, D6.3,
T3.8n), the alternative instance P-U4-1 (N4.3–N4.10), testing (N1.1), and optional results
(T3.2a `isStd_iff_paper`, L2.4c, L2.5c, R9.2 `sigma`, L6.2b, L6.2d, L7.3a, L7.3b, L7.5b, L7.5c).
