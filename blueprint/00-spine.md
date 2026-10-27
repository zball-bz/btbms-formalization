# Blueprint spine

**Task:** T-016, spine step. **Companion Lean file:** `blueprint/lean/Spine.lean`. It typechecks
with
`cd lean && PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake env lean ../blueprint/lean/Spine.lean`
(only `declaration uses 'sorry'` warnings).

**Integration (2026-10-27):** the applied spine-change requests are recorded in §i; the
integration report, with the full node table, is `blueprint/INTEGRATION.md`.

**Inputs read:**
- the paper, `paper/paper.txt`, cited as txt:LINE;
- both reviews: `tracker/review/claude-review.md`, `tracker/review/codex-review.md`;
- the cross-check `tracker/review/codex-crosscheck-1.md`;
- `tracker/ledger.json` (nodes, G-001…G-007, S-1…S-6, R-1…R-6, D-1…D-3);
- `tracker/review/reuse-audit.md`;
- the locked statement files `lean/BTBMS/{Syntax,Expansion,Mahlo,Statement}.lean`.

**How to read this file:**
- §a is the architecture. §b assigns every ledger node to a unit. §c is the shared vocabulary:
  every definition used by more than one unit, with owner, precise informal definition and Lean
  name/type. §d lists what each unit provides and consumes. §e is the module plan. §f gives the
  naming rules. §g records the disposition of every gap, simplification, risk and decision.
  §h gives the rules for the five drafters.
- Section numbers §c.1…§c.13 are the same in `Spine.lean`.

**Firm and refinable items:**
- **FIRM** items may be changed only through a spine-change request (§h). They are:
  - every type signature in `Spine.lean`;
  - every definition with a real body there;
  - every structure's field list;
  - the interface `Hier.Interface`;
  - the predicates `SStrict`, `WFit`, `AllowedInput`, `DCore`, `DLab`, `SpecialDesc`,
    `StrictDescent` and `FinalHyps`.
- **REFINABLE** items are named here with an informal statement, but the owner unit writes the
  exact Lean statement. A refinable statement may gain hypotheses only if the consumer's use
  (cited here) still goes through.

---

## a. Architecture overview

**The Lean target.** The locked theorem is `BTBMS.MainTheorem.{u}`:

> `(∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) → IsWellOrder Std Std.lt`

- `Std` is the subtype of forests generated from the seeds `seed m` by `expand` (D1.7).
- `Std.lt` is the syntax order `instLTForest`.
- `expand` mirrors the reference `FS` (decision D-3).
- The hypothesis is weakly n-Mahlo (decisions D-1, D-2, simplification S-1).

**The S-5 abstract final theorem (N5.1, §c.13).** Let `Conf : Forest → Ordinal.{u} → Prop` be
any predicate; read `Conf E θ` as "Γ(E) has a configuration of maximum θ". Assume:

1. **(O) Order** [U1, D1.1]: `<` on forests is a strict total order, and `∅` is least.
2. **(C) Closure** [U2, T3.2]: every standard expression lies in the class L.
3. **(F) Cofinality** [U2, T3.8]: if `B` is standard, `E ∈ L` and `B < E`, then some `n` has
   `expand E n = some E'` with `B ≤ E'`.
4. **(Σ) Seed configurations** [U5, L6.7]: every seed `L_m` has some `θ` with `Conf L_m θ`.
5. **(Δ) Strict descent** [U5, T9.1 (27)]: if `A` is standard and nonempty, `Conf A θ`, and
   `expand A n = some A'` with `A'` nonempty, then `Conf A' θ'` for some `θ' < θ`.

Then `(Std, <)` is a well-order (`Descent.abstract_wellOrder`). Moreover,
`Descent.abstract_implies_main` turns "the Mahlo hypothesis gives such a `Conf`" into
`MainTheorem`. The proof (S-2) uses no choice recursion. It is an accessibility argument with
ordinal labels, written out in §c.13.

**How the units feed it.**

```
 U1 syntax-scans ──► U2 closure-cofinality ──► (C), (F)
   │  (O), occurrences, conditions, scans, operation
   ├──────────────► U3 records-packets ──┐
   │                                     ├──► U5 descent-main ──► (Σ), (Δ), N5.1, MainTheorem
 U4 hierarchy (S-4 Interface + J) ───────┘
```

- **U1** (§1–§2) gives:
  - the syntax order (O);
  - occurrences (addresses and roles);
  - the conditions V, I, H, A, S and the class L;
  - scans, words and the operation's branch data;
  - the paper's operation with its agreement lemma (G-001).
- **U2** (§3) gives:
  - profiles, caps and repairs;
  - closure (C), with strict decrease;
  - cofinality (F), also for admissible caps, which §8.5 needs.
- **U3** (§4, §6.1, §7) gives the finite records, the graph Γ(E) and configurations, occurrence
  maps, names, frames and blocks, the packet grammar (G-003), and the packet lemmas L7.3–L7.6.
- **U4** (§5, §6.2 except the seed lemma) gives the S-4 semantic interface `Hier.Interface` and
  its instance `Hier.jInterface` built from the J-hierarchy:
  - levels `Elem a b` (`J_a ≺Σ1 J_b`) and edges `Edge C b a` (`R(C,b,a)`);
  - capture, transport and budgets;
  - (13) and (14).
- **U5** (L6.7, §8, §9) proves:
  - the seed lemma (Σ);
  - the induction `S_<n ⇒ W_<n ⇒ D_<n ⇒ S_n` (18);
  - special descent, and from these (Δ);
  - the S-5 theorem, and the assembly
    `std_isWellOrder := abstract_implies_main (fun hM => ⟨_, finalHyps jInterface hM⟩)`.

**Four design decisions made by this spine.**

1. **Certificates in ordinal form (S-4, R-4).** The paper realizes diagrams by set-coded
   certificates in levels `J_w`. Here a diagram is a finite list of atoms over variables, and
   "has a complete certificate in `J_w`" is replaced by `Diagram.RealizableBelow … w`: some
   ordinal assignment satisfies the diagram with every coordinate below `w`. The paper's
   certificate lemma L5.8 proves both directions for limit `w` (txt:879-881, 1038-1040). With
   that equivalence, every budget statement of §7–§8 becomes a strict coordinate inequality:
   - `w_low ∈ J_β` becomes "all low coordinates are below β";
   - "J_u and its history in `J_{u+ω} ⊆ J_W`" becomes `u < W`.

   Labels are a fixed grammar of atoms, including the negative label `No_B` (16). U4 proves
   capture and transport for exactly this grammar. That is the "schema-level transport lemma"
   that R-4 asks for. §c.7 has the translation table.
2. **Occurrences are addresses (R-3).** An occurrence is named by its address: the path of
   `(column index, entry index)` steps of its containing entries. Visibility, printed numbers
   and both representatives `O(p)`, `P(p)` are computable functions of the address with real
   bodies (§c.2). Chart names are `Name.role tag r` with an instance tag. The persistent map ι
   is the identity on the pre-stop roles. The latest-copy maps q and f are separate functions,
   so the ι-versus-f distinction (txt:965-968) is explicit.
3. **Two operations, one agreement lemma (G-001, D-3).** Proofs reason about `Scan.paperOp`,
   which is written from §1.2 alone, and its branch data (`stepKind`, `stopData`, `rootData`).
   `Scan.expand_eq_paperOp` identifies it with the locked `expand` on nonempty V∧I inputs. Every
   decrease or descent statement assumes a nonempty input.
4. **Exact records and packets (G-003).**
   - `Packet.SrcRecord` (3 constructors) and `SrcRecord.Admitted` fix the record class:
     occurrence maps, actual scan indices, retained marked entries, move lists.
   - `Packet.SourcePacket.Valid` fixes the packet class.
   - `Descent.SStrict` quantifies over exactly these classes, so every readmission in §8.5 is a
     checkable proposition.

---

## b. Ownership

**Default:** ownership by section, exactly as fixed in the task:
- U1: §1–§2.
- U2: §3.
- U3: §4, §6.1, §7.
- U4: §5, and §6.2 except the seed lemma.
- U5: the seed lemma L6.7, §8, §9.

**Moved nodes: none.** Every node's proof obligations fall inside its default unit. Cross-unit
needs are met by the contracts of §c and §d. Two placements were considered and kept:
- D6.4 stays in U4. Its definitions are locked; U4 adds `Hier.isLim_ord`, and U5 uses the
  locked definitions in L6.7.
- F5.1 stays in U4. It is pure ordinal arithmetic (`Hier.add_omega_le`), and U3 and U5 may cite
  it.

Counts: U1 17, U2 9, U3 12, U4 12, U5 11, total 61.

| ID | Title | Paper | Unit | Lean (spine names; "states" = name fixed, statement written by the unit) |
|---|---|---|---|---|
| D1.1 | Forests, columns, entries; syntax order (proper prefix smaller) | §1.1 txt:60-66 | U1 | `Forest.instLinearOrder`, `Tree.instDecidableEq`, `Forest.empty_lt` |
| D1.2 | Column numbering, visibility, occurrences | §1.1 txt:66-75 | U1 | `ColAddr`, `EntryAddr`, `Role`, `ColAddr.num/resolve/container/rep/reps0`, `Tree.roles` |
| D1.3 | Conditions V, I, H | §1.1 txt:76-80 | U1 | `Scan.CondV`, `Scan.CondI`, `Scan.CondH` |
| D1.4 | Relative key h_a (false/true fields) | §1.1 | U1 | `relKey`, `keyCmp` (locked); `Key.instLinearOrder`, `relKey_lt_iff` |
| D1.5 | Shifts T_{r,d}, replacement A_{r,d,l,Z} | §1.1 p.3 | U1 | `Scan.shift`, `replaceAt` (locked), `Scan.Hole` |
| D1.6 | Fundamental operation E[n]: deletion / special / ordinary | §1.2 txt:95-137 | U1 | `expand` (locked); `Scan.stepKind/stopData/rootData/paperOp`, `Scan.expand_eq_paperOp` |
| D1.7 | Seeds L_m, Std, generation witness | §1.3 txt:138-143 | U1 | `seed`, `IsStd`, `Std` (locked); `Closure.isStd_iff_paper` |
| C1.8 | Compact word injective and order-preserving | §1.3 txt:144-151 | U1 | `Scan.word`, `Scan.mu`, `Scan.word_lt_iff`, `Scan.word_injective` |
| D1.9 | Safe prefix | §1.3 txt:152-153 | U1 | `Scan.safePrefix`, `Scan.word_safePrefix`, `Scan.truncAfter_safePrefix` |
| D2.1 | nu reduction; boundaries B_c(i) strictly increase | §2 txt:157-164 | U1 | `Scan.nu`, `Scan.cutQuery`, `Scan.boundary`, `Scan.cursor`, `Scan.trace`, `Scan.cutQuery_lt_succ` |
| L2.1 | Scan boundary lemma | §2 txt:165-176 | U1 | `Scan.cursor_spec`, `Scan.cursor_nu` |
| D2.2 | g_W, ancestors, condition A | §2 txt:177-193 | U1 | `Scan.KeySys`, `Scan.actualKeys`, `Scan.capKeys`, `Scan.resp`, `Scan.Edge`, `Scan.Path`, `Scan.CondAK`, `Scan.CondA` |
| L2.2 | Path nesting lemma | §2 txt:194-200 | U1 | `Scan.path_nesting` |
| D2.3 | Owner return, condition S, class L | §2 txt:201-204 | U1 | `Scan.IsOwnerReturn`, `Scan.CondS`, `Scan.InL` |
| L2.3 | Barrier lemma | §2 txt:205-219 | U1 | `Scan.barrier`, `Scan.cut_barrier` (U1 states) |
| L2.4 | Capping lemma; operations defined on V,I,A,S | §2 txt:220-236 | U1 | `Scan.capping_iff` (U1 states), `Scan.expand_isSome` |
| L2.5 | Exact trace facts (1)-(3) | §2 txt:237-249 | U1 | `Scan.trace_map`, `Scan.trace_cap_top`, `Scan.trace_agree`, `Scan.sign_of_agreement` (U1 states) |
| D3.1 | Profile, condition P, literal and upward caps | §3.1 txt:254-262 | U2 | `Closure.profile`, `Closure.CondP`, `Closure.litCap`, `Closure.IsUpward` |
| L3.1 | Profile and repair lemma | §3.1 txt:263-298 | U2 | `Closure.condS_of_condP`, `Closure.upward_condS`, `Closure.repair` (U2 states the last two) |
| T3.2 | Closure theorem | §3.2 txt:301-414 | U2 | `Closure.std_inL`, `std_condP`, `inL_expand`, `condP_expand`, `inL_safePrefix`, `expand_lt` |
| D3.3 | Kernel F_H and context C_H | §3.3 txt:421-426 | U2 | `Closure.kernel`, `Closure.context` (U2-internal) |
| L3.4 | Word criterion | §3.3 txt:427-437 | U2 | `Closure.word_criterion` (U2-internal) |
| L3.5 | Filling identity (1), cancellation (2) | §3.3 txt:438-458 | U2 | `Closure.filling_identity`, `Closure.cancel_eq` (U2-internal) |
| L3.6 | Cap completion lemma | §3.3 txt:459-481 | U2 | `Closure.cap_completion` (U2-internal) |
| L3.7 | Delayed-change lemma | §3.3 txt:482-487 | U2 | `Closure.delayed_change` (U2-internal) |
| T3.8 | Cofinality theorem (n <= mu(B)+1) | §3.4 txt:489-643 | U2 | `Closure.cofinal`, `Closure.cofinal_bound` |
| D4.1 | Scan / descendant / repair records | §4 txt:646-663 | U3 | `Packet.RecKind`, `Packet.SrcRecord`, `SrcRecord.Admitted` |
| L4.2 | First-difference lemma | §4 txt:664-686 | U3 | `Packet.SrcRecord.FirstDiff`, `SrcRecord.firstDiff`, `Packet.firstDiff_cap` (U3 states) |
| L4.3 | Source reduction lemma, (6), (7) | §4 txt:687-730 | U3 | `Packet.reduce_confined`, `Packet.repair_output`, `Packet.query_size_bound`, `Packet.reduce_childEnds` (U3 states) |
| F5.1 | (8) v<u, Lim(u) => v+omega <= u | §5.1 txt:735-737 | U4 | `Hier.add_omega_le` |
| D5.2 | Basis B, S(X), J-hierarchy | §5.1 txt:739-766 | U4 | `Hier.S`, `Hier.J` (U4-internal) |
| C5.3 | Truth tables, bounded verifier, S(T) inside closed levels | §5.1 txt:768-798 | U4 | U4-internal |
| C5.4 | (9) Ord cap J_lambda = lambda; size bound | §5.1 txt:799-807 | U4 | U4-internal |
| L5.5 | History and hull lemma | §5.1 txt:808-841 | U4 | U4-internal |
| L5.6 | Condensation lemma | §5.1 txt:842-853 | U4 | U4-internal |
| D5.7 | Control edge R(C,b,a) and its basic properties | §5.2 txt:859-873 | U4 | `Prims.Edge`, `Interface.edge_*` fields of `Hier.jInterface` |
| L5.8 | Certificate lemma | §5.2 txt:874-905 | U4 | `Diagram.RealizableBelow`, `BlockAbove` (ordinal form); U4 proves the equivalence |
| L5.9 | Capture and transport | §5.2 txt:909-918 | U4 | `Interface.capture`, `Interface.transport` |
| D6.1 | Graph Gamma(E), configurations, role sets | §6.1 txt:922-943 | U3 | `Packet.graph`, `IsConfig`, `cfgMax`, `Configured`, `RoleSets`, `roleSets`, `prefixGraph` |
| L6.2 | Occurrence-map identity | §6.1 txt:944-964 | U3 | `Packet.qMap`, `Packet.fMap`, `Packet.occurrence_map_identity` (U3 states) |
| D6.3 | Persistent map iota_m | §6.1 txt:965-968 | U3 | `Packet.iota` |
| D6.4 | Finite Mahlo hierarchy M_n | §6.2 txt:970-975 | U4 | `IsWeaklyMahlo`, `IsMahlo`, `StationaryIn` (locked); `Hier.isLim_ord` |
| L6.5 | (13) J_lambda <Sigma1 J_u | §6.2 txt:976-983 | U4 | `Interface.card_elem` |
| L6.6 | (14) club of reflection points | §6.2 txt:984-999 | U4 | `Interface.club_edge` |
| L6.7 | Seed lemma | §6.2 txt:1000-1013 | U5 | `Descent.seed_config` |
| D7.1 | Names, charts, frames, blocks, Cert_B, No_B | §7.1 txt:1017-1044 | U3 | `Packet.Name`, `Frame`, `frameOf`, `BlkVar`, `freeBlock`, `posBlock`, `noB`, `Hier.Atom.noReal` |
| D7.2 | Source packet | §7.1 txt:1045-1065 | U3 | `Packet.SourcePacket`, `SourcePacket.Valid`, `SourcePacket.TargetAbove` |
| L7.3 | Factorization lemma | §7.2 txt:1068-1081 | U3 | `Packet.factorization` |
| L7.4 | Joint cap lemma | §7.2 txt:1082-1099 | U3 | `Packet.joint_cap` (U3 states) |
| L7.5 | Joint repair lemma; admission after §4 reductions | §7.2 txt:1100-1124 | U3 | `Packet.joint_repair` (U3 states) |
| L7.6 | Complete packets at a scan (17) | §7.3 txt:1126-1167 | U3 | `Packet.ScanSetup`, `ScanSetup.Valid`, `Packet.scan_packet` |
| D8.1 | S_n, W<n, D<n and the induction (18) | §8.1 txt:1171-1189 | U5 | `Descent.SStrict`, `WFit`, `AllowedInput`, `DCore`, `DLab` |
| L8.2 | (19) owner-path elementarity | §8.1 txt:1190-1200 | U5 | `Descent.owner_path_elem` (U5 states) |
| L8.3 | Two-candidate fact | §8.1 txt:1201-1210 | U5 | `Descent.two_candidates` (U5 states) |
| L8.4 | Base S_0 | §8.1 txt:1211-1214 | U5 | `Descent.sStrict_zero` (U5 states) |
| L8.5 | S<n => W<n (query fitting) | §8.2 txt:1216-1248 | U5 | `Descent.wFit_of_sStrict` (U5 states), `Descent.wFit_all` |
| L8.6 | W<n => D<n (ordinary descent) | §8.3 txt:1250-1323 | U5 | `Descent.dLab_of_wFit` (U5 states), `dLab_all`, `dCore_all` |
| L8.7 | Special descent | §8.4 txt:1325-1346 | U5 | `Descent.SpecialDesc`, `Descent.specialDesc` |
| L8.8 | D<n => S_n (least failure) | §8.5 txt:1348-1474 | U5 | `Descent.sStrict_of_dLab` (U5 states), `Descent.sStrict_all` |
| T9.1 | Main theorem: (Std,<) is a well-order | §9 txt:1477-1504 | U5 | `Descent.StrictDescent`, `strictDescent`, `FinalHyps`, `finalHyps`; `std_isWellOrder` (Main.lean) |
| R9.2 | Ordinal interpretation sigma | §9 txt:1505-1512 | U5 | `Descent.sigma` (U5 states) |

**New nodes introduced by the spine** (naming per §f; drafters add more):

| ID | Unit | Content | Repairs / applies |
|---|---|---|---|
| D1.2a | U1 | Address types `ColAddr`, `EntryAddr`, `Role`; `num`, `resolve`, `container`, `rep`, `reps0`; `Tree.roles` | R-3 |
| D1.6a | U1 | `Scan.paperOp` and branch data written from §1.2; `expand_eq_paperOp`; `stepKind_isSome`; branch lemmas | G-001, D-3 |
| L2.3a | U1 | Barrier as the joint induction of `C_e(c,k)`/`R_e(c,k)` on `(c,k)`; localized pre-entry-cut barrier | G-006 |
| L2.4a | U1 | Reverse capping by the first-divergence argument | G-006 |
| D3.1a | U2 | `Closure.Move`, `applyMoves`, `MovesValid`, `RepairList`, `moveAddr`, `AdmCap`, `AdmCap.origin` (χ), `anchor` | G-003 |
| L3.1a | U2 | `V ∧ I ∧ H ∧ P ⇒ S` (`Closure.condS_of_condP`) | G-002 |
| T3.2a | U2 | `IsStd` equals the paper's Std generated by `paperOp` (`Closure.isStd_iff_paper`) | G-001 |
| D4.1a | U3 | `SrcRecord.Admitted`, `AnchorAt`, `anchorSrc`; `FirstDiff`/`firstDiff` classifier | G-003 |
| D7.2a | U3 | `SourcePacket.Valid`, `lowNames`, `joint`, `TargetAbove` | G-003 |
| D7.2b | U3 | `Packet.ScanSetup` and `ScanSetup.Valid` (the §7.3 hypotheses) | G-003 |
| N3.1 | U3 | Finite-name amalgamation and packing: `holds_append`, `holds_map`, `amalgamate`, `pack_below` | S-6 |
| D5.7a | U4 | `J_b ∈ Hull^{J_C}(J_a ∪ {b})`, then relativization: `J_a ≺ J_b` (field `edge_elem_low`) | G-004 |
| L5.8a | U4 | Ordinal form of certificates: `RealizableBelow D F σ w` ↔ a complete certificate in `J_w` (limit `w`) | S-4, R-4 |
| N4.1 | U4 | Diagram grammar `BaseAtom`/`Atom`/`Diagram`, its semantics, and `Hier.Interface` | S-4 |
| N4.2 | U4 | `Hier.jInterface`: the J-hierarchy instance | S-4, R-1, R-6 |
| D8.1a | U5 | Label-free core `DCore` of `D_<n`, and `dCore_of_dLab` | S-6 |
| N5.1 | U5 | `Descent.FinalHyps`, `abstract_wellOrder`, `abstract_implies_main` | S-5, S-2 |
| T9.1a | U5 | `Descent.finalHyps`: assembly of all units into `FinalHyps (Configured jInterface)` | S-5 |

---

## c. Shared vocabulary

### c.0 Conventions

- **Universe.**
  - All ordinals are `Ordinal.{u}` and all cardinals `Cardinal.{u}`, for the single universe `u`
    of `MainTheorem.{u}` (D-1).
  - The J-hierarchy is built in `ZFSet.{u}`. Mathlib supplies `Ordinal.toZFSet`, `ZFSet.rank`
    and `Ordinal.toZFSetIso`.
  - `universe u` in `Spine.lean` is scoped to `namespace BTBMS`; unit files re-declare it.
- **Totality.**
  - Lean functions are total. Outside their intended domain they return `none`, or a `getD`
    default (`∅`, `0`, `[]`).
  - Every lemma carries its domain hypotheses explicitly, for instance
    `E ≠ Tree.empty`, `CondV E`, `CondI E`.
  - No lemma may rely on a default value without stating it.
- **Paper notation to Lean.**

  | Paper | Lean |
  |---|---|
  | `E[n]` | `expand E n = some E'` |
  | `B ≤ E'` | the `LinearOrder Forest` instance (`≤`) |
  | `h_a(H)` | `relKey a H` |
  | `µ(E)` (the length of `w(E)`) | `Scan.mu E` |
  | `N(B)` | `B.size` |
  | `L` | `Scan.InL` |
  | "configuration" | `Packet.IsConfig P E α` |

- **No well-foundedness of syntax.** No recursion or induction may use `<` on forests. The
  allowed measures are those of txt:41-44:
  - structural recursion on trees, lists and addresses;
  - `Nat` induction (sizes `N(B)`, column numbers, entry indices, scan cursors);
  - induction on `IsStd` (generation witnesses);
  - ordinal well-foundedness, in particular lexicographic pairs `(ρ, u)`.

### c.1 Syntax and order (U1: D1.1, D1.4)

- **`Tree.instDecidableEq : DecidableEq (Tree α)`.** Real body: hand-written mutual decision
  procedure. The derived handler fails on this nested inductive.
- **`Forest.instLinearOrder : LinearOrder Forest`** (FIRM; proofs: U1).
  - Its `lt` is definitionally the locked `instLTForest`, so `Std.lt a b` is `a.1 < b.1` in
    this instance; `Forest.lt_iff_cmp` holds by `Iff.rfl`.
  - `le a b := Tree.cmp compare a b ≠ .gt`.
  - U1 proves the order axioms. That compares entries by parent then height, and columns and
    forests lexicographically with a proper prefix smaller (txt:62-64).
- **`Forest.empty_lt : E ≠ ∅ → ∅ < E`** (U1). The empty forest `.node []` is a proper prefix of
  every nonempty forest.
- **`Key.instLinearOrder : LinearOrder Key`** (FIRM; proofs: U1).
  - `lt x y := keyCmp x y = .lt`.
  - Labels compare false fields `(false, p)` before true fields `(true, p − a)`, then by value.
  - `WithTop Key` adds the formal top `⊤` of txt:221.
- **`relKey_lt_iff : relKey a H < relKey a H' ↔ H < H'`** (U1, txt:84-85). Normalization at one
  threshold preserves and reflects order.

### c.2 Occurrences (U1: D1.2, D1.2a; risk R-3)

An *occurrence* is a node of a particular syntax tree (txt:45-47). It is identified by its
address. Addresses are relative to the tree in which they are read; the same address in `E` and
in `E[n]` may be different occurrences, and maps between them are explicit (§c.8).

- **`ColAddr := { path : List (Nat × Nat), col : Nat }`** (FIRM).
  - `path = [(c_0,i_0), …, (c_{k-1},i_{k-1})]` lists the containing entries: entry `i_0` of
    column `c_0` of the outer forest, then entry `i_1` of column `c_1` of its height, and so on.
  - `col` is the column's index in its own forest.
- **`EntryAddr := { col : ColAddr, idx : Nat }`** (FIRM).
  - `heightPath e = e.col.path ++ [(e.col.col, e.idx)]` is the path of the columns of `e`'s
    height.
- **`Role := ord (c : ColAddr) | slot (e : EntryAddr)`** (FIRM). These are the ordinary role
  `A_c` of a column and the slot `U_e` of an entry (txt:923-924). `Role.inEntry x e` holds iff
  `x = U_e` or `x` lies inside `e`'s height.
- **`Role.under π : Role → Role`** (FIRM, real body; added at integration, §i.6). It prefixes the path
  `π` to the address of a role read relative to a height: `A_c ↦ A_{⟨π ++ c.path, c.col⟩}`,
  `U_e ↦ U_{⟨⟨π ++ e.col.path, e.col.col⟩, e.idx⟩}`. Owner U1 (its lemmas are U1 D1.2e).
- **Accessors** (real bodies):
  - `Tree.forestAt t path`;
  - `Tree.colAt t c`;
  - `Tree.entryAt t e : Option (label × height)`;
  - `Tree.heightAt t e`.
- **`Tree.roles t : List Role`** (real body). The reading order of txt:923-924 is depth first:
  for each column in order, its ordinary role, then for each entry in order its slot,
  immediately followed by the roles of its height. Also `Tree.colAddrs`, `Tree.entryAddrs`.
- **`Tree.size t := t.roles.length`.** This is `N(B)` of txt:709-711 and txt:1172: the number of
  ordinary and slot roles internal to `B`.
- **`ColAddr.num base c := base + Σ_k (c_k + 1) + c.col`** (real body).
  - It gives printed column numbers (txt:65-66): the outer forest starts at `base`, and a height
    attached to column `a` starts at `a + 1`.
  - Forests use `base = 0`. A relative key `h_a(B)` uses `base = 1`: its host is relative
    number `0`, and its `k`-th outer column has relative number `k + 1`.
- **`ColAddr.resolve base c q : Option ColAddr`** (real body). It returns the column occurrence
  denoted by the printed number `q` on the visible stack of `c` (txt:66-69):
  - at each containing level `k`, the columns `0…c_k` of that forest;
  - at `c`'s own level, the columns `0…c.col − 1`.

  It returns `none` iff `q` is not on that stack; in particular iff `q ≥ c.num base`, or
  `q < base` for relative keys. Numbers on the stack are unique (txt:69).
- **`ColAddr.container q c : Option EntryAddr`** (real body). This is the entry of column
  occurrence `q` whose height contains `c`. It exists iff `q` is a containing column of `c`.
- **`ColAddr.rep base c q : Option (Role × Role)`** (real body). These are the two
  representatives seen from column `c` (txt:924-926):
  - `O(q) = A_{resolve q}`;
  - `P(q) = U_{container}` when `q` contains `c`, otherwise `A_{resolve q}`.

  Entering an entry of column `c` changes only `P(c)`; so for every entry of `c` and every
  `q < c.num`, these are the representatives used by its edges (11).
- **`ColAddr.reps0 c := [rep 0 c 0, …, rep 0 c (c.num 0 − 1)]`** gives all visible
  representatives below a forest column (used for frames, §c.9).
- **`Tree.truncAfter t e`** (body: U1). It keeps everything up to and including entry `e` with
  its complete height, and deletes all later context:
  - later entries of `e`'s column, and later columns of `e`'s forest;
  - in every containing forest, the columns after the containing column, and the entries of
    that column after the containing entry.

  Concretely, for `e = ⟨⟨[(c_0,i_0),…], j⟩, i⟩`:
  - at level 0, keep columns `0…c_0`;
  - in column `c_0`, keep entries `0…i_0`, and truncate the height of entry `i_0`
    recursively;
  - at the last level, keep columns `0…j`, and in column `j` keep entries `0…i`.

  If `e` is not an entry of `t`, the result is `t`. U1 proves `truncAfter_safePrefix`: it is a
  safe prefix.
- **`Tree.setHeight t e h`** (body: U1) replaces the height of entry `e` by `h` and changes
  nothing else. If `e` is not an entry, the result is `t`.

### c.3 Keys, scans and the conditions V, I, H, A, S, L (U1: D1.3, D1.4, D2.1–D2.3)

**Generic word library (S-6)** (real bodies). These live over any `LinearOrder α`; they are used
at `α = Key` and `α = WithTop Key`.

- **`nu`** is ν of txt:157-158: it appends letters one by one, first deleting terminal letters
  strictly smaller than the appended letter. Equal letters are kept.
- **Boundaries** (D2.1):
  - `cutQuery ks k = ν(ks[0..k−1])` is `B_c(k−1)` (the query of the cut before entry `k`);
  - `boundary ks i = ν(ks[0..i])` is `B_c(i)`;
  - `cutQuery ks 0 = [] = B_c(−1)`.
- **`cursor src qry`** is the raw two-cursor scan of txt:122-124 (generic form of the locked
  `scanCount`). At letters `x, y` it advances the source cursor when `x ≤ y` and the query
  cursor when `x ≥ y`, stops when either list ends, and returns the final source cursor.
  `trace src qry` lists all states `(i, j)` visited, including the final one.
- **`ReachesGT src qry i j`**: state `(i, j)` is on the trace and `qry[j] < src[i]`. This is
  the "source-greater comparison" of txt:1144 and txt:1227.

**Key systems (txt:220-222).**

- **`KeySys := ColAddr → List (WithTop Key)`**: a key system assigns the entry keys of every
  column occurrence.
- **`actualKeys E c = [h_{c.num 0}(H_i)]`**: actual relative keys of the explicit heights of
  column `c`, normalized at its printed number.
- **`routeCols E`** (real body): the columns of the terminal last-column, last-entry route,
  outermost first.
- **`capKeys E sel`** (real body): the independently capped system. The last key of every
  selected column is replaced by `⊤`; children are kept. Lemmas assume `sel ⊆ routeCols E`
  (txt:221: "on the terminal containment route").

**Responses and paths (D2.2).** These are FIRM, with real bodies.

- **`resp E ks o W`** is `g_W(o)`: the parent of the first unconsumed entry of column `o` after
  `cursor (ks o) W`. It is `none` when the scan is exhausted.
- **`Edge E ks c W x p`**: number `x` resolves on `c`'s stack to `o`, and `resp E ks o W = some p`.
- **`Path E ks c W`**: the reflexive-transitive closure of `Edge E ks c W`.
- Every path is read on one fixed visible stack, that of the column `c` whose test is checked.
  The cross-check (codex-crosscheck-1 Q2) shows that restricting to the stack of a visited
  column changes no lower occurrence.

**Conditions** (FIRM, real bodies):

- **`CondV E`** (V, txt:71): every entry's parent resolves on its column's stack, hence is a
  visible smaller number.
- **`CondI E`** (I, txt:72-73): for every entry `e` with nonempty height `h`, every column of
  `h` is nonempty and its first parent is at least `e.col.num 0` (the host number `a`). The
  outer forest's columns may be empty.
- **`CondH E`** (H, txt:74): in every column, consecutive entries are nonincreasing in entry
  order (`EntryLe`: parent first, then height).
- **`CondAK E ks`** (A, txt:185-190) in key system `ks`: for every column `c` with parents
  `p_0, …`, and every `i`, `p_i` is reached by a `Path` at query `cutQuery (ks c) i` from
  `c.num 0 − 1` (if `i = 0`) or from `p_{i−1}`.
  - `CondA E := CondAK E (actualKeys E)`.
  - "Decorated A" is `CondAK E (capKeys E sel)`.
- **`IsOwnerReturn E e0 e`** (txt:201-202): `e`'s column lies inside the height of `e0`
  (`e0.heightPath` is a prefix of `e.col.path`), and `e`'s parent resolves to `e0`'s column.
- **`CondS E`** (S, txt:203): at every owner return,
  `relKey (e.col.num 0) J < relKey (e0.col.num 0) H`.
- **`InL E := CondV E ∧ CondI E ∧ CondH E ∧ CondA E ∧ CondS E`** (the class L, txt:204). P is
  deliberately *not* part of L (S-6, codex simpl. 5); see §c.6.

**G-006 (closed): explicit induction predicates.** These are U1-internal and FIRM in content;
U1 writes them as lemmas L2.3a and L2.4a, following codex-crosscheck-1 Q2.

- Barrier: a joint strong induction on `(c, k)` of
  - `C_e(c,k)`: an actual `g_{W(c,k)}`-path from `x(c,k)` that reaches `a` has
    `W(c,k) < D_e = B_a(u)`;
  - `R_e(c,k)`: if entry `k` has parent `a`, then `B_c(k) < D_e`.
  Both are quantified over all containing entries `e` and all scopes.
- The localized consequence: `C_e(c,k)` needs only earlier return bounds.
- Reverse capping: the first-divergence argument.

A proof that carries only "earlier A holds" is not accepted (G-006 detail).

### c.4 Words and safe prefixes (U1: C1.8, D1.9)

- **`WordAtom := Nat ×ₗ Nat ×ₗ Nat`**, ordered lexicographically.
- **`word E`** (real body), at depth `e` (txt:143-146):
  - an empty column gives `(2e, 0, 0)`;
  - the first entry `(p, H)` of a column gives `(2e, 1, p)` followed by the word of `H` at depth
    `e + 1`;
  - every later entry gives `(2e + 1, 0, p)` followed by its height's word.

  `List WordAtom` carries Mathlib's lexicographic `LinearOrder`, with a proper prefix smaller.
- **`mu E := (word E).length`** is `µ(E)`.
- **Contracts** (U1, C1.8): `word_lt_iff : word E < word F ↔ E < F` and `word_injective`.
- **`safePrefix E k`** (body: U1, D1.9) is the forest whose word is `(word E).take k` (txt:152-153).
  - It is well defined because every prefix of a word decodes to a forest: the first entry of a
    column carries its column marker, so no empty internal column is created.
  - For `k ≥ µ(E)`, the result is `E`.
  - Contracts: `word_safePrefix`, and `truncAfter_safePrefix` (`truncAfter` is a safe prefix).

### c.5 Shifts, the continuation hole and the operation (U1: D1.5, D1.6, D1.6a; G-001)

- **`shift r d F := Tree.map (shiftVal r d) F`** is `T_{r,d}` (txt:86): it adds `d` to every
  parent `≥ r`, at every depth.
- **`Hole := { outer : Forest, depth : Nat }`** and
  **`Hole.fill h r d Z := replaceAt r d Z h.depth h.outer`**.
  - This is `A_{r,d,ℓ,Z}`: shift by `T_{r,d}` and replace the last column at depth `ℓ` on the
    route by the columns of `Z` (unshifted).
  - It is the one typed continuation-hole operation of S-6. U2 (kernels `F_H`, (1)) and U3
    (occurrence maps) use it.
- **Branch data** (FIRM types; bodies: U1).

  **`StopData`** has fields `depth = ℓ`, `col`, `t = col.num 0`, `r` and `Q` (txt:98-104):
  - `col` is the stopping column's address: the last column of `F_ℓ`.
  - `r` is the parent of the last entry.
  - `Q` is the stopping column without its last entry.

  **`RootData`** has fields `layer = j`, `idx = i`, `col = ⟨π_j, i⟩`, `owner` and `cursor`
  (txt:121-122):
  - `owner` means `i = |F_j| − 1`.
  - `cursor` is the final source cursor of the raw scan
    `cursor (rootKeys E rd) (queryKeys sd)`.
  - `rootKeys` normalizes at `r` and `queryKeys` at `t`.

  Derived data (real bodies):
  - `closingSlot sd = ⟨sd.col, |Q|⟩` is the closing slot `N`.
  - `StopData.ownerEntry sd` is the direct owner entry of the stopping forest, given by the
    last step of `sd.col.path`. For a special step this is the entry
    `(p, C ⌢ [[(a, ∅)]])` that is replaced.
- **`paperOp E n`** (body: U1). It is written from §1.2 only, with this exact algorithm:
  1. If `E = ∅`: `none` (txt:96).
  2. If the last outer column is empty: `some` (`E` without it).
  3. Route. Start with `F_0 = E` and `π_0 = []`.
     - At depth `d`, let `col` be the last column of `F_d`. If `d > 0` and `F_d` has no columns
       or `col = []`, return `none`: the paper's route is stuck (X-02; it cannot happen
       under I).
     - Let `(p_d, G)` be the last entry of `col`. If `G = ∅`, stop with `ℓ = d`,
       `col_stop = ⟨π_d, |F_d|−1⟩`, `Q = col.dropLast` and `r = p_d`.
     - Otherwise set `F_{d+1} = G` and `π_{d+1} = π_d ++ [(|F_d|−1, |col|−1)]`.

     Then `t = col_stop.num 0`, which equals `Σ_{i≤ℓ}|F_i| − 1`.
  4. **Special** iff `ℓ > 0`, `Q = []` and `r = t − |F_ℓ|`, the number of the direct owner
     column. The containing column `P ⌢ [(p, C ⌢ [[(a,∅)]])]` of `F_{ℓ−1}` is replaced by
     `P ⌢ [(p, C)]^{n+ε}`, with `ε = 1` iff `P = []`. Containers are already last entries.
  5. **Ordinary** otherwise. Let `o = col_stop.resolve 0 r`; if `none`, return `none` (root not
     visible).
     - Write `o = ⟨π_j, i⟩` and `F = F_j`, and put `d = t − r`.
     - Scan the root keys against the query keys; `c` is the final source cursor and
       `U = R[c:]`.
     - If `i = |F| − 1`, `n ≥ 1` and `U = []`, return `none` (txt:129).
     - Otherwise run the loop of txt:125-131 for `k = n, …, 1`, starting from `Z = ∅`:
       - the head is `T_{r,(k−1)d}(Q)` followed by `U`, each entry keeping its parent with its
         height shifted by `T_{r,kd}`;
       - in the body case, the new `Z` is the head followed by `A_{r,kd,ℓ−j,Z}(F[i+1:])`;
       - in the owner case, the last restored height uses `A_{r,kd,ℓ−j−1,Z}`, and the new `Z`
         is the head alone.
     - Return `some (replaceAt 0 0 Z ℓ E)`, which is `A_{0,0,ℓ,Z}(E)`.

  `stepKind E` is `deletion`, `special` or `ordinary` by steps 2, 4 and 5, and `none` where
  `paperOp` is `none` for a reason other than owner-root exhaustion. `stopData E` is `some`
  iff step 3 stops. `rootData E` is `some` iff `stepKind E = some .ordinary`.
- **Contracts provided by U1** (FIRM):
  - `expand_eq_paperOp`: on nonempty V∧I inputs, `expand E n = paperOp E n` (G-001).
  - `expand_empty`: `expand ∅ n = some ∅` (real proof `rfl`; the reference's self-loop).
  - `expand_isSome`: V, I, A, S imply `expand E n` is defined (L2.4).
  - `stepKind_isSome`: on nonempty V∧I inputs, `stepKind E` is `some`.
  - Branch data exist: `stopData_of_stepKind`, `rootData_of_ordinary`, `ownerEntry_of_special`.
  - `expand_deletion`: a deletion step removes the empty last outer column.
- **Scan contracts** (U1; REFINABLE in form, FIRM in content):
  - `cutQuery_lt_succ`: boundaries strictly increase (D2.1).
  - `cursor_spec`: for a reduced (nonincreasing) query `W`,
    `cutQuery ks (cursor ks W) ≤ W` and, if not exhausted, `W < cutQuery ks (cursor+1)`
    (L2.1, txt:165-168).
  - `cursor_nu`: reducing a query does not change the final source cursor.
  - `path_nesting` (L2.2): under V and `CondAK E ks`, with reduced `W ≤ Z`, every `g_Z` edge is
    a `g_W` path.
- **Named by U1, stated by U1:**
  - `barrier`, `cut_barrier` (L2.3, L2.3a);
  - `capping_iff` (L2.4, L2.4a): under V and S, `CondA E ↔ CondAK E (capKeys E sel)` for
    `sel ⊆ routeCols E`;
  - the trace facts `trace_map` (1), `trace_cap_top` (2), `trace_agree` (3) and
    `sign_of_agreement` (txt:246-249) (L2.5);
  - `cursor_eq_scanCount`, linking `cursor` on keys to the locked `scanCount`.

### c.6 Profiles, caps, repairs; closure and cofinality (U2: D3.1, D3.1a, L3.1, L3.1a, T3.2, T3.2a, T3.8)

- **`profile H : WithBot (Nat ×ₗ Nat)`** (body: U2, txt:254-256).
  - `profile ∅ = ⊥`, which stands for `(−1, 0)`.
  - Otherwise let `H_0 = H`. While the first entry of the first column of `H_k` has a nonempty
    height, let `H_{k+1}` be that height.
  - Let `d` be the number of steps, and `m` the length of the leading run of entries of
    `H_d`'s first column whose parent equals that column's first parent. Under H these are
    exactly the "m maximal-parent entries".
  - Then `profile H = (d, m)`.
- **`CondP E`** (P, txt:258) (real body): `profile J < profile H` at every owner return. P is a
  separate invariant, not part of L (S-6).
- **`litCap E c k p`** (body: U2, txt:261-262). Let `c = ⟨[(c_0,i_0),…,(c_{m-1},i_{m-1})], j⟩`.
  1. In the forest at each level `d < m`, keep the columns `0…c_d`. In column `c_d`, keep the
     entries `0…i_d`; the last of them is the containing entry, whose height is processed at
     level `d+1`.
  2. In `c`'s own forest, keep the columns `0…j`.
  3. Replace column `j` by its first `k` entries, with their complete heights, followed by
     `(p, ∅)`.

  All later context is removed. If `c` is not a column of `E`, the result is `E`.
- **`IsUpward E c k p`** (real body, txt:262): if entry `k` exists, its parent is `< p`;
  otherwise `k = |c|` (an append at the column's end).
- **`Move := { col, i, j }`** (FIRM). The entry at index `j` of column `col` moves to index
  `i < j`; entries `i…j−1` are deleted (txt:284-285).
  - `applyMove` (body: U2); with invalid indices the result is the input unchanged.
  - `applyMoves E ms := ms.foldl applyMove E`.
- **`MovesValid K ms`** (body: U2, L3.1). Each move `m`, applied in order to the current
  expression, satisfies all of the following:
  - `m.col` is a containing column of the cap's stopping column, and its last entry `j` is the
    active one;
  - entries `i…j` share one parent `p`;
  - writing `C` for the height of `j`, `i` is the least index of that same-parent run with
    `H_i < C`.
- **`RepairList K b ms`** (body: U2, record-level, txt:656-658). Each move, in order, satisfies:
  - it lies in `b`'s column or in a strict container column of `b` (at `b`'s current
    address);
  - it deletes only closed entries (none contains `b`), all with the moved entry's parent;
  - the retained later entry is `b` or `b`'s container.

  `moveAddr ms b` (body: U2) is `b`'s current address after the moves. An index `j` on `b`'s
  path through a moved column becomes `i`.
- **`AdmCap E`** (FIRM structure, D3.1a). An admissible upward cap of `E` consists of `col`,
  `cut`, `par`, `moves`, and the proofs `upward`, `movesValid` and
  `inL : InL (applyMoves (litCap E col cut par) moves)`.
  - `AdmCap.H` is the resulting expression.
  - `AdmCap.origin w : Role → Option Role` (body: U2) is the surviving-role map χ into `E`.
    It is `none` exactly on the appended closing slot. A literal cap keeps `E`'s addresses
    for all other roles; moves shift indices back.
  - `anchor E none = E`, `anchor E (some w) = w.H`, `anchorOrigin E none = some`.
  - "An admissible cap of an original standard `E`" (txt:1127, 1187) always means
    `anchor E (some w)` with `IsStd E`.
- **Contracts provided by U2** (FIRM):
  - `condS_of_condP` (L3.1a, G-002): `V ∧ I ∧ H ∧ P ⇒ S`. Bare P does not imply S (X-03
    counterexample).
  - `std_inL`, `std_condP` (T3.2).
  - `inL_expand`, `condP_expand` (L and P preserved), `inL_safePrefix` (T3.2).
  - `expand_lt`: on nonempty V∧I inputs, `E[n] < E` (T3.2, the paper's hypothesis).
  - `isStd_iff_paper` (T3.2a): the paper's Std, generated by `paperOp` from the seeds, equals
    `IsStd`. It uses T3.2 and D1.6a.
  - `cofinal` (T3.8): `IsStd B → InL E → B < E → ∃ n E', expand E n = some E' ∧ B ≤ E' ∧ E' < E`.
    It is used with an admissible cap as `E` in §8.5 Case 3 (txt:1396).
  - `cofinal_bound` (T3.8): if the last outer column of `E` is nonempty, some `n` with
    `1 ≤ n ≤ µ(B) + 1` has `B < E[n]`.
- **Named by U2, stated by U2** (REFINABLE):
  - `upward_condS` (L3.1): an upward cap of a V,I,H,P expression that satisfies V and I
    satisfies S.
  - `repair` (L3.1): decorated A gives an `AdmCap` with the same final parent and an unchanged
    internal cap.
  - The kernel API (D3.3, L3.4, L3.5, L3.6, L3.7) is U2-internal.

### c.7 The diagram language and the S-4 semantic interface (U4: N4.1, N4.2, D5.7, D5.7a, L5.8, L5.8a, L5.9, L6.5, L6.6; G-004)

**Diagram grammar** (FIRM, real bodies; owner U4 because U4 must validate it, txt:874-877).

- **`IsLim o := Order.IsSuccLimit o ∧ ω < o`** is `Lim(a)` (txt:735-736).
- **`Prims := { Elem, Edge }`**.
  - `Elem a b` means `J_a ≺_{Σ1} J_b`.
  - `Edge C b a` means `R(C, b, a)` of (10).
- **`BaseAtom V`**: `lim x`, `lt x y`, `le x y`, `eq x y`, `elem x y`, `edge c b a`. Each has
  `vars`, `map` and `Holds P a`, with the obvious ordinal semantics.
- **`BlockAbove P D fr L w`** (ordinal form of `Cert_D(·; frame, L)` in `J_w`, txt:1033-1040).
  Some `β` extends the partial frame assignment `fr` and satisfies all atoms of `D`, with:
  - every new coordinate (variable not in the frame) `> L`;
  - every coordinate `< w`.
- **`Atom V := base (BaseAtom V) | noReal (D : List (BaseAtom W)) (fr : W → Option V) (u L : V)`**.
  - `noReal D fr u L` holds iff `¬ BlockAbove P D (a ∘ fr) (a L) (a u)`.
  - This is the bounded failure predicate (16), `No(J_u; frame, L)`, for an arbitrary base
    diagram `D`. In the paper `D` is a positive block, `Packet.noB K sel fr u L`.
  - Its variables are `u`, `L` and the frame images. Its budget is therefore "every variable
    below the level", matching the `J_{u+ω}` budget of txt:1085-1086, 1386.
- **`Diagram V := List (Atom V)`**, with `vars`, `map`, `ofBase` and `Holds P a` (all atoms
  hold).
- **`Diagram.RealizableBelow P D F σ w`**: some `a` agrees with `σ` on the fixed variables `F`,
  has every variable of `D` below `w`, and satisfies `D`.

**Translation table** (paper → ordinal form). U4 owns its justification (L5.8a). Every use of
budgets in §7–§8 must be read through it.

| Paper | Ordinal form |
|---|---|
| complete certificate of a finite diagram in `J_w` (`w` limit) | `RealizableBelow … w` (L5.8 both directions, txt:879-881, 905) |
| `w_low ∈ J_β` | every low coordinate `< β` (β chosen `< u` above them; `u` limit) |
| genuine `J_u` with history in `J_{u+ω} ⊆ J_W` | `u < W`, with `u` a variable of the atom that reads the level |
| `Cert_B(z; ρ, c⃗, L)` in `J_u` | `BlockAbove P (posBlock K sel) frame L u` |
| `No_B(U; ρ, c⃗, L)`, `U = J_u` | `Atom.noReal (posBlock K sel) fr u L` |
| fixed parameters in `J_a` | fixed coordinates `< a` |
| capture, control transport | `Interface.capture`, `Interface.transport` |
| "genuine histories identify its whole set as `J_{u'}`" (txt:1430-1431) | the label's variable `u` takes the value `u'` |

**`Hier.Interface extends Prims`** (FIRM, S-4). Its fields are exactly what §6–§9 use:

| Field | Statement (ordinals of universe `u`) | Paper source | Used at |
|---|---|---|---|
| `elem_le`, `elem_lim` | `Elem a b → a ≤ b`; both limits | (9), txt:735 | everywhere |
| `elem_refl` | `IsLim a → Elem a a` | — | (19) trivial path |
| `elem_trans` | transitivity | Σ1 composition | (19) txt:1190-1200; txt:1289-1291 |
| `elem_mid` | `Elem a c → a ≤ b ≤ c → IsLim b → Elem a b` | upward absoluteness | txt:1230 |
| `edge_lt`, `edge_lim` | `a < b < C`, all three limits | (10), txt:860 | seed lemma; packets |
| `edge_elem_low` | `Edge C b a → Elem a b` | txt:864-866 (G-004: `J_b ∈ Hull`) | (19); txt:1005, 1327 |
| `edge_elem_high` | `Edge C b a → Elem b C` | (10) | txt:1285 |
| `edge_restrict` | `Edge C b a → IsLim D → b < D ≤ C → Edge D b a` | txt:867-869 | txt:1213, 1229, 1239 |
| `edge_extend` | `Edge C b a → Elem C D → Edge D b a` | txt:869-871 | txt:1231 |
| `capture` | `Elem a b`, fixed variables `< a`, `RealizableBelow … b` ⇒ `RealizableBelow … a` | L5.9 txt:909-911 + L5.8 | txt:1209, 1213, 1285, 1291, 1332, 1361, 1377, 1467 |
| `transport` | `Edge C b a`, `t ∉ F`, fixed `< a`; realizable below `C` with `t ↦ b` ⇒ realizable below `b` with `t ↦ a` | L5.9 txt:912-918 (collapse, then capture into `J_b`) | txt:1283-1286 |
| `card_elem` | `ℵ₀ < κ → IsLim w → κ.ord < w → Elem κ.ord w` | (13) txt:976-983 | used by U4 for (14) |
| `club_edge` | `ℵ₀ < κ`, `κ.IsRegular`, `IsLim w`, `κ.ord < w` ⇒ there is a club `C` of `Set.Iio κ.ord` (Mathlib `IsClub`) with `Edge w κ.ord x` for all `x ∈ C` | (14) txt:984-999 | seed lemma txt:1006-1011 |

**Why the laws are sound for J** (U4's obligations). Set
`Elem a b := IsLim a ∧ IsLim b ∧ a ≤ b ∧ J_a ≺_{Σ1} J_b`, and let `Edge C b a` be (10) with all
three coordinates limits and `a < b < C`.

- **Capture.** "∃ a certificate with fixed parameters `σ(F)`" is Σ1 over `J_b`. Its parameters
  are ordinals `< a`, hence in `J_a` by (9). Every atom of the grammar has a bounded checker
  whose data lies in `J_{v+ω}` for `v` the largest coordinate it reads; for `noReal` this
  includes the whole `J_u` and its history (txt:1086). Reflecting to `J_a` gives a certificate
  whose recorded ordinals are `< a`.
- **Transport.** Reflect into `Hull^{J_C}_{Σ1}(J_a ∪ {b})` and collapse (L5.6). The collapse
  fixes `J_a` and sends `b ↦ a` (txt:872-873). Then capture into `J_b` along
  `J_b ≺_{Σ1} J_C`.
- **`noReal` is preserved by both,** because it is Δ0 in the parameter `J_u`, and collapse
  sends `J_u` to `J_{π(u)}` (L5.6, final clause).

U4 must prove these from §5. Any atom added to the grammar later would need the same argument.
The instance is **`Hier.jInterface : Interface.{u}`** (body: U4).

- **Contracts:**
  - `add_omega_le` (F5.1): `IsLim w → v < w → v + ω ≤ w`.
  - `isLim_ord` (D6.4): uncountable `κ` gives `IsLim κ.ord`.
- **U4-internal:**
  - the hierarchy `Hier.S`, `Hier.J` (D5.2), and C5.3, C5.4, L5.5, L5.6;
  - CU primitives may be vendored later under R-5 (Apache-2.0). The Σ1-J condensation is new
    (R-6);
  - helper lemmas on `IsWeaklyMahlo`: `IsWeaklyMahlo.uncountable_regular` and
    `IsWeaklyMahlo.stationary_pred`.

### c.8 The graph Γ(E), configurations, role sets, occurrence maps (U3: D6.1, L6.2, D6.3)

- **`Packet.graph E : List (BaseAtom Role)`** (FIRM, real body, D6.1 txt:927-933). It contains:
  - `lim x` for every role;
  - `lt x y` for consecutive roles in reading order;
  - `elem (A_c) (A_{c'})` for consecutive columns `c, c'` of one forest;
  - for every entry `e = (p, H)` in column `c` with `(o, v) = c.rep 0 p`, the atoms
    `edge (U_e) (A_c) o` and `edge (U_e) (A_c) v`. These are (11); duplicates are harmless.

  If `p` does not resolve, no edge is emitted. Γ is only used for V-expressions. There is no
  `elem` pair between sibling height forests.
  Checked on `L_3`: the edges are `R(U_i, A_i, A_{i−1})`, `R(U_i, A_i, U_{i−1})` and
  `elem A_0 A_1`, exactly the edges of the seed lemma (txt:1001-1004).
- **`IsConfig P E α := BaseHolds P (graph E) α`** (FIRM), with `α : Role → Ordinal.{u}`.
  The empty expression has no roles, so every `α` is a configuration (txt:934).
- **`cfgMax E α := (E.roles.map α).foldr max 0`**, and
  **`Configured P E θ := ∃ α, IsConfig P E α ∧ cfgMax E α = θ`**.
- **`rolesBefore E x`** (roles strictly before `x`), **`prefixRoles E e`**, which is `P(E,e)`
  (txt:1022), **`restrictTo D S`** and **`prefixGraph E e`** (real bodies).
- **`RoleSets` and `roleSets H`** (real body, txt:935-939): roles `R`, `T`, `N`, and lists `Q`,
  `K`, `D`, `P`.
  - `K` is the interval `(R, T)` minus the slots and heights of consumed root entries, those of
    index `< rd.cursor`.
  - `D = (roles before R) ++ [R] ++ K` and `P = roles before T`.
- **`qMap H n m`, `fMap H n m : Role → Role`** (bodies: U3, L6.2 txt:944-964). These are the
  query map `q_m` and retained map `f_m` of stage `m` into the roles of `H[n]`.
  - Stage `m` corresponds to loop index `k = m`: the `m`-th head in reading order.
  - `q_{m+1}(T) = h_{m+1}`; on `Q` it is the fresh query copy; on `D` it equals `f_m`.
  - `f_{m+1}(R) = h_{m+1}`; on `K` it is the fresh retained copy; below `R` it is the
    identity; `f_0` is the identity on `D`.
  - Stage blocks nest through the continuation hole: at depth `ℓ − j` of the body copy, or
    `ℓ − j − 1` in the last restored height in the owner case.

  U3 states `occurrence_map_identity`: `graph (H[n])` has, as a set of atoms, the union over
  stages of the images of retained atoms under `f_m` and of query atoms under `q_m`, plus the
  entering pairs of txt:961-963. This is REFINABLE in form.
- **`iota H n := id`** (real body, D6.3). `A_{0,0,ℓ,Z}` replaces only the stopping column, so
  every role before `T` keeps its address. ι is the identity on `P` and generally differs
  from `f_n`. Old labels read ι, never f (txt:967-968, 1310).

### c.9 Names, charts, frames, blocks (U3: D7.1; risk R-3)

- **`Name := role (tag : Nat) (r : Role) | aux (k : Nat)`** (FIRM, txt:1018-1021). Names are
  immutable: `role tag r` is role `r` of chart instance `tag`, and `aux k` is an auxiliary
  coordinate (floor, stage, separating bound).
  - A **chart** is a map `Role → Name` that is injective on its graph's roles.
  - Charts overlap only where a validity clause forces equality.
  - Fresh names use unused tags.
- **`Frame V := { host : V, reps : List (V × V) }`** (FIRM, txt:1024-1027). A frame is the
  physical host plus both representatives `(O(q), P(q))` of every externally visible column
  `q < host number`. Unused representatives are kept.
  - `frameOf e := ⟨A_{e.col}, e.col.reps0⟩` (real body). It depends only on the address.
  - `Frame.map` maps a frame through a function.
- **`BlkVar := host | ord q | cur q | owner | inner (r : Role)`** (FIRM). These are the
  variables of a block problem. `Frame.toFr` sends `host`, `ord q` and `cur q` to frame
  entries and leaves `owner` and `inner` free.
- **`freeBlock K`** (real body). Here `K = h_a(B)` is a relative key; the internal roles are
  `K.roles`. It contains:
  - `lim` on the owner and on every internal role;
  - the strict chain `owner < r_1 < r_2 < …` in reading order;
  - `elem` for consecutive internal columns;
  - for every internal entry `e` with label `ℓ_e` in column `c`, the atoms
    `edge (inner U_e) (inner A_c) X` and `edge (inner U_e) (inner A_c) Y`, where:
    - `ℓ_e = (false, q)`: `(X, Y) = (ord q, cur q)`, an external column from the frame;
    - `ℓ_e = (true, 0)`: `(X, Y) = (host, owner)`, the host column, whose current
      representative inside the height is the owner;
    - `ℓ_e = (true, v+1)`: `(X, Y) = c.rep 1 (v+1)` mapped to `inner`, an internal column.

  Checked on `L_3`'s height: `freeBlock` reproduces exactly the internal edges of Γ(L_3).
  The block depends only on the relative key, so equal keys give the same free problem
  (txt:1235-1237).
- **`blockMap e : BlkVar → Role`** (FIRM, real body; added at integration, §i.6). It reads the
  block variables of the height of entry `e` as roles of the surrounding tree: `host ↦ A_{e.col}`,
  `ord q`/`cur q ↦` the two components of `e.col.rep 0 q`, `owner ↦ U_e`,
  `inner r ↦ Role.under e.heightPath r`. This is "the internal graph of B interpreted at this frame"
  (txt:1028-1030).
- **`posBlock K sel := freeBlock K ++ [edge owner host (ord sel), edge owner host (cur sel)]`**
  (real body). The two added atoms are the target heads (15); `sel` is the outer entry's parent.
- **`noB K sel fr u L := Atom.noReal (posBlock K sel) fr.toFr u L`** is (16).
- **N3.1** (U3 states; FIRM content, S-6): one finite-name amalgamation and packing lemma.
  - `Diagram.holds_append`, and `Diagram.holds_map : (D.map f).Holds P a ↔ D.Holds P (a ∘ f)`.
  - `amalgamate`: two assignments that agree on all shared names realize the union.
  - `pack_below`: finitely many coordinates `< u` with `IsLim u` lie below some `β < u`.

### c.10 Records (U3: D4.1, D4.1a, L4.2; G-003)

A record relates two heights:
- a **target**: entry `b` of the *original standard* expression `E`, with height
  `B = tgtHeight`, printed host `t = b.col.num 0` and key `h_t(B) = tgtKey`;
- a **source**: entry `a` of a truncated admissible context `F`, with height
  `A' = srcHeight`, host `r = a.col.num 0` and key `h_r(A') = srcKey`.

These are four fields of **`SrcRecord := { E, b, F, a, kind : RecKind E }`** (FIRM). The
original target address `b` and the current source address `a` are distinct fields (X-04).

**`RecKind E`** (FIRM, txt:650-658):

- **`scan cap i j`.** The anchor is `H = anchor E cap`, either `E` itself or an admissible cap.
  The record names the actual source index `i` (root entry `i` of `H`) and the query index `j`.
  The target is the `E`-origin of query entry `j`.
- **`desc cap i j`.** The same anchor, source entry and pre-entry context; the source height is
  replaced by an admissible `A' ≤ A_i` (txt:653-654).
- **`repair ms`.** Source and target have the same printed host. Outside the source height,
  `F` is the target context truncated after `b` and moved by the same-parent move list `ms`
  (txt:655-658).

**`SrcRecord.Admitted`** (FIRM, real body; D4.1a). The common clauses are:
- `IsStd E`;
- `b ∈ E.entryAddrs` and `a ∈ F.entryAddrs`;
- `InL F`, and `F.truncAfter a = F` (the context is truncated after the marked height);
- `tgtKey < srcKey` (a strict source).

The kind clauses are:

- **scan:**
  - `AnchorAt E cap i j b`: `H` is ordinary, and the `E`-origin of query slot `⟨sd.col, j⟩` is
    `b`;
  - `ReachesGT (rootKeys H rd) (queryKeys sd) i j`: the actual raw scan reaches `(i,j)` with
    `x_i > y_j`;
  - root entry `i` is closed (it is not the container of the stopping column);
  - `anchorSrc E cap i = some a`, that is `a = ⟨rd.col, i⟩`;
  - `F = H.truncAfter a`.
- **desc:** `AnchorAt` and `anchorSrc` as for scan;
  `F.setHeight a (H.heightAt a) = H.truncAfter a`; and `srcHeight ≤ H.heightAt a`.
- **repair:** `RepairList (E.truncAfter b) b ms`; `a = moveAddr ms b`; and
  `F.setHeight a B = applyMoves (E.truncAfter b) ms`.

**What G-003 required and where it is now:**
- explicit occurrence maps: `anchorOrigin`/`AdmCap.origin`;
- actual scan indices and the source/query projection equations: `AnchorAt` with `ReachesGT`
  and the closedness clause;
- retained marked entry and pre-entry context: the `truncAfter`/`setHeight` equations;
- a finite repair list with surviving roles: `ms`, `RepairList`, `moveAddr`;
- the boundary instance of X-04 (a special step on `L_2` replacing the marked entry): excluded
  by L4.3's "confined" definition below, which requires the marked entry to survive.

`g_Z(t) = r` "asserted in H" (txt:652) is not a field: the scan boundary lemma (L2.1) makes it
true of every column at its own complete query.

**`Packet.SrcRecord.FirstDiff` and `SrcRecord.firstDiff`** (FIRM type; classifier body: U3, real
since integration, §i.3; txt:1357-1382).
Compare `tgtKey` with `srcKey` at their first difference. Column addresses are absolute in `E`.

- **`wholeEnds`** (Case 1): `tgtKey` is a proper prefix of `srcKey`.
- **`childEnds path`** (Case 2): the proper child forest of `B` at `path` ends while the source
  forest has another column.
- **`capAt c k p`** (Case 3): at target column `c` and cut `k`, either the source entry has a
  larger parent field, or the target column ends and the source column has another entry. `p`
  is the absolute parent in `E`: `q` for a false field `(false, q)`, `t + v` for a true field
  `(true, v)`.

**Contracts provided by U3** (statements written by U3; REFINABLE in form; consumers in
parentheses):

- **L4.2 `firstDiff_cap`** (L8.8 Case 3). Admitted `rk` with `firstDiff rk = capAt c k p`, and
  `K = litCap E c k p`, give all of:
  - `IsUpward E c k p`;
  - `CondV K`, `CondI K`, `CondS K`, and decorated A, `CondAK K (capKeys K (routeCols K))`;
  - `stepKind K = some .ordinary`;
  - `p` lies on the target's actual complete-cut chain, that is
    `Path E (actualKeys E) c (cutQuery (actualKeys E c) k) (Scan.cutStart E c k) p`, with U1's
    `Scan.cutStart` (D2.2a; registered in §i.1).
- **L4.3 `reduce_confined`** (L8.8 Cases 2–3; W).
  - An operation on `F` is **confined** iff its stopping column lies strictly inside the
    marked height `A'`, and, for a special step, its owner entry also lies strictly inside
    `A'`. Hence the marked entry `a`, its pre-entry context and its frame survive.
  - Safe prefixes cut inside `A'` and confined operations keep admission when the result stays
    strictly above `B`. The kind is kept, except that `scan` becomes `desc`.
- **L4.3 `repair_output`** (L8.8 Case 3).
  - Setting: `H` is the repaired cap, `anchor E (some w)`, of the first-difference cap.
  - If `H[k] > E`, then:
    - the height `B'` of `H[k]` at `moveAddr ms b` satisfies `B' > B_good ≥ B` (6);
    - the repair record `(E, b, F := H[k].truncAfter (moveAddr ms b), a := moveAddr ms b,
      repair ms)` is admitted.
  - Cofinality (`Closure.cofinal`) supplies such a `k > 0`.
- **L4.3 `query_size_bound`** (L8.8 Case 3). Every terminal-query height `J` of `H` is a
  retained occurrence of `E` (through `AdmCap.origin`) that lies strictly inside the original
  `B`, and `J.size + 2 ≤ B.size` (7).
- **L4.3 `reduce_childEnds`** (L8.8 Case 2). If `firstDiff rk = childEnds π`, there are:
  - a safe truncation `F₁` of `F`, through the first entry of the extra column, with that
    entry's height cleared;
  - a parameter `k`;

  such that the step of `F₁` is confined and is either ordinary with empty query or special,
  `F₂ = F₁[k]` satisfies `tgtKey < srcKey(F₂) < srcKey(F)`, and the record with `F₂` is
  admitted.

### c.11 Source packets, factorization, the scan setup (U3: D7.2, D7.2a, D7.2b, L7.3–L7.6)

**`SourcePacket := { rk : SrcRecord, tgtChart srcChart : Role → Name, aux : Diagram Name, asg : Name → Ordinal.{u} }`**
(FIRM, txt:1045-1053).

Derived names and data (real bodies):
- `host = srcChart (A_{a.col})` is the physical host ρ;
- `owner = srcChart (U_a)` is the source owner `u`;
- `tgtFrame = (frameOf b).map tgtChart` and `srcFrame = (frameOf a).map srcChart`;
- `lowNames` are the names of both prefixes `P(E,b)`, `P(F,a)` and of the auxiliary diagram;
- `joint` is the diagram consisting of `prefixGraph E b` through `tgtChart`, `graph F` through
  `srcChart`, and `aux`.

**`SourcePacket.Valid P pk`** (FIRM, real body; D7.2a). It is the conjunction of:

1. `tgtChart` is injective on `P(E,b)`, and `srcChart` on the roles of `F`. These are paper
   clauses 1 and 2; charts are injections (txt:1019).
2. `tgtChart (A_{b.col}) = host`: "the two physical host roles share ρ" (txt:1054).
3. `srcFrame.reps.take r = tgtFrame.reps.take r`, with `r = a.col.num 0`: the external frame
   below the source printed host agrees.
   - For cross-host records (scan, desc; `r < t`) this is txt:1054-1055.
   - For same-host repair records (`r = t`) it is the whole frame, txt:1055-1057.
4. `joint.Holds P asg`: one assignment realizes both charts and the auxiliary diagram (clauses
   3 and 4).
5. Both target heads at `u`: `Edge(asg u, asg ρ, asg o)` and `Edge(asg u, asg ρ, asg v)`, for
   `(o, v) = tgtFrame.reps[tgtSel]` (clause 5, (15)).
6. Every low name has value `< asg u` (clause 6: the low certificate lies in `J_u`). Neither `u`
   nor the source height is low (txt:1059-1060).

**Deliberate weakenings, with their justification.**
- Validity does not forbid extra overlaps between charts. Overlaps only add constraints, and
  no step of §7–§8 uses that two names differ. Fresh names are always available, because
  packets are finite.
- The auxiliary diagram may contain any atoms of the grammar. Its content is opaque to S_n: it
  is carried through capture and transport (txt:1063-1065).

**`SourcePacket.TargetAbove P L`** (FIRM, real body; the conclusion of S_n). Some `β : BlkVar → Ord`
satisfies:
- `β` agrees with the target frame's values;
- every new variable (owner, inner) is `> L` and `>` every low value, and `< asg u`;
- `posBlock tgtKey tgtSel` holds at `β`.

The clause "above every low value" encodes "compatible with all unchanged low resources". With
fresh names, compatibility amounts to the reading order between the target prefix and the new
block (txt:1074-1077).

**L7.3 `factorization`** (FIRM statement; hypothesis `a ∈ F.entryAddrs` added at integration, §i.4).
Let `pk` be valid, `pk.rk.a ∈ pk.rk.F.entryAddrs` and `L < u`. Then some `L*` with
`L ≤ L* < u`, and above every low value, has this property: a positive block above `L*` below
`u` gives `TargetAbove L`. Its contrapositive is the failure label: if `TargetAbove L` fails, then
`noB tgtKey tgtSel tgtFrame owner ℓ` holds at `asg` extended by a fresh auxiliary name `ℓ` with
value `L*` (txt:1079-1080).

**`ScanSetup`** (FIRM fields; D7.2b; the hypotheses of §7.3 txt:1127-1137 and of W). Its fields
are `E`, `cap`, `sd`, `rd`, and:
- `ePre : Role → Name`: the transported target-prefix chart on `P_E`, the roles of `E` strictly
  before the `E`-copy of the stopping ordinary role;
- `stopNm`: the new stopping role, of value `ρ`;
- `qNm`: the original positive query;
- `bankNm`: the source bank;
- `aux`, `asg`.

Derived (real bodies):
- `H = anchor E cap`;
- `preStop`, the roles of `H` before `T`;
- `queryRoles`, the roles strictly between `T` and `N`;
- `queryGraph`, the atoms of Γ(H) inside `P⁻ ∪ {T} ∪ Q` that involve `T` or `Q`. This includes
  the entering ordinary pair and `lt (·, T)`;
- `baseVal`: on `P⁻` it is `asg ∘ ePre ∘ χ`, and `T ↦ ρ`;
- `fitVal β`, which is `β` on query roles;
- `ownerVal i = u_i`.

**`ScanSetup.Valid P S`** (body: U3). Exactly these clauses. Write `T = A_{sd.col}`,
`R = A_{rd.col}`, `c = rd.cursor`, `ρ = asg stopNm`, `χ = anchorOrigin E cap`, and `T_E = χ T`.

- **S1.** `IsStd E` and `InL H`. `stepKind H = some .ordinary`, with
  `stopData H = some sd` and `rootData H = some rd`. The scan does not exhaust the bank:
  `c < |root column|` (the endpoint hypothesis of W, txt:1184-1185). Root entry `c` is closed:
  `rd.col.container sd.col ≠ some ⟨rd.col, c⟩`. W is called only at a closed root owner `u_c`
  (txt:1295-1297); the active-owner case is handled without W (txt:1290).
- **S2 (target prefix, txt:1128).** `ePre` is injective on `P_E = rolesBefore E T_E`. The
  graph `restrictTo (graph E) P_E` through `ePre` holds at `asg`. Every `asg (ePre y) < ρ`.
  For a cap, `P_E` contains the deleted blocks, so they are realized here (txt:1123, 1101).
- **S3 (old auxiliary data).** `aux` holds at `asg`, and every `aux` variable is `< ρ`.
- **S4 (new stopping role and positive query, txt:1129-1130).** `queryGraph` holds under
  `P⁻ ↦ ePre ∘ χ`, `T ↦ stopNm` and `Q ↦ qNm`.
- **S5 (source bank, txt:1131-1137).** Let `bank` be the roles of root entries `0…c` (slots and
  heights). The atoms of Γ(H) inside `preRoot ∪ {R} ∪ bank` that involve `R` or `bank` hold
  under `preRoot ↦ ePre ∘ χ`, `R ↦ stopNm` and `bank ↦ bankNm`. The bank root is the same
  role `ρ`; it is not the transported old root `ePre (χ R)`.
- **S6 (freshness).** `qNm` is injective on `Q`, and `bankNm` on `bank`. Their images are
  disjoint from each other, from `ePre`'s image, from `stopNm`, and from the `aux` variables.

**L7.6 `scan_packet`** (FIRM statement). Assume:
- `S` is valid;
- `ReachesGT (rootKeys H rd) (queryKeys sd) i j`;
- `S.Fitted P j β`: entries `< j` are fitted;
- (17): `Lmax j β < u_i` and `Lmax j β ≤ Cmax j`;
- `HeadsAt P j i β`: both target heads of entry `j` at `u_i`.

Then there is a packet `pk` with `pk.rk = S.scanRecord i j`, `pk.rk.Admitted`, `pk.Valid P` and
owner value `u_i`. Moreover, every `pk.TargetAbove P L` with `L ≥ Lmax j β` extends `β` to a
fitting of entry `j`, with the new values in `(L, u_i)` (txt:1138-1167).

**Named by U3, stated by U3** (REFINABLE in form):

- **L7.4 `joint_cap`** (L8.8 Case 3, txt:1082-1099). Let `pk` be admitted and valid, with
  `firstDiff = capAt c k p` and `K = litCap E c k p`. Then there is a chart `κ` of Γ(K) and an
  extension `asg'` of `asg` to fresh names such that:
  - Γ(K) holds through `κ`;
  - `κ` is `tgtChart` on `P(E,b)`, and `κ(U_b) = owner`;
  - on the common internal prefix and on the closing entry, `κ` is `srcChart` of the
    corresponding source roles;
  - with `W = asg' (κ T_K)` and `C = asg' (κ N_K)`: `asg u < W < C`, and every value on
    `P_K⁻`, every low value and every `aux` value is `< W`.
- **L7.5 `joint_repair`** (L8.8 Case 3, txt:1100-1124). Let `ms` be the repairs of L3.1 giving
  an `AdmCap`. Then:
  - the old assignment, restricted through `AdmCap.origin`, realizes Γ(H);
  - host, owner and full frame are unchanged;
  - deleted blocks stay realized as auxiliary atoms;
  - `P(H, moveAddr ms b)` injects into `P(E, b)` with the same names.

### c.12 Induction predicates (U5: D8.1, D8.1a, L8.7, T9.1)

All of these have FIRM real bodies, except where marked.

- **`SStrict P n`** (S_n, txt:1173-1180). For every packet `pk` such that `pk.rk.Admitted`,
  `pk.Valid P` and `pk.rk.tgtHeight.size = n`, and every `L < asg u`, `pk.TargetAbove P L`
  holds.
- **`WFit P n`** (W_<n, txt:1183-1185). For every valid scan setup whose query children all
  have size `< n`, some `β` satisfies:
  - `BaseHolds P S.queryGraph (S.fitVal β)`;
  - every fitted value is `< u_c` (`ownerVal rd.cursor`).

  This is "fit a complete query below its final unconsumed closed source owner".
- **`AllowedInput n H`** (D8.1a, txt:1186-1189). `H` is in L and ordinary, and either its
  query is empty, or `H` is standard with every query child of size `< n`.
  - Admissible caps of standard expressions, the other inputs of the paper's D_<n, are inputs
    of `DLab` only.
  - The reason: their deleted blocks belong to the target prefixes of the subsidiary S-calls
    (txt:1101, 1123). These blocks must travel in the label through `eν`, and a bare
    configuration of `H` does not supply them.
- **`DCore P n`** (D8.1a, label-free D_<n). For an allowed `H`, a configuration `α`, and
  `expand H k = some H'`, some configuration `γ` of `H'` has every value `< α(T)`
  (txt:1185-1186).
- **`DLab P n`** (D_<n with labels; txt:1255-1323). Hypotheses:
  - an ordinary `H = anchor E cap` in L, with `sd`, `rd` and a configuration `α`;
  - either `Q = []`, or `IsStd E` and every query child has size `< n`;
  - a label over a type `V`: a diagram `Λ`, maps `ν` on `P`, `eν` on `E`'s prefix before `T_E`,
    an assignment `b`, and a set `Fix` of fixed variables;
  - `b ∘ ν = α` on `P`, and `eν ∘ χ = ν` on `P`;
  - Λ contains the `E`-prefix graph through `eν` (deleted blocks travel inside Λ);
  - Λ holds at `b`, and every Λ-value is `< W = α(T)`;
  - every fixed Λ-value is `< p = α(R)` (txt:1259-1263).

  Conclusion: for each `k` with `expand H k = some H'`, there are a configuration `γ` of `H'`
  with all values `< W`, and `b'` agreeing with `b` on `Fix`, such that:
  - `b' ∘ ν = γ ∘ ι_k` on `P`, so old labels read the persistent occurrences;
  - Λ holds at `b'`, with every value `< W`;
  - `γ = α` on the pre-root roles;
  - (moving clause) if `k > 0`, then every nonfixed `x ∈ P` at or after `R` has
    `γ x < p`.

  The moving clause gives the marker identity (22) and the host decrease used at txt:1451-1453.
  The fixed clause is the case `Fix ⊇` (data below `p`), used at txt:1454-1458.
  `DCore` follows from `DLab` (`dCore_of_dLab`†): take `E = H`, `cap = none`, `V = Role`,
  `ν = eν = id`, `b = α`, `Fix = ∅`, and Λ the prefix graph of `H` before `T`. It holds at `α`,
  and all its values are `< α(T)` by the `lt` chain.

  S-6 ("label-free descent before labels"): U5 drafts `DCore`'s proof outline first, then
  `DLab`.
- **`SpecialDesc P`** (L8.7, txt:1325-1346). For `H` in L with a special step, owner entry `e`
  and configuration `α`, and every floor `L` with `prefix ≤ L < s = α(U_e)`: some configuration
  `γ` of `H[k]` equals `α` on `P(H,e)` and puts every other role in `(L, s)`.
  - In ordinal form, the "limited label clause" is automatic: fixed labels keep their values
    and read no new role.
  - The restriction "whole `J_s` cannot be fixed" (txt:1344-1345) is the fixed-below-`s`
    requirement of `capture`.
- **`StrictDescent P`** (T9.1 (27)). For standard nonempty `A` with a configuration `α`, and a
  nonempty `A' = A[k]`: `cfgMax A' γ < cfgMax A α` for some configuration `γ` of `A'`.

**Contracts** (U5): `seed_config` (L6.7), `sStrict_all`, `wFit_all`, `dLab_all`, `dCore_all`
(18), `specialDesc` (L8.7), `strictDescent` (T9.1).

**Named by U5, stated by U5:**
- `owner_path_elem` (L8.2, (19));
- `two_candidates` (L8.3);
- `sStrict_zero` (L8.4). It keeps the capture; S-3 is rejected;
- `wFit_of_sStrict` (L8.5), `dLab_of_wFit` (L8.6), `sStrict_of_dLab` (L8.8);
- `sigma` (R9.2).

The least-failure argument of L8.8 minimizes `(asg host, asg owner)` in the lexicographic
order on `Ordinal × Ordinal`, over the failing packets of one `n`. This is legitimate: Lean's
`WellFounded.min` on a nonempty `Set` of pairs (txt:1349-1352).

### c.13 The S-5 abstract final theorem (U5: N5.1, T9.1a)

**`FinalHyps Conf`** (FIRM, §a) has the fields:
- `order : IsStrictTotalOrder Forest (· < ·)` (U1);
- `empty_least` (U1);
- `closure : IsStd E → InL E` (U2);
- `cofinal : IsStd B → InL E → B < E → ∃ n E', expand E n = some E' ∧ B ≤ E'` (U2);
- `seed : ∀ m, ∃ θ, Conf (seed m) θ` (U5);
- `descent` (U5).

**`abstract_wellOrder : FinalHyps Conf → IsWellOrder Std Std.lt`**, proof plan (S-2):

1. **Every nonempty standard `A` has some `θ` with `Conf A θ`.** Induct on `IsStd` (D1.7).
   - `seed m`: use `seed`.
   - `expand e n = some e'` with `e' ≠ ∅`: if `e = ∅` then `e' = ∅` (`expand_empty`, D1.6a),
     a contradiction. Otherwise the induction hypothesis and `descent` apply.
2. **Labels.** Put `valid B a :⇔ (B = ∅ ∧ a = 0) ∨ ∃ A θ, IsStd A ∧ A ≠ ∅ ∧ B ≤ A ∧ Conf A θ ∧ a = θ + 1`.
   Every standard `B` has a valid label, by step 1 with `A = B`.
3. **Lowering.** Let `C < B` be standard and `valid B a`. Then `B ≠ ∅` by `empty_least` and
   `order`.
   - If `C = ∅`, take `a' = 0 < a`.
   - Otherwise `C < B ≤ A`:
     - `closure` puts `A` in L;
     - `cofinal` gives `A' = A[n]` with `C ≤ A'`;
     - `A' ≠ ∅`, since otherwise `C ≤ ∅` forces `C = ∅`;
     - `IsStd A'` holds by `IsStd.expand`;
     - `descent` gives `θ' < θ` with `Conf A' θ'`;
     - take `a' = θ' + 1 < θ + 1`.
4. **Conclusion.** `Std.lt` is well-founded: for instance by
   `InvImage (· < ·) (fun B => min {a | valid B a})` on `Ordinal`, or by accessibility on the
   label (codex simpl. 2). With `order`, it is a well-order (`IsWellOrder` = trichotomous,
   irreflexive, transitive, well-founded).

**`abstract_implies_main`**:
`(hyp → ∃ Conf, FinalHyps Conf) → MainTheorem`, proved by
`fun h hM => (h hM).elim fun _ hC => abstract_wellOrder hC`.

**`finalHyps I hM : FinalHyps (Configured I.toPrims)`** (T9.1a) assembles the units:
- `order` and `empty_least` from U1 (`Forest.instLinearOrder`, `Forest.empty_lt`);
- `closure := Closure.std_inL`;
- `cofinal`, projected from `Closure.cofinal`;
- `seed`: `seed_config I m (hM (m − 1))`;
- `descent`, from `strictDescent I`. Its proof is a case split on `stepKind A`, using
  `stepKind_isSome` and `std_inL`:
  - **deletion:** restrict `α`; the removed last ordinary role is the maximum, by the `lt`
    chain;
  - **special:** `specialDesc` with `L = max of α` on `P(A,e)`, below `α(U_e)` by the `lt`
    chain;
  - **ordinary:** `dCore_all I n` with `n` above every query size, `E = A` and `cap = none`.
    The values are `< α(T) ≤ cfgMax A α`.

**Main.lean (root, not a unit):**
`std_isWellOrder h := Descent.abstract_implies_main (fun hM => ⟨_, Descent.finalHyps Hier.jInterface hM⟩) h`.

---

## d. Per unit: provides and consumes

- "Provides" lists Lean names, with node IDs in brackets.
- Names marked † are fixed here, but their statements are written by the unit.
- Everything else is declared in `Spine.lean`.

### U1 syntax-scans (`BTBMS.Scan`; root `BTBMS.Tree`, `BTBMS.ColAddr`, `Forest.*`, `Key.*`)

**Provides:**
- **Order and keys:**
  - `Tree.instDecidableEq` (given), and the proofs of `Forest.instLinearOrder` and
    `Key.instLinearOrder` [D1.1, D1.4];
  - `Forest.empty_lt`, `relKey_lt_iff` [D1.1, D1.4].
- **Occurrences** [D1.2, D1.2a]:
  - `ColAddr`, `EntryAddr`, `Role`, `Role.inEntry`;
  - `ColAddr.num/resolve/container/rep/reps0`;
  - `Tree.forestAt/colAt/entryAt/heightAt/roles/colAddrs/entryAddrs/size`;
  - bodies of `Tree.truncAfter` and `Tree.setHeight`;
  - lemmas: `roles_nodup`†, `resolve_spec`† (exactly the visible numbers `< num` resolve, and
    they are unique), `truncAfter_roles`† (the roles of `truncAfter t e` are the roles of `t`
    up to the end of `e`'s height).
- **Conditions** [D1.3, D2.2, D2.3]:
  - `CondV`, `CondI`, `CondH`, `CondAK`, `CondA`, `IsOwnerReturn`, `CondS`, `InL`;
  - `KeySys`, `actualKeys`, `routeCols`, `capKeys`, `resp`, `Edge`, `Path`, `parents`.
- **Word library** [D2.1, L2.1, L2.5]:
  - `nu`, `cutQuery`, `boundary`, `cursor`, `trace`, `ReachesGT`;
  - `cutQuery_lt_succ`, `cursor_spec`, `cursor_nu`, `cursor_eq_scanCount`†;
  - `trace_map`†, `trace_cap_top`†, `trace_agree`†, `sign_of_agreement`†.
- **Words** [C1.8, D1.9]: `WordAtom`, `word`, `mu`, the body of `safePrefix`, `word_lt_iff`,
  `word_injective`, `word_safePrefix`, `truncAfter_safePrefix`.
- **Operation** [D1.5, D1.6, D1.6a]:
  - `shift`, `Hole`, `Hole.fill`;
  - `StepKind`, `StopData`, `RootData`;
  - bodies of `stepKind`, `stopData`, `rootData`, `paperOp`;
  - `closingSlot`, `StopData.ownerEntry`, `rootKeys`, `queryKeys`;
  - `expand_eq_paperOp`, `expand_empty`, `stepKind_isSome`, `stopData_of_stepKind`,
    `rootData_of_ordinary`, `ownerEntry_of_special`, `expand_deletion`;
  - `paperOp_special`† and `paperOp_ordinary`† (the outputs of each branch, in terms of
    `Hole.fill` and `shift`, as in §c.5).
- **Paths and barrier** [L2.2–L2.4, L2.3a, L2.4a]:
  - `path_nesting`;
  - `barrier`† and `cut_barrier`† (the codex-crosscheck predicates);
  - `capping_iff`†, `expand_isSome`.

**Consumes:** only the locked files and Mathlib.

### U2 closure-cofinality (`BTBMS.Closure`)

**Provides:**
- **Profiles and caps** [D3.1, D3.1a]:
  - `profile` (body), `CondP`, `litCap` (body), `IsUpward`;
  - `Move`, `applyMove` (body), `applyMoves`, `MovesValid` (body), `RepairList` (body),
    `moveAddr` (body);
  - `AdmCap`, `AdmCap.H`, `AdmCap.origin` (body), `anchor`, `anchorOrigin`;
  - `origin_spec`†: χ is injective, the identity on addresses before the cut for a literal cap,
    and `none` only on the closing slot.
- **Repair** [L3.1, L3.1a]: `condS_of_condP`, `upward_condS`†, `repair`†.
- **Closure** [T3.2, T3.2a]: `std_inL`, `std_condP`, `inL_expand`, `condP_expand`,
  `inL_safePrefix`, `expand_lt`, `isStd_iff_paper`.
- **Cofinality** [T3.8]: `cofinal`, `cofinal_bound`.
- **Internal:** D3.3, L3.4–L3.7. These are the second half of the S-6 word library:
  cancellation `∂_Q`, `e_0/e_1`, and delayed change.

**Consumes from U1:**
- order and words: `word_lt_iff`, `safePrefix`, `truncAfter`;
- conditions and the class L;
- `nu`, `cursor`, `trace` and the trace facts L2.5;
- path nesting, barrier, capping;
- branch data, `paperOp` and its branch lemmas, `expand_eq_paperOp`, `Hole.fill`, `shift`;
- occurrences.

### U3 records-packets (`BTBMS.Packet`)

**Provides:**
- **Graph** [D6.1, L6.2, D6.3]:
  - `graph`, `IsConfig`, `cfgMax`, `Configured`, `rolesBefore`, `prefixRoles`, `restrictTo`,
    `prefixGraph`, `RoleSets`, `roleSets`;
  - bodies of `qMap` and `fMap`; `iota`; `occurrence_map_identity`†;
  - `graph_prefix`†: `prefixGraph H x` is unchanged in `H[n]` for `x` before `T`. U5 uses it
    with ι.
- **Names and blocks** [D7.1]: `Name`, `Frame`, `Frame.map`, `frameOf`, `BlkVar`,
  `Frame.toFr`, `freeBlock`, `posBlock`, `noB`.
- **Amalgamation** [N3.1]: `holds_append`†, `holds_map`†, `amalgamate`†, `pack_below`†.
- **Records** [D4.1, D4.1a, L4.2, L4.3]:
  - `RecKind`, `SrcRecord` and its accessors, `AnchorAt`, `anchorSrc`, `Admitted`;
  - `FirstDiff`, the body of `firstDiff`;
  - `firstDiff_cap`†, `reduce_confined`†, `repair_output`†, `query_size_bound`†,
    `reduce_childEnds`†.
- **Packets** [D7.2, D7.2a, D7.2b, L7.3–L7.6]:
  - `SourcePacket` and its derived data, `Valid`, `TargetAbove`, `factorization`;
  - `ScanSetup` and helpers, the body of `ScanSetup.Valid`, `scan_packet`;
  - `joint_cap`†, `joint_repair`†.

**Consumes:**
- **from U1:** occurrences, conditions, `truncAfter`/`setHeight`, branch data, `rootKeys`,
  `queryKeys`, `ReachesGT`, `capKeys`, `routeCols`, `Path`, the barrier, the trace facts;
- **from U2:**
  - `AdmCap`, `origin`, `Move`, `RepairList`, `moveAddr`, `litCap`, `IsUpward`;
  - `std_inL`, `inL_safePrefix`, `inL_expand`;
  - `condS_of_condP` and `upward_condS` (profile safety, txt:686);
  - `repair`, and `cofinal` (in `repair_output`);
- **from U4:** the diagram grammar only (`IsLim`, `Prims`, `BaseAtom`, `Atom`, `Diagram`,
  `BlockAbove`, `RealizableBelow`). No interface law is needed. Every ordinal fact U3 uses
  comes from the `lim`/`lt` atoms of graphs that a valid packet or setup realizes. For
  example, `IsLim u` and `ρ < u` come from `lim U_a` and `A_{a.col} < U_a` in `graph F`. So
  `factorization` and `scan_packet` hold for an arbitrary `P : Prims`.

### U4 hierarchy (`BTBMS.Hier`)

**Provides:**
- **Grammar and interface** [N4.1]:
  - `IsLim`, `Prims`, `BaseAtom` (with `vars`, `map`, `Holds`), `baseVars`, `BaseHolds`,
    `BlockAbove`;
  - `Atom` (with `vars`, `map`, `Holds`), `Diagram` (with `ofBase`, `vars`, `map`, `Holds`,
    `RealizableBelow`), `Interface`.
- **Instance** [N4.2]: `jInterface`, with all fields proved from:
  - D5.2, C5.3, C5.4, L5.5, L5.6;
  - D5.7 and D5.7a (G-004: `J_b ∈ Hull`);
  - L5.8 and L5.8a (the ordinal-form equivalence);
  - L5.9, L6.5, L6.6.
- **Lemmas:** `add_omega_le` [F5.1], `isLim_ord` [D6.4], and Mahlo helper lemmas [D6.4]†.

**Consumes:** nothing from other units. It uses Mathlib (ZFSet, Ordinal, Cardinal,
Cofinality.Club, ModelTheory if useful) and the locked `Mahlo.lean`.

### U5 descent-main (`BTBMS.Descent`)

**Provides:**
- **Seeds** [L6.7]: `seed_config`.
- **Predicates** [D8.1, D8.1a, L8.7, T9.1]: `SStrict`, `WFit`, `AllowedInput`, `DCore`,
  `DLab`, `SpecialDesc`, `StrictDescent`.
- **Lemmas** [L8.2–L8.8]: `owner_path_elem`†, `two_candidates`†, `sStrict_zero`†,
  `wFit_of_sStrict`†, `dLab_of_wFit`†, `dCore_of_dLab`†, `sStrict_of_dLab`†.
- **Induction (18):** `sStrict_all`, `wFit_all`, `dLab_all`, `dCore_all`.
- **Special and strict descent:** `specialDesc`, `strictDescent`.
- **Final:** `FinalHyps`, `abstract_wellOrder`, `abstract_implies_main` [N5.1]; `finalHyps`
  [T9.1a]; `sigma`† [R9.2].

**Consumes:**
- **from U1:** order instance, `empty_lt`, branch data and lemmas, `expand_empty`,
  `expand_deletion`, `ReachesGT`, `rootKeys`, `queryKeys`;
- **from U2:** `std_inL`, `inL_expand`, `cofinal`, `AdmCap`, `anchor`, `anchorOrigin`;
- **from U3:** everything in its "provides" list: `graph`, configurations, role sets, maps;
  packets, records, `factorization`, `scan_packet`, `joint_cap`, `joint_repair`,
  `firstDiff_cap`, the L4.3 contracts, and amalgamation;
- **from U4:** all `Interface` fields; `isLim_ord`; `jInterface` (in `Main.lean` only);
- **locked:** `IsWeaklyMahlo`, `StationaryIn`, `MainTheorem`.

---

## e. Lean module layout (planned; nothing is created now)

The spine's declarations move to their owner's modules at T-018. Import order:
`Scan → Closure → Hier.Diagram/Interface → Packet → Descent`. The J instance depends only on
Mathlib and `Hier.Interface`.

```
lean/BTBMS/
  Scan/      (U1)
    Order.lean           D1.1 instances, DecidableEq, empty_lt; D1.4 Key order, relKey_lt_iff
    Occurrence.lean      D1.2a ColAddr, EntryAddr, Role, num/resolve/container/rep, Tree accessors, roles
    Words.lean           S-6 word library: nu, cutQuery, boundary, cursor, trace; D2.1, L2.1, L2.5
    Conditions.lean      D1.3, D2.2 (KeySys, resp, Path, CondAK), D2.3
    CompactWord.lean     C1.8, D1.9 (word, mu, safePrefix, truncAfter, setHeight)
    Step.lean            D1.5 shift, Hole; D1.6 StepKind, StopData, RootData, stepKind/stopData/rootData, paperOp
    Agreement.lean       D1.6a expand_eq_paperOp, branch lemmas
    Paths.lean           L2.2, L2.3, L2.3a
    Capping.lean         L2.4, L2.4a, expand_isSome
  Closure/   (U2)
    Profile.lean         D3.1 profile, CondP; L3.1a
    Caps.lean            D3.1 litCap, IsUpward; D3.1a Move, AdmCap, origin; L3.1 repair
    SafePrefix.lean      T3.2 (safe prefixes)
    Ordinary.lean        T3.2 (ordinary steps: classes, S, A, P, decrease)
    Special.lean         T3.2 (special steps, seeds); T3.2a
    Kernel.lean          D3.3, L3.4, L3.5 (1)
    WordCancel.lean      L3.5 (2), L3.7
    CapCompletion.lean   L3.6
    Cofinality.lean      T3.8
  Hier/      (U4)
    Diagram.lean         N4.1 grammar and semantics
    Interface.lean       N4.1 Interface
    OrdinalFacts.lean    F5.1, isLim_ord, Mahlo helper lemmas
    Basis.lean           D5.2 B, S, J
    TruthTables.lean     C5.3
    Height.lean          C5.4
    Hulls.lean           L5.5
    Condensation.lean    L5.6
    ControlEdge.lean     D5.7, D5.7a
    Certificates.lean    L5.8, L5.8a
    Capture.lean         L5.9
    Reflection.lean      L6.5, L6.6
    Instance.lean        N4.2 jInterface
  Packet/    (U3)
    Graph.lean           D6.1
    OccurrenceMaps.lean  L6.2, D6.3
    Names.lean           D7.1 names, frames, blocks; N3.1
    Records.lean         D4.1, D4.1a
    FirstDifference.lean L4.2
    SourceReduction.lean L4.3
    Packets.lean         D7.2, D7.2a
    Factorization.lean   L7.3
    JointCap.lean        L7.4
    JointRepair.lean     L7.5
    ScanPackets.lean     D7.2b, L7.6
  Descent/   (U5)
    Seed.lean            L6.7
    Predicates.lean      D8.1, D8.1a, SpecialDesc, StrictDescent
    OwnerPath.lean       L8.2, L8.3
    Base.lean            L8.4
    Fitting.lean         L8.5
    Ordinary.lean        L8.6
    Special.lean         L8.7
    Strict.lean          L8.8
    Induction.lean       (18)
    Abstract.lean        N5.1
    Final.lean           T9.1, T9.1a, R9.2
  Main.lean  (root)      std_isWellOrder, mainTheorem, paperTheorem
```

---

## f. Naming conventions

**Namespaces.**
- `BTBMS.Scan` (U1), `BTBMS.Closure` (U2), `BTBMS.Packet` (U3), `BTBMS.Hier` (U4),
  `BTBMS.Descent` (U5).
- One deliberate exception: functions on trees, addresses and roles live in the root namespaces
  `BTBMS.Tree`, `BTBMS.ColAddr`, `BTBMS.EntryAddr`, `BTBMS.Role`, together with `Forest.*` and
  `Key.*` instances. Reasons:
  - dot notation (`E.roles`, `c.resolve 0 q`) works through the `Forest`/`Key` abbreviations;
  - it matches the locked `Syntax.lean`, which puts `Forest`, `Key` and `relKey` in the root.

**Identifiers.** Mathlib style:
- `UpperCamelCase` for types, structures and Props (`CondV`, `InL`, `SStrict`);
- `lowerCamelCase` for functions and theorems (`stepKind`, `cofinal`, `scan_packet`).

  The snake_case exceptions follow Mathlib's theorem naming (`expand_eq_paperOp`).

**Node IDs.**
- A sub-lemma of an existing node appends a lowercase letter (`L2.3a`).
- A wholly new node is `N<unit>.<k>`. The spine has used `N3.1`, `N4.1`, `N4.2`, `N5.1`; the
  next free ones are `N1.1`, `N2.1`, `N3.2`, `N4.3`, `N5.2`.
- Every unit file's declaration docstring begins with its node ID, as in `Spine.lean`.

**Contracts.**
- `-- provides: U<k>, <node>` precedes every cross-unit theorem.
- `-- body: U<k>` follows every `sorry` definition body.
- `-- proofs: U1` marks instance proof fields.

---

## g. Disposition of gaps, simplifications, risks, decisions

| Item | Disposition in this blueprint |
|---|---|
| G-001 | `Scan.paperOp` from §1.2 + `expand_eq_paperOp` on nonempty V∧I (D1.6a); `expand_empty`; all decrease/descent statements carry `≠ ∅`; `isStd_iff_paper` (T3.2a). |
| G-002 | `Closure.condS_of_condP` with hypotheses V, I, H (L3.1a). |
| G-003 | Exact `SrcRecord`/`Admitted` (D4.1a), `SourcePacket.Valid` (D7.2a), `ScanSetup.Valid` (D7.2b); `SStrict` quantifies exactly over them; "confined" requires survival of the marked entry (L4.3); readmission in L8.8 must prove `Admitted ∧ Valid` for the new packet. |
| G-004 | Field `edge_elem_low`, proved via `J_b ∈ Hull` (D5.7a). |
| G-005 | §10 is not used anywhere. |
| G-006 (closed) | L2.3a, L2.4a written as explicit lemmas with the cross-check predicates (§c.3). |
| G-007 (closed) | Nothing: it concerned the locked port. |
| S-1 | `MainTheorem` (locked) uses `IsWeaklyMahlo`; L6.7 uses only regularity and stationarity; (13) only uncountability (`card_elem`). |
| S-2 | `abstract_wellOrder` by ordinal labels/accessibility (§c.13); no choice recursion. |
| S-3 (rejected) | L8.4 keeps the Σ1 capture along `J_u ≺ J_b` (cross-check Q1). |
| S-4 | `Hier.Interface` + `jInterface`; §6–§9 use only the interface. |
| S-5 | `FinalHyps`, `abstract_wellOrder`, `abstract_implies_main` (N5.1). |
| S-6 | Word library in `Scan/Words.lean` (U1) + `Closure/WordCancel.lean` (U2); one hole `Scan.Hole`; P separate from `InL`; `DCore` before `DLab`; N3.1 amalgamation/packing. |
| R-1 | §5 isolated behind the interface (U4). |
| R-2 | `Closure.cofinal` is stated for arbitrary `InL E`; U2 should formalize T3.8 early. |
| R-3 | Occurrence and name types fixed with real bodies (§c.2, §c.9); `iota = id` on `P`, distinct from `fMap`. |
| R-4 | Certificates in ordinal form (§c.7); U4 proves capture/transport once for the fixed grammar. |
| R-5 | Only Mathlib now; CU (Apache-2.0) may be vendored by U4; nothing from the unlicensed reference or YesMetaZFC/BM4 is copied. |
| R-6 | U4 proves Σ1-J condensation new; CU's full-elementary condensation is not a substitute. |
| D-1 | Host-Lean theorem; the Mahlo premise is in universe `u`; `jInterface : Interface.{u}`. |
| D-2 | Weakly n-Mahlo is the hypothesis; `PaperTheorem` follows (locked). |
| D-3 | `expand` (locked) mirrors the reference; `paperOp` + agreement lemma. |

---

## h. Rules for the drafters

1. **Read before drafting.**
   - Read this file, `Spine.lean`, the paper sections of your unit, and the ledger entries and
     review passages that touch them.
   - U1 also reads codex-crosscheck-1 Q2.
   - U4 also reads the reuse audit, §2–§3.
2. **Unit Lean files.** Write `blueprint/lean/U<k>.lean`; the task names the file.
   - It is appended after `Spine.lean`, so it has **no imports**.
   - It re-declares `universe u` and opens `namespace BTBMS` and its own namespace.
   - It ends with every namespace closed.
   - Stubs (facts owned by another unit) follow §i.5.
   - Typecheck with
     `cat blueprint/lean/Spine.lean blueprint/lean/U<k>.lean > <scratch>/check.lean`, then run
     `lake env lean` on it from `lean/`.
3. **Never redeclare** a spine name. To refine a REFINABLE contract, declare it under the name
   given here with the † mark, and record in your unit doc which consumer use (cited in §c/§d)
   it still serves.
4. **Spine-change requests.** If a FIRM item is wrong or insufficient, do not work around it.
   Write a section "SPINE-CHANGE REQUEST" in your unit doc stating:
   - the item;
   - the counterexample or missing case;
   - the proposed replacement;
   - every consumer affected.

   The reconciler decides.
5. **Precision rules** (task brief):
   - every hypothesis is explicit;
   - no "clearly" or "similarly" without an exact reference;
   - every proof step that needs a fact cites the node ID that provides it;
   - every definition that is `sorry` in Lean has a precise informal definition in the unit
     doc.
6. **Forbidden.**
   - Editing `lean/`, `checks/`, `tracker/` or `paper/`.
   - `lake build`; axioms; copying reference code.
   - Recursion or induction on the syntax order (§c.0).

---

## i. Integration amendments (T-016 integration step)

The five unit drafts and their verifications were integrated on 2026-10-27. The spine-change
requests listed below were applied to this file and to `Spine.lean`; the full record, with the
deferred request and the node table, is `blueprint/INTEGRATION.md`. The integrated check (Spine
plus U1–U5, the task's command) has 0 errors.

### i.1 FIRM vocabulary registered from U1 (U1 SCR-1, U2 SCR-U2-1)

These U1 definitions are read by other units. They are FIRM types with U1 bodies, declared in
`U1.lean` unless §i.2 says otherwise:
- addresses and the route: `EntryAddr.Contains` (D1.2b: `e.heightPath <+: c.path`),
  `ColAddr.OnStack` (D1.2b), `Tree.lastStep?` and `Scan.IsRoutePath` (D1.2d);
- conditions and the barrier: `Scan.cutStart` (D2.2a, the start `x(c,k)` of the cut-`k` test),
  `Scan.AAt` (D2.2a), `Scan.CutBound` and `Scan.ReturnBound` (L2.3a);
- the operation: `Scan.specialStop`, `Scan.ordStep`, `Scan.ordLoop`, `Scan.ordZ`,
  `Scan.specialOut`, `Scan.ordinaryOut` (D1.6; in `Spine.lean` since §i.2) and `Scan.Hole.put`
  (D1.5a);
- the word library: `Scan.Noninc`, `Scan.nuStep` (D2.1a), `Scan.qcursor` (L2.1a), `Scan.GAtom`,
  `Scan.gwordAt`, `Scan.gword` (N1.2).

These U1 theorems are registered as provides (§d): `Scan.nu_map`, `Scan.cutQuery_map`,
`Scan.boundary_map` (D2.1a); `Scan.trace_fst_le_cursor` (L2.5a); `Forest.compare_eq_cmp` (D1.1);
`Key.compare_eq_keyCmp` (D1.4); `Scan.sign_of_agreement_compare` (L2.5c); `Scan.paperOp_ordinary`
and `Scan.paperOp_special` (D1.6b); and every declaration of U1 Part J (nodes D1.2e, D1.2f, D1.3b,
D1.4b, D1.5b, D1.6d, D1.9b, N1.4, L2.1d, L2.3c, L2.5d), which other units requested. In §c.10 the
informal `x(c,k)` is now `Scan.cutStart E c k`.

### i.2 U1's bodies are the spine's bodies (U1 SCR-2)

`Spine.lean` now contains, verbatim from `U1.lean`: `Tree.truncAux`, `Tree.truncAfterBody`,
`Tree.setAux`, `Tree.setHeightBody` (§c.2); `Scan.spF`, `spCols`, `spCol`, `spLater`,
`safePrefixBody` (§c.4); `Scan.stopF`, `stopCols`, `stopCol`, `stopDataBody`, `specialStop`,
`stepKindBody`, `rootDataBody`, `ordStep`, `ordLoop`, `ordZ`, `specialOut`, `ordinaryOut`,
`paperOpBody` (§c.5, placed after `queryKeys`). The seven spine names `Tree.truncAfter`,
`Tree.setHeight`, `Scan.safePrefix`, `Scan.stepKind`, `Scan.stopData`, `Scan.rootData` and
`Scan.paperOp` are defined by these bodies (owner U1). Every bridge `…_eq_body` of U1 holds by `rfl`
(`scratch/blueprint/all/rfl_check.lean`, which also evaluates `expand (seed 2) n = paperOp (seed 2) n`
for `n < 5` and `stepKind (seed 3) = some .special`). Statements are unchanged.

### i.3 U2's and U3's bodies are the spine's bodies (U2 SCR-U2-2, U3 SCR2)

- §c.6 now contains U2's `profileAux`, `profileBody`, `litCapAux`, `litCapBody`, `modifyColAux`,
  `modifyCol`, `applyMoveBody`, `MoveOK`, `MovesValidBody`, `Move.fwdIdx`, `Move.bwdIdx`,
  `Move.mapPath`, `Move.mapEntry`, `Move.mapRole`, `moveAddrBody`, `RepairStepOK`, `RepairListBody`
  and `originBody`. `profile`, `litCap`, `applyMove`, `MovesValid`, `moveAddr`, `RepairList` and
  `AdmCap.origin` are defined by them; `moveAddr` now precedes `RepairList`, whose body uses it.
- §c.8 now contains U3's `relocCol`, `transColumn`, `relocEntryCol`, `transEntry`, `relocCols`,
  `transCols`, `nextHead`, `headAddr`, `rootLenOf`, `inQueryRegion`, `inRootSuffix`, `fMapDef` and
  `qMapDef`; `qMap H n m := qMapDef H n m`, `fMap H n m := fMapDef H n m`.
- §c.10 now contains U3's `labelAbs`, `FDStep`, `fdForest`, `fdCols`, `fdCol` and `firstDiffDef`
  (the namespace `SrcRecord` is closed around them); `SrcRecord.firstDiff := firstDiffDef`. The type
  is `Packet.SrcRecord.FirstDiff`.
- §c.11 now contains U3's `anchorD` and the `ScanSetup` helpers `chi`, `TE`, `PE`, `R`, `preRoot`,
  `rootLen`, `bankRoles`, `qVal`, `bankVal`, `bankGraph` and `ValidDef`;
  `ScanSetup.Valid S P := S.ValidDef P`. This is the owner's formulation of S1–S6. U5's SCR-2
  (body `SetupClauses`) is superseded: the equivalence `valid_iff` is the U5 node L8.5h.

All bridges (`profile_eq_body`, …, `qMap_eq_def`, `fMap_eq_def`, `firstDiff_eq_def`,
`valid_iff_def`) hold by `rfl` or `Iff.rfl` (same scratch file).

### i.4 `factorization` carries `a ∈ F.entryAddrs` (U3 SCR1)

The FIRM statement of L7.3 was false: `IsLim u` comes only from `lim U_a ∈ graph F`. The spine
statement now has the hypothesis `(ha : pk.rk.a ∈ pk.rk.F.entryAddrs)`. Its consumers (U5 L8.4,
L8.8) assume `pk.rk.Admitted`, which contains `ha`. U3's workaround `factorization_mem` is removed.

### i.5 Stubs (U2 SCR-U2-1; rule §h.2)

After integration no unit Lean file contains stubs: every former stub is a declaration of the node
that provides it (table "Requires resolution" of `INTEGRATION.md`). A stub added in later work must
be declared before its first use (Lean is declare-before-use), may therefore sit at the top of a
unit file, and must be listed under Requires.

### i.6 `Role.under` and `Packet.blockMap` (U5 SCR-1)

- `Role.under` (§c.2, owner U1): the body proposed by U5, identical to U3's former `underRole`.
- `Packet.blockMap e : BlkVar → Role` (§c.9, owner U3): `host ↦ A_{e.col}`, `ord q`/`cur q ↦` the
  components of `e.col.rep 0 q` (default `A_{e.col}`), `owner ↦ U_e`,
  `inner r ↦ Role.under e.heightPath r`. This is U3's former `blkRole`; it equals U5's proposed
  body (`reps0[q]?` instead of `rep 0 q`) by U3 D7.1b `reps0_getElem?`.
- Contracts: U1 D1.2e `Tree.roles_entry`; U3 D7.1a `posBlock_heads_graph` and D7.1b
  `blockMap_frame` (together U5's `graph_block`).

### i.7 Name hygiene

- Removed duplicates (the owner's declaration is kept): U3 `Packet.cutStart` (= U1
  `Scan.cutStart`); U3 `Hier.Diagram.holds_congr` (= U4 N4.1a); U3 `factorization_mem` (= §i.4);
  U5 `le_cfgMax`, `cfgMax_lt` (= U3 D6.1a), `baseHolds_map` (= U3 N3.1), `baseHolds_congr` (= U4
  N4.1b); U2's stubs `Scan.ordZ`, `Scan.gwordAt` (= U1).
- Moved: U3 `roles_map` to U1 D1.4b (`Tree.roles_map`); U5 N5.7's seven helper definitions to U3
  D6.1c; U5's `ChildData`, `CapData` to U3 L4.3d, L7.5d.
- U3's N3.1 lemmas are declared as `BTBMS.Hier.*` (the draft had put them under `BTBMS.Packet.Hier.*`).

### i.8 Not applied

- U4 SCR-U4-1 (the reflection instance P-U4-1 as the body of `Hier.jInterface`): a fidelity
  decision, deferred to root with a recommendation in `INTEGRATION.md`. No statement depends on it.
- U1 SCR-3: a note only (`#eval!` is needed while the order instances have `sorry` proof fields).
