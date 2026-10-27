# Bounded tests of the untested integration statements (INTEGRATION.md §2.3, I-2, I-3, I-4)

**Inputs.** The blueprint at 133f5d8 (unchanged on disk; `git diff 133f5d8 -- blueprint/lean
blueprint/*.md` is empty), `blueprint/INTEGRATION.md` §2.3, the unit documents and Lean files,
the verification notes, and the verifiers' scripts `scratch/blueprint/U1-verify/tests-raw.lean`
(raw generators, reused verbatim), `scratch/blueprint/U5-verify/test_u5.py` (I-2) and
`scratch/blueprint/U3-verify/t3_records.py`, `t4_synthetic.py` (record pools, I-3).

**Result.** Every statement in scope was tested on the real Lean bodies by `#eval!`. **No
statement failed.** No statement is false, so there is no correction (§5).
- **I-4:** all 20 Lean theorems of the list passed (§2.1, §2.2). The list is D1.2e items 2–3,
  D1.2f (2), D1.3b, D1.4b (3), D1.5b, D1.6d items 4–8, D1.9b, N1.4 (2), D3.1d items 3–4 and D7.2d.
- **I-2:** the stage check of `test_u5.py` passes against the spine bodies of `qMap`/`fMap`
  (U3's `qMapDef`/`fMapDef`) on the same standard pool as U5's run, and on raw inputs in L (§2.3).
- **I-3:** the construction in L4.3's proof of `reduce_childEnds` satisfies
  `F₁.roles <+: F.roles` and `graph F₁ ⊆ graph F` on every instance (§2.4). This covers 2,805
  admitted records with a `childEnds` first difference and 107,599 further instances.

**Method.** Every check evaluates the integrated declarations themselves: the spine bodies
(`truncAfter`, `setHeight`, `roles`, `graph`, `stopData`, `rootData`, `stepKind`, `routeCols`,
`wordAt`, `safePrefix`, `litCap`, `applyMoves`, `AdmCap.origin`, `anchorOrigin`, `roleSets`,
`qMap = qMapDef`, `fMap = fMapDef`, `firstDiff = firstDiffDef`, `ScanSetup.scanRecord`), the U1/U3
definitions (`WordAtom.relabel`, `queryAtoms`, `retAtoms`, `Packet.prefixRoles`, …) and the
locked `expand`, `replaceAt`, `relKey`, `Tree.map`, `Tree.cmp`. No Python port was used, so no
port needed validation. Every statement is checked in its Lean form (the Lean name is given in
each row), with every hypothesis evaluated by a Bool mirror: the U1 N1.1 mirrors `condVb`,
`condIb`, `inLb`, plus literal transcriptions in `lib.lean` (`onStackb`, `isUpwardb`, `moveOKb`,
`movesValidb`). The scripts print the first failing case of every check. Every check also prints
branch counters, which give the coverage figures in §3.

**Integrated check.** Each run builds one check file, as the task prescribes:
```
cd /home/dev/ggg/btbms-formalization
T="scratch/blueprint/repairs/tests/raw.lean scratch/blueprint/repairs/tests/lib.lean scratch/blueprint/repairs/tests/<t>.lean"
{ grep -h '^import ' blueprint/lean/U*.lean $T; cat blueprint/lean/Spine.lean; for f in blueprint/lean/U{1,2,3,4,5}.lean $T; do grep -v '^import ' $f; done; } > scratch/blueprint/repairs/tests/check_<t>.lean
(cd lean && PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake env lean ../scratch/blueprint/repairs/tests/check_<t>.lean)
```
`scratch/blueprint/repairs/tests/run.sh <t>` runs exactly this. The test files have no imports.
- Every run has **0 errors**.
- Every run has 662 diagnostics, all ``declaration uses `sorry` ``:
  - 661 come from the blueprint (as in `INTEGRATION.md`; also `base.log`, the check without
    test files);
  - 1 comes from `CapData.toAdm` in `lib.lean`, whose three `AdmCap` proof fields are `sorry`
    (each field is checked by a Bool mirror before the cap is used, see §1).
- All other output is the `#eval!` / `IO.println` test output, saved in `<t>.out` (full log
  `<t>.log`).

| Test file | Statements | Wall time |
|---|---|---|
| `t_u1.lean` | D1.2e 2–3, D1.2f, D1.3b, D1.4b, D1.5b, D1.6d 4–8, D1.9b, N1.4 | 12 min |
| `t_caps.lean` | D3.1d 3–4, D7.2d (standard and raw pools) | 6 min |
| `t_nest.lean` | D3.1d 3–4, D7.2d on caps with 2–3 repair moves | 31 min |
| `t_nest2.lean` | the same on a tenth of the depth-3 part (quick variant) | 4 min |
| `t_stage.lean` | I-2: L6.2e (`stage_zero`, `stage_succ`, `queryAtoms_struct_vars`) | 4 min |
| `t_child.lean` | I-3: the construction of L4.3 `reduce_childEnds` | 8 min |

---

## 1. Pools

| Name | Definition | Size |
|---|---|---|
| RAW | `pool` of `raw.lean` (U1-verify's `raws 4000 17 ++ nears 6000 29`). Raw forests up to depth 3. `genRaw` breaks I and H and makes 1/16 of the parents invisible; `genNear` biases parents towards A. | 10,000 forests: 9,288 V, 6,818 V∧I, 6,280 in L (`inLb`) |
| RAW-L | `pool.filter inLb` (or its first 3,000) | 6,280 (3,000) |
| STD(m,p,r,N) | `stdBFS m p r N`: breadth-first closure of the seeds `0…m` under the locked `expand` with parameters `0…p`, keeping expressions with `≤ r` roles, deduplicated, stopped at `N` expressions. Every member is standard (`IsStd.seed`, `IsStd.expand`). Every member of STD-U1 (which contains STD-U5, the same BFS cut earlier) passes `inLb`. | see rows |
| STD-U1 | STD(5,3,40,6000) | 6,002, ≤ 40 roles |
| STD-U5 | STD(5,3,40,4000), the pool of U5's `test_u5.py 40 4000` (seeds 0–5, parameters 0–3, ≤ 40 roles, 4,000 expressions) | 4,001; 3,073 ordinary, as in U5's run |
| STD-caps | STD(5,3,30,2500) ∪ STD(5,3,40,1500) (two BFS cut-offs reach different shapes) | 2,976 |
| STD-T3 | STD(4,2,20,∞), the pool of U3's T3 (seeds ≤ 4, parameters ≤ 2, size ≤ 20, no depth limit; the BFS is exhaustive) | 58,309, as in T3 |
| CAPS(E) | `admCaps E d`, enumerated exhaustively: every column `c`, cut `k ≤ |col|`, visible parent `p < c.num 0` with `isUpwardb`, every move list of length `≤ d` that is `MovesValid` (each move passes `moveOKb` on the expression produced by the moves before it), whose result passes `inLb`. A `MoveOK` move must sit at a container column of the stopping column, with `j` its containing entry, so the enumeration of moves is complete. These are all `AdmCap E` with `≤ d` moves. | 55,648 caps over STD-caps ∪ RAW-L, 2,163 moved, none with ≥ 2 moves |
| NEST | `nestE 2 1 ++ nestE 3 40`, filtered by `inLb` (`lib.lean`): `[[], [(0,X),(0,Y)]]` with `Y ≤ X`, where every height is `∅`, `[[(a,X)]]` or a same-parent pair `[[(a,X),(a,Y)]]`, nested to depth 2 (all 406) or 3 (every 40th of 94,830). It is built because a cap with two moves needs two container levels of the stopping column whose containing entry has an earlier entry with the same parent, and no standard expression of the BFS pools has such a column: 0 of 40,004 searched, STD(5,3,60,20000) and STD(6,4,50,20000). | 2,777 forests in L; 160,087 caps (`d = 4`): 66,334 moved, 19,399 with 2 moves, 2,064 with 3 moves, none with 4 |
| REC | Admitted records over STD-T3, built from the spine bodies as U3's T3 builds them (`t_child.lean`). **Scan records:** for every anchor (`E` itself, or an admissible cap at an inner column with `≤ 3` moves) and every state `(i,j)` of `trace` with `x_i > y_j` and source entry `i` closed (`AnchorAt`, `anchorSrc`), `F = H.truncAfter a`. **Descendant records:** every safe prefix of `A'`, and every confined-operation output (`n ≤ 2`) of the context with a safe-prefix height. Admission (`InL F`, truncation, strictness) is checked with `inLb` and `decide`. | 92,187 admitted (27,007 scan, as in T3; 65,180 desc); first differences 87,508 whole, 2,805 child, 1,874 cap |

---

## 2. Results

Columns: statement (node, Lean name in the integrated files), pool, cases, failures,
counterexample. "Cases" counts the instances on which the full conclusion was evaluated with
every hypothesis true.

### 2.1 I-4, U1 (`t_u1.lean`)

| Statement | Pool | Cases | Failures | Counterexample |
|---|---|---|---|---|
| D1.2e item 2 `Tree.truncAfter_roles_under`: `(E.truncAfter e).roles = P(E,e) ++ U_e :: h.roles.map (Role.under e.heightPath)` | every entry `e` of RAW ∪ STD-U1 | 137,067 (40,720 raw) | 0 | — |
| D1.2e item 3 `Tree.stack_mem_prefix`: `A_{e.col}`, every `A_o` with `e.col.OnStack o`, and every `U_{e'}` with `e'.Contains e.col` lie in `P(E,e)` (`o` and `e'` enumerated from the bodies of `OnStack` and `Contains`; the enumeration matches `onStackb` on every syntactic `⟨path.take k, j⟩`, `j < 6`) | as above | 137,067 | 0 | — |
| D1.2f `Tree.truncAfter_spec` (idempotence, membership, `heightAt`, `entryAt`, prefix inclusion and equality) | as above | 137,067 | 0 | — |
| D1.2f `Tree.setHeight_basic` (membership, `heightAt`, `∀ h'` idempotence with 7 values `h'`, identity when `heightAt e = some h`, truncation preserved, label kept) | forests `t` and `t.truncAfter e`; heights: `t`'s own height at `e` and 7 fixed forests | 2,193,072 | 0 | — |
| D1.3b `Scan.firstParent_host` (V, I) | entries with nonempty height of `condVb ∧ condIb` forests of RAW ∪ STD-U1 | 29,039 (533 raw) | 0 | — |
| D1.4b `Tree.roles_map` (`f` = `+1`, `2·`, `const 0`, `relLabel 2`, `toString`) | RAW ∪ STD-U1 and every height of their entries | 153,069 forests × 5 maps | 0 | — |
| D1.4b `relKey_roles`, `relKey_eq_empty` (`a = 0…5`) | as above | 153,069 × 6 | 0 | — |
| D1.5b `Scan.shift_replaceAt` | 4,000 RAW and 3,000 STD-U1 forests `G`; `δ ≤ |routeCols G| + 1`; `(r,a) ∈ {(0,0),(0,3),(1,2),(2,1),(3,4),(5,2)}`; 6 fillers `Z` including `∅` | 1,334,304 | 0 | — |
| D1.6d item 4 `Scan.lastCol_of_ordinary` | ordinary forests of RAW ∪ STD-U1 | 8,883 | 0 | — |
| D1.6d item 5 `Scan.stopData_roles` (all six clauses; `qs` is the unique candidate `(roles after rolesBefore).tail.dropLast`) | forests of RAW ∪ STD-U1 with `stopData = some` | 10,387 | 0 | — |
| D1.6d item 6 `Scan.rootData_path` (all seven clauses) | forests with `stopData` and `rootData` `some` | 8,883 | 0 | — |
| D1.6d item 7 `Scan.stepKind_ordinary_iff_unfold` (both directions; `E ≠ ∅`, V, I) | `condVb ∧ condIb`, nonempty forests of RAW ∪ STD-U1 | 12,819 | 0 | — |
| D1.6d item 8 `Scan.stopData_of_route` (no condition on `E`) | forests whose last route column ends in an entry `(r, ∅)` | 10,387 | 0 | — |
| D1.9b `Scan.routeCols_of_word_snoc` (`hw` re-checked; witnesses `c` = last route column, `k = |E.colAt c| − 1`, which the conclusion forces) | every pair `(E, G)` satisfying `hw`: `G = safePrefix E (µ − 1)` when the last atom of `w(E)` is an entry atom. By `word_injective` and `word_safePrefix`, no other `G` satisfies `hw`. | 10,387 | 0 | — |
| N1.4 `Scan.wordAt_add` (`e, δ ≤ 3`) | RAW ∪ STD-U1 and all their entry heights | 153,069 × 16 | 0 | — |
| N1.4 `Scan.wordAt_map` with `WordAtom.relabel` (`e ≤ 3`; `f` = `+1`, `2·`, `const 0`, `mod 2`, `+7`, `9 −`) | as above | 153,069 × 24 | 0 | — |

### 2.2 I-4, U2 D3.1d items 3–4 and U3 D7.2d (`t_caps.lean`, `t_nest.lean`)

| Statement | Pool | Cases | Failures | Counterexample |
|---|---|---|---|---|
| D3.1d item 3 `Closure.anchorOrigin_prefix` (`InL E`; `stopData (anchor E cap) = some sd`). Checked: `T'` exists; injectivity over the roles of the anchor, the roles of `E`, and 2–3 off-tree neighbours of each; every `x ∈ rolesBefore (anchor E cap) A_{sd.col}` has an origin in `rolesBefore E T'` and in `E.roles` | `cap = none` and every cap of CAPS(E), `E` ∈ STD-caps ∪ RAW-L | 59,343 (3,695 `none`, 53,485 caps without moves, 2,163 with one move) | 0 | — |
| the same | `none` and CAPS(E), `E` ∈ NEST | 162,864 (21,463 with 2–3 moves) | 0 | — |
| D3.1d item 4 `Closure.lt_admCap` (no hypothesis on `E`; checked as `decide (E < w.H)` and as `Tree.cmp compare E w.H = .lt`) | CAPS(E), `E` ∈ STD-caps ∪ first 3,000 of RAW (1,681 caps over `E ∉ L`) | 56,465 (2,626 moved) | 0 | — |
| the same | CAPS(E), `E` ∈ NEST | 160,087 (21,463 with 2–3 moves) | 0 | — |
| D7.2d `Packet.scanRecord_tgtHeight` (`S.Valid P`, `j < |S.sd.Q|`). Setup `S` built from `E`, `cap`, `sd = stopData H`, `rd = rootData H` and dummy name/value fields; `i ∈ {0, cursor, rootLen − 1}`. Hypothesis: S1 of `ValidDef` (`IsStd E`, `InL H`, ordinary, stop and root data, `cursor < rootLen`, root entry closed). The proof uses only S1, and S2–S6 constrain only the name and value fields, which `scanRecord` and `tgtHeight` do not read. | anchors over STD-caps | 11,390 (1,538 `none`, 9,852 caps, 82 moved) | 0 | — |
| the same, with only `stopData`, `rootData` `some` (S1 otherwise not imposed) | as above | 110,866 | 0 | — |
| the same, `InL E` in place of `IsStd E` (NEST is not standard; the proof uses `IsStd E` only through T3.2 `std_inL`) | anchors over NEST | 78,220 (172 with 2–3 moves; 41,794 with nonempty query height) | 0 | — |
| the same, S1 not imposed | anchors over NEST | 267,966 | 0 | — |

`t_nest2.lean` runs the same test on `nestE 3 400`, a tenth of the depth-3 part: 644 forests,
24,489 caps (2,450 with 2 moves, 209 with 3), 0 failures in every row.

### 2.3 I-2: the stage check of `test_u5.py` on the spine `qMap`/`fMap` (`t_stage.lean`)

U5's verifier tested L6.2e against its own Python model of `q_m`, `f_m`. Here the same checks
run on the integrated declarations by `#eval!`:
- the maps are `Packet.qMap H n m = qMapDef H n m` and `fMap = fMapDef` (spine §c.8, U3's
  bodies);
- the roles and graphs come from the spine's `roleSets` and `graph`;
- the steps come from the locked `expand`;
- the atom sets are U3's `queryAtoms` and `retAtoms`.

The test covers both the forward classification and U5's converse check (`R22_images_in_graph`).

| Statement | Pool | Cases | Failures | Counterexample |
|---|---|---|---|---|
| L6.2e `Packet.stage_zero`: `H[0].roles = rs.P`, `graph H[0] ⊆ graph H`, `fMap H 0 0 = id` on `rs.D` | `H` ∈ STD-U5 ∪ RAW-L (`InL H`) with `roleSets H = some rs` | 4,802 (3,073 std) | 0 | — |
| L6.2e `Packet.stage_succ`, roles: `H[m+1].roles = H[m].roles ++ (f(R) :: q(Q) ++ f(K))`, `q = qMap H (m+1) (m+1)`, `f = fMap H (m+1) (m+1)` | as above, `m = 0…3` | 19,208 (12,292 std) | 0 | — |
| L6.2e `stage_succ`, maps: `q(T) = f(R)`, `q = fMap H m m` on `rs.D`, `f = id` on `rolesBefore H R` | as above | 19,208 | 0 | — |
| L6.2e `stage_succ`, atoms: every structural atom of `Γ(H[m+1])` is in `Γ(H[m])`, or the `q`-image of a structural atom of `queryAtoms H rs`, or the `f`-image of an atom of `retAtoms H rs` | every structural atom of the 19,208 cases | 930,668 | 0 | — |
| (converse, U5's `R22_images_in_graph`; not part of L6.2e, used by U5 L8.6) every such image is an atom of `Γ(H[m+1])` | as above | 211,968 | 0 | — |
| L6.2e `Packet.queryAtoms_struct_vars` | every structural atom of `queryAtoms H rs` | 14,792 | 0 | — |

U5's run (`test_u5.py 40 4000`) had 9,219 role cases: 3,073 inputs × 3 stages, `m = 0…2`. This
run covers the same 3,073 standard inputs with `m = 0…3`, and adds 1,729 raw inputs in L. U5's
stage form holds with the spine bodies on these inputs, so the open item of L6.2e's Testable line
("re-running the same test with the spine bodies … is open") is done.

### 2.4 I-3: the construction inside the proof of L4.3 `reduce_childEnds` (`t_child.lean`)

**The construction** (L4.3 proof step 5.3):
- `ρ := π.drop |b.heightPath|`;
- `X, Y` are the target and source forests at `ρ`, and `m := |X.cols|`;
- `e₁ := ⟨⟨ρ, m⟩, 0⟩` (relative to `A'`), `A₁ := (A'.truncAfter e₁).setHeight e₁ ∅`, and
  `F₁ := F.setHeight a A₁`;
- `e₁' := ⟨⟨a.heightPath ++ ρ, m⟩, 0⟩` is the address of `e₁` in `F`.

**Clauses checked** for every case:
1. the shape `π = b.heightPath ++ ρ`, `ρ ≠ []`, and that `e₁` exists;
2. the identity of L4.3d step 2: `F₁ = (F.truncAfter e₁').setHeight e₁' ∅`;
3. the strengthening asked by I-3: `F₁.roles <+: F.roles` and `graph F₁ ⊆ graph F`;
4. `F₁.roles = P(F, e₁') ++ [U_{e₁'}]`;
5. the first conjuncts of `reduce_childEnds`: `InL F₁`, `A₁ ≤ A'`, and
   `tgtKey < relKey r A₁`.

| Statement | Pool | Cases | Failures | Counterexample |
|---|---|---|---|---|
| Construction, clauses 1–5 | REC: admitted scan and descendant records with `firstDiff = childEnds π` | 2,805 (551 scan, 2,254 desc; 2,457 over caps) | 0 | — |
| the same | synthetic pairs as U3's T4(c): `E` ∈ STD(5,3,30,3000), entries `a`, `b`, `F = E.truncAfter a`, common admission clauses, `childEnds` | 10,790 | 0 | — |
| General form: for `F` with `F.truncAfter a = F` and every entry `e₁'` of `F` with `a.heightPath <+: e₁'.col.path` (any index, including `ρ = []`), `F.setHeight a ((A'.truncAfter e₁).setHeight e₁ ∅) = (F.truncAfter e₁').setHeight e₁' ∅`, with prefix roles and graph inclusion | `F = F₀.truncAfter a`, `F₀` ∈ first 5,000 of RAW ∪ STD(5,3,30,3000), every `a` | 96,809 (22,971 raw) | 0 | — |
| Control: the general form with `F₀.truncAfter a ≠ F₀` (expected to fail; shows that the hypothesis `F.truncAfter a = F` of admission is used) | first 2,000 of RAW | 5,251 | 5,251 (expected) | `[[],[],[(1,[[(0,[]),(0,[[],[(4,[])]]),(1,[])]])]]`, `a = ⟨[(2,0)],0,1⟩`, `e₁' = ⟨[(2,0),(0,1)],1,0⟩` |

**Answer to I-3.** The construction satisfies both properties on every bounded instance. If L4.3's
formalizer exposes `A₁` only through the statement, the strengthening INTEGRATION.md proposes
passes. The proposed `reduce_childEnds` adds two conjuncts after `Scan.InL (rk.F.setHeight rk.a A₁)`:
```lean
(rk.F.setHeight rk.a A₁).roles <+: rk.F.roles ∧
(∀ x ∈ graph (rk.F.setHeight rk.a A₁), x ∈ graph rk.F)
```
These are exactly the `ChildData` fields `roles_pre` and `graph_sub` (U3 L4.3d). The proof of the
two conjuncts is L4.3d step 2. It needs one address identity that is not yet a named node: row 3
above, `F.setHeight a ((A'.truncAfter e₁).setHeight e₁ ∅) = (F.truncAfter e₁').setHeight e₁' ∅`
when `F.truncAfter a = F` and `A' = F.heightAt a`. This row was tested on 96,809 cases, 0
failures. Its proof is an induction on `a.heightPath` through the bodies `truncAux` and `setAux`
(U1 D1.2c), using D1.2f `setHeight_basic` at the last level. From the identity, D6.1a item 8
`graph_truncClear` gives the graph clause. D1.2e item 2 `truncAfter_roles_under` with D1.2f gives
the roles `P(F,e₁') ++ [U_{e₁'}]`, a prefix of `F.roles` by D1.2e item 1. This is a test result,
not a closed proof: the identity's induction is written here only as a plan.

---

## 3. Branch coverage, and the branches never reached

The scripts count each branch; the counts below are their output.

- **D1.2e 2–3, D1.2f.**
  - Reached: entries with nonempty heights (39,851); truncations that remove roles (97,468);
    entries with and without containers (96,326 with).
  - Reached: both hypotheses of `setHeight_basic` true and false (`heightAt e = some h`: 468,566;
    `truncAfter e = t`: 1,413,328).
- **D1.3b.** Only 533 raw cases: raw forests with V, I and a nonempty height are rare. Control:
  without V ∧ I the claim fails on 6,760 of 10,812 cases, so the hypotheses are needed.
- **D1.4b.** `B = ∅` reached (97,217). Non-injective `f` and label-type-changing `f` reached.
- **D1.5b.**
  - `δ` beyond the route: 504,000 cases, where `Z` is never placed.
  - `G = ∅`: only 72 cases.
- **D1.6d.**
  - Item 5: empty and nonempty query (6,224 nonempty); depth 0 and > 0 (5,907 at depth > 0).
  - Item 6: owner root (1,839), body root in the stopping forest (5,398), body root in a
    shallower forest (1,646).
  - Item 7: ordinary (6,702), special (1,274) and deletion (4,843) reached.
    - **Never reached: `stepKind E = none`, and stop data with an invisible root.** Both are
      unreachable under the hypotheses. V makes `r` visible from `sd.col`, because `(r, ∅)` is an
      entry of `sd.col`. I with `E ≠ ∅` makes the route reach a stop (D1.6b `stopData_isSome`).
    - Without V ∧ I the equivalence still held on all 3,182 cases. It is unconditional. The
      body of `stepKind` adds only "the last outer column is nonempty" to the right side, and
      when that column is empty, or `E = ∅`, `stopData E = none` (bodies of `stopCols` and
      `stopCol`). The hypotheses are harmless but not needed.
  - Item 8: the hypothesis fails on 5,614 forests (the route ends in an empty column or at a
    nonempty height).
- **D1.9b.** First entry (`k = 0`: 4,163) and later entry (`k ≠ 0`: 6,224) reached; depth `e > 0`:
  5,907.
- **N1.4.** Empty-column atoms (the fixed branch of `relabel`) occur in 21,632 forests.
- **D3.1d 3–4, D7.2d.**
  - In the standard and raw pools no cap has two or more moves. No expression of 40,004 standard
    BFS expressions (up to 60 roles) satisfies the necessary condition for one (see NEST).
  - **Caps with 2–3 moves are reached only on NEST.** NEST is in L but not standard, so for
    D7.2d they are tested with `InL E` in place of `IsStd E`. On standard expressions this branch
    of D7.2d was never reached.
  - **Never reached: 4 moves** (`d = 4` was allowed; none exists in NEST).
  - Every NEST cap with ≥ 2 moves moves at two different columns (21,463 of 21,463). A second
    move at the same column would need an inner move in between, and none occurs within 4 moves.
  - D7.2d with S1: only 82 moved-cap cases and 84 nonempty query heights over STD-caps; NEST adds
    41,794 nonempty query heights and 172 cases with 2–3 moves.
- **L6.2e.**
  - Reached: owner root (3,808 stage cases), body root in the same forest (13,576), body root in a
    shallower forest (1,824); `K ≠ []` (13,036), `Q ≠ []` (11,688).
  - Atoms already in `Γ(H[m])`: 718,700. New `q`-images: 59,168. Atoms that are only `f`-images:
    152,800.
  - **Never reached: `expand H (m+1) = none`** (owner-root exhaustion). It is unreachable for
    `H ∈ L`: U1 L2.4c, every operation is defined on V, I, A, S.
- **I-3.**
  - All 2,805 `childEnds` records have a special `F₁`, consistent with U3's T3 ("all special").
  - **Never reached by an admitted record: the ordinary branch of `F₁`.** It is reached by 145
    synthetic pairs.
  - The clearing step removes roles in 2,344 synthetic cases (`e₁` had a nonempty height). The
    truncation step removes roles in 8,374.

---

## 4. Statements tested elsewhere (not re-run here)

INTEGRATION.md §2.3 I-4 excludes these, because the verifiers tested them under their stub
names:
- D1.2e item 1, tested by U5 on 34,794 entries;
- D1.6d items 1–3, tested by U5;
- D3.1d items 1–2, tested by U3's T7 and on the caps of T3/T4.

## 5. Statements found false

None. Every statement in §2 passed every bounded case, so no corrected statement is needed.

Two remarks, neither a defect:
- D1.6d item 7 holds without V, I (§3).
- D7.2d holds with S1 dropped as long as stop and root data exist: 110,866 cases.

## 6. Limits

These are finite falsification attempts on the pools of §1, not proofs.
- The checked domain of `∀` clauses over infinite types is finite:
  - injectivity of `anchorOrigin` over roles: anchor roles, `E` roles and off-tree neighbours;
  - `∀ h'` in `setHeight_basic`: 7 forests;
  - the maps `f` in D1.4b and N1.4.
- Move lists are bounded by 3 (standard and raw pools) and 4 (NEST). NEST is a targeted family:
  nested same-parent pairs under one outer column.
- The record pool REC follows U3's T3. Its descendant candidates are one level of confined
  operations over safe prefixes.

---

## 7. Files

All under `scratch/blueprint/repairs/tests/`:
- `run.sh` builds and runs a check file;
- `raw.lean` is a verbatim copy of `scratch/blueprint/U1-verify/tests-raw.lean`;
- `lib.lean` holds the pools, the Bool mirrors and the report helpers;
- the test files `t_u1.lean`, `t_caps.lean`, `t_nest2.lean`, `t_nest.lean`, `t_stage.lean`,
  `t_child.lean`;
- for each test file: its check file `check_<t>.lean`, the full log `<t>.log` and the test
  output `<t>.out`;
- `base.lean` and `base.log`, the integrated check without test files (661 sorry warnings,
  0 errors).
