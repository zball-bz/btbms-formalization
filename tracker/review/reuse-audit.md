# Reuse audit — T-007

**Recommendation:** for (H), use a new Lean 4.33.1 project with one pinned Mathlib/CU source family and narrow imports; for (O), use KP1Y's Lean 4.33.1 / YesMetaZFC foundation and extend its arbitrary-model proofs to the specified object ZFC+Mahlo theory. Neither route can import a completed BTBMS theorem, and neither candidate hierarchy can simply be renamed J. The largest genuinely reusable foundations are CU's host satisfaction/collapse machinery for H, and KP1Y's internal syntax/recursion/satisfaction/compiler and Hilbert-completeness machinery for O.

This is a **read-only source audit**. I read `REUSE-BRIEF.md`, `tracker/GAPS.md`, and the `nodes` in `tracker/ledger.json`, plus the requested KP1Y entry documents and the candidate sources cited below. No candidate was modified; no `lake build`, elaboration check, fetch, or candidate audit script was run. I did run the already installed portable compiler with `--version`: it reports Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Source declarations, local file counts, dependency pins and saved logs were inspected; a new combined project has **not** been built. Fit assessments and effort ranges are engineering inferences, not verified ports.

## One object-theory specification issue to settle

The (O) notation `ZFC + {n-Mahlo} ⊢ WO(Std)` is ambiguous. An external family of axioms `∃κ M_n(κ)` for each **metatheoretic** n is different from the single internal sentence `∀n∈ω ∃κ M_n(κ)`. A finitary Hilbert derivation from the external family uses only finitely many of its members. In arbitrary, possibly nonstandard models, that family cannot simply be used as an assertion about every internal seed depth. KP1Y explicitly handles internal ω, so its completeness route makes this distinction unavoidable.

The estimates and recommendation for O below assume the **uniform internal finite-Mahlo sentence**, matching the uniform seed argument in the paper. If the intended axiom set is literally the external family, a separate finite-strength reduction or different target specification is needed. This audit does not prove that the external family cannot prove the conclusion; it identifies an implication that the proposed proof translation does not supply. A family of bounded-seed derivations would not by itself be the requested single derivation of WO(all Std).

D-2 (strong or weak finite Mahlo) remains open. The reusable infrastructure does not decide it: define the recurrence with the chosen base class and prove initialization from that hypothesis. D-3 is already fixed: total reference-compatible FS, with nonempty decrease and a paper-agreement lemma. Existing 0-Y/1-Y/BM4 expansions do not implement that FS.

## 1. Candidate results, foundations, size and provenance

LOC below means physical Lean source lines including comments/blanks, excluding generated `.olean`, caches and non-Lean documentation. Subtree rows overlap and must not be added twice; the two YesMetaZFC copies are also largely the same source.

| Candidate and inspected HEAD | Foundation / actual endpoint | Toolchain | Measured source size |
|---|---|---|---|
| KP1Y, `455c3d05811e97a35e18c0a3862ff3e798711b5e` | Deep pure-∈ theory and Hilbert derivation; arbitrary KPω models, no Mathlib dependency | 4.33.1 | `KP1Y/`: 566 files / 88,901 LOC; 205 notation-specific `OneY*` files / 58,380 LOC; 361 other files / 30,521 LOC. YesMetaZFC namespace: 825 files / 252,224 LOC. |
| DH/BM4, `e1849485ee1d54f92dc4eb42ee93b702c71e67a9` | Host theorem over Mathlib `ZFSet`, ordinals and a realized label system; first-order syntax is represented, but no final Hilbert derivation | 4.30.0 + Mathlib v4.30.0 | `lean/Bm4/`: 65 files / 25,838 LOC; `SetTheory/` subset: 48 files / 22,415 LOC. Root import closure: 63 files / 25,227 LOC including the aggregator. |
| 1Y, `6533b2975f3cafb3582dc8f8127e9ea7144d7e69` | Host 0-Y/BMS and 1-Y well-ordering; core Lean/Std plus selected YesMetaZFC.BMS; concrete model uses Mathlib/CU/BMS bridge | Main projects 4.33.1; some vendor source pins declare 4.33.0-rc1 | Entire `formalization/`: 444 files / 51,992 LOC; ZeroY 50 / 7,782; OneY 123 / 18,043; OneYTruth 260 / 25,561. Vendored CU: 274 / 92,284; BMS bridge: 148 / 37,511; Mathlib: 8,811 / 2,366,838. `y1/` contains no Lean files. |

### KP1Y: an actual object-theory theorem

Namespace `KP1Y.OneYTheorem`. These declarations are verbatim from [OneYMainTheorem.lean](/home/dev/ggg/kp-simplified-verification/KP1Y/OneYMainTheorem.lean:28):

```lean
theorem main_semantic_actual_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) : MainSemantic M :=
  main_semantic_d hM (rank_transfer_at_of_canonical canonical_copy_bound hM) (order_facts_at_actual_d hM)

/-- 定理 1：KPω ⊢ mainSentence（纯 ∈ 闭句的真实 Hilbert 推导）。 -/
theorem theorem1_derivable : KP1Y.Derives mainSentence :=
  main_derivable_of_steps (fun _ hM => TerminalBase.terminal_exits_d hM) (fun _ hM => LowerLayer.lower_steps_d hM)
```

The endpoint is genuinely `Project.Derives theory mainSentence`, not a host `WellFounded` proposition with a new name. `KP1Y/Axioms.lean:26–42` defines the exact KPω axiom predicate, including the **full set-induction scheme**; `KP1Y/Completeness.lean:40–47` obtains derivability by strong completeness from all models. The closed sentence's exact semantic definitions are:

```lean
def MainSemantic (M : SetTheory.Structure.{u}) : Prop :=
  (∃ D : TheoremData M.Domain, D.Valid M) ∧ ∀ D : TheoremData M.Domain, D.Valid M → ConclusionClause M D

def ConclusionClause (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) : Prop :=
  ∀ ν, UncountableOrdinal M D.expr.omega ν →
    RankClause M D ν ∧ WellFoundedClause M D ∧ TerminationClause M D ∧ DescClause M D ∧ GenClause M D
```

Thus, inside every KPω model, auxiliary algorithm sets exist and every internally uncountable ordinal ν supplies a decreasing set-function rank into an ordinal χ≤ν, internal expansion well-foundedness/trajectory termination, and lexicographic well-ordering of each descendant set and the generated standard part. The uncountable-ordinal assumption is inside `ConclusionClause`, not a missing Lean premise. All lengths and copy counts range over the model's ω. It does not prove that the entire raw legal 1-Y lexicographic order is well-founded, and its flat 1-Y sequences are not BTBMS forests.

**Verified versus recorded:** the main declarations have bodies and no remaining reflection/descent interface premise. A source search found no `sorry`/`admit` or top-level Lean `axiom` in KP1Y. The saved `audit-results.json` has 4,216 entries using only `propext`, `Classical.choice`, `Quot.sound`; the final theorem is included. That is a prior audit record, not a fresh kernel check here. The historical incomplete notices in GOAL/OUTLINE/INTERFACES are superseded by the final source and final verification record; they are still useful design history, not current blockers.

**License/provenance:** original KP1Y code/scripts/docs are MIT; `NOTICE` retains Apache-2.0 attribution and conditions for portions ported from the 1Y snapshot above, and excludes the paper. The separately fetched YesMetaZFC snapshot is not covered by MIT. The fetch script pins `EgoFakeFantasy/BMS-Well-Ordering-Lean@bae7e3d741f24a56d80da9b99c1345562cd10c2d`, crediting `lanxinge/YesMetaZFC`; that pinned tree has no general license grant. `third_party-provenance.json` records the sole extra KP patch, `SetTheory/Notation/Surface.lean`, changing the `sentence!` certificate from `native_decide` to `decide_cbv`. Its `repo_commit:6533...` identifies the source 1Y checkout, not the upstream BMS commit.

### DH/BM4: reachable expansion well-foundedness

Namespace `BM4.ST`. Verbatim from [Reflect.lean](/home/dev/ggg/dh-bms-wf-formal/lean/Bm4/SetTheory/Reflect.lean:461):

```lean
theorem terminates_unconditional {r : ℕ} (A : BM4.Arr r) (hA : BM4.Reachable r A) (n : ℕ → ℕ) :
    ∃ T, (BM4.seq A n T).len = 0 :=
  BM4.terminates bm4LabelSystem.{0} A hA n

/-- **Proposition 22.1**: the one-step expansion relation of BM4 is well-founded. -/
theorem R_wf_unconditional (r : ℕ) : WellFounded (BM4.R r) :=
  BM4.R_wf bm4LabelSystem.{0} r

/-- **Theorem 1.2** on BM4 itself (Definition 1.1), i.e. on the union over all row counts. -/
theorem terminates_all_unconditional (A : BM4.Elts) (n : ℕ → ℕ) :
    ∃ T, (BM4.seq A.2.1 n T).len = 0 :=
  BM4.terminates_all bm4LabelSystem.{0} A n

/-- **Proposition 22.1** on BM4 itself. -/
theorem R'_wf_unconditional : WellFounded BM4.R' :=
  BM4.R'_wf bm4LabelSystem.{0}
```

Here `BM4.R` is the **one-step expansion relation on reachable arrays**, not the paper's semantic control edge R. `Defs.lean:94–119` defines `Reachable` from the seed E and expansion, the subtype `Elt r`, and `R r A B := 0 < B.1.len ∧ ∃ n, A.1 = expand B.1 n`; `R'` ranges over all row counts. “Unconditional” means the label interface has been realized, not that the explicit reachability restriction disappeared. These results do not assert lexicographic well-ordering or identify any BTBMS encoding.

`Reflect.lean:450` actually constructs `bm4LabelSystem` using admissible ordinals, `RelAdm`, initialization and `reflect_pattern`. Its first-order `Fm` syntax and set-coded satisfaction are substantive, but their semantics is host `Prop` over Mathlib `ZFSet`; representing formulas is not the same as deriving the final theorem in object KP/ZFC. The root has broad Mathlib imports. The package pins Mathlib v4.30.0 / commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

**Verified versus recorded:** no `sorry`, `admit`, or actual Lean `axiom` declarations were found in the inspected Bm4 sources. README reports only the three standard Lean axioms, but no axiom audit was rerun. This local checkout lacks its Mathlib package/build cache. Three residual files (`SetTheory/AdmP.lean`, `AdmPOK.lean`, `TV.lean`) are outside the root's import closure; they should not be mistaken for required main-theorem assumptions.

**License/provenance:** remote `koteitan/dh-bms-wf-formal`, local version v0.2.1. README attributes the mathematical paper to DH / DeltaEta22223. No LICENSE/COPYING/NOTICE or general license grant was found in the candidate snapshot. Mathlib's license does not establish a license for Bm4's original source. Treat permission/provenance for copying or redistributing it as unresolved; this audit performs no copy.

### 1Y: completed host theorem, substantial vendored constructibility

Namespace `OneYTruth.WellOrdering`. Verbatim from [ActualWellOrdering.lean](/home/dev/ggg/1Y-Well-Ordering-Lean/formalization/Concrete/OneYTruth/ActualWellOrdering.lean:15):

```lean
theorem expansion_wellFounded : WellFounded (ZeroY.ExpansionStep expand) :=
  RootSemantics.actual_expansion_wellFounded RootSemantics.actual_finiteReflection.{0}

/-- The standard generated 1-Y sequence order is a strict well-order. -/
theorem generated_strictWellOrder : StrictWellOrder GeneratedExpr GeneratedLt :=
  RootSemantics.actual_generated_strictWellOrder RootSemantics.actual_finiteReflection.{0}

/-- Every fixed starting sequence's generated descendant order is a strict well-order. -/
theorem descendants_strictWellOrder (s : ZeroY.Expr) :
    StrictWellOrder (Descendant s) DescendantLt :=
  RootSemantics.actual_descendants_strictWellOrder RootSemantics.actual_finiteReflection.{0} s

/-- Arbitrary choices of finite copy counts still reach the empty sequence. -/
theorem expansion_chain_reaches_empty (chain : Nat → ZeroY.Expr)
    (hNext : ∀ n, ∃ N, chain (n+1) = expand (chain n) N) :
    ∃ n, (chain n).values = [] :=
  RootSemantics.actual_expansion_chain_reaches_empty RootSemantics.actual_finiteReflection.{0} chain hNext
```

`actual_finiteReflection` is supplied by a proved theorem (`ActualFiniteReflection.lean:14`), not an unfilled semantic axiom. `ZeroY.Expr` is a legal flat natural sequence; generated/descendant lexicographic orders are distinguished from expansion well-foundedness and from the non-well-founded raw lexicographic order (`ZeroY/Syntax.lean:81`). The candidate also has concrete 0-Y/BMS endpoints; representative declarations from [ZeroYConcrete.lean](/home/dev/ggg/1Y-Well-Ordering-Lean/formalization/Concrete/ZeroYConcrete.lean:20) are:

```lean
theorem bms_step_wellFounded : WellFounded Step :=
  ZeroY.BMS.step_wellFounded_any
    reflectionData_l.wellOrderingModel.representationDescentSystem

theorem bms_descendants_strictWellOrder (root : ValidArray) :
    StrictWellOrder (ZeroY.BMS.Descendant root) ZeroY.BMS.DescendantLt :=
  ZeroY.BMS.descendants_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem root

theorem bms_generated_strictWellOrder :
    StrictWellOrder GeneratedArray ZeroY.BMS.GeneratedMatrixLt :=
  ZeroY.BMS.generatedMatrix_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem

theorem y_step_wellFounded : WellFounded YStep :=
  ZeroY.yStep_wellFounded reflectionData_l.wellOrderingModel.representationDescentSystem

theorem y_generated_strictWellOrder : StrictWellOrder YGeneratedExpr YGeneratedLt :=
  ZeroY.yGenerated_strictWellOrder reflectionData_l.wellOrderingModel.representationDescentSystem
```

The concrete development uses Mathlib `ZFSet`/`Ordinal`, CU's constructible universe and a BMS bridge. Its formula languages and truth sets are represented and proved correct in Lean, but the final 1Y theorem is **not** an object-ZFC Hilbert derivation. The project documentation explicitly leaves that migration separate. `y1/engine.js` and four `.cjs` programs are runtime/UI/testing material, not an extra Lean library and not the BTBM reference algorithm.

**Verified versus recorded:** all quoted endpoint declarations have bodies. A static import scan from the 1Y/0Y concrete endpoints resolved 1,895 modules; its 837 own/CU/BMS modules had no `sorry`, `sorryAx`, `admit`, or Lean `axiom` token after comments/strings were stripped. This is not a kernel audit. The supplied `OneYTruth-audit-output.txt` records 153 declarations, including the four endpoints, with only standard Lean axioms; the dated build/audit records are historical evidence, not a new run on this machine.

**License/provenance:** own 1Y and CU source are Apache-2.0; CU headers credit Zike Liu. Mathlib and most tooling are Apache-2.0, Cli MIT. CU is pinned at `7f5a7d03d63d9769172f17350bbe8303996e5b53`; Mathlib at `eba3d887fc52c98627f4b81507c0efc3096e91b9`. The BMS/YesMetaZFC pin is `bae7e3d...`; `vendor/THIRD-PARTY-NOTICES.md` explicitly says the parent Apache license does **not** cover that unlicensed snapshot. A recorded plan to request upstream licensing is not a supplied grant. Widget/transitive asset notices are separate from Lean-proof reuse.

The KP and 1Y BMS dependency trees contain the same **974 relative Lean file paths**. Byte comparison found exactly one differing Lean file: KP's `Surface.lean` patch above. Their BMS bridge proof-performance patches are otherwise identical. Do not count these as independent libraries or load both copies under the same `YesMetaZFC` module name. The substantive CU library is available through 1Y's vendor tree; it is not an additional object-theory proof merely because a copy of the bridge is physically present in KP's third-party directory.

## 2. Claim-to-module reuse map

Paths use these exact roots: `K` = `/home/dev/ggg/kp-simplified-verification`; `B` = `/home/dev/ggg/dh-bms-wf-formal/lean/Bm4`; `Y` = `/home/dev/ggg/1Y-Well-Ordering-Lean/formalization`; `CU` = `/home/dev/ggg/1Y-Well-Ordering-Lean/vendor/cu/ConstructibleUniverse/SetTheory/ZFC/Constructible`; `ML` = `/home/dev/ggg/1Y-Well-Ordering-Lean/vendor/mathlib/Mathlib`; `YM` = `K/third_party/YesMetaZFC/YesMetaZFC`.

Every named module below exists in the inspected snapshot. All 61 ledger nodes are covered, sometimes by several alternative rows. **Direct** means a stated helper can be imported at its existing type, not that the entire listed BTBMS node is complete. **Adapt** means new definitions/bridges and proofs; **idea only** means no matching theorem interface. For O, “direct KP infrastructure” is conditional on a proved model/theory bridge from the chosen ZFC+Mahlo theory to KP1Y's exact KPω theory.

Adaptation sizes are rough new/changed Lean LOC: **S** under 300, **M** 300–1,500, **L** 1,500–5,000, **XL** more than 5,000 or a substantial new proof family. They describe overlapping work, so do not sum the rows. A row with several candidate ASTs is a choice of substrate, not an instruction to import and translate all of them.

| Ledger IDs | Existing module path(s) | What transfers / what does not | Fit by deliverable | Estimated adaptation work |
|---|---|---|---|---|
| T9.1 | `K/KP1Y/Axioms.lean`; `K/KP1Y/Completeness.lean`; `YM/SetTheory/Axioms/ZFC.lean` | Pure-∈ axiom syntax, Hilbert derivations and completeness; object ZFC already has an axiom predicate. New target sentence, uniform Mahlo axiom and ZFC-model→KPω-model bridge still required. | H: idea only; O: direct logic core + adapt theory bridge | O M–L, separate from the mathematical proof. |
| D1.1, D1.7, C1.8, D1.9 | `Y/ZeroY/Syntax.lean`; `Y/ZeroY/SequenceOrder.lean`; `K/KP1Y/SequenceSpaces.lean`; `K/KP1Y/SequenceCertificate.lean` | Host flat-sequence lex/reachability patterns; object internal finite sequences and certificates. No recursive BTBMS forest/column/entry datatype or compact-word embedding. | H: adapt list helpers; O: direct sequence substrate, adapt tree coding | H M–L; O L–XL. Nested syntax, encoding and safe-prefix proofs new. |
| D1.2, D2.2, L2.2, L2.3, L2.4 | `Y/ZeroY/Forest/Stack.lean`; `Y/ZeroY/Forest/Blocker.lean`; `B/Basic.lean`; `K/KP1Y/OneYForestPaths.lean` | Leftward functional parent maps, ancestor chains, last-edge/prefix arguments. Instantiate per query where possible; no scoped visible-stack identity, query nesting or independent cap proof. | H: adapt generic paths; O: adapt KP paths; exact BTBMS lemmas new | H M–L; O L. Preserve the explicit column/index induction from codex-crosscheck-1.md, Q2. |
| D1.4, D2.1, L2.1, L2.5 | `Y/OneY/FirstMatch.lean`; `Y/OneY/Prefix.lean` | Finite search and prefix agreement patterns. Not the two-cursor scan of relative recursive heights, ν boundaries, or exact trace facts. | H: idea only/adapt search helpers; O: idea only | H L; O L–XL. Entire reduced-word boundary/reset theory still needed. |
| D1.5, D1.6, D3.3, L3.5 | `Y/ZeroY/Expansion/Context.lean`; `Y/ZeroY/Expansion/CopyRows.lean`; `Y/OneY/CopyCoordinates.lean`; `B/Copy.lean`; `K/KP1Y/OneYCopyPathTransport.lean` | Copy indices, phase shifts and seams for other algorithms. Neither operation is BTBM.ts; owner-root holes, special branch and frozen-cursor filling identity must be defined/proved anew. | H: idea only; O: idea only with local KP helper adaptation | H L–XL; O XL. No algorithm-identification theorem was found. |
| D1.3, D2.3, D3.1, L3.1, T3.2 | `B/Standard.lean`; `B/CopyPaper/Assemble.lean`; `Y/OneY/RelativeBlocker.lean`; `K/KP1Y/OneYForestClosure.lean` | Examples of generation invariants, structural closure and copy classification. No V/I/H/A/S/P contract, profile cap repair or BTBMS closure theorem. | H: idea only; O: idea only | H XL; O XL. Preserve corrected V∧I∧H∧P premise (G-002). |
| L3.4, L3.6, L3.7, T3.8 | `Y/OneY/ExpansionCanonical.lean`; `K/KP1Y/OneYExpansionOrderLex.lean` | Canonical expansion/order proof designs, not literal-cap kernels or cofinality for arbitrary L upper bounds. No candidate discharges these statements. | H: idea only; O: idea only | H XL; O XL. Major new finite gate; include reset cursors and unequal-prefix cancellation. |
| D4.1, L4.2, L4.3 | `Y/OneY/RootIndexed/CopyDiagram.lean`; `Y/OneY/RootIndexed/ActualScheme.lean`; `K/KP1Y/ReflectionTemplateShape.lean` | Explicit finite geometry/template records. Different source relations; BTBMS scan/descendant/repair constructors and admission closure absent. | H: adapt record architecture; O: adapt code/record architecture | H L; O L–XL. First freeze exact G-003 predicates; no semantic theorem substitutes for them. |
| F5.1 | `ML/SetTheory/Ordinal/Arithmetic.lean`; `K/KP1Y/OrdinalAdditionKP.lean`; `K/KP1Y/OrdinalArithmeticLimits.lean` | Host ordinal/limit arithmetic, or object ordinal addition/limit equations. Add the precise v<u, Lim(u) ⇒ v+ω≤u wrapper. | H: direct primitives; O: adapt proved arithmetic | H S; O S–M. No admissibility hypothesis should be added. |
| D5.2, C5.4 | `CU/Rudimentary.lean`; `CU/Def.lean`; `CU/LStageZFCardinality.lean`; `B/SetTheory/L.lean` | Rudimentary operations, Def-successor L, transitivity/continuity and cardinality of L stages. The paper uses finite-generator S-successors; L=J is not an available identification. | H: adapt low-level sets/recursion; O: idea only | H L–XL for actual S/J and rank/cardinality; no blanket substitution. |
| D5.2, C5.4 | `K/KP1Y/SigmaRecursion.lean`; `K/KP1Y/ConstructibleHistory.lean`; `K/KP1Y/ConstructibleLevels.lean`; `K/KP1Y/ConstructibleOrdinalContent.lean` | Genuine internal transfinite recursion and Def-based L histories, compatibility and ordinal content. Generic recursion can build a new S/J, but its invariants and budgets are new. | H: idea only; O: direct recursion substrate + adapt hierarchy | O XL; this avoids rebuilding object recursion, not proving J by renaming L. |
| C5.3, L5.8 | `CU/CodedSatisfaction.lean`; `CU/FormulaSyntaxCode.lean`; `Y/Concrete/OneYTruth/Complexity.lean`; `Y/Concrete/OneYTruth/PureSetSatisfaction.lean` | Set-domain satisfaction, formula codes and membership-bounded Δ₀/Σ₁ syntax. Useful H basis for verifiers; exact finite B-table construction and J_{v+ω} budgets remain to prove. | H: adapt; O: idea only unless translated into derivations | H L–XL. Pick one formula AST; do not confuse variable-context BoundedFormula with Δ₀. |
| C5.3, L5.8 | `B/SetTheory/Fm.lean`; `B/SetTheory/Defin.lean`; `B/SetTheory/Code.lean`; `B/SetTheory/SatCode.lean`; `B/SetTheory/SatInL.lean` | Alternative H formula/definability and supplied satisfaction-record checker. satCode_exists_in_L assumes IsAdmissible θ, unlike the paper’s arbitrary-limit budget. | H: adapt substrate; budget theorem: idea only; O: idea only | H L if this AST is chosen; avoid paying for conversion among all three stacks. |
| C5.3, L5.8, D7.1 | `K/KP1Y/SatisfactionRecursion.lean`; `K/KP1Y/TypedSatisfaction.lean`; `K/KP1Y/SatisfactionDefinability.lean`; `K/KP1Y/UniformCompile.lean`; `K/KP1Y/UniformFiniteQuantifiers.lean` | Proved internal satisfaction/evaluation tables, bounded certificates and one code interpreted uniformly across structures; arbitrary internal finite blocks, not only standard lengths. | H: idea only; O: direct compiler substrate + adapt BTBMS atoms/labels | O L–XL. J stage-membership budgets must be proved separately. |
| L5.5 | `CU/CanonicalBareHistoryGlobal.lean`; `CU/CanonicalBareHistoryBounds.lean`; `K/KP1Y/ConstructibleHistory.lean`; `B/SetTheory/LCode.lean`; `B/SetTheory/LCodeEx.lean` | CU has an unconditional history∈L_{ξ+ω} theorem; KP has internal histories; BM4 L-code existence uses admissibility. All concern different histories from finite-stage J plus its decorated production order. | H: adapt CU history argument; O: adapt KP history/checking | H L; O XL for exact decorated J-history budget. Similar +ω notation is not type equality. |
| L5.5 | `CU/CanonicalSkolemSelection.lean`; `CU/TextbookEElementaryHull.lean`; `CU/TextbookEUniformWitnessCardinality.lean`; `B/SetTheory/Skolem.lean` | CU canonical least selection, completed full elementary hull and smallness; BM4 choice-based ω₁ stage chain. No verified globally compatible partial Σ₁ functions on all paper J-levels. | H: adapt CU primitives; BM4 mainly idea only; O: idea only | H XL. Prove least valid records, compatible partial domains, continuity and general cardinal bound. |
| L5.5, L6.5 | `K/KP1Y/SkolemFunction.lean`; `K/KP1Y/CountableSkolemHull.lean`; `K/KP1Y/CountableOperationsClosure.lean`; `K/KP1Y/TarskiVaught.lean` | Internal least-witness graph and countable Skolem closure/Tarski–Vaught. Function is total on a fixed ordinal carrier (zero fallback), not paper’s partial compatible J functions; countable is not arbitrary card(J_a). | H: idea only; O: adapt | O XL. Generalize carriers/cardinality and derive J-local canonical witness budgets. |
| L5.6 | `CU/MostowskiCollapse.lean`; `CU/MostowskiCollapseOrdinals.lean`; `CU/MostowskiElementarity.lean`; `CU/StandardCondensation.lean`; `CU/CondensationFixedParameters.lean` | Actual set-sized extensional membership collapse, ordinal transport and full-elementary L condensation. Low-level collapse is usable; Σ₁-J condensation and whole J_u↦J_{π(u)} require new proofs. | H: direct collapse primitives + adapt/new condensation; O: idea only | H L–XL. Full elementarity cannot be inferred from Σ₁ elementarity. |
| L5.6 | `YM/SetTheory/Ord/OrderType.lean`; `K/KP1Y/ConstructibleOrdinalContent.lean` | Object well-order→ordinal collapse and L ordinal content. Not a general membership Mostowski collapse and not J-condensation. | H: idea only; O: idea only for target theorem | O XL. Build arbitrary-model internal collapse, extensionality and genuine J-history identification. |
| D5.7, L5.9, L8.2 | `B/SetTheory/Elem.lean`; `B/SetTheory/Rel.lean`; `Y/Concrete/OneYTruth/ActualReflectionMap.lean`; `Y/Concrete/OneYTruth/RootSemantics.lean` | Elementarity composition/relativization and Σ₁-map capture patterns. 1Y R k η a b uses mixed-truth L languages; BTBMS R(C,b,a) uses a J-hull trace and an elementary pair. | H: adapt logic/transport primitives; relation itself idea only; O: idea only | H L–XL for exact hull-trace and joint-record transport; no direct R adapter supplied. |
| D5.7, L5.9 | `K/KP1Y/ReflectionClause.lean`; `K/KP1Y/ReflectionTable.lean`; `K/KP1Y/ReflectionHeightAgreement.lean`; `K/KP1Y/ReflectionPrefixExistence.lean` | Internally recursive four-argument FR/R table and uniform finite-diagram existential compilation. Different relation and reflected language; not a theorem about BTBMS hulls. | H: idea only; O: adapt formula transport, relation idea only | O L–XL. Reuse quantifier/name code, prove new R and collapse transport. |
| L6.5 | `CU/TextbookEUniformWitnessCardinality.lean`; `ML/SetTheory/Cardinal/Regular.lean`; `B/SetTheory/Omega1.lean` | CU internal-L smallness for a chosen ambient level, and host cardinal bounds; BM4 only countable stages below ω₁. Need J_λ≺Σ₁J_u for every uncountable cardinal λ, via the newly proved J-condensation. | H: adapt; O: idea only from these modules | H M after L5.5/L5.6. Regularity is not needed for this cardinal lemma. |
| D6.4, L6.6, L6.7 | `ML/SetTheory/Cardinal/Regular.lean`; `ML/SetTheory/Cardinal/Cofinality/Club.lean` | IsRegular, IsInaccessible, IsClub, IsStationary and closure/intersection APIs. No matched finite-Mahlo predicate or reflection-hull club theorem was found in the inspected pins. | H: direct base API + adapt/new seed construction; O: idea only | H L after hull continuity/cardinality. Define finite Mahlo and prove actual hull closure points form a club. |
| D6.4, L6.6, L6.7 | `YM/SetTheory/Card/Properties/Regularity.lean`; `YM/SetTheory/Card/Cofinality/Boundedness.lean`; `YM/SetTheory/Card/Cofinality/Comparison.lean`; `K/KP1Y/ReflectionInitialRepresentation.lean` | Object cardinal/cofinality substrate and a different finite-graph initialization. No club/stationarity/Mahlo construction found; KP initialization is countability-based, not the needed stationary recursion. | H: idea only; O: adapt base cardinal machinery | O XL. Internal quantifiers, regular-cardinal closure and stationary intersections all need proofs. |
| D6.1, L6.2, D6.3 | `Y/OneY/RootIndexed/Representation.lean`; `Y/OneY/RootIndexed/CopyDiagram.lean`; `K/KP1Y/ReflectionNameFrame.lean`; `K/KP1Y/AssignmentFamilyPatch.lean` | Finite ordered diagrams and explicit copy/patching maps. New graph must have both parent representatives, correct same-forest pairs, fresh instances and persistent ι distinct from latest-copy f. | H: adapt Y diagrams; O: adapt K code/assignment substrate | H L; O L–XL. No existing exact occurrence identity for BTBM FS. |
| D7.1, D7.2, L7.3, L7.4, L7.5, L7.6 | `K/KP1Y/AssignmentFamilyPatch.lean`; `K/KP1Y/FrameAgreement.lean`; `K/KP1Y/ReflectionNameFrameFacts.lean`; `Y/OneY/RootIndexed/ActualScheme.lean` | Shared-variable and unchanged-frame proof patterns; useful local patching. BTBMS complete-prefix charts, source record grammar, whole-level negative label and resource budgets are new. | H: adapt architecture; O: direct local patching + adapt packet grammar | H XL; O XL. G-003 is an explicit design/proof gate, not discharged by generic diagram code. |
| D8.1, L8.2, L8.3, L8.4, L8.5, L8.6, L8.7, L8.8 | `Y/Concrete/OneYTruth/FiniteReflectionAssembly.lean`; `K/KP1Y/ReflectionTopInduction.lean`; `K/KP1Y/OneYCopySeamsInduction.lean` | Examples of staged reflection, shared existential witnesses and copy induction. Neither implements S_<n→W_<n→D_<n→S_n or exact least-failure packet readmission. | H: idea only/adapt proof organization; O: idea only/adapt compiler substrate | H XL; O XL. New semantic proof; moving whole-level labels and fixed-parameter clauses dominate. |
| T9.1, R9.2 | `Y/OneY/RootIndexed/Representation.lean`; `Y/ZeroY/Transport.lean`; `K/KP1Y/RankedDynamics.lean`; `K/KP1Y/RankedDescendantOrder.lean` | Y has generic lowerable-label accessibility/WF (Std-only import), directly usable for H; K has internal rank/minimality and trajectory lemmas. Need cofinality→full Std order, not just step WF. | H: direct generic WF lemma + adapt instantiation; O: direct rank core + adapt order proof | H S–M; O M–L after all earlier gates. σ/minimum and precise sentence still require identification. |

## 3. The important mismatches, with concrete theorem contracts

**L is not J, and full elementarity is not Σ₁ elementarity.** CU is significantly more complete than an early file header might suggest: `TextbookEElementaryHull.lean:164` proves full `SatisfactionAbsolute` for its constructed hull, and `TextbookEUniformWitnessCardinality.lean:173,185` proves the cardinal-smallness interface. These are completed proofs, not missing fields. Their scope also matters: the hull chooses a special ambient level depending on constructible κ,x, and its smallness conclusion is an **internal-L injection**, assuming `IsCardinal LMem κ` and ω⊆κ (`TextbookEUniformWitnessCardinality.lean:173–177`). It is not already an external cardinal bound for an arbitrary generator set X inside a specified J_C. Nevertheless, its strongest standard condensation endpoint has the following exact header ([source](/home/dev/ggg/1Y-Well-Ordering-Lean/vendor/cu/ConstructibleUniverse/SetTheory/ZFC/Constructible/StandardCondensation.lean:66)):

```lean
theorem condensation_of_elementary_isSuccLimit
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})) :
    range domain = LStageZF (ordinalHeight (range domain)) := by
```

`SatisfactionAbsolute` here means full first-order elementarity. BTBMS L5.6 starts only with `H≺Σ₁J_C`, and the paper's S-successor J is not `LStageZF`. The raw collapse primitives are useful directly; the displayed theorem does not discharge the weaker-elementarity J theorem. Strengthening the input hypothesis or silently changing the hierarchy would change the proof obligation.

CU also proves the following genuinely unconditional budget ([source](/home/dev/ggg/1Y-Well-Ordering-Lean/vendor/cu/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalBareHistoryGlobal.lean:85)):

```lean
theorem canonicalBareHistory_mem_LStageZF_add_omega
    (ordinal : Ordinal.{u}) :
    canonicalBareHistory ordinal ∈
      LStageZF (ordinal + Ordinal.omega0) :=
  canonicalBareHistory_mem_LStageZF_add_omega_of_finite_correct
    finiteBareGodelDefOutputCorrectIn_omega_succ ordinal
```

This is particularly valuable proof structure for L5.5. It is not a theorem about the paper's history or its decorated finite-production order. Conversely BM4's internal satisfaction endpoint is conditional ([source](/home/dev/ggg/dh-bms-wf-formal/lean/Bm4/SetTheory/SatInL.lean:2136)):

```lean
theorem satCode_exists_in_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {A : ZFSet.{u}}
    (hA : A ∈ L θ) :
    ∃ U ∈ L θ, ∃ T ∈ L θ, SatCode (L Ordinal.omega0) ωZ A U T := by
```

The `IsAdmissible` premise cannot be substituted for the paper's arbitrary limit coordinates. Generic existence of a truth set also does not imply that its entire checking record lies in `J_{v+ω}`. Those budgets are substantive new proofs in either route.

**The relations called R differ in all three projects.** BM4 has an expansion relation named R and a different semantic `RelAdm k`; 1Y's `RootSemantics.R k η a b` is a Σ₁ map between mixed-truth L-stage structures; KP1Y's `Query ... K θ a b` is an internally recursive FR table. The paper's `R(C,b,a)` is a canonical J-hull trace plus `J_b≺Σ₁J_C`. There is no verified equivalence among these interfaces. Existing positive pattern-splicing proofs suggest how to organize transport, but do not establish transport of the paper's whole-level negative label `No_B` or its exact chart/budget equations.

**Object-model proofs cannot be imported as arbitrary host facts, or vice versa.** KP1Y's useful lemmas take `M.Models KP1Y.theory`. Reuse in O needs an actual theorem that a model of the new ZFC+Mahlo theory satisfies that theory, including KP1Y's full set-induction scheme; upstream ZFC does not literally have the same axiom constructors. The needed bridge is expected to be derivable from object ZF, but must be provided. Reuse in H would instead require an explicit interpretation in Mathlib's ZFSet universe, usually less economical than using the host CU/Mathlib proofs directly. The upstream `TarskiTruth` module adds definitions as axioms of expanded theories; use KP1Y's proved `Satisfaction*` construction, not those new axioms as an unexplained shortcut to a pure-∈ result.

**The finite algorithms differ.** BM4 arrays and 0-Y/1-Y natural lists are not the recursive BTBMS syntax. Similar ancestry, copied-block and blocker proofs do not identify the actual BTBM two-cursor scan, its special branch, owner-root continuation hole, normalization, or cap repair. In particular, expansion-step well-foundedness alone is insufficient for T9.1; the BTBMS cofinality theorem T3.8 must supply the connection to the full standard lexicographic order.

One small **direct** H reuse is especially clean. `Y/OneY/RootIndexed/Representation.lean` imports only `Std`, and states ([source](/home/dev/ggg/1Y-Well-Ordering-Lean/formalization/OneY/RootIndexed/Representation.lean:515)):

```lean
theorem wellFounded_of_lowerable_labels
    {State : Type v} (step : State → State → Prop)
    (lt : α → α → Prop) (valid : State → α → Prop)
    (hWF : WellFounded lt)
    (initial : ∀ s, ∃ a, valid s a)
    (lower : ∀ {s t a}, valid s a → step t s →
      ∃ b, lt b a ∧ valid t b) : WellFounded step := by
```

For the BTBMS lexicographic relation, assign the empty expression the valid label 0. For nonempty B, set `valid B a` to “some nonempty standard A≥B has a configuration of maximum a.” Initial configurations supply labels, and a nonempty configuration has positive maximum. For C<B, if C is empty use its label 0<a; otherwise cofinality yields A[k]≥C, so A[k] is nonempty and descent supplies its smaller configured maximum. This directly reuses the generic theorem without taking the maximum of an empty configuration, while leaving the genuine BTBMS obligations visible. It does not assume that the configuration minimum σ itself is an order embedding. The analogous O proof should use internal ranked-dynamics/set-minimum machinery and a proved internal cofinality wrapper.

## 4. Estimated new work, separately for H and O

These are order-of-magnitude planning estimates of **new or substantially changed Lean source**, excluding unchanged dependencies and inherited proof files. They include statements, definitions and proofs, with the same physical-LOC convention as the measured candidates. They are not elapsed-time commitments. Different AST choices, automation, and resolution of G-003 can change them by a factor of two. A small semantic interface theorem alone is not the completed project: its J realization and exact FS fidelity must also be proved.

### H — host-Lean conditional well-order

**Working estimate: 40,000–90,000 new/adapted LOC**, with roughly 2,000–4,000 of that for final assembly, tests, public statement and dependency adapters beyond the three large components below. The best baseline is one compatible Mathlib/CU source family, plus selective standalone finite helpers. BM4 is an alternative formula substrate/proof reference, not a mandatory second L development. KP1Y's internal set coding is normally unnecessary overhead for this route.

| Largest new component | Rough scale | Main technical risk |
|---|---:|---|
| §§1–4: actual nested syntax/FS, scoped scan invariants, closure, cap repair and cofinality | 12k–28k LOC | Existing list/matrix expansions are different. Exact frozen cursors, query normalization, same-parent repairs and all selected-root positions must be proved, including the corrected profile premise. |
| §§5–6: exact S/J hierarchy, compatible partial Σ₁ hulls, J-condensation, complete-record budgets, reflection club and Mahlo initialization | 14k–32k LOC | Reusing full L condensation or admissible-stage satisfaction would silently strengthen hypotheses. The new globally compatible functions and exact `ξ+ω` budgets must be established for the actual hierarchy. |
| §§6–8: occurrence graph identity, complete packet grammar, joint capture/transport and least-failure descent | 12k–26k LOC | G-003: every transported failure must inhabit the identical admitted class, with both heads, full frames, old-prefix domain, ι/f distinction and whole-level label budgets. |

Some H coding can be streamlined by proving schema-level realization/capture interfaces rather than implementing unnecessary general-purpose object syntax. This does **not** allow arbitrary Lean predicates to become Σ₁-reflectable: their required definability and set-sized witness/budget lemmas still need proofs. D-2's choice changes a small initialization layer, not the dominant components.

### O — a pure-∈ Hilbert derivation

**Working estimate: 110,000–250,000 new/adapted LOC**, under the uniform internal Mahlo axiom specified above. Approximately 5,000–10,000 covers the target theory bridge, sentence/compiler assembly, semantic equivalence and final axiom audit beyond the three major components. This estimate reuses the existing YesMetaZFC and KP1Y generic substrate rather than rebuilding a first-order prover or object arithmetic. KP1Y's measured 30.5k largely generic lines supporting 58.4k notation-specific lines illustrates the cost: a host finite-tree proof is not automatically a derivation about all internally finite trees in an arbitrary model.

| Largest new component | Rough scale | Main technical risk |
|---|---:|---|
| Internal BTBMS finite-tree/word/stack encoding and §§1–4 derivations | 35k–80k LOC | Every recursive definition, generation witness, trace, cap and size induction must work for the model's internal ω. Proving each standard host n separately does not give the uniform object statement. |
| Internal S/J, canonical Σ₁ functions, extensional collapse/condensation, certificates and cardinal/club/Mahlo layer | 40k–90k LOC | KP's available L/countable closure does not supply arbitrary-cardinal J-hulls. Host well-founded recursion, Separation, Choice and Mostowski collapse cannot be silently used as object axioms. |
| Internal packet grammar, shared-variable compilation, reflection/descent and exact readmission | 30k–70k LOC | An entire jointly quantified record must survive reflection with the same named projections; code correctness, negative predicate budgets and allowed fixed parameters have to be object theorems. |

The existing uniform finite-template compiler, assignment patching and arbitrary-KP-model method are real savings. The planned endpoint should mirror KP1Y's structure: a closed sentence, a proved equivalence to the intended semantic property in arbitrary models of the chosen theory, and then the existing Hilbert completeness bridge. Truth in one Mathlib ZFSet/constructible model alone cannot supply that derivation.

## 5. Can the reusable parts share one toolchain?

**Architecturally yes for a selected source stack; not as an unmodified union of all three checkouts. The recommended common compiler is Lean 4.33.1. No combined build has been verified by this audit.**

Verified pins and constraints:

- KP1Y and its YesMetaZFC dependency declare 4.33.1. The local portable compiler `/home/dev/ggg/.tools/lean-4.33.1-linux/bin/lean` reports that version. `lean`/`elan` are not on the audit shell's PATH; KP's checker already knows the portable fallback.
- Both 1Y project toolchain files declare 4.33.1. Its CU and Mathlib source files retain the historical 4.33.0-rc1 toolchain declaration, but `Concrete/dependencies-lock.json` fixes a **4.33.1 source-build** configuration. The vendor README says all relevant sources are compiled by the root compiler rather than mixing rc1 caches. Saved validation records support that configuration; they do not prove a new Linux/BTBMS merge works.
- BM4 requires Lean/Mathlib 4.30.0. Its Mathlib pin and 1Y's Mathlib pin are two versions of the **same package/module namespace**, not libraries that can simply coexist under separate imports. A 4.33.1 project must port the selected BM4 source against its one chosen Mathlib revision, or leave BM4 as a proof reference. Downgrading the larger 4.33.1 stacks merely to keep BM4 unchanged is not justified.
- Compiled `.olean` artifacts are version-sensitive; rebuild source under the chosen compiler. This audit found no particular BM4 declaration failing under 4.33.1 because that migration was not attempted. Likely migration surfaces are its broad Mathlib imports, ZFSet/Ordinal APIs, recursors and tactic elaboration; these are risks, not observed compile errors.
- KP and 1Y require the same `YesMetaZFC` name from different physical paths. Select **one** copy in the new integration workspace and make dependency paths agree. Prefer retaining KP's recorded kernel-checked Surface patch, and preserve the two existing bridge performance patches if the bridge is actually needed. Re-audit dependent declarations after this selection; identical public types are not a substitute for compiling the affected closure.
- Three formula ASTs coexist in these sources (BM4 Fm, CU/Mathlib-oriented formulas, YesMetaZFC Project). Their semantics/checkers are not definitionally equal. Choosing one is a proof-interface decision, not a compiler flag. For H prefer the CU/Mathlib family unless a measured BM4 advantage justifies conversion; for O keep YesMetaZFC/KP's proved internal syntax/compiler.

A practical H integration can avoid both the full BMS bridge and KP1Y: use Mathlib, narrow CU collapse/satisfaction/set-construction imports, and standalone generic representation lemmas such as the Std-only module above. Other apparently small ZeroY ancestry modules import `YesMetaZFC.BMS`, so inspect their dependency closures before calling them license-independent. An O integration can keep Mathlib/CU out of the proof dependency altogether, using them as references while retaining KP1Y and one YesMetaZFC package. If both deliverables are later desired, source-level coexistence is plausible at 4.33.1, but the host/object semantic bridge remains separate work.

Any future migration check should occur in a separate integration copy, with narrow module checks and axiom audits. KP's `check-module.sh` without `--emit` is its non-emitting single-module checker; the `--emit` form writes `.olean`. Its scripts and fingerprints are useful verification infrastructure. No candidate checker or full build was invoked here, and this audit creates no new project/dependency configuration.

## 6. Recommended reuse boundary and acceptance gates

1. **Freeze the deliverable and O quantifiers.** D-1 and the uniform-versus-external-Mahlo issue determine whether host syntax/ordinals or arbitrary internal codes are the primary objects. Do not write a host theorem first and report it as an object derivation.
2. **Keep the actual BTBM operation and finite calculus independent.** Existing notation systems provide helpers and proof patterns, not an established embedding of BTBMS. Finish the domain agreement, scoped occurrence representation and early scan/cap interfaces against the paper/reference contract.
3. **Resolve the exact packet predicate before semantic induction.** G-003 remains new work regardless of reuse. Use candidate name/assignment helpers only after specifying the intended constructor fields and preservation laws.
4. **Prove a small semantic interface, then its exact J instance.** A useful first reuse pilot is one genuine history/certificate budget and one control transport problem, followed by Σ₁-J condensation. A full-L condensation import passing typechecking would not count as that pilot.
5. **Import narrow, licensed/provenanced foundations.** Own Apache/MIT modules and CU/Mathlib have explicit notices; BM4 original source and the pinned BMS/YesMetaZFC snapshot have unresolved grants in the supplied material. Preserve the existing provenance and obtain the appropriate basis before copying/distributing those sources. No permission is requested for this completed read-only audit.
6. **Keep evidence levels separate.** Source-exact statements and counts are verified here; saved audit/build logs are historical records; successful new compilation, full dependency axiom audits, port feasibility and LOC forecasts remain unverified or estimated as stated.

Detailed candidate notes and machine-readable mapping are retained in `scratch/codex/reuse-kp.md`, `reuse-bm4.md`, `reuse-y1.md`, `reuse-y1-imports.json`, and `reuse-map.json`. They support the decisions above; they do not change the candidate projects or discharge any new ledger theorem.

STATUS: COMPLETE
