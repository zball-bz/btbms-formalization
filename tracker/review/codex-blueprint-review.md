STATUS: COMPLETE

# Codex blind blueprint review — T-017

**Target:** `133f5d880eb10bf18baa5621f39190817e993ce0` (`133f5d8`). All blueprint line citations below refer to that snapshot.

**Gate recommendation: HOLD G1 at this snapshot.** The abstract assembly is sound, and I recommend Part C for D-4. However, five groups of helper claims are false as stated, and two essential cofinality arguments still need precise cap-sensitive path invariants. These are reasons to repair the blueprint before freezing its signatures. I found no counterexample to the locked `MainTheorem`, and none of the required repairs calls for changing that theorem.

## Scope, method and evidence

I read the spine, all five units and their Lean signatures, the allowed integration sections, relevant paper passages and the P1 gap descriptions/repair records. I did not read `blueprint/verification/`, `blueprint/repairs/`, `INTEGRATION.md` §2, or `scratch/blueprint/*-verify/`. The snapshot was copied by an explicit whitelist to `scratch/codex/bp133f5d8/`; `snapshot.json` records hashes. The integration copy contains only §1 and §§3–5. Claims embedded in the allowed prose that something had been verified were not used as evidence. Parallel finite, packet and hierarchy audits observed the same restrictions; I checked their findings against the source contracts before incorporating them.

The combined six-file Lean skeleton **typechecks**, against an isolated scratch copy of the locked project and pinned dependencies. This establishes type correctness, not truth: admitted proofs can hide false statements. An independent environment inspection found exactly three `BTBMS` definitions with direct `sorry` expressions: `Forest.instLinearOrder`, `Key.instLinearOrder`, and `Hier.jInterface`. The first two have executable order operations and admitted proof fields. No fourth missing computational body was found. Evidence: `bp133f5d8/definition-audit.lean` and `.log`.

I also compiled an independent proof of the final accessibility/assembly argument, two hierarchy API/semantics probes, and a packet counterexample; ran the actual snapshot bodies on finite counterexamples; and ran independent bounded finite corpora. The probe proofs do not invoke the blueprint theorem stubs they test. The concrete imports inherit `sorryAx` through the unfinished syntax-order instances and types containing them; I explicitly distinguish this from an independent completed formalization. The generic assembly proof and both hierarchy probes print only `[propext, Classical.choice, Quot.sound]`.

## Verdicts by question

| Question | Verdict | Reason |
|---|---|---|
| Q1: top-level assembly and fields | **sound-with-issues** overall; the conditional assembly is **sound** | An independently written Lean proof derives exactly the locked `IsWellOrder Std Std.lt` and `MainTheorem.{u}` from the stated fields. Packaging requires no hidden hypothesis. The cofinality/descent field developments still depend on the repairs below. |
| Q2(a): hierarchy interface | **sound** | U5 uses its ordinal semantics, capture, transport, structural laws and cardinal/club fields; no extra J-specific theorem is smuggled into the descent contracts. |
| Q2(b): Part C instance | **sound** at proof-plan level | Locality, the recursion, finite formula translation, simultaneous condensation induction, cardinal bounds and universe lifts survive the independent checks below. This is an assessment of the mathematical construction, not a claim that its `sorry` proofs are finished. |
| Q2(c): D-4 | **sound** to choose Part C | It provides the required interface directly, with the locked hypothesis unchanged. Keep Part B as a separate paper-fidelity development. |
| Q3: G-001–G-005 repairs | **sound-with-issues** | G-001, G-002, G-004 and G-005 are fixed at blueprint level; G-003 is partial because exact closure providers still need correction. |
| Q4: both critical chains | **unsound as a verbatim lemma package** | T3.2i contains a false numerical statement, and other false providers feed both chains. The chain tables distinguish these failures from adequate conditional assembly and unresolved mathematical steps. |
| Q5: risky/open arguments | **sound-with-issues** as a proposed route | T3.8li and T3.8lo remain unresolved major proof obligations. L4.2c needs explicit transport bookkeeping; L7.5d/L8.8f have adequate semantic interfaces once their providers are repaired. No counterexample to the intended admissible conclusions was found. |
| Q6: exact signatures versus prose | **unsound as written** | BP-01–BP-05 are actual counterexamples to overgeneralized helper claims. BP-08–BP-09 are provider/consumer gaps. I found no contradictory or vacuous core `FinalHyps`, `SStrict`, `DLab`, or `Hier.Interface` contract. |

“Sound” in a node table below means that I accept the stated mathematics and proposed route at blueprint level. It does not mean the declaration's admitted proof has been replaced.

## Findings

| ID | Node / declaration | Severity | Issue | Evidence | Minimal fix |
|---|---|---|---|---|---|
| BP-01 | D3.3b, `word_kernel` | major | Word factorization is asserted even when an exhausted owner root leaves no continuation hole. | `U2.lean:438`; actual V-valid forest gives word lengths 2 and 3. | Add `KernelDefined E rd` and discharge it at consumers. |
| BP-02 | T3.2i, `num_phaseCol` | major | Arbitrary `StopData`/`RootData` need not encode coherent printed numbers or an actual operation. | `U2.lean:624`; concrete records give `1 = 0`. | Require actual-data/coherence hypotheses; recheck every application. |
| BP-03 | D3.1d, `origin_spec_full` | major | The total origin map is claimed to preserve parent lookup at nonexistent output slots. | `U2.lean:265`; admissible cap, lookup `none` versus `some 1`. | Restrict the slot clause to actual output entries/roles. Audit the other unrestricted clauses. |
| BP-04 | D3.1e `moves_spec`, `applyMoves_litCap_addr`; L4.3c and downstream repairs | major | “Outside the marked height” uses its original address after earlier moves have relocated it. Two provider conclusions are false. | `U2.lean:308,334`; two legal moves satisfy the static premise but change the marked height and predicted cap address. | State exclusion at every current `moveAddr (moves.take i) b`; prove U3 supplies it and propagate it through the cap/readmission chain. |
| BP-05 | L8.8a, `failure_floor` | major | Drops factorization's actual-source-entry premise. `Valid` alone allows a successor-valued owner. | `U5.lean:800`; a valid empty-source packet with owner 2 and low value 1 would require `1 < Ls < 2`. | Add `Admitted` or source-entry membership and pass it to FIRM `factorization`. |
| BP-06 | T3.8li with T3.2q | major | The cited forward path theorem uses actual keys of the original/output expressions; the projection proof needs changed-container, decorated-cap transport. | `U2-closure-cofinality.md:1668–1705`, `U2.lean:744–769,1006–1013`. | State and justify a cut-specific forward transport invariant, including restored-owner and copied-query cuts. |
| BP-07 | T3.8lo | major | A path ending at the proposed root does not establish its outgoing non-exhausted response. The low-detour extension used in step 3 is not supplied. | `U2-closure-cofinality.md:1778–1794`, `U2.lean:1054–1060`. | Prove the low-query orbit/response invariant through previous heads and capped containers. |
| BP-08 | D3.1d → L8.6a, `anchorOrigin_prefix` → `nu_mem_vars` | minor | Provider needs `InL E`; empty-query `DLab` over a cap assumes only `InL(anchor E cap)`. | `U2.lean:284`, `U5.lean:496–512,542`; `Spine.lean:1837`. | Supply the structural origin-prefix lemma without `InL E`, or a separate raw-origin version. Do not silently narrow `DLab`. |
| BP-09 | L4.3 → L4.3d, `reduce_childEnds` → `childEnds_package` | minor | Consumer uses prefix/subgraph facts about an existential witness that the provider does not export. | `U3.lean:521–533,865–887`; prose explicitly acknowledges this at `U3-records-packets.md:1681–1684`. | Export the role-prefix and graph-subset properties, or expose the shared explicit truncation construction. |

No finding is labelled fatal: the demonstrated false statements have local scope repairs, and the two unresolved mathematical obligations have plausible intended formulations. Their being plausible is insufficient for declaring the current blueprint ready to freeze.

### BP-01: undefined owner kernel

Use `∅=[]`, with forests written as lists of columns:

```
J = [[(2, ∅)]]
H = [[(0, J), (1, ∅)]]
E = [[], [(0, H)]]
X = [[]]
```

`CondV E` holds. Its actual stop is at path `[(1,0)]`, column 0, with depth 1, `t=2`, `r=1` and one query entry. The actual root is outer column 1, owner=true, cursor=1; its sole entry has been consumed. Thus `unconsumed E rd=[]`. The owner branch of `kernel` discards X, while the right side of `word_kernel` appends `word X`. The computed lengths are 2 versus 3. This E fails I, which is permitted by this theorem's actual hypotheses. It is not a counterexample to an InL consumer.

The adjacent `expand_eq_iterate` already asks for `KernelDefined`; carry the same conceptual condition into the word theorem. Adding a generic validity premise without explaining why the hole exists obscures the reason for the repair. See `scratch/codex/bp-finite-probes.lean` and the final evaluations in `bp-finite-run.log`.

### BP-02: incoherent phase records

Take

```
sd = {depth=0, col=([],1), t=0, r=0, Q=[]}
rd = {layer=0, idx=0, col=([],0), owner=false, cursor=0}
i=1; a=rd.col
```

The real `phaseCol` computes `some ([],1)`. Its printed number is 1. The asserted right side is `0 + 1*(0-0)=0`. Both stated premises hold. The neighboring classification/local-suffix theorems have actual input/data equations; this theorem needs an appropriate version of those assumptions too. The independent admissible-data corpus below does not find a failure when those equations hold.

### BP-03: an origin outside the output domain

Let `E=[[],[(0,∅)],[(1,∅)]]`. Cap outer column 1 at its end, cut 1, parent 0, with no moves. Then `w.H=[[],[(0,∅),(0,∅)]]`; both E and w.H are in L, and the cap is upward. For `e=e'=(outer column 2,entry 0)`, the total `w.origin` returns `some (.slot e')`. Yet the cap has no such slot, while E has parent 1 there. The parent-lookup equality in `origin_spec_full` is false.

The basic origin contract's on-domain restriction is appropriate. Preserve that restriction in this strengthened provider. Altering the origin function itself to reject invalid addresses is a larger API change and is unnecessary for intended consumers.

### BP-04: the mark moves

This is not merely a hypothetical mismatch between two predicates. A concrete admissible-cap witness is:

```
J = [[(2,∅)]]
H = [[(1,J),(1,J)]]
E = [[],[(0,H),(0,H)]]
b = (outer column 1, entry 1)
cap column = (path [(1,1),(0,1)], column 0), cut=1, parent=2
m0 = (outer column 1, i=0, j=1)
m1 = (column (path [(1,0)], column 0), i=0, j=1)
moves = [m0,m1]
```

The cap changes the second J inside the second H to `Jcap=[[(2,∅),(2,∅)]]`. The outer H violation can legally be repaired first: m0 moves the second H to outer slot 0. Then m1 repairs the internal violation of this relocated H. The snapshot bodies confirm both sequential `MoveOK` conditions, original E and final cap in L, upwardness, and the theorem's original `hb`/`hout` premises.

Neither move's column path starts with the original `b.heightPath=[(1,1)]`. But m1 is inside the current mark at path `[(1,0)]`. Applying the same moves to `E.truncAfter b` changes the marked height's first-column length from 2 to 1. `moves_spec` therefore has a false height-preservation conjunct. At q=2, `applyMoves_litCap_addr` predicts cap path `[(1,0),(0,1)]`, whereas the actual cap lies at `[(1,0),(0,0)]`; its equality is false too. Evidence: `bp-finite-moves.lean/.log`.

The sufficient premise is indexed:

```lean
∀ idx (hidx : idx < w.moves.length),
  ¬ (moveAddr (w.moves.take idx) b).heightPath <+: w.moves[idx].col.path
```

U3's intended first-difference cap has an H-correct interior. Inductively preserve that interior at the **current** address; a legal move there would contradict H, so every move is outside it. This should establish the stronger premise and then `RepairList`, commuting replacement, and the preserved-height/literal-cap claims. The general witness above is not claimed to be a first-difference cap: it refutes the overgeneralized U2 providers those consumers cite.

### BP-05: failure-floor countermodel

Take universe 0, `E=F=∅`, and both marked addresses equal to the nonexistent `(outer column 1,entry 0)`. Use kind `repair []`. Map every ordinary role to `aux 2` and every slot to `aux 1`, in both charts. Let both primitive predicates be constantly True. Set `asg(aux 0)=1`, `asg(aux 1)=2`, and all other values to zero; take auxiliary diagram `[base (eq (aux 0) (aux 0))]`.

The two actual chart domains are empty, so their injectivity requirements hold. The host and frame equalities hold; the target frame has one pair `(aux 2,aux 2)`, and the totalized target selector is 0. Both target heads hold. The joint graph is just the auxiliary reflexive equality. The two low-name occurrences both have value 1, below owner value 2. Thus `Valid` holds.

`TargetAbove 0` fails because even the empty target's positive block contains `Lim(owner)`, while its coordinates must lie below 2. The claimed raised floor would satisfy `1<Ls<2`, which is impossible for ordinals. `bp-packet-counterexample.lean` proves these assertions by unfolding the real definitions and ordinary ordinal facts; it compiles without invoking any blueprint theorem. Its transitive `sorryAx` caveat is documented above and in the log.

FIRM `factorization` correctly includes actual-source-entry membership (`Spine.lean:1632`). Every `Fails` packet in the intended L8.8 use is admitted, so restoring that premise here costs nothing in the induction.

## Q1: exact top-level assembly

`FinalHyps` at `Spine.lean:1901–1914` keeps the actual syntax order, `IsStd`, optional `expand`, natural parameters, InL closure, cofinal lower bounds, seed configurations and strict decrease for nonempty outputs. `abstract_implies_main` retains the locked single-universe premise `∀ n, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ`. No stronger Mahlo hierarchy or substituted standard domain appears.

The independent proof in `scratch/codex/bp-finalhyps-probe.lean` establishes:

1. Every nonempty standard A has some `Conf A θ`, by induction on the locked standard-generation witness. An empty predecessor cannot produce nonempty A: `expand ∅ n = some ∅` reduces directly from the locked definition.
2. Empty is accessible by leastness. For nonempty configured A, ordinal induction on θ proves accessibility of **every standard B≤A**. If C<B≤A and C is nonempty, cofinality at A gives an output A′ with C≤A′. Empty leastness implies A′ is nonempty. Descent supplies a smaller θ′ and configuration of A′; the induction hypothesis applies. Empty C is handled separately.
3. Trichotomy is inherited on the subtype. This gives exactly `IsWellOrder Std Std.lt`.
4. The Mahlo premise supplies `Conf`/`FinalHyps`; unfolding the locked theorem finishes `MainTheorem.{u}`. An independent constructor check packages the six actual leaves into `FinalHyps (Configured P)`.

In particular, cofinality does **not** need `A′<A` in this abstract interface: the induction decreases the ordinal label. Nor does it need a configuration or a strict rank drop for the empty self-loop. The seed index `m-1` creates no boundary hole: the premise supplies index zero as well.

The concrete proof uses the unfinished syntax-order instance but no blueprint theorem stubs. A second generic version over an arbitrary genuine `LinearOrder` validates the same argument with no `sorryAx`. Thus I accept the architecture and the exact `abstract_implies_main (fun hM => ⟨_, finalHyps jInterface hM⟩)` assembly **conditional on the leaf proofs**. The defects in those leaf developments are not an assembly defect.


For the second part of Q1, the field-by-field assessment is:

| Field | Assessment of the actual obligation |
|---|---|
| `order` | The generic syntax comparison/word order gives the intended strict total order; no extra order is assumed in the target. Its two instance proof bodies remain to be implemented. |
| `empty_least` | Correct for the actual proper-prefix comparison; no nonempty syntax lies below the empty forest. |
| `closure` | Correctly scoped to generated standards. The preservation plan is plausible, but its supporting helper statements need the finite repairs above. |
| `cofinal` | Correct intended scope, including arbitrary InL upper expression and standard lower expression. I cannot independently certify its proof plan as complete while BP-06/BP-07 remain open. No counterexample found. |
| `seed` | The finite seed construction uses the available weak Mahlo index and the interface's cardinal/club laws. It asks only for an existential configuration maximum, including at m=0. No overstrong field identified. |
| `descent` | Correct scope and guards; the packet/label argument is adequate conditional on the corrected finite providers and completed cofinality. No counterexample to this field found. |

Thus Q1 is not an unconditional approval of all field realizations. The independent assembly proof establishes sufficiency and exactness; the unresolved upstream mathematics accounts for the overall `sound-with-issues` verdict.

## Q2: hierarchy interface, Part C and D-4

### Interface sufficiency

`Hier.Interface` (`Spine.lean:1116–1145`) supplies every semantic operation used by U5: monotone/reflexive/transitive elementarity, intermediate restriction, both elementarity projections of an edge, edge restriction/extension, diagram capture/transport, uncountable-cardinal elementarity and the regular-cardinal club. U5 is parametrized by `Interface`/`Prims`; its J-language describes an interpretation and does not add an extra axiom. The finite diagram grammar includes the negative block labels used by least failure, with the actual frame, floor and owner variables in their support.

### Locality and well-founded recursion

For a base atom, every primitive coordinate occurs in its variable list. A negative `noReal D fr u L` exposes u, L and every active framed coordinate. Under an outer bound b, every candidate inner block witness is bounded below the assigned u<b. Hence both existence and nonexistence depend only on primitive tuples below b. Fixed variables outside the finite support can be patched independently; they are not silently dropped from the universal frame/fixed-value equations.

At recursive level z, the guarded Elem clause reads realizability only at bounds ≤z and therefore primitives strictly below z. The Edge clause reads lower `Elem a b` at b<z and writes the current `Elem b z` clause inline, rather than recursively requesting the unfinished level z. This makes `Ordinal.lt_wf.fix` legitimate (`U4.lean:935–976`).

### Exact θ/τ translation

The finite first-order translation (`U4.lean:732–931`) separates occurring fixed/free variables and binds precisely the active unframed block variables. The distinguished transport variable is handled before the ordinary split; `¬F t` is explicit. If t is absent from the diagram, the valuation is patched off support. Fixed off-support variables are likewise restored afterward. The explicit target-below-bound premise in `realize_realFml_some` is available from `a<b<c`.

The limit formula correctly expresses a nonzero limit with a smaller nonzero limit, hence a limit strictly above ω. I checked its binder expansion independently in Lean. The empty ambient-order case of `transfer_top` is treated separately: realizability below zero forces empty support and thus an empty diagram. No nonempty-carrier assumption is hidden.

### Condensation, especially N4.7 step 4

Collapse an elementary substructure of the ordinal carrier to its order type ν≤w, using the unbounded class `X ∪ Ici w` and ordinal enumeration. Transport the predicates to the collapsed structure. Induct on the **collapsed top coordinate** o. Transfer each individual finite θ formula by elementarity/isomorphism; agreement of predicates below o, supplied by induction, and locality identify its semantics with the genuine recursively defined hierarchy. This identifies the current Elem clause. Then transfer each τ and use the just-identified current Elem and the lower Elem induction hypothesis to identify Edge at o.

There is no attempt to put an infinite conjunction of all diagrams into one first-order formula, and no assumption of the very Edge/Elem equality being proved. The bad-order/bad-limit cases are false on both sides. The cut conclusion follows from order type: if the source points below k are exactly all ordinals below x, the image of k is x. These steps justify the actual isomorphism contract (`U4.lean:1046–1062`), not merely an elementary order embedding.

### (13), (14), universes

For (13), finitely many fixed parameters below an uncountable κ are bounded by some m<κ. A countable-language Skolem hull of the full initial segment m has size at most `max(ℵ₀,lift(m.card))<lift κ`, even if κ is singular. Its collapse height is below κ and fixes those parameters; transfer and bound monotonicity give reflection. Regularity and strong-limitness are unnecessary here.

For (14), regularity bounds the hull's values below κ. Iterate the bounding function together with strict increase for ω steps. Uncountable regularity keeps the supremum below κ. Monotonicity and nonempty directed-union continuity of hulls give a reflection point; the same continuity proves closedness. The hull contains all points below that point x and κ itself, has cut x below κ, and collapses κ to x. Transfer yields `Elem x κ` and the required distinguished-parameter transport, while (13) supplies `Elem κ w`.

The model/hull carrier is in `Type (u+1)`. The comparisons correctly use `Cardinal.lift.{u+1} κ`, and the collapsed ordinal stays in `Ordinal.{u}`. I checked the needed large-index regularity adapter in Lean for `ι : Type (u+1)`, `#ι<lift κ`. No resizing or inaccessible-universe premise is required. Type0 diagram-variable types are compatible with valuations in the higher-universe carrier. The language remains countable: each diagram produces a finite formula, not a new symbol or an infinite conjunction.

Evidence and pinned library citations are in `scratch/codex/bp-hierarchy-review.md`; `bp-hierarchy-probe.lean/.log` contains the binder and lifted-regularity checks, both without `sorryAx`.

**D-4 recommendation: Part C.** N4.4 and N4.7 remain substantial proof engineering, but their plans contain the necessary mathematics. Part B additionally requires new Σ₁-J condensation, history and certificate developments. Part C avoids those obligations while providing exactly the interface and preserving the locked theorem. This recommendation does not certify the paper's §5 proof by substitution.

## Q3: G-001–G-005

| Gap | Verdict | Independent check |
|---|---|---|
| G-001 | **fixed** at blueprint level | `expand_eq_paperOp` has nonempty V,I hypotheses; U1 separates empty/reference behavior, route termination, visible roots, special/ordinary outputs and owner exhaustion. Parameter zero is handled separately. The paper-standard bridge obtains the hypotheses by closure. Independent comparison: 4,800 operation pairs, no failure. |
| G-002 | **fixed** at blueprint level | `condS_of_condP` explicitly requires V,I,H,P (`Spine.lean:963`). The pure-tower bounds and upward-cap S lemma keep the needed V,I,H and P assumptions. The false unrestricted P⇒S is not used. |
| G-003 | **partial** | Records, admission, packet validity, label grammar and readmission targets are now exact predicates. The survival condition on confined special steps fixes the old boundary case. But BP-03–BP-05 and BP-08–BP-09 leave false or insufficient providers on the closure route; the moving-address invariant must be exported explicitly. |
| G-004 | **fixed** as a mathematical repair | `J_b∈H`, rather than `J_b⊆H`, is the needed statement. Relativizing an arbitrary formula to the set parameter `J_b` turns it into a bounded formula; hull elementarity plus the trace equality gives full elementarity of the trace. See `U4.lean:505–528`. Part C avoids the J obligation altogether. |
| G-005 | **fixed** by exclusion | The absent accompanying programs are not proof providers. The blueprint's only §10 disposition is that it is unused; no critical node imports their claimed evidence. Our new bounded checks are explicitly diagnostics, not proof. |

Closing the four gaps above means accepting their repairs and scoped proof plans, not asserting completed Lean theorems. G-003 should remain open until its exact provider/consumer chain is repaired.

## Q4: node-by-node critical chains

A is the 25-node longest chain in the allowed integration §4; B is the 23-node weighted chain. Shared nodes are listed once, with both positions. “Yes, conditional” means the local argument is adequate given its named providers; it does not close a defective or unresolved provider. The tables cover every node of both chains, plus the final MAIN assembly.

### Shared prefix

| Node | A/B position | Statement judgment | Plan sufficient without new mathematics? | Evidence / consumer check |
|---|---|---|---|---|
| D1.2a | A1/B1 | sound | yes | `Spine.lean:156–236`: concrete addresses, roles and numbering. Entry indices do not contribute to column numbers. |
| D1.2b | A2/B2 | sound | yes | `U1.lean:124–213`: resolver ranges partition the visible stack; lookups/injectivity have the necessary occurrence/on-stack premises. |
| D1.2d | A3/B3 | sound | yes | `U1.lean:240–258`: last-entry route and `size+1` fuel; every descent consumes an actual height occurrence. |
| D1.5a | A4/B4 | sound | yes | `U1.lean:593–631`: fill/shift law leaves the inserted filling unshifted; the word law has the depth-in-route condition. |
| D1.6b | A5/B5 | sound | yes | `U1.lean:647–718`: actual branch-data equations; explicit owner suffix and n=0 treatment, rather than unconditional owner rejection. |
| D1.6c | A6/B6 | sound | yes | `U1.lean:724–791`: root visibility keeps the admissible operation out of the reference's extra raw-input branch; helper agreements are decomposed. |
| D1.6a | A7/B7 | sound | yes | `Spine.lean:706–725`: nonempty V,I agreement; empty self-loop separately accounted for. G-001 is scoped correctly. |
| D3.3a | A8/B8 | sound | yes | `U2.lean:414–430`: iterate identity has `KernelDefined`; zero/context and undefined-owner cases are separate. BP-01 concerns the adjacent word lemma, not this correctly scoped identity. |

### Remaining longest-chain nodes

| Node | A/B position | Statement judgment | Plan sufficient without new mathematics? | Evidence / consumer check |
|---|---|---|---|---|
| T3.8c | A9 | sound | yes, conditional | `U2.lean:822–836`: upward cap, old I and new V,I exclude special; full/end cuts are included. Uses the corrected word library. |
| D3.1a | A10 | sound definitions | yes for the basic on-domain contract | `Spine.lean:829–951`, `U2.lean:81–88`: ordered legal moves, structural repair lists and surviving-role origins are concrete. Later strengthened providers fail BP-03/BP-04. |
| L3.1g | A11 | sound | yes | `U2.lean:227–231`: finite cut queries do not consume ⊤; scans stop in a shared prefix or a same-parent block, so deleting that block preserves the response. |
| L3.1 | A12 | sound | yes | `U2.lean:240–246`: old P is explicit; repair preserves V,I,decorated A, recovers S from the profile bound and fixes containing H violations. This does not justify the stale-address variants of BP-04. |
| L3.6 | A13 | sound-with-issues | yes, conditional on corrected helpers | `U2.lean:896–905`: `Cof B` is a premise, avoiding circular cofinality; old P is present in success-unmoving. The move/root scan cases are specified, but kernel-word uses need BP-01's condition. |
| T3.8lc | A14 | sound-with-issues | local argument yes; prerequisite incomplete | `U2.lean:962–974`: compare the remaining iterate with `Q++[(r,∅)]`, use downward success and conjugacy. T3.8lb's decorated old-cap proof inherits BP-06. |
| T3.8l | A15 | sound-with-issues | **no, not yet** | `U2.lean:953–1104`: the cut case split is exhaustive, but projected and previous-phase roots require BP-06/BP-07. |
| T3.8m | A16 | sound-with-issues | yes, conditional | `U2.lean:1107`: induction is on generation witnesses, not on the syntax well-order being proved. It inherits T3.8l's open cases. |
| T3.8 | A17 | sound-with-issues | yes, conditional | `Spine.lean:987–994`: cofinality and positive bounded strict covering have the consumers' needed hypotheses. The proof route remains dependent on BP-06/BP-07. |
| L4.3 | A18 | sound-with-issues | source reduction yes; repair part needs BP-04 | `U3.lean:465–533`: scan→descendant and repair→repair preserve target and exact context equations. Query-size bound is adequate. Repaired output/admission depends on corrected moving-address providers. |
| L4.3d | A19 | sound intended statement | yes after an interface repair | `U3.lean:865–887`: `ChildData` supplies exactly Case 2's graph/prefix/branch/admission facts. BP-09 prevents extracting them solely from the current existential provider. |
| L8.8d | A20 | sound, conditional | yes | `U5.lean:842–850`: ordinary empty-query/internal-root and special strictly-internal-owner branches preserve the old marked owner/prefix before the second capture. Needs the strengthened `ChildData` provider. |
| L8.8 | A21/B19 | sound intended implication; defective provider | yes after local/preceding repairs | `U5.lean:882–884`: least failure and first-difference case split are adequate. BP-05 must be corrected; admission available in `Fails` discharges it. Case 3 inherits the cap-chain obligations. |
| D8.1 | A22/B20 | sound-with-issues | yes as induction architecture | `Spine.lean:1806–1861`: size belongs to the original target, which readmission preserves. The stages `S_<n→W_<n→D_<n→S_n` use strictly smaller query heights. The empty-query label proof needs BP-08. |
| T9.1d | A23/B21 | sound, conditional | yes | `U5.lean:901–904`: choose n above finitely many query sizes, apply DCore, then bound the finite maximum below α(T). Empty output has maximum 0, below the limit α(T). |
| T9.1 | A24/B22 | sound, conditional | yes | `Spine.lean:1874–1877,1895`: nonempty standard input gives exhaustive deletion/special/ordinary descent. No decrease is demanded on the empty self-loop. |
| T9.1a | A25/B23 | sound, conditional | yes; independently checked in Lean | `Spine.lean:1927`: converts seed/configuration and descent facts to `FinalHyps`; no packet invariant is lost or newly assumed. |
| MAIN / N5.1 | after A25/B23 | sound, conditional | yes; independently checked in Lean | Exact locked conclusion and Mahlo premise. See Q1; the abstract argument has a generic proof without `sorryAx`. |

### Weighted-chain-only nodes

| Node | B position | Statement judgment | Plan sufficient without new mathematics? | Evidence / consumer check |
|---|---|---|---|---|
| T3.2i | B9 | **unsound as a set of statements** | concrete address plan after fixing hypotheses | `U2.lean:559–671`: Q-material correctly has phase i−1, other material phase i. `num_phaseCol` is false on arbitrary records (BP-02). |
| T3.2m | B10 | sound-with-issues | substantial explicit case work | `U2.lean:715–730`: common κ fixes keys normalized at/below r. Context/query/restored/body first-change offsets must be exposed, but no separate missing mathematical principle was identified. |
| T3.2n | B11 | sound, conditional | yes | `U2.lean:733`: T3.2m's first-change alternatives imply S. Output A is not a premise, so this does not hide an A/S preservation cycle. |
| T3.2r | B12 | sound-with-issues | plausible detailed path case work | `U2.lean:744–773`: the reverse transfer concludes in decorated B, which is precisely what decorated-A preservation uses before capping equivalence. Unlike T3.8li, this application does not require a forward decorated-cap theorem. Low-head details remain high risk. |
| T3.2 | B13 | sound-with-issues | assembly yes | `Spine.lean:967–983`: separate V,I,H,S,A/P preservation, seeds and safe prefixes support generation induction. Supporting false helpers BP-01/BP-02 must be fixed. Successful-output decrease asks for V,I and nonempty input. |
| L4.3a | B14 | sound | yes | `U3.lean:442–457`: both stop and special owner must be strictly inside the marked height; `truncAfter a=F` makes the setHeight comparison valid. The old marked-entry deletion counterexample is excluded. |
| L4.2c | B15 | sound-with-issues; high risk | plausible after explicit move induction; not independently completed | `U3.lean:411–414`: source/target barriers, source-key raising and same-parent collapse are the right ingredients. See the detailed assessment below; moved-anchor crossing remains untested in my corpus. |
| L4.2 | B16 | sound, conditional | yes given L4.2c | `U3.lean:428–436`: path membership plus upward-cap legality yields precisely V,I,S,decorated A and ordinary branch needed downstream. |
| L7.5d | B17 | sound intended interface | yes after BP-03/BP-04 provider fixes | `U3.lean:893–930`: complete frame, origins, compatible charts, original prefix, query-size bound and readmission for every output above E are all present. See Q5. |
| L8.8f | B18 | sound, conditional | yes | `U5.lean:865–872`: if root≤host, labelled movement lowers the host; if root is inside the mark, preserve host/owner and capture a smaller owner. Every required `CapData` field is supplied in the contract. |

I did not accept the phrase “Fidelity: as in paper” as a proof. Most chain entries contain actual branch arguments or finite inductions. The material gaps are specifically the unprovided capped transport in BP-06/BP-07, the stale-address reasoning in BP-04, and the hidden witness/provider premises in BP-08/BP-09. Saying “as in T3.8li” in T3.8lb does not close T3.8li. Saying “by the construction” in L4.3d does not make that construction recoverable from its current existential theorem.

## Q5: independent assessment of the marked open arguments

### T3.8li and T3.2q

**Still unresolved; no counterexample to the intended projection conclusion.** `head_path` transports a path in `B` with `actualKeys B` to one in A with `actualKeys A`. Projection starts from the final test of a literal cap of B, whose strict containing heights have been shortened/capped, and needs decorated A for a literal cap of A. Those are different systems. `head_path_rev` goes in the other direction and does not repair the missing implication.

A sufficient added lemma should name an actual old cut `(a,k)`, its phase copy `(c,k)`, the two caps and their container paths, and the retained-prefix query. It should assert corresponding capped scan cursors before the first low head, permit deletion of low-head detours without changing the capped old-root response, and cover a cut inside a restored root height and a cut inside copied Q-material. Proving a theorem for an arbitrary reduced query would require more than the current argument supplies. I have not supplied a full proof of this strengthened invariant; the 21,208 passing projection instances are supporting diagnostics only.

### T3.8lo

**Still unresolved; no counterexample to the intended previous-root response.** The final A-test certifies an orbit ending at ρ. It does not certify the next response at ρ. `sign_indep` identifies comparison signs between appropriate phase images; it does not on its own prove the non-exhausted cursor or extend that stopped orbit.

A sufficient invariant is: after a low visit to head `s_h`, the full orbit at the actual finite cut query, with the allowed strict-container modifications, reaches `s_(h−1)` without dropping below it, and intermediate vertices have the corresponding non-exhausted old cursors. A body endpoint then has response at least `s_(h−1)≥r`; a head endpoint follows from the head-cursor law. The missing work is to supply the path-nesting bounds and show they survive every container truncation/cap. I could not close that step from the present cited contracts. The independent corpus contains 1,110 nontrivial previous-phase cases and no failure; this does not establish the invariant.

### L4.2c

**Plausible and considerably more explicit than the paper; retain as high risk until the move induction is explicit.** Internal edges transfer with paired source/target complete-cut barriers. In the low region the changed source height and truncated ancestors require `cursor_raise`; equality of old keys alone would be wrong. At the first edge from t, the target cap stops at query index j rather than at the anchor's final query entry, so both scans must first be compared with the common list ending in ⊤ at j.

For a moved anchor, carry through each prefix of the move list: current query column, current active container entry, backward origin of the compared column, equality of retained finite keys before the active entry, the finite-query/non-exhaustion bound, and equality of responses. A legal move replaces a same-parent block by its last active entry; `capped_block_resp` supplies the local equality. Compose these equalities while updating addresses. Closed off-route columns carry their old keys through the origin. This is a concrete route using the stated elementary scan laws, but it needs to be expressed with current addresses, as BP-04 requires. I do not identify a further independent combinatorial principle here, and I have not independently completed all cases.

One wording correction is advisable: step 4(b2)'s path starting at t cannot literally be on `T_H`'s own `resolve` stack, which contains only numbers strictly below t. Use the actual anchor copy of the target cut column inside query entry j as the viewpoint; T_H is visible there. The retained query is preserved by `admCap_query`. This is an ambient-address clarification, not a counterexample to `firstDiff_path`.

My direct bounded evidence covers 416,367 admitted same-host repair records with empty move list and no path failure. It does not cover moved-cap-anchor crossing. The separate scan corpus found only whole-end differences, so its large state count is **not evidence** for this branch.

### L7.5d with L8.8f

**No new semantic principle is missing after the finite providers are repaired.** `CapData` is genuinely a package of the needed facts, not just a name for the desired final theorem. In particular it includes both frame representatives, the original prefix and deleted resources, owner/host origins, chart compatibility/injectivity, `u<W`, strict query-size decrease, and repaired-output admission for every output above E.

The chart construction can use `nm=capChart pk` and `nmH=nm∘capRole w`. Compatibility is then definitional where origin exists. For injectivity, target-prefix values are below u, the marked owner is u, and copied internal source roles have values above u; these ranges are disjoint, while the charts are injective within each region. The repaired marked frame is proved by induction on moves at the current marked address. Entry-index movement does not alter printed numbers; ordinary and active-owner representatives both must be tracked. This supplies the missing detail behind “induction through the containers.”

In L8.8f's `p≤ρ` branch, positive iteration and DLab's moving clause lower the marked host; the original-prefix label contains the marked slot and both target heads, so those heads remain available at the moved values. Its low-value inequalities and negative block atom give a smaller failing packet. In the `p>ρ` branch, the root is inside the mark, so DLab preserves the old prefix/owner and second capture lowers the owner at the same host. These are the correct lexicographic decreases. This conditional argument does not fix the invalid U2 move providers or prove L4.2c for free.

## Other high-risk nodes

The following are outside the literal chains or are supporting subnodes not individually listed there. Risk is not itself a finding of falsity.

| Node | Risk and independent assessment |
|---|---|
| D3.3b | Continuation-hole word factorization; BP-01 is an actual failure. Other order-embedding/cancellation claims must retain the structural hypotheses when used. |
| D3.1d | Total origins versus actual occurrences; BP-03 is an actual failure. The stronger raw-prefix lemma needed by DLab is structurally plausible, as explained under BP-08. |
| D3.1e | Sequential cap moves; BP-04 is an actual failure of the static-address contract. This is the principal finite repair-interface risk. |
| L2.3a / L2.4a | Joint cut/return barrier induction and reverse capping. The plan uses the lexicographic `(c,k)` induction and a first-divergence argument, rather than simply assuming uncapped/capped equality. I found no new defect; this remains substantial finite proof work. |
| T3.2q | Low-head detours and actual/decorated query systems. Its exact forward/reverse domains must not be conflated; BP-06/BP-07 show where the available contract is insufficient. |
| T3.8li / T3.8lo | Projection and outgoing previous-root response; the two major unresolved invariants above. |
| L6.2e / L6.2f | Ordinary-stage and special-copy graph identities. Role order and structural atoms must be separated: an order edge can read a consumed role even when structural query atoms cannot. Exact-body bounded check results are recorded below; no finite sample proves these universal contracts. |
| L7.3 / L8.8a | Finite floor raising needs a limit owner. FIRM factorization gets this from actual source membership; BP-05 shows why the weaker wrapper fails. |
| L8.6a–j | Label support, off-support fixed values, moving clause, and sharing between stages. The bound only on `Λ.vars` is sufficient once every shared pre-stop name is shown to occur there. BP-08 is the missing provider premise, not a reason to assume all original E are standard. |
| N4.4 | Exact finite first-order translation, including empty/off-support cases. I accept the plan and independently checked the delicate limit binder expansion; implementing every semantic equivalence remains substantial. |
| N4.7 | Condensation's simultaneous predicate induction. The local step is mathematically specified; finite θ/τ transfer and locality avoid circularity. An order-only collapse would be too weak, but the plan supplies more. |
| L5.5c/d, L5.6, L5.8 (Part B) | Histories, Σ₁ condensation and complete certificate coding are much larger than routine reuse of Mathlib or an existing full-elementarity condensation theorem. This is implementation/mathematical-development risk, not a demonstrated contradiction; it strengthens the recommendation for Part C. |

## Q6: FIRM scope and consumer audit

The real finite vocabulary matches the prose's intended distinctions: actual versus decorated keys; complete cut queries; response paths rather than mere parent monotonicity; CondP separate from InL; original/query/retained occurrence maps; an admissible cap carrying ordered legal repairs and final InL. `Confined` protects survival of the marked entry. The explicit packet grammar allows the needed negative labels and does not assume unjustified global name disjointness.

The core semantic contracts also retain the necessary strength:

- `SStrict` quantifies over **admitted and valid** packets of the original target size. `Valid` alone is deliberately weaker; BP-05 arises from forgetting this distinction.
- `TargetAbove` puts every new active coordinate above the floor and every low resource. This is the conclusion readmission needs, rather than mere existence of an unrelated target configuration.
- `AllowedInput`/DCore retain the general-L empty-query case. DLab's cap branch retains the original E-prefix in the label, so deleted resources survive transport.
- DLab preserves all fixed variables, including off-support variables, and all pre-root main values; its positive-iteration moving clause is strong enough for L8.8f. To justify its support-only fixed bound, remove the unnecessary original-InL premise from the structural origin-prefix provider (BP-08). A prefix plus a closing slot, followed by legal subtree-retaining moves, supplies the needed origin fact even if discarded parts of E are invalid. Each old role has its own `lim` atom in `graph E`, so the label hypothesis puts its name in `Λ.vars`.
- `SpecialDesc` has the required prefix and floor bounds; `StrictDescent` has nonempty input/output guards; `FinalHyps` asks only for what the final ordinal induction uses.
- `Hier.Interface`'s finite-support inequalities still leave off-support fixed equations to be patched; they do not silently assume every value of an infinite valuation is bounded.

No core FIRM predicate was found contradictory, vacuous on its intended domain, or too weak for the final consumer. This does **not** rescue the false helper package. Restore actual occurrence/branch premises, the moving-address invariant, and factorization's membership premise; then recheck the callers. For L4.3d, expose the chosen truncation witness and its graph/role properties so later code need not extract facts from an opaque existential proof.

## Independent checks and their limits

All files mentioned here are in `scratch/codex/`; the production source, checks and blueprint files were not edited.

| Check | Coverage / result |
|---|---|
| Combined snapshot typecheck | Six files; exit 0 with expected admitted-proof warnings. `bp133f5d8/integrated-check.log`. |
| Missing computational bodies | Exactly the two order instances' proof fields and `Hier.jInterface`; `bp133f5d8/definition-audit.log`. |
| Independent final assembly | Exact concrete assembly plus generic order theorem, and leaf packaging; `bp-finalhyps-probe.lean/.log`. Generic theorem has no `sorryAx`. |
| Hierarchy probes | Limit formula binder semantics and large-index regularity lift; `bp-hierarchy-probe.lean/.log`. Both have no `sorryAx`. |
| Finite false signatures | BP-01–BP-03: `bp-finite-probes.lean`, appended snapshot `bp-finite-run.lean/.log`; BP-04: `bp-finite-moves.lean/.log`. Computed failed equalities and premise checks described above. |
| Packet countermodel | BP-05: `bp-packet-counterexample.lean/.log`; exit 0, with the imported-type axiom caveat explained above. |
| Independent admissible finite corpus | Seed 17017 sample of 1,200 independently generated standard states, word length≤24; operations n=0…3, ordinary outputs retained at length≤80. `bp-finite-corpus.lean/.log`, `bp-finite-corpus-result.json`. |
| Operation and ordinary invariants | 4,800 locked/paper pairs; 892 ordinary input/kernel cases; 2,639 ordinary outputs with InL/P/iterate checks; no failures. |
| Phase/body identities | 48,455 output-column classification/uniqueness checks; 20,637 coherent-data number identities; 15,396 template local-suffix identities; no failures. |
| Cofinality subcases | 31,672 upward InL template-cap instances; 1,110 previous-root response cases; 21,208 projected old-cap cases, including 882 Q-material cases; no failures. Repeated geometric cases from different phase/source tuples count separately. |
| Exact ordinary-stage graph identities | 892 stage-zero cases; 2,639 successor pairs at m=0,1,2, length≤80; 116,269 output-role instances and 168,772 structural converse atoms, plus all old/query/retained forward inclusions and shared-map identities; no failures. `bp-stage-probe.lean/.log`, `bp-stage-probe-result.json` (hashes and limits included). |
| Exact special-copy graph identities | 234 inputs, 702 outputs at n=0,1,2, length≤80; 20,484 role instances, 26,505 structural converse atoms, 3,171 block forward atoms and 25,026 frame instances; no failures. Same stage-probe artifacts. |
| Scan-record search | 29,839 standard states of length≤60, 458,643 upward already-in-L anchors with base length≤36; 505 strict scan records, all `wholeEnds`. **No capAt branch evidence** from this search. `bp-packet-finite.py/.json`. |
| Repair-record path search | 8,965 standard targets of length≤24, 1,821,660 proposed internal caps, 416,367 admitted repair-[] capAt records; no target actual-cut-chain failure. **Same-host/no-move only.** `bp-packet-repair-finite.py/.json`. |

The finite Lean tests evaluate the real snapshot bodies, not the lemmas they are testing. The separate Python record checks use the earlier independent immutable model/corpus. `#eval!` is needed for executable data whose order instances contain unfinished proof fields. Passing checks are **not proof**, and a large total does not imply coverage of a missing branch. In particular, neither moved-anchor crossing nor the semantic ordinal induction is validated by the finite record corpus.

## Required before G1

1. Correct BP-01–BP-05 and propagate the strengthened premises/invariants to their consumers. These changes repair false statements and cannot be deferred as ordinary proof filling.
2. Export the raw origin-prefix and child-truncation facts required by BP-08/BP-09. Make L4.2c's moved-anchor induction and viewpoint explicit.
3. Supply precise cap-sensitive transport/low-detour statements and mathematical arguments closing BP-06/BP-07, or keep those items expressly open and decline to freeze the blueprint as complete.
4. Choose Part C for D-4, then replace the placeholder interface by that proved construction during formalization. Keep its proof status separate from this design approval.
5. Re-typecheck the amended package and rerun the concrete regressions. Do not treat successful compilation with `sorry`, or passing bounded tests, as a substitute for resolving the stated counterexamples and missing arguments.

This review completes the requested blind assessment of the snapshot. It does not approve G1 at `133f5d8`.

STATUS: COMPLETE
