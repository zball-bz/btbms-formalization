# QUESTIONS FOR ROOT

1. **Nonblocking domain decision:** should the formalization identify the paper's operation with the default `BTBM.FS` **restricted to nonempty pointer-valid, internally legal expressions**, leaving the empty input undefined? I have assumed yes. The reference totalizes the empty input and has extra behavior on some raw expressions with internal empty columns; see X-01 and X-02. Neither difference changes the intended standard reachable set once closure is proved.

# Codex independent review

Reviewer: Codex. Paper: *BTBMS and finite Mahlo reflection*, 27 October 2026, 32 pages. Reference revision: `SmileLee-lyx/ne-rewritten@88df7989e270fe6eb447d7fd174d1c06ffc53cf0`.

I read all ten sections and checked every named lemma and the nontrivial intermediate claims inventoried below. I did not read `tracker/review/claude-review.md`, `tracker/ledger.json`, or `tracker/GAPS.md`, and did not coordinate with the other reviewer. All reviewer writes and executable copies are confined to this file and `scratch/codex/`. Internal audit subtasks are part of this Codex review, not consultation with the other reviewer. References of the form `paper.txt:LINE` mean `paper/paper.txt`; subsection numbers disambiguate the claim. Ambiguous extracted formulas were checked against rendered PDF pages, particularly pp. 3, 10, 13–14, 16–17, 19, and 21.

**Overall assessment:** I found no fatal flaw, no unrepaired substantive mathematical gap, and no counterexample to the main well-order claim on the intended standard domain. The argument appears sound at the level of an informal mathematical proof after the domain and hypothesis clarifications below. There are six findings: three repairable specification/hypothesis issues and three exposition/reproducibility issues. In particular, the unconstrained reading of “P implies S” is false, but its intended version with V, I, H is supported by the proof and is the version used later. I do not infer correctness from passing tests, and I do not equate this review with a formal verification.

The main formalization risks are substantial despite this assessment: the exact finite cap/cofinality transformations, the custom hierarchy's bounded checkers and history budgets, and admission of the transported joint packet in precisely the original class. The paper generally addresses the usual circularity and parameter-budget hazards explicitly; the audit below records those checks rather than treating every long proof as an unsupported assertion.

## Section verdicts

Here “sound” is an informal-proof verdict with the dependencies explicitly stated, not a claim that Lean has checked it.

| Section | Verdict | Reason and dependency |
|---|---|---|
| §1 | repairable gaps | Syntax, order, normalization, seeds, and both operations agree clause by clause with the default reference on the intended nonempty V,I domain. Raw-domain behavior needs X-01/X-02. |
| §2 | sound | Scan boundaries, path nesting, barriers, independent capping, and exact trace arguments survive the empty/equal/end-cut cases. Capping does not assume output A. |
| §3 | repairable gaps | Add the ambient V,I,H hypotheses to the profile lemma (X-03). With them, closure and the full generation-induction cofinality argument appear sound; actual cursor agreement and separate prefix cancellation are explicitly supplied. |
| §4 | repairable gaps | The record types and “confined operation” relation need the exact occurrence/retention fields in X-04. Under their intended reading, the first-difference and source-reduction proofs appear sound. |
| §5 | sound | The custom finite-generator hierarchy, history/hull/condensation and certificate arguments are coherent. They require construction in Lean, not an assumed black box. X-05 is wording only. |
| §6 | sound | The occurrence identity respects both representatives and same-forest pairs; Mahlo initialization follows from §5 and finite stationary/club choices, including m=0 and m=1. |
| §7 | sound | Conditional on the clarified finite records and §5. Complete prefixes, fresh names, full frames, both heads, and one jointly checked assignment supply the needed compatibility. |
| §8 | sound | Conditional on §§2–7. All scan signs, empty cases, copy-stage budgets, special-label restrictions, and both root positions in the least-failure argument are covered; the induction measures do not use the unproved syntax well-order. |
| §9 | sound | Closure, cofinality, seed configurations, and descent imply the entire standard well-order. The final recursion is set-sized; the configuration-minimum rank is legitimate. |
| §10 | could not evaluate | Its mathematical statement about the limits of finite checks is correct. The reported historical counts cannot be reproduced from the supplied accompanying material (X-06). They were not used to approve any lemma. |

## Findings

### X-01 — the empty-input operation differs from the reference API

- **Location:** `paper.txt:96`, §1.2; reference `BTBM.ts:235`–239, especially line 237; default wrapper `notation_utils.ts:220`–261.
- **Severity:** exposition.
- **Claim / issue:** the paper leaves the empty forest without an operation. The default reference returns the empty forest for every parameter. Thus literal equality of the two operations on their full raw domains is false.
- **Concrete instance:** with `E=[]` and `n=0` (also `n=2`), the paper has no `E[n]`; the actual copied reference returns `[]`.
- **Effect on the proof:** this is an API-domain mismatch, not a counterexample to well-ordering or to strict decrease on nonempty inputs. An empty self-loop adds no new reachable expression, so the two reachability definitions of Std coincide after the nonempty operations are identified.
- **Repair:** state explicitly that mathematical `E[n]` is the restriction of default `BTBM.FS` to nonempty inputs. Alternatively totalize `∅[n]=∅` and keep all strict-decrease/descent statements explicitly nonempty.
- **Confidence:** high.

### X-02 — terminal traversal is not defined for all raw forests of §1.1

- **Location:** `paper.txt:59`, §1.1; `paper.txt:98`–100 and `paper.txt:121`–129, §1.2; reference `BTBM.ts:105`–125, 235–288.
- **Severity:** repairable.
- **Claim / issue:** “otherwise follow last columns and last entries until the first empty height” silently needs nonempty internal columns, and visible-root lookup needs V. Raw syntax was introduced without those restrictions. Some raw forests therefore have no terminal entry of the asserted form even though the code returns an output.
- **Concrete instance:** in the paper's zero-based pair notation, `E=[[],[(0,[[]])]]`. Its only nonempty attached height is a one-column forest whose column is empty. The paper's route becomes stuck there rather than reaching an entry with empty height. The reference display is `(0)(1^(0))`; reference `FS(E,0)=[[]]`, and `FS(E,1)=[[],[]]`. This E satisfies V but violates I.
- **Effect on the proof:** the raw-domain specification is incomplete; this is **not** a counterexample on L or Std. The later V,I and closure hypotheses are enough to exclude it. Root lookup is likewise only justified when the last parent is visible and smaller than the stopping column.
- **Repair:** define a genuinely partial operation with an explicit legal-route/root condition, or declare V,I as its input domain and then prove the stronger V,I,A,S definedness lemma. Keep that domain statement separate from the proof that seeds and successors stay in it. Do not silently adopt the reference's extra behavior on I-invalid inputs.
- **Confidence:** high.

### X-03 — bare P does not imply S without the structural hypotheses

- **Location:** `paper.txt:254`–268, §3.1, especially the lemma statement at 263 and the direct-owner assertion at 266.
- **Severity:** repairable.
- **Claim / issue:** the short statement “P implies S” is missing the ambient V,I,H hypotheses used to make first-entry branches pure normalized owner towers. The preceding definition itself invokes H when asserting that the terminal maximal-parent heights are empty. If the implication is read over all raw syntax, it is false.
- **Concrete counterexample:** let `∅=[]`, `K=[[(2,∅)]]`, `J=[[(3,∅)]]`, `H=[[(0,K)],[(1,J)]]`, and `E=[[],[(0,H)]]`. The outer nonempty column has number 1; H's columns have numbers 2 and 3; K's column has number 3 in its own scope; J's column has number 4. Every parent is visible and smaller, and all nonempty columns are singletons, so V and H hold. Every owner return satisfies P: the nonempty return to owner 1 has `π(J)=(0,1)<(1,1)=π(H)`, and the other returns have empty heights. But `h_3(J)` starts with the true relative field `(1,0)`, while `h_1(H)` starts with the false field `(0,0)`, so `h_3(J)>h_1(H)` and S fails. I fails at H's first column, whose parent 0 is below owner 1. The independently written predicate checker also verifies this example.
- **Effect on the proof:** the unconstrained lemma statement is false. The intended V,I,H version is not refuted; its pure-tower comparison proof is sound and is the version required by the cap argument. This does not establish a counterexample in Std.
- **Repair:** state `V ∧ I ∧ H ∧ P ⇒ S`, and make V,I,H standing hypotheses for the profile construction and greatest-cap comparison. State the subsequent cap/repair conclusions separately with their decorated-A assumptions.
- **Confidence:** high for the counterexample and needed premise; medium that a reader would otherwise interpret the short statement as deliberately unconstrained rather than shorthand.

### X-04 — admitted records and confined reductions need exact occurrence predicates

- **Location:** `paper.txt:647`–658 and `paper.txt:664`–686, §4; `paper.txt:688`–695 and `paper.txt:724`, §4; downstream uses at `paper.txt:1127`–1167, §7.3 and `paper.txt:1393`–1470, §8.5.
- **Severity:** repairable.
- **Claim / issue:** the proof quantifies over “precisely” three finite record types, but their compact declarations do not give all their occurrence/scan compatibility equations. In particular a scan record must identify which closed root height and which query member are being compared, their actual raw scan state/anchor, their embeddings into the original target context, and which pre-entry context is retained by a descendant record. “Confined to the marked source” must also include retention of the marked outer entry, not merely that the terminal column is somewhere inside its height. These data are used by the complete-query barrier, the first-difference transfer, and the exact packet readmission.
- **Concrete boundary example:** in `L_2=[[],[(0,[[(1,∅)]])]]`, mark the outer entry at column 1. The terminal column lies inside its height, but a special step with parameter 1 replaces the marked entry by two shortened entries. It is therefore not an operation preserving that one marked occurrence and owner. This does not contradict the intended “confined” statement; it shows why the phrase must exclude a step whose special replacement reaches the marked slot.
- **Effect on the proof:** this is an under-specified quantified record predicate, **not** a demonstrated counterexample to the intended finite or semantic theorem. The later prose supplies much of the intended information, and the proper-child reduction explicitly puts the special owner strictly inside the marked source. I found no failure after reading those constraints into the records. A looser Lean structure would nevertheless state a different theorem.
- **Repair:** define constructors with explicit original/current occurrence maps; actual scan indices and source/query projection equations; retained marked-entry and pre-entry-context equations; and a finite repair list with surviving-role injection and deleted-block data. Define a confined operation by the survival of the marked occurrence and its prefix/frame. Prove preservation for those exact constructors before using them in S_n. The two addresses `b_0` and `b_m`, and original target B versus B_good, must remain distinct fields.
- **Confidence:** medium as a mathematical exposition gap; high as a formal specification obligation. No claim that the final theorem is false.

### X-05 — “contains the whole J_b” must mean membership, not inclusion

- **Location:** `paper.txt:864`–866, §5.2.
- **Severity:** exposition.
- **Claim / issue:** the control hull “contains the whole J_b.” The required statement is `J_b ∈ H`, obtained from `b ∈ H` by the canonical history function. It cannot mean `J_b ⊆ H`.
- **Concrete consistency check:** if `a<b` and `J_b⊆H`, then `H∩J_b=J_b`, contradicting the defining trace equation `H∩J_b=J_a`. With `J_b∈H`, there is no contradiction; bounded relativization to that set gives `H∩J_b ≺ J_b` and hence `J_a≺J_b`.
- **Effect on the proof:** the following sentence already indicates the correct element meaning. This is not a flaw in the condensation or transport argument.
- **Repair:** write `J_b∈H` explicitly, followed by the relativized Tarski–Vaught inference.
- **Confidence:** high.

### X-06 — the reported supplementary programs are not supplied here

- **Location:** `paper.txt:1516`–1534, §10.
- **Severity:** exposition.
- **Claim / issue:** the text refers to accompanying Python implementations and reports exact finite counts. No corresponding paper-check programs, version identifier, invocation, or captured output are supplied in the paper/reference/script materials available for this review. `scripts/fetch-reference.sh` only fetches reference notation files.
- **Concrete reproducibility limitation:** I could execute independent tests against the copied TypeScript source, but could not run the claimed 50,001-state/131,988-graph/350,387-cap experiments from the supplied artifacts. Independent experiments with different counts do not reproduce those claims.
- **Effect on the proof:** unavailable empirical evidence, not evidence that the reported counts are false. Section 10 correctly says that those computations prove no universal lemma or set-theoretic assertion; the mathematical verdict does not depend on them.
- **Repair:** supply the exact scripts, revision/hash, command lines, limits, and outputs, or remove “accompanying” and identify the computations as unavailable supplementary material.
- **Confidence:** high about the supplied material and inability to reproduce; no judgment on whether the historical runs occurred.

## Claim inventory

Each line is a definition, lemma, or substantive inference in textual order. The inventory records what was checked; its entries are not additional finding IDs.

- `paper.txt:38`, Scope: the ambient theory is ZFC plus one n-Mahlo cardinal for each finite n, and the conclusion concerns all of Std.
- `paper.txt:41`, Scope: finite syntax/column/generation induction, finite target-size induction, and least actual ordinal pairs are the permitted measures; none presupposes the BTBMS well-order.
- `paper.txt:45`, Scope: occurrence identity is separate from printed number and address; copies create new occurrences and retained occurrences survive address changes.
- `paper.txt:48`, Scope: closure, cofinality, seed configurations, and strict configuration transport are the four obligations used for the final well-order.

### §1

- `paper.txt:59`, §1.1: finite mutually recursive forest/column/entry syntax; empty forest distinct from one empty column.
- `paper.txt:62`, §1.1: recursively defined entry and list lexicographic comparisons give a computable linear order; no well-foundedness is assumed.
- `paper.txt:65`, §1.1: absolute column numbers and scoped visibility uniquely identify each visible occurrence.
- `paper.txt:71`, §1.1: V requires a visible strictly smaller parent.
- `paper.txt:72`, §1.1: I requires every internal-height column nonempty, with first parent at least its owner.
- `paper.txt:74`, §1.1: H requires nonincreasing column entries.
- `paper.txt:75`, §1.1: host normalization h_a, with one threshold at all descendant depths, preserves and reflects order.
- `paper.txt:86`, §1.1: T shifts all parents at least r; A does that shift while replacing exactly one terminal-route column and never shifts the inserted forest.
- `paper.txt:96`, §1.2: empty-input undefinedness and deletion of an empty final outer column.
- `paper.txt:98`, §1.2: terminal route, stopping prefix Q, root r, depth ℓ, and column-number sum formula.
- `paper.txt:109`, §1.2: special-step criterion and repetition count n+ε, retaining/truncating strict containers.
- `paper.txt:121`, §1.2: visible-root lookup and raw two-cursor normalized-height scan, advancing both cursors at equality.
- `paper.txt:125`, §1.2: ordinary expansion loop, head query shift, unchanged restored outer parents, restored-height phase shift, body versus owner-root continuation insertion.
- `paper.txt:129`, §1.2: owner-root branch needs a nonempty unconsumed suffix.
- `paper.txt:132`, §1.2: outer replacement and zero-parameter deletion of the entire stopping column.
- `paper.txt:139`, §1.3: seeds L_m and Std as finite defined-operation descendants, with finite generation witnesses.
- `paper.txt:143`, §1.3: compact word w and size μ, with separate first-entry/continuation markers and no closing tokens.
- `paper.txt:147`, §1.3: w is injective and an order embedding.
- `paper.txt:152`, §1.3: safe word prefixes close containers and cannot create an empty internal column.

### §2

- `paper.txt:157`, §2: decreasing-stack reduction ν and reduced column boundaries B_c(i).
- `paper.txt:163`, §2: boundaries strictly increase, including equal-letter appends.
- `paper.txt:165`, §2: scan-boundary lemma, including exhaustion and invariance of final source cursor under query reduction.
- `paper.txt:177`, §2: g_W response and reflexive/transitive ancestor paths; V makes nontrivial edges numerically decrease.
- `paper.txt:185`, §2: A tests each parent from predecessor column/previous parent at its pre-entry boundary; A implies parent monotonicity.
- `paper.txt:194`, §2: path nesting replaces each larger-query edge by a smaller-query path by induction below the source column.
- `paper.txt:201`, §2: owner returns, strict relative-height condition S, and class L=V∧I∧H∧A∧S.
- `paper.txt:205`, §2: barrier bounds returning-entry boundaries and all complete-cut reads of active owners, including final cuts.
- `paper.txt:211`, §2: auxiliary reduction observation preserves W<D after appending J below the final key of D.
- `paper.txt:214`, §2: simultaneous descendant-column/entry induction proves the return and complete-cut barriers.
- `paper.txt:220`, §2: independently capped terminal-route last keys are formal top keys without changing children; no own entry query contains a capped last key.
- `paper.txt:223`, §2: under V,S, A is equivalent before and after any independent selection of those caps.
- `paper.txt:224`, §2: V,I,A,S imply all nonempty fundamental operations defined, by strict owner-root nonexhaustion.
- `paper.txt:237`, §2: a common strictly increasing key map preserves exact raw cursor traces.
- `paper.txt:239`, §2: capping an unconsumed final source key preserves the full trace.
- `paper.txt:240`, §2: equal prefix and equal signs at a potentially changed source entry preserve traces ending at/before that entry.
- `paper.txt:247`, §2: agreement for more atoms than a query-height length gives identical strict comparison signs; normalization preserves positions/lengths.

### §3

- `paper.txt:254`, §3.1: first-entry-tower profile π, its terminal maximal-parent multiplicity, and owner-return profile condition P.
- `paper.txt:261`, §3.1: literal caps and upward caps, discarding all later context.
- `paper.txt:263`, §3.1: profile separation implies S via comparison of normalized pure first-entry towers (ambient V,I,H required).
- `paper.txt:269`, §3.1: greatest legal upward literal cap Γ(J), obtained by increasing terminal multiplicity, is at most H when π(J)<π(H).
- `paper.txt:279`, §3.1: upward caps satisfying V,I inherit S from the profile bound and strictly enlarged containing heights.
- `paper.txt:283`, §3.1: move an H-violating active entry to the first smaller same-parent height; interval lemma preserves the exact internal cap.
- `paper.txt:290`, §3.1: decorated same-parent block contraction preserves returned parents and A tests; finitely many outer moves produce an L cap with the same final parent/internal cut.
- `paper.txt:301`, §3.2: L is closed under safe prefixes and all operations; P is preserved; Std⊆L∩P; every defined nonempty V,I operation strictly decreases.
- `paper.txt:304`, §3.2: two first-change-position word inequalities, invariant under common embeddings.
- `paper.txt:308`, §3.2: containment offsets preserve S for safe prefixes, then independent capping preserves retained A and enables uncapping.
- `paper.txt:313`, §3.2: safe-prefix decreases cannot increase profiles; changed pure-tower profiles preserve strict owner-return separation.
- `paper.txt:318`, §3.2: exhaustive four-class classification of ordinary output occurrences, including closed side heights with numbers beyond t.
- `paper.txt:331`, §3.2: normalization/shift identity h_(x+jd)(τ_j H)=κ_j(h_x H), κ_iκ_j=κ_(i+j), ν-commutation and root-key fixedness.
- `paper.txt:337`, §3.2: A makes first-parent edges a preorder forest; path nesting puts every body column in the root subtree.
- `paper.txt:341`, §3.2: matching shifts and the empty-internal-query case establish V,I after ordinary expansion.
- `paper.txt:345`, §3.2: query/restored parent separation, copied H, and the first changed terminal comparison establish output H and strict decrease.
- `paper.txt:350`, §3.2: exhaustive origin classification of owner returns, with only the first following query able to return to a shifted owner.
- `paper.txt:363`, §3.2: transport by κ and containment-offset word inequalities prove S without using output A.
- `paper.txt:367`, §3.2: classification of changed first-entry profiles proves P for positive ordinary outputs; no-head outputs are safe prefixes.
- `paper.txt:377`, §3.2: capped-root cursor interval and exact reset ν(Z⌢[K_c])=B_c, iterated through the restored suffix.
- `paper.txt:386`, §3.2: low/high head scan split and high cursor formula m+γ−c, including exhaustion.
- `paper.txt:390`, §3.2: low-head substitution repeatedly reaches an earlier head or fixed old root/prefix; head index is the terminating natural measure.
- `paper.txt:395`, §3.2: starts/endpoints for each of the four occurrence classes transfer A; established S then permits uncapping.
- `paper.txt:404`, §3.2: special-step V,I,H, strict decrease, sibling-scope S, and P preservation.
- `paper.txt:410`, §3.2: capped same-parent repetitions preserve A; seeds have reflexive ancestry and strictly shorter return profiles; generation induction proves standard admissibility.
- `paper.txt:421`, §3.3: ordinary one-period kernel F_H, terminal context C_H, iteration formula, and positive-length prefix plus fixed letterwise embedding representation.
- `paper.txt:427`, §3.3: kernel success iff an iterate covers, downward success, explicit q|P|>μ(Y) bound, and full one-column-cut success.
- `paper.txt:438`, §3.3: frozen-cursor filling, root restriction, Q⋄X, and exact filling identity (1), with owner-root insertion shifted once and no rescan.
- `paper.txt:448`, §3.3: separate prefix deletion and two encodings e_0/e_1 yield identity (2); only equal ε encodings are compared.
- `paper.txt:459`, §3.3: conditional cap completion first repairs to L and gets success by assumed cofinality for the same target; reversed repairs compare suffixes Y_i≥Y_j.
- `paper.txt:466`, §3.3: three moved-host/root cases give identical kernels or exact actual-cursor agreement, using the owner bound c≤i and trace facts.
- `paper.txt:476`, §3.3: completed safe truncations properly extend, rooting does not delete the decision, and filling transfers success backward through every repair.
- `paper.txt:482`, §3.3: delayed-change lemma proves L′>R′ from agreement before the inserted last target atom and a strict decrease on the right.
- `paper.txt:490`, §3.4: cofinality for Std target and arbitrary L upper expression, with strict positive cover and n≤μ(B)+1 for a nonempty final column.
- `paper.txt:495`, §3.4: easy deletion/first-approximant cases reduce ordinary cofinality to successful upward literal caps.
- `paper.txt:500`, §3.4: no I-legal intermediate height lies between C and C plus the least new internal column; enough special repetitions strictly cover.
- `paper.txt:504`, §3.4: generation induction handles seeds, safe prefixes, special outputs, and full containing cuts.
- `paper.txt:511`, §3.4: ordinary generated target reduces to caps between A[n] and A, classified as body, closed-height, or head cuts.
- `paper.txt:520`, §3.4: projection of proper current roots, head roots, original-root stopping paths and below-root endpoints; low-head detours terminate and delete to the old path.
- `paper.txt:531`, §3.4: truncated restored origins retain cursor ≤c≤u; copied-query-height cuts project; old barriers give V,I,decorated A and ordinary upwardness, allowing cap completion.
- `paper.txt:542`, §3.4: proper current-root kernels are conjugate and use downward success.
- `paper.txt:547`, §3.4: current-head high scans have exact cursor m+γ−c after nonexhaustion checks; low scans win at the first restored parent.
- `paper.txt:553`, §3.4: previous-phase-root case has phase-independent scan signs, all positive heads low, and an immediate restored-parent win.
- `paper.txt:564`, §3.4: below-original-root and original-root cases separately establish actual cursor agreement using capped-owner and long-prefix sign facts.
- `paper.txt:572`, §3.4: shift composition identity (3) and restricted inverse phase map on already-cancelled remainders.
- `paper.txt:577`, §3.4: closed-side targets use completed-prefix extension and separate cancellation to establish strict kernel success.
- `paper.txt:585`, §3.4: direct-body target filling identities and four remainders (4); terminal rooting survival and delayed-change lemma give success even at zero remaining periods.
- `paper.txt:606`, §3.4: cuts inside a head's query part project to old-terminal caps and use downward success.
- `paper.txt:613`, §3.4: exact seam cap identity H[q]=A[i−1+q]; smaller closing roots cannot be upward on the complete-cut path.
- `paper.txt:621`, §3.4: restored-suffix head cuts reset to B_(w−1), force a below-root closing parent, and preserve the actual selected-root source cursor using query reduction.
- `paper.txt:628`, §3.4: mixed prefixes are deleted separately before inverse phase; four remainders (5), surviving old terminal and delayed change establish success.
- `paper.txt:642`, §3.4: occurrence/root cases exhaust all ordinary upward caps, completing generation induction and cofinality.

### §4

- `paper.txt:647`, §4: fixed original marked target versus marked current source in a truncated admissible context; target need not be independently standard.
- `paper.txt:650`, §4: scan record names ordinary anchor, complete terminal query, actual source index and strictly ordered closed retained source/target heights.
- `paper.txt:653`, §4: descendant record retains anchor/pre-entry context and admits an admissible decreased source height.
- `paper.txt:655`, §4: repair record stores same-host explicit same-parent moves and deleted blocks; records assert no future realizability.
- `paper.txt:664`, §4: recorded relative first parent/entry difference supplies an ordinary upward target-context cap with V,I,A,S and closing parent on the actual complete-cut chain.
- `paper.txt:667`, §4: scan-record common prefixes transfer internal paths; false-parent interval exclusion and barrier/path nesting handle exits through source/target hosts.
- `paper.txt:675`, §4: descendant-record external keys can first be raised to anchor values and unread entries restored; current barriers protect the path until the external identification is justified.
- `paper.txt:680`, §4: repair-record parent responses transfer paths; upwardness supplies I and ordinaryness; barriers and profile safety give A,S.
- `paper.txt:687`, §4: source reduction is closed under confined safe prefixes/operations; repaired caps yield larger marked targets; proper-child prefix differences admit strict source reduction.
- `paper.txt:697`, §4: repair cannot occur inside the already-H internal cap; interval comparisons give B≤B_good through every moved ancestor.
- `paper.txt:705`, §4: all terminal-query heights belong to the original target and satisfy N(J)+2≤N(B), independently of B_good.
- `paper.txt:714`, §4: actual operation keeps the marked entry; outputs above E must have B′>B_good≥B; cofinality supplies a positive output above E.
- `paper.txt:718`, §4: extra proper-child column is truncated to an empty-height first entry; earlier-root ordinary or direct-owner special expansion leaves a smaller source still above B.
- `paper.txt:729`, §4: whole-target prefix endings need no source operation; the listed first-difference cases exhaust finite syntax.


### §5.1

- `paper.txt:735`, §5.1: coordinates are limit ordinals greater than ω; if v<u and u is limit, v+ω≤u.
- `paper.txt:739`, §5.1: finite operation family B, Kuratowski pairs, right-associated tuples, and fibre notation.
- `paper.txt:749`, §5.1: every B-generator has a bounded graph.
- `paper.txt:751`, §5.1: definition X⁺ and one-stage closure S(X).
- `paper.txt:755`, §5.1: S preserves transitivity; pair/triple/wrapper/fibre outputs supply every member required for transitivity.
- `paper.txt:760`, §5.1: the graph of S is bounded in its input and asserted output.
- `paper.txt:761`, §5.1: transfinite hierarchy J₀=∅, Jξ₊₁=S(Jξ), continuous at limits; nonzero limit levels are transitive and B-closed.
- `paper.txt:768`, §5.1: each fixed first-order truth table over a whole transitive set T is produced by finitely many B-operations.
- `paper.txt:775`, §5.1: one bounded verifier handles variable finite formula codes, parses, assignment sets, and subformula tables; parse-tree induction proves correctness and uniqueness.
- `paper.txt:779`, §5.1: bounded-formula truth is absolute between a transitive parameter-containing set T and the universe.
- `paper.txt:781`, §5.1: finite truth-table constructions collect unordered-pair families and fibre families on T.
- `paper.txt:787`, §5.1: B_T bounds all members of generator values on T.
- `paper.txt:792`, §5.1: incidence relations and their fibres collect every generator value, constructing S(T) in any larger transitive B-closed level containing T.
- `paper.txt:799`, §5.1: at nonzero limits λ, Ord∩Jλ=rank(Jλ)=λ and |Jξ|≤max(ℵ₀,|ξ|); proof by finite arities, ω-block rank induction, and continuity.
- `paper.txt:808`, §5.1: history/hull lemma asserts global single-valued Σ1 J-map, history through ξ in Jξ+ω, compatible canonical partial Σ1 Skolem functions, elementary/monotone/continuous hulls, and their cardinal bound.
- `paper.txt:814`, §5.1: bounded history checker plus external recursion gives uniqueness.
- `paper.txt:816`, §5.1: production-code decorated histories define a unique end-extending well-order; finite lexicographic products are well-orders.
- `paper.txt:821`, §5.1: at ω-block boundaries, shorter histories lie internally; fixed-formula table construction gives the next history/order within the ξ+ω budget.
- `paper.txt:827`, §5.1: each global-order predecessor set I_x is stage-independent and belongs to every closed limit level containing x.
- `paper.txt:830`, §5.1: uniform bounded validity predicate V for Σ1 witness records; every genuine local witness has a local V-record.
- `paper.txt:833`, §5.1: least V-record in the canonical global order has a Σ1 definition and agrees across limit levels on common domains.
- `paper.txt:839`, §5.1: closure under the canonical functions is Δ0 then Σ1 elementary; countably many finitary functions yield size, monotonicity, and increasing-union continuity.
- `paper.txt:842`, §5.1: condensation: a Σ1 elementary H⊆J_C collapses to Jδ, with limit ω<δ≤C, and whole J_u collapses to Jπ(u).
- `paper.txt:844`, §5.1: reflected symmetric-difference witnesses make H extensional; Foundation gives well-foundedness; collapse N is B-closed, contains ω, and has limit ordinal height δ>ω.
- `paper.txt:848`, §5.1: reflected genuine histories establish Jδ⊆N.
- `paper.txt:850`, §5.1: reflected stage-membership witnesses establish N⊆Jδ; the inverse collapse increases ordinals and whole-level transport follows from history uniqueness.

### §5.2

- `paper.txt:860`, §5.2: definition R(C,b,a) by canonical hull trace and J_b≺Σ1J_C.
- `paper.txt:864`, §5.2: control edge implies full J_a≺J_b via J_b∈H and bounded relativization.
- `paper.txt:867`, §5.2: environment restriction preserves R; environment extension preserves R when J_C≺Σ1J_D.
- `paper.txt:872`, §5.2: control collapse fixes J_a, maps b↦a, and has height a<δ≤C.
- `paper.txt:874`, §5.2: finite diagrams and complete certificates include histories, truth tables, assignments, sharing, and separately budgeted auxiliary records.
- `paper.txt:878`, §5.2: complete certificates have a bounded checker; existence is Σ1; maximum v gives Jv+ω certificate budget.
- `paper.txt:882`, §5.2: uniform local Σ1 satisfaction and canonical hull membership are expressible by bounded-in-level witness/evaluation records.
- `paper.txt:891`, §5.2: fixed first-order formulas express elementarity and hull trace; the top level is an ambient tag, never an element parameter of itself.
- `paper.txt:900`, §5.2: histories/tables/finite packing give the claimed budget; passing certificates prove genuine levels and true assertions.
- `paper.txt:909`, §5.2: capture under J_a≺Σ1J_b with fixed parameters in J_a places all captured coordinates below a.
- `paper.txt:912`, §5.2: control transport reflects one joint existential record into the hull and collapses it, preserving checked relations, genuine levels, and explicit sharing, then captures the resulting problem into J_b.

### §6.1

- `paper.txt:923`, §6.1: ordinary/slot roles and visible representatives O(p), P(p), with stack replacement/restoration.
- `paper.txt:927`, §6.1: expression graph Γ(E) has both R-head edges per entry, Lim labels, global strict reading order, and consecutive ordinary pairs only within each forest; configurations are satisfying assignments.
- `paper.txt:935`, §6.1: ordinary-step role sets R,T,N,Q,K,D,P and consumed closed root blocks.
- `paper.txt:941`, §6.1: retained edges read only D; query edges only D∪{T}∪Q; removing closed siblings creates no new cross-forest ordinary pair.
- `paper.txt:944`, §6.1: occurrence-map identity defines q_{m+1}, f_{m+1}; n append stages yield Γ(E[n]).
- `paper.txt:958`, §6.1: stack substitutions commute with syntax shifts; the rightmost hole is inserted once; entering ordinary pair uses f_m, retained pairs f_{m+1}; zero is restriction.
- `paper.txt:965`, §6.1: persistent original-occurrence injection ι_m differs from latest-copy map f_m and must be used by old labels.

### §6.2

- `paper.txt:971`, §6.2: finite Mahlo classes M₀ and M_{n+1}, and the explicit large-cardinal axiom.
- `paper.txt:976`, §6.2: every uncountable cardinal λ is a Σ1 elementary J-height below every higher limit u, using small hulls and condensation.
- `paper.txt:984`, §6.2: for uncountable regular λ and higher limit u, a club Cλ,u supplies every R(u,λ,a); regularity bounds hull traces and provides closure points.
- `paper.txt:1000`, §6.2: seed graph edges and top choice a_m∈M_{m−1}, u_m=a_m+ω.
- `paper.txt:1006`, §6.2: downward stationary/club selections provide all seed roles; L₀ uses ω·2.

### §7.1

- `paper.txt:1018`, §7.1: immutable occurrence names/instance tags, injective charts, explicit overlaps, and separate private-chart orders.
- `paper.txt:1022`, §7.1: complete prefix P(F,e) ends immediately before the marked slot and need not itself be admissible syntax.
- `paper.txt:1024`, §7.1: full external frame and parent selectors, including unused visible representatives.
- `paper.txt:1028`, §7.1: positive/free attached blocks and floors; positive block includes both target heads.
- `paper.txt:1034`, §7.1: independent bounded target checker Cert_B; certificate/max-budget equivalence; bounded negative predicate No_B(U; frame,L).
- `paper.txt:1045`, §7.1: six source-packet components, including complete original target prefix, full source context, auxiliary labels, one shared assignment, both heads at u, and one joint low certificate in J_u.
- `paper.txt:1054`, §7.1: cross-host versus same-host frame identifications; u, its private height, and whole J_u are excluded from its low certificate.
- `paper.txt:1061`, §7.1: shared projections and labels are bounded checks on one assignment; whole-record transport preserves them.

### §7.2

- `paper.txt:1068`, §7.2: factorization raises a floor so every fresh target certificate is compatible with unchanged low resources.
- `paper.txt:1070`, §7.2: continuity supplies a stage for the low record; fresh names and a floor above all old coordinates establish all union atoms.
- `paper.txt:1078`, §7.2: low records and genuine stage history have a new-owner budget; resource-preserving failure implies No_B at the raised floor.
- `paper.txt:1082`, §7.2: joint cap lemma keeps original marked owner u, gives u<W<C, and permits genuine J_u and already-true bounded labels in the pre-stop JW certificate.
- `paper.txt:1087`, §7.2: matched relative syntax identifies internal stacks, external false parents, true parents, and closing head edges.
- `paper.txt:1093`, §7.2: union of original target prefix and corresponding source roles realizes the cap; finite max and whole-level budgets prove joint certification.
- `paper.txt:1100`, §7.2: outer repairs preserve marked host/owner/frame and retained names/values; repaired prefix injects into original target prefix.
- `paper.txt:1107`, §7.2: same-parent deletion leaves the visible stack and existing graph atoms unchanged; deleted blocks keep their old auxiliary low certificate.
- `paper.txt:1115`, §7.2: composed surviving-role injection, finite repacking, and floor increase preserve the negative predicate.
- `paper.txt:1118`, §7.2: source reductions preserve packet admission; subsidiary query children retain their original target occurrence and size bound, while current address is separately recorded.

### §7.3

- `paper.txt:1127`, §7.3: scan admission inputs are transported full pre-stop chart, new positive query at ρ, and a fresh closed source bank sharing exactly the pre-root chart and new root.
- `paper.txt:1138`, §7.3: fitted-prefix maxima L_j, original positive-prefix maxima C_j, bound invariant (17), and both target heads give a complete strict-source packet.
- `paper.txt:1146`, §7.3: full source/target prefixes include consumed root blocks and entering ordinary pair, at the current cap address.
- `paper.txt:1154`, §7.3: common assignments and finite maxima produce one joint low certificate; transient fitting certificates are not automatically retained as resources.
- `paper.txt:1161`, §7.3: source and target cursor advances preserve admitted-prefix structure whenever updated bounds hold; original positive query remains an independent candidate.

### §8.1

- `paper.txt:1172`, §8.1: target-size N(B) and strict-source assertion S_n quantify original standard target, admitted record, complete source packet, all floors, and all already-budgeted low resources.
- `paper.txt:1181`, §8.1: induction cycle S_{<n}⇒W_{<n}⇒D_{<n}⇒S_n; precise input restrictions for W and D, including unrestricted admissible empty-query inputs.
- `paper.txt:1190`, §8.1: any nonempty block's owner is Σ1 elementary below every private coordinate, by first-parent V/I, forest pairs, and entry edges.
- `paper.txt:1201`, §8.1: two-candidate lemma produces a free block simultaneously no larger in owner or maximum than either candidate, using capture if the minimizers differ.
- `paper.txt:1211`, §8.1: S₀ follows from first-source-column owner elementarity, factorization, limit-coordinate capture, and head restriction.

### §8.2

- `paper.txt:1217`, §8.2: source/query keys, owner/max reading inequalities, independent positive candidate, and initial (17).
- `paper.txt:1224`, §8.2: x_i<y_j advances only source, preserves bounds, and never needs a strict-source call.
- `paper.txt:1227`, §8.2: x_i>y_j either reuses a sufficiently low positive target block or transports both heads to u_i and applies the smaller S-index.
- `paper.txt:1235`, §8.2: x_i=y_j identifies the same free problem, adds unused frame fields, applies the two-candidate lemma, restricts positive heads, and advances both cursors, including empty equal heights.
- `paper.txt:1242`, §8.2: decreasing remaining cursor count terminates; source nonexhaustion forces complete query exhaustion; the final max is below final owner, with empty query immediate.

### §8.3

- `paper.txt:1251`, §8.3: ordinary R(C,W,p) control edge and joint pre-stop label/resource budget; no circular certificate containing its own external top value.
- `paper.txt:1259`, §8.3: fixed pre-root/low parameters and separating floor η, with explicit rules for which coordinates must exceed η.
- `paper.txt:1264`, §8.3: copy-stage invariant keeps latest root p and latest retained copy at original values, while the whole earlier graph/labels are certified in JW.
- `paper.txt:1268`, §8.3: fresh full reference chart shares D, includes consumed blocks under fresh names, and joins the old certificate.
- `paper.txt:1273`, §8.3: temporary old positive query at W, genuine JW, history, and w_old fit in JC; complete Σ1 state includes w_old∈J_t and every sharing/inequality condition.
- `paper.txt:1283`, §8.3: control transport W↦p and capture into JW put old main/reference data below p and its certificate in genuine Jp, while leaving a positive query above p.
- `paper.txt:1288`, §8.3: empty K is immediate; ordinary/active first retained role v yields Jv≺Σ1JW and captures the entire existence problem into Jv.
- `paper.txt:1295`, §8.3: closed first owner uses original closed bank through the final unconsumed cursor and W_{<n}, with all admission data; empty query needs no standard anchor.
- `paper.txt:1306`, §8.3: restore retained K at original values; query reads preceding transported copy; the union is exactly G_{m+1}; labels use persistent ι, and finite certificate repacking closes the stage invariant.
- `paper.txt:1312`, §8.3: ordinary parameter zero uses restriction.
- `paper.txt:1313`, §8.3: marked host/owner/frame and all labels follow persistent original-occurrence projections; nonfixed hosts at/after the root move below p, whereas allowed pre-root data may be fixed.

### §8.4

- `paper.txt:1325`, §8.4: special stop gives J_s≺Σ1J_W and an original positive shortened block certified in JW.
- `paper.txt:1329`, §8.4: floor includes all retained/fixed low data; capture quantifying the old owner yields a fresh positive copy entirely below s.
- `paper.txt:1334`, §8.4: finitely many floor raises and captures produce exactly n+ε sibling copies, all below s<W; zero copies retain the prefix.
- `paper.txt:1343`, §8.4: only already-Js-budgeted labels avoiding new private roles stay fixed; whole Js cannot be fixed as a parameter of capture into Js; strict containers retain their names/frames.

### §8.5

- `paper.txt:1349`, §8.5: choose a failing S_n packet of least actual ordinal pair (ρ,u), justified by bounded Separation without a syntax well-order.
- `paper.txt:1353`, §8.5: factorization produces β<L*<u, low certificate in Jβ, and No_B(Ju; frame,L*), with Ju only an external parameter at this stage.
- `paper.txt:1357`, §8.5: whole target ending first gives a positive source-prefix witness, captured along the owner path into Ju, contradicting failure.
- `paper.txt:1364`, §8.5: proper child ending first uses source reduction plus empty-query ordinary or limited-label special descent, retaining fixed prefix/frame/low data and leaving the negative assertion external.
- `paper.txt:1375`, §8.5: capture the resulting complete smaller source into Ju with a new owner w<u and unchanged finite record; low budget survives and No_B restricts to Jw, yielding a smaller failure.
- `paper.txt:1382`, §8.5: parent/end-of-column difference supplies an ordinary cap and joint pre-stop realization carrying already-true negative label with Ju+ω budget.
- `paper.txt:1389`, §8.5: outer repairs preserve marked frame and internal cap; query-child size bounds allow D_{<n}; cofinality supplies positive k with H[k]>E and B'>B_good≥B.
- `paper.txt:1400`, §8.5: exact source/target prefix projections, one assignment, genuine whole-level field, and No_B/low-stage checks establish the labelled D-premise.
- `paper.txt:1418`, §8.5: all external representatives, including unused frame fields, survive same-parent outer repairs.
- `paper.txt:1422`, §8.5: for root p≤ρ, moving-parameter descent carries host, owner, frame, whole level, and negative label to matching output projections.
- `paper.txt:1438`, §8.5: output source graph, original target-prefix domain, surviving source-prefix sharing, head relations, and transported low budget verify packet admission; ρ'<p≤ρ makes its ordinal pair smaller.
- `paper.txt:1454`, §8.5: for p>ρ the root is internal, u<p; frame/prefix/negative whole-level data have Jp budget and can be fixed during descent.
- `paper.txt:1459`, §8.5: a separate capture fixes only low frame/record parameters and quantifies new owner w<u; whole Ju and No_B are deliberately absent; externally restricting No_B yields a smaller failure at (ρ,w).
- `paper.txt:1471`, §8.5: cases exhaust first differences, proving S_n and then the finite-size induction cycle without a syntax-order induction.

### §§9–10

- `paper.txt:1478`, §9: ZFC plus all finite Mahlo levels proves Std well-ordered.
- `paper.txt:1480`, §9: seed configurations and completed finite-size induction give ordinary descent for every standard input by choosing n above all query-height sizes.
- `paper.txt:1482`, §9: special descent and deletion yield a smaller-maximum configuration for every nonempty successor.
- `paper.txt:1483`, §9, (27): any nonempty standard A with configuration α has every nonempty A[k] configured by γ with max γ<max α.
- `paper.txt:1488`, §9: ordinary/special output bounds lie below their deleted stopping values, hence below the old maximum.
- `paper.txt:1489`, §9: induction on a finite generation witness configures every standard expression (empty outputs use the empty configuration).
- `paper.txt:1491`, §9: a hypothetical descending sequence has no empty term and its first expression has a configuration with some ordinal maximum θ.
- `paper.txt:1494`, §9: all recursively chosen states can be restricted to the set ω×Std×(θ+1)^{<ω}.
- `paper.txt:1496`, §9: eligible-state predicate requires standard A≥E_i and a correctly indexed configuration.
- `paper.txt:1497`, §9: cofinality produces A[k]≥E_{i+1}; it is nonempty and standard and has smaller configured maximum.
- `paper.txt:1500`, §9: Choice well-orders the state set, enabling least-successor recursion on ω and an impossible strictly descending sequence of ordinals.
- `paper.txt:1502`, §9: a nonempty subset without a least member produces a descending sequence by set-sized choice recursion, establishing the well-order property.
- `paper.txt:1505`, §9: define σ(∅)=0 and σ(E) as minimum of max α+1 over configurations of E.
- `paper.txt:1510`, §9: this possibly proper-class minimum is legitimate by bounding with any existing member and using Separation.
- `paper.txt:1511`, §9: minimizing configuration and (27) imply σ(E[k])<σ(E), including empty output.
- `paper.txt:1516`, §10: accompanying Python implementations are supplementary reproducibility material, not formal verification.
- `paper.txt:1518`, §10: stated BFS counts, size/call bounds, structural tests, and exclusions.
- `paper.txt:1524`, §10: stated ordinary occurrence-map graph checks and skipped branches.
- `paper.txt:1528`, §10: stated sampled-cap counts and µ(B)+1 bound checks.
- `paper.txt:1532`, §10: finite computations prove no universal finite lemma, certificate fact, condensation, minimality argument, or Mahlo axiom.

## Definition fidelity and concrete expressions

The intended implementation is the default `BTBM.FS`, not `FS_short` or a display conversion. The default wrapper preserves the raw operation's outputs: it dispatches infinity to the seed constructor, uses index 0 on nonlimits whose outputs are index-independent, and memoizes limits. An expression below uses zero-based `(parent,height)` pairs unless explicitly marked as **reference display**; reference display adds one to a parent and writes an empty column as `(0)`.

| Paper definition | Reference location | Audit result |
|---|---|---|
| Finite forests/columns/entries, `paper.txt:59`, §1.1 | `BTBM.ts:13`–19 | Same finite recursive shape for natural-valued entries; the runtime `number` type is a larger, machine-limited domain. |
| Entry order then list lexicographic order, `paper.txt:62`, §1.1 | `BTBM.ts:445`–455; `utils.ts:54`–65 | Same parent-first, recursive-height-second order; proper prefixes are smaller. |
| Scoped column numbering, `paper.txt:65`, §1.1 | `BTBM.ts:128`–155, 322–352, 474 onward | Heights start at host+1; returning from a height restores the outer scope. Repeated printed numbers are not shared occurrences. |
| Fixed-host relative key, `paper.txt:75`, §1.1 | `BTBM.ts:40`–99 | Same false/true split, natural offset, and same threshold throughout descendants; false fields precede true fields. |
| T and A, `paper.txt:86`, §1.1 | `BTBM.ts:157`–180 | Same shifts at all depths; replacement follows exactly the last-column/last-entry route, and does not shift inserted Z. |
| Empty input / empty outer column, `paper.txt:96`, §1.2 | `BTBM.ts:235`–239 | Empty outer-column deletion agrees. Empty-input partiality differs as X-01. |
| Terminal route and root, `paper.txt:98`, §1.2 | `BTBM.ts:105`–155 | Agree on V,I expressions; X-02 covers the extra raw inputs. The PDF confirms `t=(Σ_{i=0}^ℓ |E_i|)-1`, with only one subtraction of 1. |
| Special criterion and n+ε copies, `paper.txt:109`, §1.2 | `BTBM.ts:182`–216 | Same owner test, empty-prefix exception, and zero-parameter behavior. |
| Raw scan, `paper.txt:121`, §1.2 | `BTBM.ts:218`–228 | Same two cursors; equality advances both. The copied suffix is selected by the raw final source cursor, not by reducing the source entries. |
| Ordinary head/body/owner-root loop, `paper.txt:125`, §1.2 | `BTBM.ts:258`–288 | Same descending parameter loop, query phase k−1, restored-height phase k, unchanged restored outer parents, and active-owner hole. Zero deletes the entire stopping column. |
| Seeds, `paper.txt:139`, §1.3 | `BTBM.ts:31`–38 | L_m is exactly `infinity_FS(m)` for every natural m by the displayed recursion. |
| Std, `paper.txt:141`, §1.3 | `INFINITY` plus default `FS` | Code does not export a separate Std predicate. Finite reachability from its seeds is the paper's intended domain, with the harmless empty self-loop removed. No claim is made about arbitrary strings accepted by `from_display`. |
| Word and safe prefixes, `paper.txt:143`, §1.3 | No separate reference API needed | Auxiliary mathematical encoding; direct comparison agrees on the tested pairs. It is not the reference's textual serialization. |

There are exactly two observed operation-domain discrepancies, with explicit expressions in X-01 and X-02. I found no discrepancy in nonempty standard syntax, order, seeds, normalization, or either operation branch. This conclusion rests on the clause comparison as well as falsification attempts; the finite test range is not a proof of universal agreement.

The following outputs were obtained by the actual copied reference and the independent §1 implementation. In this table all expressions are **reference display**. A witness `[m,n1,...,nk]` means start at L_m and successively apply n1,...,nk.

| Edge case | Input / standard witness | Parameter | Common output |
|---|---|---:|---|
| Empty outer column | `(0)` / `[0]` | 0 | empty forest |
| Depth zero ordinary, empty root | `(0)(1)` / `[1]` | 3 | `(0)(0)(0)(0)` |
| Special, P empty, n=0 | `(0)(1^(2))` / `[2]` | 0 | `(0)(1)` |
| Special, P empty | `(0)(1^(2))` / `[2]` | 2 | `(0)(1,1,1)` |
| Special, P nonempty, zero copies | `(0)(1^(2),1^(2))` / `[3,1,1,1,1,1]` | 0 | `(0)(1^(2))` |
| Special, P nonempty | same | 2 | `(0)(1^(2),1,1)` |
| Ordinary n=0, nonempty Q | `(0)(1,1)` / `[2,1]` | 0 | `(0)` |
| Owner-root ordinary | `(0)(1^(2,2))` / `[3,1]` | 2 | `(0)(1^(2,1^(3,1)))` |
| Equal keys, both cursors move | `(0)(1,1)(2,2)` / `[2,2,2]` | 1 | `(0)(1,1)(2,1)` |
| Exhausted nonowner source | `(0)(1^(2)(3,3))` / `[3,1,1,2,0,1]` | 2 | `(0)(1^(2)(3)(4))` |
| Source-only advance | `(0)(1^(2)(3^(4),3))` / `[3,1,1,2,1,1,1]` | 2 | `(0)(1^(2)(3^(4))(4^(5)))` |

The owner-root example's scan has source key strictly greater than the empty query key, so it also checks the query-only advance. Exact zero-based input/output trees, raw cursor traces, and witnesses are in `scratch/codex/ref-targeted-results.json`.

## Proof audit and adversarial checks beyond the findings

### Finite calculus, §§1–4

The syntax order is recursively computable because comparisons recurse on proper finite subtrees; this does not supply well-foundedness of the order being defined. The compact word's depth/first-entry/continuation distinctions are sufficient to reconstruct the finite syntax and make the first syntactic difference the first word difference (`paper.txt:147`, §1.3). Closing a safe prefix is different from deleting arbitrary entries: it cannot introduce an empty internal column.

The scan-boundary proof distinguishes reduction of a **query**, which preserves its final source cursor, from exact equality of raw traces (`paper.txt:165`, §2). Repeated equal keys are retained by ν; deleting them would invalidate the endpoint counts. Empty source, empty query, a proper-prefix query, equal complete lists, and a cut after the final entry all have the stated boundary interpretation. The path-nesting induction calls only smaller column numbers; the barrier's own induction additionally decreases entry index. The capping equivalence is obtained from the barrier and a reverse uncapping induction, rather than presupposing capped and uncapped paths agree. Owner-root nonexhaustion follows from the strict inequality `Z<ν(Z⌢[∅])<B_r(u)`; an exhausted **nonowner** root is allowed and is not an illegal state.

For closure, the important separation is that S is proved before output A (`paper.txt:350`–403, §3.2). The classification includes closed side heights whose printed column numbers exceed the stopping number t; the proof cannot treat a numerical interval as a complete set of occurrences. At an owner return only the first following query phase can hit a shifted owner; later phases' parents are too large. The containment-offset word comparison handles simultaneous shortening of upper and lower heights. The same-parent cap repair preserves returned **parents**, not necessarily identical raw cursors; where subsequent kernels need actual cursor equality the paper supplies separate sign/nonexhaustion arguments.

For cofinality, cap completion is conditional on cofinality already established for the **old target** (`paper.txt:459`, §3.3), and is invoked inside induction on a finite generation witness (`paper.txt:504`, §3.4). This is not induction on the unproved syntax order and is not a circular invocation of current-target cofinality. The kernel has a nonempty word prefix P, so its iterates strictly extend; failure is upward closed and the successful iteration bound is length-based. The delayed-change estimate preserves at least the whole right-hand word, giving `L′≥R>R′` even when the left becomes exactly R.

I checked every selected-root group in §3.4: proper current root, current head, proper previous-phase root, original root and lower root; every body/closed-side/query/head/restored-suffix cut; and the seam `H[q]=A[i−1+q]`, including q=0. In the fixed-root cases the paper proves actual source-cursor agreement before applying the filling identity. The different Q-prefixes in (4)–(5) are canceled separately, and the inverse phase map is applied only to its image. The original terminal survives rooting, so the displayed agreement length used in delayed change is available. These are essential checks, not cosmetic algebra.

The source-reduction proof separates a whole-target prefix ending from a proper-child prefix ending (`paper.txt:718`, §4). Only the latter requires an operation, whose direct child owner is strictly internal to the marked source. Outer repairs can change the current address and B_good but preserve the internal cap; the terminal-query heights still come from the original B and satisfy `N(J)+2≤N(B)`, not merely a bound by B_good. X-04 asks that these exact relations be made constructor fields. I found no finite counterexample on the intended record class.

### Hierarchy and initialization, §§5–6

I checked the listed generators for the transitivity claim at `paper.txt:755`, §5.1. The pair/triple support sets matter: the extra wrapper `{x,⟨y,z⟩}` supplies the otherwise missing member of a Kuratowski triple. Fibre-family members are supplied by the separate fibre operation. The incidence/fibre construction of S(T) avoids assuming closure under an arbitrary collection of generator outputs. The rank/ordinal-height argument is an ω-block argument; it is not claiming that every individual successor stage has ordinal height equal to its index.

Histories are checked by bounded recursive production clauses. One must not replace that checker with “this relation is a well-order,” an unbounded property; external induction is what proves the decorated order well-founded. At a limit λ, a history through ξ<λ lies in `J_{ξ+ω}⊆J_λ`, including the equality case ξ+ω=λ. This is enough to form predecessor sets and least witness records locally. Arbitrary choice-based Skolem functions would not suffice: the end-extending decorated order is what gives compatibility of the **partial domains and values** across levels.

The uniform table verifier does not assume a truth predicate for the universe. A finite formula code, parse tree, assignment sets and every subformula table are supplied as sets, and a bounded checker validates them. Similarly, the top level `J_v` is the ambient domain of its tables, not an element parameter of itself (`paper.txt:895`, §5.2). The certificate that also contains that whole level lives in `J_{v+ω}`. I found no self-membership or Tarski-style contradiction in this construction. Its actual compiler and boundedness/budget theorems remain a large formalization task.

Condensation uses extensionality from reflected symmetric-difference witnesses and genuine histories in both directions. Reflection alone would not identify a collapse with the chosen J-levels; the history uniqueness argument supplies that identification, including `π(J_u)=J_{π(u)}`. Control transport acts on an existentially chosen **joint** record. It does not promise to transport an arbitrary specified realization pointwise, and the later proof does not require that stronger claim (`paper.txt:917`, §5.2).

The cardinal lemma (13) is valid also for singular uncountable λ: only the one chosen parameter-containing stage has size below λ, and a hull of that size collapses below the initial ordinal λ. Regularity is needed only in (14), to bound the trace and form club closure points. In seed initialization, each chosen pair satisfies `a_{i−1}<u_{i−1}<a_i<u_i`; stationarity picks the next Mahlo ordinary value and unboundedness picks its slot. The m=1 case needs no U_0; the m=0 seed is just one limit-valued ordinary role. Strong-limitness is not otherwise used by this initialization.

The occurrence-map identity was checked at the level of constraints, not just counts or output text (`paper.txt:941`–968, §6.1). A retained block uses the fresh f-map; a query reads the **previous** f-map; an entering pair `(a,T)` becomes `(f_m(a),h)`. Original pre-stop occurrences remain on the persistent ι-map. Consumed closed root blocks are removed from K but remain in the original pre-stop prefix P; their private roles cannot be read by later visible-stack edges. No new ordinary pair is inserted between sibling height forests. These distinctions cover owner-root holes, empty K/Q and closed side columns beyond t.

### Joint packets and induction, §§7–8

The positive target predicate `Cert_B` is defined independently of strict-source assertions (`paper.txt:1034`, §7.1). A packet contains **both** source and target heads at the same owner, and one assignment with checked projections; independent realizability of the components would not imply a packet. Its low certificate contains neither the owner u nor the whole J_u. Fresh target names share only their prescribed frame, and the raised floor exceeds all old coordinates and an actual stage containing the low certificate. This is why factorization preserves resources without using a nonexistent global amalgamation principle.

At a scan, the transported reference root below ρ is different from the bank root/new stopping role of value ρ (`paper.txt:1136`, §7.3). The target prefix includes all transported old pre-stop roles, including consumed root blocks, plus the fitted query prefix and any entering pair. The two charts share the genuine pre-root frame and new physical host, not accidentally all bank-private coordinates. Transient certificates from earlier fitting steps are not automatically admitted as fixed low resources. Their graphs can be recertified from current finite maxima instead.

The two-candidate lemma requires simultaneous bounds on owner and maximum (`paper.txt:1201`, §8.1). If one candidate minimizes both, use it. Otherwise the strict chain `h_Y<h_X≤c_X<c_Y` allows capture of X's free existence problem along Y's owner path, below h_Y. In particular, equal scan keys cannot always be handled by simply reusing the source block. The paper correctly uses this lemma, then restricts the positive target heads. Empty equal heights cause no failure: owner and maximum coincide.

For strict scan comparisons, if the old positive block is already below u_i it is reused on fresh names. Otherwise, when `h<u_i≤c_0`, the block is nonempty and its owner path gives intermediate Σ1 elementarity, allowing the target heads' environments to grow to u_i. The S-call is then on `N(J_j)<n`, with the complete admitted packet; the original positive maximum bounds the new prefix. Source-only advances use no S-call. Nonexhaustion of the stipulated bank forces eventual exhaustion of the query. An empty query needs no source theorem at all.

In ordinary descent, the temporary state includes a fresh reference chart of the **whole** P and a checked budget `w_old∈J_t` (`paper.txt:1268`–1287, §8.3). Control collapse sends t=W to p and moves the old graph/labels together below p. The whole genuine level travels as part of the record. A subsequent capture may choose a new joint realization; it need not preserve arbitrary nonfixed old numerical values. K is then restored at original values. Empty K, a first ordinary/active role, and a first closed owner are separate cases. The last case invokes W with the original closed bank through its unconsumed endpoint. All old labels continue to read ι(P), never the restored latest copy.

Special descent has a deliberately weaker label clause (`paper.txt:1343`, §8.4). A label can stay fixed only if its certificate/parameters already lie in J_s and it reads no fresh private role. Capturing into J_s cannot fix J_s itself as an element parameter. The zero-copy case leaves the prefix; the n=0, ε=1 case still captures one shortened copy. Strict containers keep their occurrence identities, but the replaced entry's own owner is freshly chosen.

For the S_n induction, the minimum is a pair of actual ordinals, selected with bounded Separation from one existing failure (`paper.txt:1349`, §8.5). No well-order on syntax, all configurations, or a proper class is assumed. A whole-target prefix supplies a direct positive witness. A proper-child ending invokes only empty-query descent or the limited special clause, with all control strictly inside the marked height. The negative assertion stays external in the later capture into J_u.

In the remaining cap case, the source prefix has its **repaired** domain, while the entire original target prefix remains auxiliary. The shared assignment in (24)–(25) pins the host, owner, full frame, low stage and negative predicate to the actual named projections. If p≤ρ, moving descent carries all of them together and decreases the host. If p>ρ, the root is internal and u<p; the whole J_u and its history have J_p budget and can be fixed during descent. A second, distinct capture into J_u then omits the whole J_u and No_B from its fixed parameters, chooses a new owner w<u, and uses the external monotonicity of No_B under `J_w⊆J_u`. These are different legal uses of reflection. In both cases the proof checks readmission into the same packet class before using minimality.

### Full well-order, §9

The final reduction is sound conditional on the earlier obligations. The tuple bound in `X=ω×Std×(θ+1)^{<ω}` makes the recursive choices a set, even though configurations originally range over ordinals without a fixed global bound. Cofinality uses a standard target E_{i+1} and an admissible standard covering state A. Its successor remains nonempty because it covers the nonempty target. Strict decrease of the finite configuration maximum yields the contradiction. There is no assumption that every admissible expression is standard.

The minimum defining σ is legitimate for a nonempty definable class of ordinals: one configuration supplies a bound, and Separation obtains a nonempty set of candidates below it. The result proves `σ(E[k])<σ(E)`, including an empty output. It does **not** assert, and the proof does not establish, that this particular σ is an order embedding of all syntax comparisons. The empty configuration never needs an ordinary maximum.

## Independent tests and reproducibility

The TypeScript source and its imported helpers were inspected before execution. The principal differential harness copies them into `scratch/codex/`, strips TypeScript type syntax, and evaluates the copied code in a fresh VM without process, require, fetch, or filesystem capabilities. A separate tuple-based program implements §1 from the paper. The finite-invariant checker is a second, immutable Python implementation. No supplied §10 implementation was used. Exact input hashes are recorded in `scratch/codex/input-sha256.txt`.

| Test | Exact checked sample | Result/artifact |
|---|---|---|
| Default reference versus independent §1 operation | 30,000 stored states, size≤80; first 12,000 processed; seeds 0–5; n=0–4; 59,995 generated nonempty operation comparisons | No generated nonempty mismatch; `ref-results.json`. Separate raw inputs expose X-01/X-02. |
| Seeds, order and relative keys | Seeds 0–9; 30,000 selected syntax/reference comparisons, compact-word comparisons and relative-key comparisons | No mismatch; `ref-results.json`. |
| Targeted branch cases | Seven nontrivial selected examples at n=0–3, plus basic empty/deletion/special cases | All intended-domain outputs agree; `ref-targeted-results.json`. |
| Exact occurrence graph and persistent original map | 23,269 ordinary standard inputs at n=0–3: 93,076 graph comparisons and 93,076 persistent-map comparisons | No mismatch; `ref-graph-results.json`. |
| Closed side heights with printed columns >t | Four synthetic admissible fixtures at n=0–4: 20 additional graph and persistent-map comparisons | No mismatch; `ref-graph-fixture-results.json`. They are not asserted standard. |
| Finite invariants / prefixes / caps | 8,362 generated expressions; 8,361 nonempty V,I,H,A,S,P checks; 280,150 safe prefixes; 84,291 admissible upward caps at n=μ(B)+1; 564 generated-pair covers; 20,000 word-order pairs | No counterexample; `finite-results.json`. |
| Arbitrary admissible inputs, not just generated standards | 23,490 sampled L inputs (duplicates allowed), including 35 failing P; 93,960 operations n=0–3; 93,283 safe prefixes | L closure passed; `general-L-results.json`. |
| Independent capping under V,S without assuming A,I,H | 29,190 qualifying sampled raw inputs (duplicates allowed); 45,843 choices of independently capped route keys | A-equivalence passed; `capping-results.json`. |
| Generic scan/reduction words | All 14,641 pairs of words over {0,1,2} of length≤4; 8,537 barrier/reduction-word cases | Boundary/query-reduction checks passed; `finite-quick-results.json`. |
| Missing-I profile implication | The explicit X-03 expression | V,H,P hold and S fails; `hypothesis-counterexample.json`. |

Generated graph coverage includes 6,158 owner-root inputs, 1,434 owner-root inputs with an entering ordinary pair, 11,735 inputs with consumed closed root blocks, 2,209 with empty K, and 6,450 with empty Q. The generated set had **no** retained side columns beyond t; the four additional fixtures deliberately cover that omission. One fixture is `(0)(1^(2^(3^(4))))(2)`: r=1, t=2, but the copied closed side height has columns 3 and 4. This checks that role order, not printed-number interval, determines K.

Reproduction from the repository root, with all generated files still under the permitted scratch directory:

```sh
node scratch/codex/ref-tests.mjs
node scratch/codex/ref-targeted.mjs
node scratch/codex/ref-graph-check.mjs
node scratch/codex/ref-graph-fixtures.mjs
python3 scratch/codex/finite_model.py
python3 scratch/codex/finite_quick.py
python3 scratch/codex/capping_test.py
python3 scratch/codex/general_l_test.py
python3 scratch/codex/hypothesis_counterexample.py
```

These are finite falsification attempts and reproducible definition checks. Passing results are not evidence for the universal finite lemmas, and they say nothing about the existence of large cardinals, genuine infinite truth tables, condensation, or the least-failure construction. The mathematical review above evaluates the arguments independently of these counts.

## Outside mathematics and what Lean/Mathlib needs

The finite arguments in §§1–4 require only finite syntax/list induction, natural arithmetic, lexicographic comparison, and induction on a finite generation witness. No stationary-set or reflection theorem is used there. The following is the external mathematical dependency inventory for the rest of the proof; project-specific variants are distinguished from standard background facts.

| Fact / construction | Status and use in the paper | Formalization requirement |
|---|---|---|
| ZFC finite pairing, products, unions, Separation, Replacement, Foundation and transfinite recursion | Standard foundations; J and decorated histories at `paper.txt:739`–826, §5.1; all finite syntax/diagram/certificate collections | Choose a set-theoretic universe and code sets/ordinals consistently; prove the actual recursive definitions rather than adding a stronger global reflection axiom. |
| A finite tree/list and its natural-valued finite witnesses form a set; Std is countable | Standard; `paper.txt:141`, §1.3 and the state set at `paper.txt:1494`, §9 | An inductive syntax type, decidable comparison, and an inductive or finite-witness Std predicate. Countability is available but is not needed beyond set-sizedness in the paper. |
| If v<u and u is limit then v+ω≤u | Standard ordinal arithmetic; (8), `paper.txt:735`, §5.1, repeatedly through §§5–8 | A reusable ordinal budget lemma, including the equality case. Distinguish ordinal addition from cardinal addition. |
| Finite tuples/records in a B-closed limit level stay there; finitely many records share an earlier stage | Standard consequence of finite closure and continuity; `paper.txt:767`, §5.1; `paper.txt:1070`, §7.2; copy/floor budgets in §8 | Prove for the concrete tuple encoding and J; finite packing and earlier-stage lemmas should be shared infrastructure. |
| Rank bounds for finite set constructors and union at limit stages | Standard rank arithmetic; `paper.txt:799`–807, §5.1 | Rank monotonicity and finite-rank increment lemmas; the exact height equality for this S-hierarchy is project-specific. |
| Countably many finite-arity operations preserve cardinal bound max(ℵ₀,|X|) under ω-step closure | Standard ZFC cardinal arithmetic; `paper.txt:801`, 840, §5.1 and hull size in §6.2 | Universe-aware cardinal estimates, finite products/unions and countable closure. |
| Fixed-formula satisfaction on a set-sized structure | Standard recursive first-order semantics; `paper.txt:768`–779, §5.1 | Build formulas, assignment sets, table compiler and a uniform bounded **verifier**. A generic semantic satisfaction function alone does not prove the required Δ0 checker or J-budget. |
| Δ0 absoluteness for transitive sets | Standard; `paper.txt:779`, §5.1; histories, collapse, certificates, capture and upward/intermediate Σ1 elementarity | Bounded set-formula syntax and absoluteness theorem. All formula parameters must belong to the stated domain. |
| Finite lexicographic products of well-orders and stage-end-extended union orders are well-orders | Standard; `paper.txt:816`–820, §5.1 | Prove from the production clauses; avoid trying to certify well-foundedness by a bounded check. |
| Skolem hull elementarity, monotonicity, finite dependence and size bounds | Standard Tarski–Vaught/Löwenheim–Skolem pattern; `paper.txt:808`–841, §5.1 | The **canonical compatible partial Σ1 functions** and their local predecessor-set budgets are custom obligations, not arbitrary library Skolem choice. |
| Mostowski collapse of a set-sized well-founded extensional relation | Standard ZFC; `paper.txt:844`–853, §5.1 | Collapse existence, uniqueness, isomorphism and transitivity; then custom whole-history preservation. Extensionality of the substructure must first be proved, as in the paper. |
| Condensation to J_δ and history transport `π(J_u)=J_{π(u)}` | Standard form of a rudimentary-hierarchy theorem, but **specific to the constructed hierarchy here**; `paper.txt:842`, §5.1 | Prove the supplied history argument or prove equivalence with a previously formalized hierarchy with exactly matching index convention. Do not identify this J with an arbitrary L-hierarchy by name. |
| Bounded relativization to a whole set T∈H gives H∩T≺T | Standard model-theoretic inference; `paper.txt:864`, §5.2 | Whole-set membership, relativized formula construction, and Tarski–Vaught; see X-05. |
| Transitive intermediate Σ1 elementarity and its upward absoluteness | Standard; `paper.txt:867`, §5.2; `paper.txt:1230`, §8.2 | Prove the restriction/extension lemmas with precise inclusions and fixed parameters. |
| Capture of a Σ1 complete existence problem and hull transport | Standard reflection pattern, with custom certificates/budgets; `paper.txt:909`, §5.2; all of §§7–8 | Express the entire shared record by one bounded checker plus existential quantification. Transport genuine levels and shared projections together. |
| A small hull collapses below an uncountable cardinal λ | Standard cardinal/initial-ordinal argument once condensation is known; (13), `paper.txt:976`, §6.2 | From |η|<λ infer η<λ for λ an initial ordinal; regularity is not required here. |
| Regular uncountable λ bounds <λ many stages and countable suprema | Standard; `paper.txt:988`, §6.2 | Cofinality/regularity APIs and the conversion between set cardinality and ordinal bounds. |
| Closure points of f:λ→λ form a club for uncountable regular λ | Standard; (14), `paper.txt:988`–999, §6.2 | Carry out the closure-point construction, including all smaller arguments at each stage, and prove closedness/unboundedness. |
| Stationary sets meet clubs; clubs are unbounded | Standard definition/basic properties; `paper.txt:1006`, §6.2 | Exact stationary/club definitions on ordinals below κ, and finite successive choices. No stationary reflection principle is separately assumed. |
| Finite Mahlo hierarchy M₀=inaccessibles, M_{n+1}={κ∈M₀: M_n∩κ stationary} | Conventional strong finite Mahlo definition fixed explicitly at `paper.txt:971`, §6.2 | Define this recurrence and use the hypothesis ∀n∃κ∈M_n. Strong-limitness itself is not used elsewhere in seed initialization. |
| Nonempty sets of ordinals have minima; no infinite descending ordinal sequence; lexicographic ordinal pairs support bounded least-failure selection | Standard ordinal well-foundedness; `paper.txt:1349`, §8.5 and `paper.txt:1500`, §9 | Use actual ordinal well-foundedness, not syntax-order well-foundedness. Definable-class minima are reduced to bounded sets by one witness and Separation. |
| Choice well-orders any set; recursion on ω makes successive choices inside a set | Standard ZFC; `paper.txt:1494`–1504, §9 | Classical/dependent choice or a direct accessibility proof; no class choice is needed. |
| A nonempty definable class of ordinal candidates has a minimum after bounding by one member | Standard Separation argument; `paper.txt:1508`–1511, §9 | Define σ from a bounded set or prove a suitable existential minimum theorem; no set of all ordinal assignments is assumed. |

For background only, Jensen's primary paper develops rudimentary functions, the J-hierarchy, and its condensation/definability theory. Its common successor index convention has rank ωα, whereas the present paper states height λ at limit-indexed stages; importing a theorem requires an explicit comparison, not a shared letter J. [Jensen, *The Fine Structure of the Constructible Hierarchy*](https://www.math.cmu.edu/~laiken/papers/FineStructure.pdf).

Current official Mathlib documentation confirms useful foundations, not a ready-made proof of this project: [`Ordinal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Ordinal/Basic.html) supplies ordinal order/arithmetic infrastructure; [`ZFSet` ordinals](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Ordinal.html) supplies transitive set-coded ordinals and `Ordinal.toZFSetIso`; [`Cardinal.Regular`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Regular.html) supplies regularity/inaccessibility; and [`Cardinal.Cofinality.Club`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Cofinality/Club.html) supplies `IsClub`, `IsStationary` and club operations. I have not established that a suitable Mostowski/Σ1/J-hierarchy development is already available in the eventual pinned Mathlib revision, and do not claim absence merely from a search.

## Simplification opportunities

1. **Extract the final abstract theorem first.** A finite syntax system with closure, cofinality, seed realization and strict configuration descent already yields the standard well-order. Prove that independently of BTBMS and of J. It makes the final dependency boundary auditable.
2. **Use accessibility induction for §9.** With a supplied configuration of A of maximum θ, prove every standard B≤A is accessible by induction on θ. For C<B, cofinality yields A[k]≥C with a smaller maximum; the induction hypothesis supplies accessibility of C. This avoids the explicit set X and two choice recursions while preserving exactly the same substantive obligations. Keep the paper's original ZFC proof if minimizing changes is preferable.
3. **Unify operation contexts.** A typed rightmost continuation hole with a proved fill/shift law can handle both ordinary root locations. Derive the word-prefix kernel and occurrence substitutions from the same structural lemma rather than duplicating recursion.
4. **Build a small word library once.** Include reduction boundaries, exact cursor traces, separate cancellation, e₀/e₁ encoding, containment offsets, downward kernel success, and delayed-change comparison. Keep source-cursor equality distinct from full trace equality.
5. **Separate finite admissibility from the optional profile invariant.** L=V,I,H,A,S is the closure class; P is a stronger invariant used for cap repair and known for standards. General-L tests include non-P inputs. Making P a permanent field of every admissible object would overconstrain the theorem.
6. **Separate the semantic interface from its J implementation.** Encode complete diagrams, budgets, capture, transport and initialization as a proved interface, then instantiate it from §5. Such abstraction is organizational; the interface's nontrivial laws must still be derived from the stated assumptions.
7. **Package frame amalgamation and budgets.** One finite-name union lemma with explicit overlaps/fresh private names, one finite-packing lemma, and one `v<u ⇒ certificate∈J_u` lemma would remove much repetitive §§7–8 bookkeeping. Use distinct types for original occurrence, current address, bank role and fresh copy.
8. **Prove the stronger initialization lemma actually used.** The seed construction needs uncountable regularity and the indicated finite stationary hierarchy, not strong-limitness. This is an optional weakening; retaining the original finite-Mahlo statement avoids changing the project's advertised theorem.
9. **Avoid automatic expansion of all labels initially.** Prove label-free descent with its persistent-role maps, then a general bounded-label joint-record extension. The final negative label must still be checked in the extended theorem, with its whole-level parameter and stage budget.

## Formalization risks and recommended proof gates

- **Exact target theorem and foundations.** A Lean theorem under assumptions on `Cardinal`/`ZFSet` and a formal statement that a particular recursively axiomatized ZFC theory proves well-ordering are different deliverables. The paper's metamathematical wording should not silently become a stronger internal provability claim. Fix universes, the meaning of finite Mahlo, and the intended nonempty/default-FS domain before implementation. Lean's universe mechanisms should not be used to manufacture unadvertised same-universe large-cardinal hypotheses.
- **Nested finite syntax without assuming its order well-founded.** Recursive definitions may use tree size or mutual structural recursion, not the comparison relation whose well-foundedness is the conclusion. Keep raw syntax and admissibility proofs separate so capped keys and intermediate H-violating caps can be represented.
- **Occurrence identity and stack lookup.** Column numbers are scoped and reused; addresses change under repairs. Prove stack lookup commutes with the actual occurrence maps, and only then identify R triples and ordinary pairs. A list of parent numbers alone does not formalize §6.
- **The §3.4 case analysis.** The hardest finite gate is a fully quantified cofinality theorem with Std target and arbitrary L upper bound. Important subgates are exact kernel filling with a frozen cursor, cap-completion reversal, cursor bounds at moved root entries, separate cancellation for unequal prefixes, and the inverse phase map's domain. Testing the final inequality cannot replace any of these lemmas.
- **The §4 record type.** Freeze the precise record constructors in X-04 before proving semantic descent. Packet readmission must preserve original target code, current source context, surviving-role chart, and proper-child size witness. Allowing these fields to drift changes the least-failure predicate.
- **The bounded formula/certificate compiler.** Prove actual Δ0 syntax and correctness for histories, parse tables, finite graphs and labels. “The predicate is bounded” cannot be a primitive semantic axiom. Check every record's set membership, especially the top level as an ambient tag, and do not assume a uniform global truth predicate.
- **Canonical hulls and condensation.** The project needs compatible partial Σ1 Skolem functions with local predecessor sets, monotone hulls, exact trace equations and whole-level collapse. Generic first-order hulls or arbitrary chosen Skolem witnesses are insufficient for the environment-change lemmas.
- **Budgeted joint transport.** Keep one assignment and checked projections for every component. Capture can change existential coordinates, and old labels follow ι rather than f. Prove the moving-parameter and fixed-low-parameter clauses separately, and preserve the restricted special-step label clause.
- **Nested induction/minimality.** Formalize `S_<n ⇒ W_<n ⇒ D_<n ⇒ S_n` with explicit size hypotheses; within S_n minimize actual ordinal pairs over the complete admitted-packet predicate. A newly produced smaller source is not automatically a smaller admitted failure: both head relations, all prefix domains and the joint low budget must be verified first.
- **Verification boundary.** The reference implementation is an executable comparison target, not a proof oracle. The scratch tests do not certify infinite set-theoretic objects. Conversely the long mathematical argument need not be rejected merely because no generic Mathlib theorem already packages its custom coding.

No finding in this review establishes that the advertised well-order statement is false. The concrete false implication is the unrestricted version in X-03; the intended application includes the missing hypotheses. The domain clarifications and exact record predicates should be resolved before a formal theorem interface is frozen, while the difficult finite and semantic obligations above should remain separate proved gates.

STATUS: COMPLETE
