# Gap register

Generated from `tracker/ledger.json` by `tracker/refresh.py`; do not edit by hand.

| ID | Status | Severity | Location | Summary | Found by | Confirmed by |
|---|---|---|---|---|---|---|
| G-001 | closed | exposition | §1.2 txt:95-101 | Operation domain: ∅[n] undefined in paper but ∅ in BTBM.ts; paper stopping rule undefined on forests with internal empty columns, reference stops there | claude, codex |  |
| G-002 | closed | repairable | §3.1 txt:263-268 | "P implies S" is false without V, I, H | codex | claude |
| G-003 | repaired | repairable | §4 txt:646-686; §7.1 txt:1045-1065; §8.5 txt:1474 | Admitted records (§4) and the packet class quantified in S_n (§7) are not exact predicates; closure of the class under the §8.5 constructions is not checkable as written | claude, codex |  |
| G-004 | closed | exposition | §5.2 txt:864-866 | "The hull contains the whole J_b" must mean J_b ∈ H, not J_b ⊆ H | codex | claude |
| G-005 | closed | exposition | §10 txt:1516-1534 | The "accompanying Python programs" of §10 are not supplied | codex | claude |
| G-006 | closed | repairable | §2 txt:194-236 | Path nesting, barrier and capping proofs do not state their induction predicates and orders across height scopes | claude | codex |
| G-007 | closed | repairable | lean/BTBMS/Expansion.lean (statement port) | Lean expand returned none where BTBM.FS returns a forest, on raw non-V/I inputs whose root lies in the stopping entry's height | codex | claude |
| G-008 | closed | repairable | checks/lock/, scripts/lean-status.sh, tracker/refresh.py (tooling, not the paper) | Lock and progress tooling could certify a wrong proof: coerced or axiom-based exports passed, Mathlib/toolchain unpinned or pinned at the wrong path, stale status shown as current, opaque holes missed | codex | claude |
| G-009 | repaired | unknown | §3 txt:553-560 | Cofinality, ordinary step: the response at a previous-phase root (r < ρ < s_φ) is asserted without the invariant that relates V = κ_φ W to the old terminal queries along the low-head detour | claude | codex |
| G-010 | confirmed | unknown | §3 txt:520-541 | Cofinality, projection of the final A-test: needs a decorated-key variant of head_path whose hypotheses the paper does not fix | claude | codex |
| G-011 | repaired | unknown | §4 txt:667-681 | First-difference lemma, path transfer: the cap-anchor host crossing and the descendant identification at the source host are compressed | claude |  |
| G-012 | repaired | unknown | §8.5 txt:1418-1423 | Case 3 data: whole-frame survival through repairs ("induction through the containers") and an injective chart of the repaired cap compatible with χ are sketched | claude |  |
| G-013 | repaired | repairable | blueprint D3.3b | word_kernel asserts the word factorization when an exhausted owner root leaves no continuation hole | codex |  |
| G-014 | repaired | repairable | blueprint T3.2i | num_phaseCol holds only for coherent stop/root data of an actual operation; arbitrary records give 1 = 0 | codex |  |
| G-015 | repaired | repairable | blueprint D3.1d | origin_spec_full claims parent lookup is preserved at slots that do not exist in the output | codex |  |
| G-016 | repaired | repairable | blueprint D3.1e, L4.3c, L7.5a | moves_spec and applyMoves_litCap_addr use the marked height's original address after earlier moves relocate it; both conclusions are false | codex, claude | claude |
| G-017 | repaired | repairable | blueprint L8.8a | failure_floor drops factorization's actual-source-entry premise; Valid alone allows a successor-valued owner | codex |  |
| G-018 | repaired | exposition | blueprint D3.1d, L8.6a | anchorOrigin_prefix needs InL E, but the empty-query DLab over a cap provides only InL (anchor E cap) | codex |  |
| G-019 | repaired | exposition | blueprint L4.3, L4.3d | childEnds_package uses role-prefix and subgraph facts that reduce_childEnds does not export | codex, claude | claude |

## G-001 — Operation domain: ∅[n] undefined in paper but ∅ in BTBM.ts; paper stopping rule undefined on forests with internal empty columns, reference stops there

**Detail:** Agree on nonempty V∧I inputs, hence on L ⊇ Std. Instance: E=[[],[(0,[[]])]] (violates I): paper route stuck; reference FS(E,0)=[[]].

**Fix:** Root decision: total Lean FS mirroring BTBM.FS, plus an agreement lemma with the paper operation on nonempty V∧I inputs; all decrease statements explicitly nonempty.

**Refs:** claude C-01, codex X-01, codex X-02


## G-002 — "P implies S" is false without V, I, H

**Detail:** E=[[],[(0,H)]], H=[[(0,K)],[(1,J)]], K=[[(2,∅)]], J=[[(3,∅)]]: V, H, P hold, I fails at H's first column, and h_3(J)=(1,0)… > h_1(H)=(0,0)…, so S fails. Claude re-derived π(H)=(1,1), π(J)=(0,1) and the S comparison by hand (non-blind: done after reading X-03). The proof uses I to make first-entry branches pure towers; the intended V∧I∧H version is the one used later.

**Fix:** State V∧I∧H∧P ⇒ S; make V, I, H standing hypotheses of the profile construction.

**Refs:** codex X-03


## G-003 — Admitted records (§4) and the packet class quantified in S_n (§7) are not exact predicates; closure of the class under the §8.5 constructions is not checkable as written

**Detail:** Records need explicit occurrence maps, actual scan indices, retained marked-entry/pre-entry equations, repair lists with surviving-role injections. Packets need a fixed grammar for auxiliary diagrams and labels, closed under factorization, joint cap, joint repair, the §7.3 extension and the readmission in §8.5 Cases 2-3. Boundary instance (codex): in L_2 a special step at parameter 1 replaces the marked outer entry, so "confined" must require survival of the marked occurrence. Neither reviewer found a counterexample to the intended statement. Codex T-017: repair partial; closure providers BP-03..BP-05, BP-08, BP-09 need correction.

**Fix:** Define records and packets as explicit finite structures (constructors with occurrence/projection fields) and prove the closure lemmas before stating S_n in Lean.

**Refs:** claude C-05, codex X-04


## G-004 — "The hull contains the whole J_b" must mean J_b ∈ H, not J_b ⊆ H

**Detail:** J_b ⊆ H would give H ∩ J_b = J_b ≠ J_a, contradicting (10). Claude checked the one-line argument (non-blind).

**Fix:** Write J_b ∈ H, then relativized Tarski-Vaught.

**Refs:** codex X-05


## G-005 — The "accompanying Python programs" of §10 are not supplied

**Detail:** Only the PDF was provided. §10 is not used as evidence by either review.

**Fix:** Ask the author for the programs, or ignore §10.

**Refs:** codex X-06


## G-006 — Path nesting, barrier and capping proofs do not state their induction predicates and orders across height scopes

**Detail:** Codex (blind): the stated numerical orders suffice, but the paper does not print the needed predicates. Barrier needs a joint induction on (c,k) of C_e (cut paths reaching a have query < D_e) and R_e (return bounds). Reverse capping needs actual A together with actual return bounds, plus a first-divergence argument: the first decorated edge differing from the actual scan is at a capped column a reached by an actual path, so C_e gives W < B_a(v) <= B_a(u*), and the scan stops before the capped key. A proof carrying only "earlier entry A holds" would leave a gap. Codex verdict: no unrepaired mathematical gap. Claude checked each step of the repair. Lean: L2.2a, L2.3a, L2.4a and their lemmas proved (prove/C2).

**Fix:** Write the joint predicates C_e/R_e, the localized pre-entry-cut barrier and the first-divergence argument as explicit lemmas (codex-crosscheck-1.md, Q2).

**Refs:** claude C-06, codex CROSSCHECK-1 Q2


## G-007 — Lean expand returned none where BTBM.FS returns a forest, on raw non-V/I inputs whose root lies in the stopping entry's height

**Detail:** Not a paper gap: a defect in Claude's Lean port, outside the standard domain. E.g. [[],[(2,[[]])]] at n=0: reference ∅-column deletion, Lean none.

**Fix:** rootLayer searches tl+2 forests; expandExtraLayer reproduces the reference (empty query, negative offset, only the j=1 tail survives). Regression cases in checks/lean/gen-regression.mjs. Codex re-checked the branch at source level and reran its own raw corpus (12,000 cases, 0 mismatches; previously 80).

**Refs:** codex-statement-review.md §2


## G-008 — Lock and progress tooling could certify a wrong proof: coerced or axiom-based exports passed, Mathlib/toolchain unpinned or pinned at the wrong path, stale status shown as current, opaque holes missed

**Detail:** Codex exploits: mainTheorem : True with an admitted Coe True MainTheorem instance passed check.sh with no axioms; axiom auditShortcut : MainTheorem passed and showed as proved; changing a resolved Mathlib file in a relocated copy kept the lock intact; stale status showed a sorry theorem as proved. Claude replayed the coercion, axiom, fixed-universe and opaque exploits in a scratch copy (non-blind: explicit counterexamples). Codex fix check (follow-up): changes 1, 2, 5 fixed; 3, 4 partial: (A) status generation did not run the export audit, so clean True exports showed as proved; (B) a directory symlink into lean/.lake hid a sorry from the fingerprint; (C) malformed or >argv-size extraction output kept an older success record. Follow-up 2: A and C fixed; B partial: any directory named .lake was skipped, so lean/BTBMS/.lake/Hidden.lean (import BTBMS.«.lake».Hidden) could acquire a sorry unseen. Follow-up 3: nested case fixed; import BTBMS.«..».«.lake».Hidden (and «../.lake») still reached lean/.lake/Hidden.lean. Follow-up 4 (codex): fixed; 8 pipeline replays + 26-case policy matrix; recommends closing.

**Fix:** LockCheck compares the stored ConstantInfo.type of mainTheorem/paperTheorem syntactically with MainTheorem.{u}/PaperTheorem.{u}, rejects axiom declarations in BTBMS and axioms outside {propext, Classical.choice, Quot.sound, sorryAx}; check.sh --final also rejects sorryAx. lock.py hashes every package resolved from lake-manifest.json and the toolchain bin/ and src/. lean-status.json carries an input fingerprint; refresh.py ignores stale or failed status; extra axioms are classified, opaque bodies scanned. Follow-up: scripts/lean_status.py publishes atomically, writes an in-progress record first, runs build, LockCheck audit and extraction, validates the JSON, re-checks the fingerprint; refresh.py requires state ok, build_ok, audit_ok, a matching fingerprint and an intact lock. Symlinks in any hashed tree, including lean/, are refused. Follow-up 2: only a hashed tree root's own .lake/.git are skipped; nested ones are hashed. Row and axiom-item types validated. Follow-up 3: LockCheck rejects any module in the import closure with a non-identifier name component, so every source is read from its standard path inside a hashed tree.

**Refs:** codex-lock-review.md


## G-009 — Cofinality, ordinary step: the response at a previous-phase root (r < ρ < s_φ) is asserted without the invariant that relates V = κ_φ W to the old terminal queries along the low-head detour

**Detail:** Found while writing the blueprint (node T3.8lo). Statement passed 647 bounded caps with r < ρ < s_φ; the invariant for proof step 3 is not written.

**Refs:** blueprint/INTEGRATION.md §2.2, codex-blueprint-review.md BP-07


## G-010 — Cofinality, projection of the final A-test: needs a decorated-key variant of head_path whose hypotheses the paper does not fix

**Detail:** Found while writing the blueprint (node T3.8li, T3.2q). Decorated variant fails for arbitrary reduced W (74 bounded failures) and held for cut queries of a (9,420 cases); the projection itself held in 32,183 cases.

**Refs:** blueprint/INTEGRATION.md §2.2, codex-blueprint-review.md BP-06


## G-011 — First-difference lemma, path transfer: the cap-anchor host crossing and the descendant identification at the source host are compressed

**Detail:** Found while writing the blueprint (node L4.2c). Not exercised on any bounded instance with a moved cap anchor; 1,344 related repair-record cases pass.

**Refs:** blueprint/INTEGRATION.md §2.2-2.3


## G-012 — Case 3 data: whole-frame survival through repairs ("induction through the containers") and an injective chart of the repaired cap compatible with χ are sketched

**Detail:** Found while writing the blueprint (node L7.5d, L8.8f). Each CapData field now has a named source (L7.5, L7.5a, value separation); not yet confirmed field by field.

**Refs:** blueprint/INTEGRATION.md §2.2-2.3


## G-013 — word_kernel asserts the word factorization when an exhausted owner root leaves no continuation hole

**Detail:** Found by Codex in T-017 with an explicit counterexample (scratch/codex/).

**Fix:** Add KernelDefined E rd and discharge it at consumers.

**Refs:** codex-blueprint-review.md BP-01


## G-014 — num_phaseCol holds only for coherent stop/root data of an actual operation; arbitrary records give 1 = 0

**Detail:** Found by Codex in T-017 with an explicit counterexample (scratch/codex/).

**Fix:** Require actual-data/coherence hypotheses; recheck every application.

**Refs:** codex-blueprint-review.md BP-02


## G-015 — origin_spec_full claims parent lookup is preserved at slots that do not exist in the output

**Detail:** Found by Codex in T-017 with an explicit counterexample (scratch/codex/).

**Fix:** Restrict the slot clause to actual output entries/roles.

**Refs:** codex-blueprint-review.md BP-03


## G-016 — moves_spec and applyMoves_litCap_addr use the marked height's original address after earlier moves relocate it; both conclusions are false

**Detail:** Found by Codex in T-017 with an explicit counterexample (scratch/codex/). Found independently by the G-012 repair draft (blueprint/repairs/G-012.md §5).

**Fix:** State the exclusion at every current moveAddr (moves.take i) b (MovesOutside); U3 supplies it; propagate through the cap/readmission chain.

**Refs:** codex-blueprint-review.md BP-04


## G-017 — failure_floor drops factorization's actual-source-entry premise; Valid alone allows a successor-valued owner

**Detail:** Found by Codex in T-017 with an explicit counterexample (scratch/codex/).

**Fix:** Add Admitted or source-entry membership and pass it to factorization.

**Refs:** codex-blueprint-review.md BP-05


## G-018 — anchorOrigin_prefix needs InL E, but the empty-query DLab over a cap provides only InL (anchor E cap)

**Detail:** Found by Codex in T-017 with an explicit counterexample (scratch/codex/).

**Fix:** Supply the structural origin-prefix lemma without InL E.

**Refs:** codex-blueprint-review.md BP-08


## G-019 — childEnds_package uses role-prefix and subgraph facts that reduce_childEnds does not export

**Detail:** Found by Codex in T-017 with an explicit counterexample (scratch/codex/). Claude's TESTS draft independently flagged the missing export (INTEGRATION.md I-3).

**Fix:** Export (setHeight a A1).roles <+: F.roles and graph subset (bounded-tested in blueprint/repairs/TESTS.md).

**Refs:** codex-blueprint-review.md BP-09


# Decisions

| ID | Owner | Status | Question | Answer / impact |
|---|---|---|---|---|
| D-1 | user | decided | Which theorem is the deliverable: a host-Lean theorem (∀n ∃ n-Mahlo) → WellFounded on Std, or an object-theory derivation ZFC + {n-Mahlo} ⊢ WO(Std) as in KP1Y? | H: host-Lean theorem. Hypothesis "for every n an n-Mahlo cardinal exists" is an explicit premise (Lean cannot prove even one Mahlo cardinal exists), stated in the same universe as the J-hierarchy. Decided by the user 2026-10-27. |
| D-2 | claude | decided | Keep the paper's hypothesis (n-Mahlo over inaccessibles) or prove the stronger theorem with weakly n-Mahlo cardinals (S-1)? | Default, user may override: main theorem with weakly n-Mahlo cardinals (stronger theorem, simpler definition); the paper's n-Mahlo version as a corollary. This delivers both statements. |
| D-3 | claude | decided | Operation domain in Lean | Lean `expand : Forest → Nat → Option Forest` mirrors BTBM.FS exactly, returning none exactly where the reference throws (owner-root exhausted scan with n ≥ 1; invisible root). ∅[n] = some ∅ as in the reference. IsStd closes the seeds under defined operations, as in the paper. |
| D-4 | user | decided | Hierarchy for the main-theorem route: the paper's J-hierarchy (§5, blueprint Part B) or the reflection hierarchy (S-7 / P-U4-1, Part C)? | Part C, the reflection hierarchy (user, 2026-10-28: "just do whatever to formally verify the main theorem"). Part B is dropped from the build. |
| D-5 | user | decided | What must be verified, and by whom, from now on? | User, 2026-10-28: only the locked main theorem (the well-ordering of Std) matters. Fidelity of the proof route to the paper does not. Verification is by Lean alone (checks/lock/check.sh --final). No Codex checks during formalization; no G1 proof-fidelity sign-off. |

# Simplifications

| ID | Status | Summary | Found by |
|---|---|---|---|
| S-1 | agreed | Weakly n-Mahlo suffices: strong-limitness is never used; (13) holds for any uncountable cardinal | claude, codex |
| S-2 | agreed | §9 without the choice recursion: strictly monotone g(B)=min{σ(A): A∈Std, A≥B} (claude) or accessibility induction on the configuration maximum (codex) | claude, codex |
| S-3 | rejected | Base S_0 needs no capture: s = L*+ω works | claude |
| S-4 | agreed | Prove §6-§9 against an explicit semantic interface (levels, edges, capture, transport, budgets, (13), (14)); instantiate it with the J-hierarchy separately | claude, codex |
| S-5 | agreed | Extract the abstract final theorem first: closure + cofinality + seed configurations + strict descent ⇒ well-order | codex |
| S-6 | agreed | Engineering: one word library (reductions, traces, cancellation, delayed change); one typed continuation-hole operation; P as a separate invariant from L; label-free descent before labels; one finite-name amalgamation and packing lemma | codex |
| S-7 | proposed | P-U4-1: instantiate the S-4 interface with a reflection hierarchy on ordinals (Elem/Edge defined by well-founded recursion as "every diagram reflects/transports"), proving (13)/(14) from Mathlib Skolem hulls plus one condensation lemma, instead of building the J-hierarchy of §5 | claude |

# Risks

| ID | Risk | Mitigation |
|---|---|---|
| R-1 | §5 constructibility (J-hierarchy, canonical Σ1 Skolem functions, condensation, coded truth tables) is library-scale | S-4 interface; reuse audit T-007 |
| R-2 | Cofinality for arbitrary L caps of standard targets (§3.3-3.4) is the hardest finite gate; §8.5 Case 3 depends on it | Bounded tests (codex: 84,291 admissible caps, no counterexample); formalize early |
| R-3 | Occurrence identity, stack lookup, ι vs f maps, charts and frames in §6-§8 | Design occurrence/name types before proofs |
| R-4 | Bounded formula/certificate compiler and budgets (Δ0 checkers, histories, J_{v+ω}) | Schema-level transport lemma for realization problems instead of general coding, if host-Lean route |
| R-5 | Licensing: YesMetaZFC/BMS snapshot and BM4 have no license grant; CU, 1Y own code and Mathlib are Apache-2.0, KP1Y MIT | H can avoid the unlicensed code (Mathlib + narrow CU imports); O depends on YesMetaZFC |
| R-6 | CU proves condensation for fully elementary substructures of L-stages; the paper needs Σ1-elementary substructures of its own S/J hierarchy | Reuse CU collapse primitives and the history-budget proof structure; prove Σ1 J-condensation new |
