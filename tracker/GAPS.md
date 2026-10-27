# Gap register

Generated from `tracker/ledger.json` by `tracker/refresh.py`; do not edit by hand.

| ID | Status | Severity | Location | Summary | Found by | Confirmed by |
|---|---|---|---|---|---|---|
| G-001 | confirmed | exposition | §1.2 txt:95-101 | Operation domain: ∅[n] undefined in paper but ∅ in BTBM.ts; paper stopping rule undefined on forests with internal empty columns, reference stops there | claude, codex |  |
| G-002 | confirmed | repairable | §3.1 txt:263-268 | "P implies S" is false without V, I, H | codex | claude |
| G-003 | confirmed | repairable | §4 txt:646-686; §7.1 txt:1045-1065; §8.5 txt:1474 | Admitted records (§4) and the packet class quantified in S_n (§7) are not exact predicates; closure of the class under the §8.5 constructions is not checkable as written | claude, codex |  |
| G-004 | confirmed | exposition | §5.2 txt:864-866 | "The hull contains the whole J_b" must mean J_b ∈ H, not J_b ⊆ H | codex | claude |
| G-005 | confirmed | exposition | §10 txt:1516-1534 | The "accompanying Python programs" of §10 are not supplied | codex | claude |
| G-006 | suspected | repairable | §2 txt:194-236 | Path nesting, barrier and capping proofs do not state their induction predicates and orders across height scopes | claude |  |

## G-001 — Operation domain: ∅[n] undefined in paper but ∅ in BTBM.ts; paper stopping rule undefined on forests with internal empty columns, reference stops there

**Detail:** Agree on nonempty V∧I inputs, hence on L ⊇ Std. Instance: E=[[],[(0,[[]])]] (violates I): paper route stuck; reference FS(E,0)=[[]].

**Fix:** Root decision: total Lean FS mirroring BTBM.FS, plus an agreement lemma with the paper operation on nonempty V∧I inputs; all decrease statements explicitly nonempty.

**Refs:** claude C-01, codex X-01, codex X-02


## G-002 — "P implies S" is false without V, I, H

**Detail:** E=[[],[(0,H)]], H=[[(0,K)],[(1,J)]], K=[[(2,∅)]], J=[[(3,∅)]]: V, H, P hold, I fails at H's first column, and h_3(J)=(1,0)… > h_1(H)=(0,0)…, so S fails. Claude re-derived π(H)=(1,1), π(J)=(0,1) and the S comparison by hand (non-blind: done after reading X-03). The proof uses I to make first-entry branches pure towers; the intended V∧I∧H version is the one used later.

**Fix:** State V∧I∧H∧P ⇒ S; make V, I, H standing hypotheses of the profile construction.

**Refs:** codex X-03


## G-003 — Admitted records (§4) and the packet class quantified in S_n (§7) are not exact predicates; closure of the class under the §8.5 constructions is not checkable as written

**Detail:** Records need explicit occurrence maps, actual scan indices, retained marked-entry/pre-entry equations, repair lists with surviving-role injections. Packets need a fixed grammar for auxiliary diagrams and labels, closed under factorization, joint cap, joint repair, the §7.3 extension and the readmission in §8.5 Cases 2-3. Boundary instance (codex): in L_2 a special step at parameter 1 replaces the marked outer entry, so "confined" must require survival of the marked occurrence. Neither reviewer found a counterexample to the intended statement.

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

**Detail:** Codex judged §2 sound. Sent to Codex as a blind question (CROSSCHECK-1 Q2).

**Fix:** State each induction predicate and well-founded order explicitly.

**Refs:** claude C-06


# Decisions

| ID | Owner | Status | Question | Answer / impact |
|---|---|---|---|---|
| D-1 | user | open | Which theorem is the deliverable: a host-Lean theorem (∀n ∃ n-Mahlo) → WellFounded on Std, or an object-theory derivation ZFC + {n-Mahlo} ⊢ WO(Std) as in KP1Y? | Object theory multiplies the cost (all of §5 and the combinatorics inside the object theory) but can reuse KP1Y's YesMetaZFC stack; host Lean can use Mathlib (ordinals, regular cardinals, clubs/stationary sets). |
| D-2 | user | open | Keep the paper's hypothesis (n-Mahlo over inaccessibles) or prove the stronger theorem with weakly n-Mahlo cardinals (S-1)? |  |
| D-3 | claude | decided | Operation domain in Lean | Total FS mirroring BTBM.FS, with an agreement lemma on nonempty V∧I inputs (G-001). |

# Simplifications

| ID | Status | Summary | Found by |
|---|---|---|---|
| S-1 | agreed | Weakly n-Mahlo suffices: strong-limitness is never used; (13) holds for any uncountable cardinal | claude, codex |
| S-2 | agreed | §9 without the choice recursion: strictly monotone g(B)=min{σ(A): A∈Std, A≥B} (claude) or accessibility induction on the configuration maximum (codex) | claude, codex |
| S-3 | proposed | Base S_0 needs no capture: s = L*+ω works | claude |
| S-4 | agreed | Prove §6-§9 against an explicit semantic interface (levels, edges, capture, transport, budgets, (13), (14)); instantiate it with the J-hierarchy separately | claude, codex |
| S-5 | agreed | Extract the abstract final theorem first: closure + cofinality + seed configurations + strict descent ⇒ well-order | codex |
| S-6 | agreed | Engineering: one word library (reductions, traces, cancellation, delayed change); one typed continuation-hole operation; P as a separate invariant from L; label-free descent before labels; one finite-name amalgamation and packing lemma | codex |

# Risks

| ID | Risk | Mitigation |
|---|---|---|
| R-1 | §5 constructibility (J-hierarchy, canonical Σ1 Skolem functions, condensation, coded truth tables) is library-scale | S-4 interface; reuse audit T-007 |
| R-2 | Cofinality for arbitrary L caps of standard targets (§3.3-3.4) is the hardest finite gate; §8.5 Case 3 depends on it | Bounded tests (codex: 84,291 admissible caps, no counterexample); formalize early |
| R-3 | Occurrence identity, stack lookup, ι vs f maps, charts and frames in §6-§8 | Design occurrence/name types before proofs |
| R-4 | Bounded formula/certificate compiler and budgets (Δ0 checkers, histories, J_{v+ω}) | Schema-level transport lemma for realization problems instead of general coding, if host-Lean route |
