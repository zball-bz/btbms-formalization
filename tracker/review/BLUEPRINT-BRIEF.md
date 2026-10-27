# T-017 brief: blind review of the blueprint

The blueprint is the lemma plan for proving the locked `MainTheorem` (`lean/BTBMS/Statement.lean`).
It has a spine and five units, 302 nodes. Its Lean signatures typecheck together, with `sorry`
proofs. After your review the user signs off on it (gate G1), and it becomes the formalization
skeleton. So your review decides what is fixed before anyone proves anything.

## Blindness
- Do not read `blueprint/verification/`, §2 of `blueprint/INTEGRATION.md`,
  `scratch/blueprint/*-verify/`, or `blueprint/repairs/`. The last is being written while you
  review; you will check it afterwards.
- Treat every "fixed", "verified" or "tested" in the blueprint as a claim to check, not as
  evidence.
- Review the commit named in the prompt. `blueprint/*.md` and `blueprint/lean/` will not change
  during your review.

## What to read
- `blueprint/00-spine.md`: design, shared interfaces, node ownership, FIRM declarations.
- The five units: `blueprint/U1-syntax-scans.md`, `U2-closure-cofinality.md`,
  `U3-records-packets.md`, `U4-hierarchy.md`, `U5-descent-main.md`.
- Their Lean files: `blueprint/lean/Spine.lean`, `U1.lean` … `U5.lean`.
- `blueprint/INTEGRATION.md` §1 and §3–§5: changes, node lists, critical path, layers.
- The paper is `paper/paper.txt` (the blueprint cites it as `txt:N`), and
  `tracker/GAPS.md` lists the gaps found in P1.

Typecheck everything together like this (about 10 s):
```
mkdir -p scratch/codex/bp && { grep -h '^import ' blueprint/lean/U*.lean; cat blueprint/lean/Spine.lean; for f in blueprint/lean/U{1,2,3,4,5}.lean; do grep -v '^import ' $f; done; } > scratch/codex/bp/check.lean && (cd lean && PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake env lean ../scratch/codex/bp/check.lean)
```
Append your own `#eval!` or `example` to a copy to test statements on concrete forests. Claude
found that only three definitions in the skeleton have `sorry` bodies:
- `Forest.instLinearOrder` and `Key.instLinearOrder` (only their proof fields);
- `Hier.jInterface` (waits on decision D-4).

Check that yourself as well.

## Questions
Give each question a verdict (`sound` / `sound-with-issues` / `unsound`) and concrete evidence: a
node, a line, a counterexample or a Lean check.

1. **Top level.**
   - Does the assembly prove exactly the locked `MainTheorem` from the `FinalHyps` fields? The
     assembly is spine §c.13: `FinalHyps`, `abstract_wellOrder`, `abstract_implies_main`, and the
     planned `Main.lean` term `std_isWellOrder := abstract_implies_main (fun hM => ⟨_, finalHyps jInterface hM⟩)`.
   - Is each field true as stated in Lean? It must not be too strong, imply `False`, or
     quantify over more than the paper's argument controls.
2. **The hierarchy interface and decision D-4.**
   - (a) Are the fields of `Hier.Interface` (spine §c.7) exactly what §6–§9 need? Does U5 use
     anything else?
   - (b) Is U4 Part C (§4, N4.3–N4.10, the "reflection hierarchy") a correct instance? Check
     these points, and try to break each one:
     - the well-founded recursion is well defined: realizability below `b` reads the
       primitives only below `b`;
     - N4.7 step 4 (condensation) goes through;
     - `θ`/`τ` express `ReflectsD`/`TransportsD` exactly;
     - (13)/(14) (N4.9a/b) follow from uncountability/regularity alone;
     - the universe lifts work.
   - (c) Your recommendation on D-4: Part B (the paper's J-hierarchy) or Part C, for the
     main-theorem route.
3. **Gap repairs G-001…G-005.** `tracker/GAPS.md` gives each gap. Its `repair` field in
   `tracker/ledger.json` and spine §h name the nodes that repair it. Is each repair correct and
   complete? Verdict per gap: `fixed` / `partial` / `not fixed`. Your check is what closes these
   gaps.
4. **The two chains in INTEGRATION.md §4** (25 and 23 nodes). For each node:
   - Is the statement true?
   - Could a formalizer follow the proof plan without inventing mathematics?

   Flag any step that only says "as in the paper", and any step that cites a node whose
   statement does not give what is used. Bounded tests are welcome: use the Lean bodies with
   `#eval!`, or the reference port in `checks/`.
5. **The riskiest nodes elsewhere.** Name the ten or so nodes you consider riskiest (statement
   possibly false, or plan incomplete), with reasons. Give your own assessment of the arguments
   the unit files mark as open:
   - U2 T3.8lo and T3.8li (with T3.2q);
   - U3 L4.2c;
   - U3 L7.5d with U5 L8.8f.

   For each, can you supply the missing argument, or find a counterexample?
6. **Lean signatures.** For the nodes of Q4 and the spine's FIRM declarations, does the Lean
   statement say what the prose says? Look for:
   - hypotheses that are contradictory or vacuous, which would make a lemma trivially provable
     and useless to its consumers;
   - conclusions weaker than what the consumers use.

## Deliverable: `tracker/review/codex-blueprint-review.md`
- A verdict per question with evidence.
- A findings table: id, node, severity (`fatal` / `major` / `minor`), issue, evidence, minimal fix.
- A table for G-001…G-005 with verdicts.
- Your D-4 recommendation.
- Write it incrementally, under a `STATUS: IN PROGRESS` line, so partial results survive. End
  with `STATUS: COMPLETE`.
- Priorities if time runs short: Q1–Q3 in full, then Q6 for the critical path, then Q4 and Q5
  by risk.

Write only that file and `scratch/codex/`. Do not edit `blueprint/`, `lean/`, `checks/` or
`tracker/` otherwise.
