# T-014 brief: independent statement-fidelity review

Claude wrote a Lean statement of the paper's main theorem. You review it **independently**:
decide from the paper and the reference code whether the Lean statement says what the
paper's §9 theorem says. This is the most important review in the project. Once the user
signs off (gate G2), the statement is locked, and every later proof only proves *this*
statement.

Treat the docstrings and comments in the Lean files as claims to check, not as evidence.

## What to review
- `lean/BTBMS/Syntax.lean`: forests, the syntax order, relative keys.
- `lean/BTBMS/Expansion.lean`: the operation `expand` (port of `FS` in `BTBM.ts`), seeds,
  `IsStd`.
- `lean/BTBMS/Mahlo.lean`: `StationaryIn`, `IsWeaklyMahlo`, `IsMahlo`, and the proved
  implication between them.
- `lean/BTBMS/Statement.lean`: `std_isWellOrder` (the `sorry`) and
  `std_isWellOrder_of_mahlo` (the paper's form).
- Supporting only: `lean/BTBMS/Sanity.lean`, `lean/DiffTest.lean`, `checks/lean/*`.

Build with `PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake build` inside `lean/`.
Run the differential test with `checks/lean/run.sh`.

Decisions already made, which you need not re-argue (but do flag consequences you think
were missed):
- D-1: a host-Lean theorem with the Mahlo hypothesis as a premise.
- D-2: the main theorem uses weakly n-Mahlo cardinals, with the paper's version as a corollary.
- D-3: the operation mirrors the reference, returning `none` exactly where the reference throws.

## Questions to answer, each with evidence
1. **Order:** is `<` on `Forest` exactly the paper's syntax order (§1.1) and the reference
   `compare`?
2. **Operation:** does `expand e n` equal the paper's `E[n]` on the inputs the paper defines
   it for, and the reference `FS` where the reference returns? Check the code line by line,
   not only through tests. Look for cases the tests cannot reach.
3. **Std:** is `IsStd` exactly "obtainable from the seeds L_m by finitely many defined
   operations"? Do the `none` cases and the ∅ self-loop change the set?
4. **Mahlo hypothesis:**
   - Is `IsMahlo n` the paper's M_n?
   - Is `StationaryIn` the standard notion of a set stationary in κ?
   - Could either definition be accidentally vacuous or trivial? Consider types, universes,
     the identification of cardinals with initial ordinals, and Mathlib's `IsClub`
     closure/cofinality conditions on `Set.Iio κ.ord`.
5. **The theorem:**
   - Does `IsWellOrder Std Std.lt`, under the hypothesis, say "(Std, <) is a well-order"?
   - Is quantifying the hypothesis in an arbitrary universe `u` faithful, or does it weaken
     or strengthen the theorem in a way that matters?
   - Can Lean's universe hierarchy discharge any part of the hypothesis?
6. **Anything that would let a proof succeed without proving the paper's theorem.** Examples:
   a definition that makes `Std` smaller than intended, an order that differs on some inputs,
   a hypothesis that is false for trivial reasons.

## Deliverable: `tracker/review/codex-statement-review.md`
- One verdict per question: `faithful` / `faithful-with-note` / `not-faithful`.
- Concrete evidence for each verdict: a code citation, an explicit expression, or a
  counterexample.
- A list of required changes (if any), each minimal.
- End with `STATUS: COMPLETE`.

Write only that file and `scratch/codex/`. Do not edit `lean/` or `checks/`.
