# Cross-check 1 (T-005): points raised by only one reviewer

Each item gives a location and a question, not the other reviewer's conclusion.
Answer each independently from the paper. Write `tracker/review/codex-crosscheck-1.md`.
For each item give: your answer, the evidence (argument or explicit instance), and a
one-word verdict: `agree-gap` / `no-gap` / `unclear`. End with `STATUS: COMPLETE`.

## Q1 — §8.1 base case S_0, paper.txt:1211–1214
Is each step of the base-case argument needed as written? If any step can be removed
or replaced by something more elementary, give the replacement and check every
condition it must meet (limit/floor/host/environment conditions on the new owner, both
target heads, compatibility with low resources).

## Q2 — §2 inductions, paper.txt:194–236 (path nesting, barrier, capping)
For each of the three proofs, write down the exact induction predicate and the
well-founded order it is proved by, including how reads across height scopes are ordered.
Does the order as stated in the paper cover every read used in the inductive step,
in particular the reverse direction of the capping lemma ("Those earlier entry
assertions have already been uncapped")? Would a formalizer need information the paper
does not state?

## Root answer to your QUESTIONS FOR ROOT (domain decision)
Lean will define a total `FS` that mirrors `BTBM.FS` exactly (∅[n] = ∅, reference stopping
rule), and prove it agrees with the paper's partial operation on nonempty V∧I inputs.
Std is reachability from the seeds; the ∅ self-loop adds nothing. All decrease and
descent statements stay explicitly nonempty. No action needed from you on this.
