# Prover brief (T-022)

Goal: replace `sorry` with complete Lean proofs, so that eventually
`checks/lock/check.sh --final` passes, proving the locked `MainTheorem` (Std is well-ordered).
**Lean is the only verifier:** a proof counts when it compiles.

## Your setup
- **Worktree.** You work only in the git worktree and branch named in your prompt. Never touch
  `/home/dev/ggg/btbms-formalization` or any other worktree. Do not merge or push.
- **Build** from `<worktree>/lean`:
  `PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH lake build`. A full build takes about
  15 s. To check one file: `lake env lean BTBMS/Plan/U2.lean`. The modules form the chain
  `Plan/Spine → U1 → U2 → U3 → U4 → U5 → Main`.
- **Finding your declarations.** Each node's declarations are its `lean_decls` in
  `tracker/ledger.json`. Look up the node ID in the docstrings and comments of
  `lean/BTBMS/Plan/*.lean`.
- **Proof plans:**
  - each node's entry in `blueprint/U*.md` (search for the node ID);
  - the drafts in `blueprint/repairs/` for G-009…G-012.

  Plans are guidance. Any correct proof is fine.

## Rules
1. **Never edit** `lean/BTBMS/{Syntax,Expansion,Mahlo,Statement}.lean` (they are locked),
   `checks/`, `tracker/`, `blueprint/` or `lean/lakefile.toml`.
2. **Forbidden:** `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, and any
   option that weakens checking. `decide` and `simp` are fine.
3. **Using other declarations.** You may use any declaration that comes *earlier* in the module
   chain or file, whether it is proved or still `sorry`. Its statement is its contract.
   - If you need a fact that is not stated anywhere, add a helper lemma right before its first
     use, and prove it if you can.
   - Report every helper you leave as `sorry`.
   - **Name every new helper with your branch id as a suffix**, for example
     `forestAt_cons_D2`. Parallel branches cannot see each other's helpers, and duplicate
     names break the merge. Before you add a helper, grep `lean/` for an existing lemma that
     already says it.
4. **Statements.** Keep every statement as it is unless it is false or unprovable as stated.
   - In that case make the minimal change (an extra hypothesis, or a weaker conclusion) and
     record the reason in a comment above it. Give a concrete counterexample if you have one.
   - Report the change.
   - Never change the statement of something another proof already uses, because the build
     will tell you. Never change `FinalHyps`, `Hier.Interface` or `Main.lean`.
5. **Moving declarations.** You may move a declaration, keeping its name and statement, if the
   proof needs something declared later and nothing in between uses it.
6. **Scratch files** go only in `<worktree>/scratch/<your branch>/`, which is gitignored. Never
   use the shared session scratchpad: parallel provers overwrite each other's files there.
7. **Compute:**
   - Run one Lean or lake process at a time, and nothing in the background.
   - Kill any command that runs longer than 10 minutes.
   - No test sweeps. A quick `#eval!` on a few concrete forests is fine when you suspect a
     statement is false. Delete it afterwards.
8. **Stuck.** If a goal resists three genuinely different approaches, leave that `sorry` and
   move on. Report the exact goal state.
9. **Commit early.** Commit on your branch after each declaration you finish, with message
   `Prove <decl>`. Before your final commit, `lake build` must succeed.

## What to return
- The nodes and declarations you fully proved.
- The declarations still `sorry`: for each, why, and the stuck goal if it is short.
- Statement changes: old, new, and why.
- Your helper lemmas, and which of them are still `sorry`.
- The final build status and your last commit hash.
