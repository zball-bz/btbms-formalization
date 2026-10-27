# Bounded BTBMS checks

Run from the repository root:

```sh
checks/run.sh --quick
checks/run.sh --full
```

No argument means `--quick`; `--help` describes the entry point. The script also
resolves paths correctly when invoked by absolute path from another directory.
Requirements are Bash, Python 3.10+, and Node.js providing
`node:module.stripTypeScriptTypes` (tested here with Python 3.14.4 and Node 26.1.0).
The runner uses a Unix file lock to prevent concurrent runs from overwriting each
other. A first reference fetch additionally needs `curl` and network access.
There are no Python or npm package dependencies and no Lean build.

**Passing these checks is not proof.** They are finite falsification attempts and
definition checks. They neither establish universal closure/cofinality nor check
infinite set-theoretic certificates, J-condensation, the semantic least-failure
argument, or the Mahlo hypothesis. They are new packaged experiments, not a
reproduction of the unavailable programs/counts claimed in paper §10.

## Checks and claim coverage

Each row is one worker and one result JSON. Claim IDs refer to the `nodes` in
`tracker/ledger.json`. Testing a consequence of a claim is not proving the claim.

| Check | Packaged source / origin | What is checked | Ledger nodes |
|---|---|---|---|
| `reference-diff` | `js/run_checks.mjs`, `ref-paper.mjs`, `ref-loader.mjs`, `fixtures.mjs`; Codex reference diff and targeted harness | Independent paper operation versus actual pinned `BTBM.FS`; seeds, syntax/compact-word order, normalized height keys, strict decrease; fixed deletion, special, owner-root, equality and unilateral scan cases | D1.1, D1.4, D1.5, D1.6, D1.7, C1.8, T3.2 |
| `occurrence-graph` | `js/occurrence-graph.mjs` and the same worker; Codex graph and fixture harnesses | Direct parsing of actual reference outputs versus literal §6.1 occurrence-map stages; ordered role kinds, both R triples, same-forest elementary pairs, q/f domains/injections and persistent original occurrences. Includes fixed cases with copied closed side columns greater than stopping number t | D6.1, L6.2, D6.3 |
| `finite-invariants` | `python/finite_model.py`, `run_checks.py`; Codex finite model and finite quick harness | V/I/H/A/S/P on generated standards, all tested safe prefixes, word order, admissible upward-cap covers at μ(B)+1, sampled generated-pair cofinality and strict decrease | D1.3, C1.8, D1.9, D2.2, D2.3, D3.1, T3.2, T3.8 |
| `finite-words` | `python/run_checks.py`; Codex finite quick harness | Exhaustive small generic source/query words: boundary formula, final source cursor under query reduction, and the reduction/append observation used by the barrier | D2.1, L2.1, L2.3 |
| `capping` | `python/run_checks.py`; Codex capping harness | On sampled raw V,S inputs, actual A is equivalent to A after each selection of independently capped terminal-route last keys; I,H,A are not assumed as input filters | L2.4 |
| `general-l` | `python/run_checks.py`; Codex general-L harness | Operations and safe prefixes preserve V/I/H/A/S on sampled admissible inputs, including non-P inputs. A mandatory non-P fixture is reported separately from the random sample | T3.2 |
| `hypothesis-counterexample` | `python/run_checks.py`; Codex hypothesis counterexample | Rechecks the fixed V,H,P example that fails I,S. This is an expected counterexample to the *unrestricted* P⇒S claim, not a test failure or a counterexample to its corrected V∧I∧H version | L3.1 / G-002 |
| `claude-cofinality` | `claude/btbm.py`, `cofinality_test.py`; Claude's original port and adapted harness | Definedness/decrease during standard generation, then the strict μ(B)+1 cofinality bound or deletion cover on deterministic pairs B<E of stored standards. Upper inputs here are standard, not arbitrary L | D1.6, D1.7, L2.4, T3.2, T3.8 |

`claude/btbm.py` is byte-for-byte the supplied `scratch/claude/btbm.py`; the
cofinality driver adds bounded generation, sampled pairs, compact reports and
failure exits. The Codex models remain independently implemented from the paper;
their drivers were refactored to remove fixed scratch paths and import-time runs.
`source-provenance.json` records the original reviewer files and SHA-256s. Those
scratch paths are provenance only: a clean checkout needs no `scratch/` inputs.

The paper model is deliberately partial, while the reference has additional raw
behavior. Four fixed assertions check the known differences: the empty self-loop
at n=0,2, and the I-invalid internal-empty-column example at n=0,1. They are
reported as **expected domain checks**, not ignored mismatches. Changing any of
those outputs, failing a seed comparison, nondecrease, an unexpected exception,
or an unexpected model/graph mismatch fails the worker and the entry point.

## Quick and full limits

The authoritative, fully explicit limits and random seeds are in `limits.json`.
Parameters below are inclusive maxima. Size in the JS and Claude generators is
the number of ordinary-column plus entry vertices; μ in the Codex Python
generator is compact-word length. A generation cutoff is not a size cap on every
output that is compared. Recorded limits and stored/processed/queued counts
describe the sample; Claude's driver additionally counts rejected-output events.

| Workload | `--quick` | `--full` |
|---|---|---|
| Reference BFS | seeds 0–5, n=0–4, size≤60, at most 3,000 stored / 1,000 processed states | seeds 0–5, n=0–4, size≤80, at most 30,000 stored / 12,000 processed |
| Reference fixed cases | seeds 0–9; fixed standard witnesses and parameters 0–3; basic/domain cases | Same |
| Occurrence graph | at most 3,000 stored inputs, n=0–3; mandatory targeted cases; four side-height fixtures at n=0–4 | at most 30,000 stored inputs, n=0–3; same mandatory cases |
| Python standard generation | seeds 0–4, n=0–2, four generations, expansion μ cutoff 12, state cap 2,000; caps tested for μ(B)≤9 | seeds 0–6, n=0–3, six generations, expansion μ cutoff 60, state cap 10,000; caps for μ(B)≤25 |
| Python order/cofinality sampling | 2,000 word pairs / 1,000 cofinality pair attempts, with explicit target/upper μ filters | 20,000 / 5,000, with explicit μ filters |
| Generic words | alphabet {0,1,2}, lengths≤4: 14,641 source/query pairs | Same exhaustive finite alphabet/length range |
| Capping / general-L | 3,000 raw sampling attempts each, deterministic seeds 31 / 83, depth≤2 | 30,000 attempts each, same seeds/depth |
| Claude generation/pairs | seeds 0–3, n=0–2, size≤24, 500 stored / 500 processed, at most 2,500 pairs | seeds 0–4, n=0–3, size≤65, 5,000 stored / 5,000 processed, at most 50,000 pairs |
| Hypothesis counterexample | One fixed example | Same |

Quick mode is intended to finish within minutes on a normal development machine.
Each worker has a 180-second quick timeout or 1,800-second full timeout; a timeout
is a failure, not a passing truncated sample. Full mode is a larger **bounded**
experiment and can use substantially more memory/time. Neither mode explores all
standard expressions. Random raw input counts are sampled attempts, with
duplicates allowed. Mandatory fixtures are distinguished from generated or
random inputs. Claude's cofinality pairs use evenly spaced triangular ranks in
the sorted stored states, avoiding an allocation of all quadratic pairs.

## Reference source handling

The upstream snapshot has no supplied license grant. **No upstream TypeScript is
committed in `checks/`.** The runner uses the existing fetch script and the pin
in `reference-manifest.json`:

```sh
scripts/fetch-reference.sh \
  src/utils.ts \
  src/notation-definition.ts \
  src/notations/notation_utils.ts \
  src/notations/BM-like/BTBM.ts
```

If required files are absent, `run.sh` invokes that script for the missing files;
they are downloaded into the repository's already gitignored `reference/`.
When all files are present, runs are offline. Before any execution the runner
verifies **all four SHA-256s** against the manifest, then copies them into
`checks/.build/<mode>/reference/` and verifies the copies again. A mismatching
existing source is neither executed nor silently overwritten: the run fails.
Inspect the change before deliberately refetching with the command above.

The loader reads only these runtime copies. It extracts the exact comparator and
default-FS wrapper implementations, strips imports/types, and evaluates the
pinned source in a fresh Node VM with no ordinary Node APIs supplied. Node's VM
is **not claimed to be a security boundary**; the inspected pin and hash checks
are essential. TypeScript is neither included as a tracked file nor embedded in
the committed loader. Avoid force-adding `.build/` or `reference/`.

## Results and reproducibility

Tracked-size outputs are `checks/results/<mode>-<check>.json` and
`<mode>-summary.json`. Every JSON records the mode, input SHA-256s, explicit limits,
runtime versions, status and counts. The per-check files also name ledger nodes,
the reference pin, and bounded diagnostic details. Reference copies, generated
states, full raw reports and logs stay under ignored `checks/.build/<mode>/`.
The graph worker verifies that its generated-state artifact matches the current
mode, generation limits and successful reference run; its SHA-256 is recorded.

Each result fingerprints the complete packaged executable/configuration set,
the paper text/PDF, fetch script and verified reference inputs. This intentionally
over-records inputs for independent Python checks, making the tested package
snapshot explicit. README changes do not affect those executable hashes. Final
JSONs are capped/compacted for review (64 KiB target per file), while full failure
details remain in the raw ignored report. Counts and limits are never compacted.

A failed preflight produces a failing summary and no stale per-check results for
that mode. The graph check is skipped if reference generation fails. Other
independent checks still run, but any failure or skip makes `run.sh` exit nonzero.
There is no silent success based only on a printed report, and no git add/commit
operation in the runner. Root can commit the harness and compact result JSONs
after review.

The supplied result snapshot is from `--quick`. `--full` was configured but not
run for this packaging task.
