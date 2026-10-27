"""Deterministic, bounded packaging of Claude's cofinality experiment.

Adapted from scratch/claude/cofinality_test.py (SHA-256
fb218cd25ad2061c58e32a72a18df6aa8c969256d20df4dce4a0a1825b3d0cd6).
The sibling btbm.py is the original port, copied without alteration.  This runner
adds explicit budgets, compact reports, reproducible pair selection and nonzero
failure exits; it does not change the expansion implementation.

Checks definedness and decrease while generating standard inputs; tests the
paper's cofinality bound on a deterministic sample of generated B < E pairs.
Passing finite checks is not proof of any universal assertion.
"""
from __future__ import annotations

import argparse
from collections import deque
from functools import lru_cache
import hashlib
import json
from math import isqrt
from pathlib import Path
import sys

# Also supports `python3 -I checks/claude/cofinality_test.py ...`.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from btbm import FS, mu, seed, show, size  # noqa: E402

CHECK_NAME = "claude-cofinality"
DEFAULT_CACHE_ENTRIES = 256


def validate_limits(raw):
    names = ("max_seed", "max_parameter", "size_cutoff", "max_states",
             "max_processed", "max_pairs")
    limits = {}
    for name in names:
        value = raw[name]
        if type(value) is not int or value < (0 if name in names[:2] else 1):
            raise ValueError(f"invalid integer limit {name}: {value!r}")
        limits[name] = value
    cache = raw.get("cache_entries", DEFAULT_CACHE_ENTRIES)
    if type(cache) is not int or cache < 1:
        raise ValueError("cache_entries must be a positive integer")
    limits["cache_entries"] = cache
    if limits["max_states"] < limits["max_seed"] + 1:
        raise ValueError("max_states must accommodate every requested seed")
    if any(size(seed(m)) > limits["size_cutoff"]
           for m in range(limits["max_seed"] + 1)):
        raise ValueError("every requested seed must fit size_cutoff")
    return limits


def expression_summary(expression):
    """Inputs are size-bounded; also cap textual diagnostics on unexpected data."""
    display = show(expression)
    return {"display": display[:500], "display_truncated": len(display) > 500,
            "size": size(expression), "mu": mu(expression),
            "sha256": hashlib.sha256(repr(expression).encode()).hexdigest()}


def witness_summary(witness):
    return {"seed_and_parameters": list(witness[:128]),
            "length": len(witness), "truncated": len(witness) > 128,
            "sha256": hashlib.sha256(repr(witness).encode()).hexdigest()}


def pair_indices(state_count, sample_count):
    """Evenly spaced ranks in triangular enumeration of all sorted B < E pairs.

    Rank 0 corresponds to (B index 0, E index 1).  This avoids allocating an
    O(state_count**2) list.  When all pairs fit, exactly every pair is visited.
    """
    total = state_count * (state_count - 1) // 2
    selected = min(total, sample_count)
    for k in range(selected):
        rank = 0 if selected == 1 else k * (total - 1) // (selected - 1)
        ei = (1 + isqrt(1 + 8 * rank)) // 2
        bi = rank - ei * (ei - 1) // 2
        yield bi, ei


def run(limits):
    counts = {
        "seed_inputs": limits["max_seed"] + 1,
        "stored_states": 0, "processed_states": 0,
        "nonempty_processed_states": 0, "queued_unprocessed_states": 0,
        "generation_operation_calls": 0, "generation_strict_decreases": 0,
        "oversize_output_events": 0, "storage_limit_rejection_events": 0,
        "generation_undefined_or_exception": 0, "generation_nondecrease": 0,
        "available_ordered_pairs": 0, "selected_pairs": 0, "checked_pairs": 0,
        "deletion_pairs": 0, "limit_pairs": 0,
        "cofinality_operation_calls": 0, "cofinality_cache_hits": 0,
        "cofinality_strict_decreases": 0,
        "cofinality_undefined_or_exception": 0, "cofinality_nondecrease": 0,
        "strict_bound_failures": 0, "deletion_cover_failures": 0,
        "diagnostic_weak_witnesses": 0,
    }
    failures = []
    known = {}
    queue = deque()
    for m in range(limits["max_seed"] + 1):
        e = seed(m)
        if e not in known:
            known[e] = (m,)
            queue.append(e)

    def fail(kind, E=None, B=None, **fields):
        record = {"kind": kind, **fields}
        if E is not None:
            record["E"] = expression_summary(E)
            record["E_witness"] = witness_summary(known[E])
        if B is not None:
            record["B"] = expression_summary(B)
            record["B_witness"] = witness_summary(known[B])
        if len(failures) < 8:
            failures.append(record)

    while queue and counts["processed_states"] < limits["max_processed"]:
        e = queue.popleft()
        counts["processed_states"] += 1
        if not e:
            continue  # empty FS self-loop is intentionally excluded from decrease
        counts["nonempty_processed_states"] += 1
        for n in range(limits["max_parameter"] + 1):
            counts["generation_operation_calls"] += 1
            try:
                f = FS(e, n)
            except Exception as exc:
                counts["generation_undefined_or_exception"] += 1
                fail("generation_operation_exception", e, parameter=n,
                     exception_type=type(exc).__name__, message=str(exc)[:500])
                break
            if not f < e:
                counts["generation_nondecrease"] += 1
                fail("generation_nondecrease", e, parameter=n,
                     output=expression_summary(f))
                break
            counts["generation_strict_decreases"] += 1
            if size(f) > limits["size_cutoff"]:
                counts["oversize_output_events"] += 1
            elif f not in known:
                if len(known) < limits["max_states"]:
                    known[f] = (*known[e], n)
                    queue.append(f)
                else:
                    counts["storage_limit_rejection_events"] += 1
        if failures:
            break

    counts["stored_states"] = len(known)
    counts["queued_unprocessed_states"] = len(queue)
    states = sorted(known)
    total_pairs = len(states) * (len(states) - 1) // 2
    counts["available_ordered_pairs"] = total_pairs
    counts["selected_pairs"] = min(total_pairs, limits["max_pairs"])

    @lru_cache(maxsize=limits["cache_entries"])
    def checked_fs(e, n):
        counts["cofinality_operation_calls"] += 1
        try:
            out = FS(e, n)
        except Exception as exc:
            counts["cofinality_undefined_or_exception"] += 1
            fail("cofinality_operation_exception", e, parameter=n,
                 exception_type=type(exc).__name__, message=str(exc)[:500])
            raise
        if not out < e:
            counts["cofinality_nondecrease"] += 1
            fail("cofinality_nondecrease", e, parameter=n,
                 output=expression_summary(out))
            raise ValueError("cofinality output did not strictly decrease")
        counts["cofinality_strict_decreases"] += 1
        return out

    if not failures:
        for bi, ei in pair_indices(len(states), limits["max_pairs"]):
            B, E = states[bi], states[ei]
            if not B < E or not E:
                fail("invalid_pair_schedule", E, B, indices=[bi, ei])
                break
            counts["checked_pairs"] += 1
            try:
                if not E[-1]:
                    counts["deletion_pairs"] += 1
                    if not B <= checked_fs(E, 0):
                        counts["deletion_cover_failures"] += 1
                        fail("deletion_cover", E, B)
                else:
                    counts["limit_pairs"] += 1
                    bound = mu(B) + 1
                    if not any(B < checked_fs(E, n) for n in range(1, bound + 1)):
                        counts["strict_bound_failures"] += 1
                        # Preserve the original finite weak-form diagnostic.  A
                        # negative diagnostic is NOT a universal nonexistence claim.
                        weak_n = next((n for n in range(bound + 6)
                                       if B <= checked_fs(E, n)), None)
                        if weak_n is not None:
                            counts["diagnostic_weak_witnesses"] += 1
                        fail("strict_cofinality_bound", E, B, bound=bound,
                             weak_witness_parameter=weak_n,
                             diagnostic_parameter_max=bound + 5)
            except Exception as exc:
                if not failures:
                    fail("unexpected_cofinality_exception", E, B,
                         exception_type=type(exc).__name__, message=str(exc)[:500])
            if failures:
                break
    counts["cofinality_cache_hits"] = checked_fs.cache_info().hits
    return {
        "status": "fail" if failures else "pass",
        "counts": counts,
        "failures": failures,
        "limits_used": limits,
        "observations": {
            "pair_selection": "evenly spaced triangular ranks in sorted stored states",
            "pair_sample_complete_for_stored_states": counts["checked_pairs"] == total_pairs,
            "generation_queue_exhausted": not queue,
            "storage_limit_hit": counts["storage_limit_rejection_events"] > 0,
            "processing_limit_hit": bool(queue) and counts["processed_states"] >= limits["max_processed"],
            "scope": "stored states have seed/operation witnesses; cofinality upper inputs are standard, not arbitrary L",
            "failure_policy": "stop on first failure; finite weak-form diagnostic is not a universal claim",
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        config = json.loads(args.config.read_text())
        limits = validate_limits(config["limits"][CHECK_NAME])
        result = run(limits)
    except Exception as exc:
        result = {"status": "fail", "counts": {}, "failures": [{
            "kind": "runner_exception", "exception_type": type(exc).__name__,
            "message": str(exc)[:500]}]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(f"{CHECK_NAME}: {result['status']} ({result['counts'].get('checked_pairs', 0)} pairs)")
    return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
