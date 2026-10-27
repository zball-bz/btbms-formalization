#!/usr/bin/env python3
"""Configurable Codex bounded checks. Passing finite checks is not proof.

Ported from scratch/codex/finite_model.py, finite_quick.py, capping_test.py,
general_l_test.py and hypothesis_counterexample.py. No reference source is used.
The parent runner supplies provenance hashes and wraps this compact raw report.
"""

import argparse
import itertools
import json
from pathlib import Path
import random
import sys
import traceback

import finite_model as model


REQUIRED_KEYS = {
    "finite-invariants": {
        "max_seed", "max_param", "generation_depth", "expansion_mu_cutoff",
        "state_limit", "cap_target_mu_cutoff", "word_pair_samples",
        "cofinality_pair_attempts", "cofinality_target_mu_cutoff",
        "cofinality_upper_mu_cutoff", "random_seed",
    },
    "finite-words": {"alphabet_size", "max_word_length"},
    "capping": {"attempts", "random_seed", "max_columns", "max_entries",
                "max_depth", "height_probability"},
    "general-l": {"attempts", "random_seed", "max_columns", "max_entries",
                  "max_depth", "height_probability", "max_param"},
    "hypothesis-counterexample": set(),
}


class Failure(Exception):
    def __init__(self, kind, **details):
        self.detail = {"kind": kind, **details}
        super().__init__(kind)


def require(condition, kind, **details):
    if not condition:
        raise Failure(kind, **details)


def finite_invariants(limits, counts, observations):
    rng = random.Random(limits["random_seed"])
    seen = {model.seed(n): [n] for n in range(limits["max_seed"] + 1)}
    front = list(seen)
    require(len(seen) <= limits["state_limit"], "state limit smaller than seed set")
    counts.update(generation_calls=0, generation_processed=0,
                  generation_size_skips=0, generation_rounds=0,
                  invariants=0, empty_invariants=0, safe_prefixes=0,
                  cap_candidates=0, admissible_cap_covers=0,
                  word_pairs=0, cofinality_pair_attempts=0,
                  cofinality_pair_checks=0)
    hit_limit = False
    for _ in range(limits["generation_depth"]):
        following = []
        for forest in front:
            if not forest:
                continue
            if model.mu(forest) > limits["expansion_mu_cutoff"]:
                counts["generation_size_skips"] += 1
                continue
            counts["generation_processed"] += 1
            for parameter in range(limits["max_param"] + 1):
                output = model.step(forest, parameter)
                counts["generation_calls"] += 1
                require(output < forest, "generated operation did not decrease",
                        witness=seen[forest], parameter=parameter, output=output)
                if output not in seen:
                    if len(seen) == limits["state_limit"]:
                        hit_limit = True
                        break
                    seen[output] = seen[forest] + [parameter]
                    following.append(output)
            if hit_limit:
                break
        counts["generation_rounds"] += 1
        front = following
        if hit_limit or not front:
            break
    counts["generated_states"] = len(seen)
    observations["state_limit_reached"] = hit_limit
    observations["size_unit"] = "compact-word atoms (mu); cutoff controls expansion inputs, not stored outputs"
    for forest, witness in seen.items():
        errors = model.properties(forest)
        if forest:
            counts["invariants"] += 1
        else:
            counts["empty_invariants"] += 1
        require(not errors, "generated invariant", witness=witness, errors=errors)
        if not forest:
            continue
        for length in range(model.mu(forest) + 1):
            output = model.prefix(forest, length)
            errors = model.properties(output)
            counts["safe_prefixes"] += 1
            require(not errors, "safe prefix invariant", witness=witness,
                    length=length, errors=errors)
        if model.mu(forest) > limits["cap_target_mu_cutoff"]:
            continue
        for cap in model.caps(forest):
            counts["cap_candidates"] += 1
            if model.properties(cap, "VIHAS"):
                continue
            parameter = model.mu(forest) + 1
            output = model.step(cap, parameter)
            counts["admissible_cap_covers"] += 1
            require(forest < output < cap, "upward cap cofinality",
                    witness=witness, cap=cap, parameter=parameter, output=output)
    states = list(seen)
    require(len(states) >= 2 or not (limits["word_pair_samples"] or
                                   limits["cofinality_pair_attempts"]),
            "sampling needs at least two states")
    for _ in range(limits["word_pair_samples"]):
        left, right = rng.sample(states, 2)
        counts["word_pairs"] += 1
        require((left < right) == (model.word(left) < model.word(right)),
                "word order mismatch", left_witness=seen[left], right_witness=seen[right])
    for _ in range(limits["cofinality_pair_attempts"]):
        target, upper = sorted(rng.sample(states, 2))
        counts["cofinality_pair_attempts"] += 1
        if (not upper or model.mu(target) > limits["cofinality_target_mu_cutoff"] or
                model.mu(upper) > limits["cofinality_upper_mu_cutoff"]):
            continue
        parameter = model.mu(target) + 1 if upper[-1] else 0
        output = model.step(upper, parameter)
        counts["cofinality_pair_checks"] += 1
        require(target <= output < upper, "generated-pair weak cofinality",
                target_witness=seen[target], upper_witness=seen[upper],
                parameter=parameter, output=output)


def finite_words(limits, counts, observations):
    alphabet = range(limits["alphabet_size"])
    words = [tuple(w) for length in range(limits["max_word_length"] + 1)
             for w in itertools.product(alphabet, repeat=length)]
    counts.update(words=len(words), scan_pairs=0, barrier_word_instances=0)
    for source in words:
        boundaries = [model.reduce(source[:i]) for i in range(len(source) + 1)]
        for query in words:
            cursor = model.scan(source, query)
            reduced = model.reduce(query)
            counts["scan_pairs"] += 1
            require(model.scan(source, reduced) == cursor and
                    boundaries[cursor] <= reduced and
                    (cursor == len(source) or reduced < boundaries[cursor + 1]),
                    "scan boundary or query reduction", source=source,
                    query=query, cursor=cursor, boundaries=boundaries)
        for final in alphabet:
            boundary = model.reduce(source + (final,))
            for query in words:
                if model.reduce(query) != query or query >= boundary:
                    continue
                for appended in range(final):
                    counts["barrier_word_instances"] += 1
                    require(model.reduce(query + (appended,)) < boundary,
                            "barrier word observation", source=source,
                            final=final, query=query, appended=appended)
    observations["scope"] = "all words within configured finite alphabet/length, including empty/equal cases"


# Its leading mark 2 is above all actual relative-key marks 0 and 1.
TOP = ((((2, 0), ()),),)


def decorated_properties(forest, capped=frozenset()):
    errors = set()

    def walk(current, stack, owners, path):
        for col_index, column in enumerate(current):
            number = len(stack)
            keys = tuple(TOP if path + ((col_index, index),) in capped else model.h(height, number)
                         for index, (_, height) in enumerate(column))
            visible = stack + [(column, keys)]
            boundary, start = (), number - 1
            for index, (parent, height) in enumerate(column):
                if not 0 <= parent < number:
                    errors.add("V")
                vertex, seen = start, set()
                while vertex != parent and 0 <= vertex < len(stack) and vertex not in seen:
                    seen.add(vertex)
                    source, source_keys = stack[vertex]
                    cursor = model.scan(source_keys, boundary)
                    vertex = source[cursor][0] if cursor < len(source_keys) else -1
                if vertex != parent:
                    errors.add("A")
                for owner, upper in owners:
                    if parent == owner and not model.h(height, number) < model.h(upper, owner):
                        errors.add("S")
                walk(height, visible, owners + [(number, height)],
                     path + ((col_index, index),))
                boundary = model.reduce(boundary + (keys[index],))
                start = parent
            stack = visible

    walk(forest, [], [], ())
    return errors


def cap_route(forest):
    path, result = (), []
    while forest and forest[-1]:
        path += ((len(forest) - 1, len(forest[-1]) - 1),)
        result.append(path)
        forest = forest[-1][-1][1]
    return result


def random_raw(rng, limits, start=0, depth=0):
    out = []
    for i in range(rng.randrange(limits["max_columns"] + 1)):
        number = start + i
        column = []
        for _ in range(rng.randrange(limits["max_entries"] + 1) if number else 0):
            parent = rng.randrange(number)
            height = (random_raw(rng, limits, number + 1, depth + 1)
                      if depth < limits["max_depth"] and
                      rng.random() < limits["height_probability"] else ())
            column.append((parent, height))
        out.append(tuple(column))
    return tuple(out)


def capping(limits, counts, observations):
    rng = random.Random(limits["random_seed"])
    counts.update(random_attempts=0, qualifying_vs_inputs=0,
                  independent_cappings=0, qualifying_with_a=0,
                  qualifying_without_a=0, qualifying_with_cap_route=0)
    for _ in range(limits["attempts"]):
        forest = random_raw(rng, limits)
        counts["random_attempts"] += 1
        actual = decorated_properties(forest)
        if "V" in actual or "S" in actual:
            continue
        counts["qualifying_vs_inputs"] += 1
        counts["qualifying_without_a" if "A" in actual else "qualifying_with_a"] += 1
        route = cap_route(forest)
        counts["qualifying_with_cap_route"] += bool(route)
        for bits in itertools.product((False, True), repeat=len(route)):
            capped = frozenset(path for path, selected in zip(route, bits) if selected)
            decorated = decorated_properties(forest, capped)
            counts["independent_cappings"] += 1
            require(("A" in actual) == ("A" in decorated), "independent capping A equivalence",
                    forest=forest, capped=list(capped), actual=sorted(actual),
                    decorated=sorted(decorated))
    observations["sampling"] = "attempts, not distinct expressions; V,S filter only (A,I,H not assumed)"


def random_internally_legal(rng, limits, start=0, owner=None, depth=0):
    out = []
    for i in range(rng.randrange(1, limits["max_columns"] + 1)):
        number = start + i
        count = (rng.randrange(1, limits["max_entries"] + 1) if owner is not None
                 else rng.randrange(limits["max_entries"] + 1))
        if number == 0:
            count = 0
        column = []
        for index in range(count):
            parent = rng.randrange(number)
            if index == 0 and owner is not None:
                parent = rng.randrange(owner, number)
            height = (random_internally_legal(rng, limits, number + 1, number, depth + 1)
                      if depth < limits["max_depth"] and
                      rng.random() < limits["height_probability"] else ())
            column.append((parent, height))
        column.sort(reverse=True)
        out.append(tuple(column))
    return tuple(out)


# Admissible but not P; saved from sample 1410 at random seed 83 during the audit.
NON_P_L_FIXTURE = (
    (),
    ((0, (((1, (((2, ()), (2, ()), (2, ())),)), (1, ()), (1, ())),
          ((1, (((3, ()), (0, ())),)), (1, ())),
          ((3, (((4, ()), (1, ())), ((5, ()),))),))), (0, ())),
    ((1, (((2, ()), (1, ())), ((2, (((4, ()), (0, ())),)),))), (1, ())),
)


def general_l(limits, counts, observations):
    rng = random.Random(limits["random_seed"])
    counts.update(random_attempts=0, random_l_inputs=0, random_non_p_inputs=0,
                  random_operations=0, random_safe_prefixes=0,
                  fixture_inputs=0, fixture_non_p_inputs=0,
                  fixture_operations=0, fixture_safe_prefixes=0)

    def check(forest, category, sample):
        for parameter in range(limits["max_param"] + 1):
            output = model.step(forest, parameter)
            counts[category + "_operations"] += 1
            errors = model.properties(output, "VIHAS")
            require(not errors and output < forest, "general-L operation",
                    category=category, sample=sample, forest=forest,
                    parameter=parameter, output=output, errors=errors)
        for length in range(model.mu(forest) + 1):
            output = model.prefix(forest, length)
            counts[category + "_safe_prefixes"] += 1
            errors = model.properties(output, "VIHAS")
            require(not errors, "general-L prefix", category=category,
                    sample=sample, forest=forest, length=length, errors=errors)

    require(not model.properties(NON_P_L_FIXTURE, "VIHAS") and
            bool(model.properties(NON_P_L_FIXTURE, "P")), "non-P L fixture precondition")
    counts["fixture_inputs"] = counts["fixture_non_p_inputs"] = 1
    check(NON_P_L_FIXTURE, "fixture", "non-P L")
    for sample in range(limits["attempts"]):
        forest = random_internally_legal(rng, limits)
        counts["random_attempts"] += 1
        if model.properties(forest, "VIHAS"):
            continue
        counts["random_l_inputs"] += 1
        counts["random_non_p_inputs"] += bool(model.properties(forest, "P"))
        check(forest, "random", sample)
    observations["sampling"] = "random counts allow duplicates; fixed non-P fixture is counted separately"
    observations["fixture_mu"] = model.mu(NON_P_L_FIXTURE)


def hypothesis_counterexample(limits, counts, observations):
    empty = ()
    lower = (((2, empty),),)
    returned = (((3, empty),),)
    upper = (((0, lower),), ((1, returned),))
    forest = ((), ((0, upper),))
    verdicts = {name: not model.properties(forest, name) for name in "VIHASP"}
    require(all(verdicts[name] for name in "VHP") and not verdicts["I"] and
            not verdicts["S"] and model.profile(returned) < model.profile(upper) and
            model.h(returned, 3) > model.h(upper, 1),
            "missing-I counterexample no longer witnesses claimed failure", properties=verdicts)
    counts.update(fixtures=1, property_checks=6, profile_comparisons=1, key_comparisons=1)
    observations.update(expected_counterexample=True, zero_based_expression=forest,
                        properties=verdicts, profile_H=model.profile(upper),
                        profile_J=model.profile(returned), h3_J_greater_than_h1_H=True)


CHECKS = {
    "finite-invariants": finite_invariants,
    "finite-words": finite_words,
    "capping": capping,
    "general-l": general_l,
    "hypothesis-counterexample": hypothesis_counterexample,
}


def validate_limits(check, limits):
    if set(limits) != REQUIRED_KEYS[check]:
        raise ValueError(f"{check}: expected exactly {sorted(REQUIRED_KEYS[check])}")
    for key, value in limits.items():
        if key == "height_probability":
            if not isinstance(value, (int, float)) or not 0 <= value <= 1:
                raise ValueError(f"{key} must lie between 0 and 1")
        elif type(value) is not int or value < 0:
            raise ValueError(f"{key} must be a nonnegative integer")
    if check == "finite-invariants" and limits["state_limit"] < 1:
        raise ValueError("state_limit must be positive")
    if check == "finite-words" and limits["alphabet_size"] < 1:
        raise ValueError("alphabet_size must be positive")
    if check == "general-l" and (limits["max_columns"] < 1 or limits["max_entries"] < 1):
        raise ValueError("general-l max_columns and max_entries must be positive")


def compact_failure(detail, build_dir, check):
    text = json.dumps(detail, ensure_ascii=False, default=str)
    if len(text) <= 4096:
        return detail
    diagnostic = build_dir / "diagnostics" / (check + "-failure.json")
    diagnostic.parent.mkdir(parents=True, exist_ok=True)
    diagnostic.write_text(text + "\n")
    return {"kind": detail.get("kind", "error"),
            "detail_preview": text[:3000], "detail_truncated": True,
            "reproducer_in_build_dir": str(diagnostic.relative_to(build_dir))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=CHECKS)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    counts, observations, failures = {}, {}, []
    build_dir = args.output.parent
    exit_code = 0
    try:
        config = json.loads(args.config.read_text())
        build_dir = Path(config["build_dir"])
        limits = config["limits"][args.check]
        validate_limits(args.check, limits)
        sys.setrecursionlimit(10000)
        CHECKS[args.check](limits, counts, observations)
    except Failure as error:
        failures.append(compact_failure(error.detail, build_dir, args.check))
        exit_code = 1
    except Exception as error:
        failures.append({"kind": "unexpected exception",
                         "type": type(error).__name__, "message": str(error),
                         "traceback": traceback.format_exc(limit=6)})
        exit_code = 2
    report = {"status": "fail" if failures else "pass", "counts": counts,
              "failure_count": len(failures), "failures": failures,
              "observations": {"fail_fast": True, **observations}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"check": args.check, "status": report["status"], "counts": counts}))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
