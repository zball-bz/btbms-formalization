"""Run bounded diagnostics, preserving provenance and failing on any failed check.

No theorem is established by this runner. Runtime reference copies, generated
states, raw worker reports and logs are confined to the ignored .build directory.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

CHECKS = Path(__file__).resolve().parent
ROOT = CHECKS.parent
RESULTS = CHECKS / "results"
MAX_RESULT_BYTES = 64 * 1024
CHECK_NAMES = (
    "reference-diff", "occurrence-graph", "finite-invariants", "finite-words",
    "capping", "general-l", "hypothesis-counterexample", "claude-cofinality",
)
CLAIMS = {
    "reference-diff": ["D1.1", "D1.4", "D1.5", "D1.6", "D1.7", "C1.8", "T3.2"],
    "occurrence-graph": ["D6.1", "L6.2", "D6.3"],
    "finite-invariants": ["D1.3", "C1.8", "D1.9", "D2.2", "D2.3", "D3.1", "T3.2", "T3.8"],
    "finite-words": ["D2.1", "L2.1", "L2.3"],
    "capping": ["L2.4"],
    "general-l": ["T3.2"],
    "hypothesis-counterexample": ["L3.1"],
    "claude-cofinality": ["D1.6", "D1.7", "L2.4", "T3.2", "T3.8"],
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def write_json(path: Path, value: object) -> None:
    # Atomic replacement prevents a partial file from masquerading as a result.
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
    temporary.replace(path)


def source_hashes() -> dict[str, str]:
    files = [
        p for p in CHECKS.rglob("*")
        if p.is_file() and ".build" not in p.parts and "results" not in p.parts
        and p.suffix in {".py", ".mjs", ".sh", ".json"}
    ]
    files += [ROOT / "scripts/fetch-reference.sh", ROOT / "paper/paper.txt",
              ROOT / "paper/BTBMS_Independent_Reconstruction_20261027.pdf"]
    return {relative(p): sha256(p) for p in sorted(set(files))}


def prepare_reference(build: Path) -> tuple[dict, dict[str, str]]:
    manifest = json.loads((CHECKS / "reference-manifest.json").read_text())
    source = ROOT / "reference/ne-rewritten"
    missing = [name for name in manifest["files"] if not (source / name).is_file()]
    if missing:
        print("Fetching missing pinned reference files with scripts/fetch-reference.sh", flush=True)
        subprocess.run(["bash", str(ROOT / "scripts/fetch-reference.sh"), *missing],
                       cwd=ROOT, check=True, timeout=120)
    result = {}
    for name, expected in manifest["files"].items():
        path = source / name
        actual = sha256(path)
        if actual != expected:
            raise RuntimeError(f"Reference SHA-256 mismatch for {relative(path)}; "
                               "refusing to execute or overwrite it. See checks/README.md.")
        destination = build / "reference" / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
        if sha256(destination) != expected:
            raise RuntimeError(f"Runtime reference copy failed verification: {name}")
        result[relative(path)] = actual
    return manifest, result


def compact_detail(value: object, depth: int = 0) -> object:
    """Bound diagnostic examples, never counts or limits; full raw data stays in .build."""
    if depth > 7:
        return "[truncated; see raw worker report]"
    if isinstance(value, str):
        return value if len(value) <= 1800 else value[:1800] + "...[truncated]"
    if isinstance(value, list):
        items = [compact_detail(x, depth + 1) for x in value[:8]]
        if len(value) > 8:
            items.append({"omitted_items": len(value) - 8})
        return items
    if isinstance(value, dict):
        return {str(k): compact_detail(v, depth + 1) for k, v in list(value.items())[:40]}
    return value


def bounded_report(report: dict) -> dict:
    if len(json.dumps(report).encode()) <= MAX_RESULT_BYTES:
        return report
    for key in list(report):
        if key not in {"schema_version", "check", "mode", "status", "counts", "limits",
                       "input_sha256s", "runtime", "ledger_nodes", "reference", "exit_code"}:
            report[key] = compact_detail(report[key])
    report["details_truncated"] = True
    if len(json.dumps(report).encode()) > MAX_RESULT_BYTES:
        # Never silently discard a failure status or alter the counted sample.
        report["failures"] = [{"message": "Diagnostic detail exceeds result budget; see raw_report."}]
        for key in ("observations", "examples", "expected_domain_differences"):
            report.pop(key, None)
    return report


def command_for(name: str, config: Path, output: Path, node: str) -> list[str]:
    if name in {"reference-diff", "occurrence-graph"}:
        command = [node, str(CHECKS / "js/run_checks.mjs"), name]
    elif name == "claude-cofinality":
        command = [sys.executable, "-B", str(CHECKS / "claude/cofinality_test.py")]
    else:
        command = [sys.executable, "-B", str(CHECKS / "python/run_checks.py"), name]
    return command + ["--config", str(config), "--output", str(output)]


def execute(mode: str) -> int:
    build = CHECKS / ".build" / mode
    build.mkdir(parents=True, exist_ok=True)
    (build / "logs").mkdir(exist_ok=True)
    (build / "raw").mkdir(exist_ok=True)
    RESULTS.mkdir(exist_ok=True)
    for name in (*CHECK_NAMES, "summary"):
        (RESULTS / f"{mode}-{name}.json").unlink(missing_ok=True)

    limits = json.loads((CHECKS / "limits.json").read_text())[mode]
    inputs = source_hashes()
    runtime = {"python": platform.python_version()}
    summary = {"schema_version": 1, "check": "summary", "mode": mode,
               "input_sha256s": inputs, "limits": limits, "runtime": runtime,
               "status": "fail", "counts": {"passed": 0, "failed": 0, "skipped": 0},
               "checks": [], "passing_is_not_proof": True}
    try:
        node = shutil.which("node")
        if not node:
            raise RuntimeError("Node.js with node:module.stripTypeScriptTypes is required.")
        probe = subprocess.run(
            [node, "--input-type=module", "-e",
             "import {stripTypeScriptTypes} from 'node:module'; "
             "if(typeof stripTypeScriptTypes !== 'function') process.exit(1); "
             "console.log(process.version);"],
            text=True, capture_output=True, check=True, timeout=15)
        runtime["node"] = probe.stdout.strip()
        manifest, reference_hashes = prepare_reference(build)
        inputs.update(reference_hashes)
        reference = {"repository": manifest["repository"], "revision": manifest["revision"]}
        summary["reference"] = reference
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        summary["failures"] = [{"stage": "preflight", "message": str(error)[:1800]}]
        write_json(RESULTS / f"{mode}-summary.json", summary)
        print(f"Preflight failed: {error}", file=sys.stderr)
        return 1

    config = build / "config.json"
    write_json(config, {"mode": mode, "build_dir": str(build),
                        "reference_dir": str(build / "reference"), "limits": limits})
    statuses = {}
    for name in CHECK_NAMES:
        print(f"[{mode}] {name} ...", flush=True)
        raw_path = build / "raw" / f"{name}.json"
        raw_path.unlink(missing_ok=True)
        log_path = build / "logs" / f"{name}.log"
        effective_limits = dict(limits[name])
        effective_limits["runner_timeout_seconds"] = 180 if mode == "quick" else 1800
        if name == "occurrence-graph":
            effective_limits["state_generation"] = limits["reference-diff"]
        report = {"schema_version": 1, "check": name, "mode": mode,
                  "ledger_nodes": CLAIMS[name], "input_sha256s": inputs,
                  "limits": effective_limits, "runtime": runtime, "reference": reference,
                  "counts": {}, "failures": [], "passing_is_not_proof": True,
                  "raw_report": relative(raw_path), "log": relative(log_path)}
        if name == "occurrence-graph" and statuses.get("reference-diff") != "pass":
            report.update(status="skipped", exit_code=None,
                          failures=[{"message": "reference-diff did not pass; no stale states consumed"}])
        else:
            timeout = effective_limits["runner_timeout_seconds"]
            try:
                env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", NODE_NO_WARNINGS="1")
                with log_path.open("w") as log:
                    result = subprocess.run(command_for(name, config, raw_path, node), cwd=ROOT,
                                            stdout=log, stderr=subprocess.STDOUT, env=env,
                                            timeout=timeout, check=False)
                raw = json.loads(raw_path.read_text())
                if not isinstance(raw, dict) or not isinstance(raw.get("counts"), dict):
                    raise ValueError("Worker report must be an object with a counts object")
                if raw.get("status") not in {"pass", "fail"}:
                    raise ValueError("Worker report must explicitly say pass or fail")
                report.update({k: raw[k] for k in raw
                               if k not in report or k in {"counts", "failures"}})
                report["status"] = "pass" if result.returncode == 0 and raw["status"] == "pass" else "fail"
                report["exit_code"] = result.returncode
                if report["status"] == "fail" and not report["failures"]:
                    report["failures"] = [{"message": "Worker failed; inspect its log"}]
                if report["status"] == "pass" and report["failures"]:
                    raise ValueError("Worker claimed pass with nonempty failures")
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                report.update(status="fail", exit_code=None,
                              failures=[{"message": str(error)[:1800]}])
        statuses[name] = report["status"]
        path = RESULTS / f"{mode}-{name}.json"
        report = bounded_report(report)
        write_json(path, report)
        summary["checks"].append({"check": name, "status": report["status"], "result": relative(path)})
        bucket = {"pass": "passed", "fail": "failed", "skipped": "skipped"}[report["status"]]
        summary["counts"][bucket] += 1
        print(f"  {report['status']}: {json.dumps(report['counts'], sort_keys=True)}", flush=True)

    summary["counts"]["checks"] = len(CHECK_NAMES)
    summary["status"] = "pass" if summary["counts"]["passed"] == len(CHECK_NAMES) else "fail"
    write_json(RESULTS / f"{mode}-summary.json", summary)
    print(f"{mode}: {summary['counts']['passed']}/{len(CHECK_NAMES)} checks passed. Passing is not proof.", flush=True)
    return 0 if summary["status"] == "pass" else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--quick", action="store_true", help="small deterministic samples (default)")
    group.add_argument("--full", action="store_true", help="larger bounded samples; still not a proof")
    args = parser.parse_args()
    (CHECKS / ".build").mkdir(exist_ok=True)
    with (CHECKS / ".build/run.lock").open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("Another checks/run.sh is running; refusing to overwrite its state.", file=sys.stderr)
            return 2
        return execute("full" if args.full else "quick")


if __name__ == "__main__":
    raise SystemExit(main())
