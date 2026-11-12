#!/usr/bin/env python3
"""Reproduce the pinned proof, target audits, and exact-module kernel replays."""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent.parent
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def without_comments(text):
    """Remove nested Lean comments and strings before the static source scan."""
    out = []
    index = 0
    depth = 0
    in_string = False
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            if text[index] == "\\":
                index += 2
            elif text[index] == '"':
                in_string = False
                index += 1
            else:
                index += 1
        elif pair == "/-":
            depth = 1
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif text[index] == '"':
            in_string = True
            index += 1
        else:
            out.append(text[index])
            index += 1
    return "".join(out)


def module_order():
    order = []
    visited = set()

    def visit(module):
        if module in visited:
            return
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.is_file():
            return
        visited.add(module)
        source = without_comments(path.read_text(encoding="utf-8-sig"))
        for imports in re.findall(r"^import\s+([^\r\n]+)", source, re.MULTILINE):
            for dependency in imports.split():
                visit(dependency)
        order.append(module)

    for module in ("Erdos319Sharp", "Submission", "Solution", "Challenge"):
        visit(module)
    return order


def input_hashes():
    paths = [ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "scripts/verify.py", "scripts/Replay.lean", "verification/targets.json",
        "verification/Targets.lean", "verification/source-modules.json",
    )]
    paths.extend(ROOT.joinpath(*module.split(".")).with_suffix(".lean")
                 for module in module_order())
    return {path.relative_to(ROOT).as_posix(): digest(path) for path in sorted(set(paths))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--setup", action="store_true", help="Fetch the pinned dependencies and Mathlib cache")
    parser.add_argument("--clean", action="store_true", help="Remove this checkout's local build output before checking")
    parser.add_argument("--lake", default="lake", help="Pinned Lake executable")
    parser.add_argument("--output", type=Path, default=ROOT / ".verification")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    logs = output / "logs"
    logs.mkdir(exist_ok=True)
    scratch = output / "tmp"
    scratch.mkdir(exist_ok=True)
    environment = dict(os.environ)
    environment.update({
        "LEAN_NUM_THREADS": "1",
        "TEMP": str(scratch), "TMP": str(scratch), "TMPDIR": str(scratch),
        "MATHLIB_CACHE_DIR": str(output / "cache" / "mathlib"),
        "LAKE_CACHE_DIR": str(output / "cache" / "lake"),
        "XDG_CACHE_HOME": str(output / "cache"),
    })
    expected_toolchain = (ROOT / "lean-toolchain").read_text().strip()
    results = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "status": "running", "toolchain": expected_toolchain,
        "worker_threads": 1, "commands": [], "module_replays": [],
        "trust": "Local modules are replayed against the pinned imported environment.",
    }

    def checkpoint():
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    def run(label, command):
        log = logs / (label + ".log")
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        clock = time.monotonic()
        print(label, flush=True)
        with log.open("w", encoding="utf-8") as stream:
            process = subprocess.run(command, cwd=ROOT, env=environment,
                                     stdout=stream, stderr=subprocess.STDOUT, check=False)
        record = {
            "label": label, "command": ["lake" if command[0] == args.lake else command[0], *command[1:]],
            "started_utc": started, "elapsed_seconds": time.monotonic() - clock,
            "exit_code": process.returncode, "log": "logs/" + log.name,
            "log_sha256": digest(log),
        }
        results["commands"].append(record)
        checkpoint()
        if process.returncode:
            raise RuntimeError(f"{label} failed with exit code {process.returncode}. See {log}.")
        return log.read_text(encoding="utf-8", errors="replace")

    try:
        results["proof_commit"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        results["input_sha256_before"] = input_hashes()
        versions = run("tool-versions", [args.lake, "env", "lean", "--version"])
        expected_version = expected_toolchain.split(":v")[-1]
        if ("version " + expected_version) not in versions:
            raise RuntimeError("The active Lean version differs from lean-toolchain.")
        results["lean_version_output"] = versions.strip()
        manifest = read_json(ROOT / "lake-manifest.json")
        pins = {package["name"]: package["rev"] for package in manifest["packages"]}
        if args.setup:
            run("mathlib-cache", [args.lake, "exe", "cache", "get"])
            new_pins = {p["name"]: p["rev"] for p in read_json(ROOT / "lake-manifest.json")["packages"]}
            if pins != new_pins:
                raise RuntimeError("Dependency setup changed the locked revisions.")
        results["dependencies"] = []
        for package in manifest["packages"]:
            directory = ROOT / ".lake" / "packages" / package["name"]
            revision = subprocess.check_output(
                ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
            changed = subprocess.check_output(
                ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True).strip()
            if revision != package["rev"] or changed:
                raise RuntimeError("Dependency revision or tracked-source mismatch for " + package["name"])
            results["dependencies"].append({"name": package["name"], "revision": revision, "tracked_sources_clean": True})
        modules = module_order()
        declared = read_json(ROOT / "verification" / "source-modules.json")
        if modules != [item["module"] for item in declared]:
            raise RuntimeError("Local module manifest differs from the import closure.")
        for item in declared:
            if digest(ROOT / item["path"]) != item["sha256"]:
                raise RuntimeError("Frozen source hash mismatch for " + item["path"])
            text = without_comments((ROOT / item["path"]).read_text(encoding="utf-8-sig"))
            forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b|debug\.skipKernelTC", text)
            if forbidden:
                raise RuntimeError("Trust-sensitive source requires review in " + item["path"] + ": " + repr(forbidden))
        results["local_modules"] = modules
        results["static_source_check"] = "passed"
        if args.clean:
            build = ROOT / ".lake" / "build"
            if build.exists():
                resolved = build.resolve()
                if resolved != ROOT.resolve() / ".lake" / "build":
                    raise RuntimeError("Refusing to clean a redirected build directory.")
                shutil.rmtree(build)
        results["clean_local_build_requested"] = args.clean
        checkpoint()
        if args.clean:
            for number, module in enumerate(modules, start=1):
                run(f"build-{number:03d}-{module}", [args.lake, "--no-cache", "--fail-fast", "build", "+" + module])
        run("default-build", [args.lake, "--no-cache", "--fail-fast", "build"])
        audit = run("target-axioms", [args.lake, "env", "lean", "-DwarningAsError=true", "verification/Targets.lean"])
        expected_targets = read_json(ROOT / "verification" / "targets.json")["axiom_targets"]
        closures = {}
        for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit):
            closures[name] = [value.strip() for value in body.split(",") if value.strip()]
        for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
            closures[name] = []
        for target in expected_targets:
            if target not in closures:
                raise RuntimeError("Missing axiom output for " + target)
            if set(closures[target]) - STANDARD_AXIOMS:
                raise RuntimeError("Unexpected axiom dependency for " + target)
        results["axiom_closures"] = {name: closures[name] for name in expected_targets}
        for number, module in enumerate(modules, start=1):
            artifact = ROOT.joinpath(".lake", "build", "lib", "lean", *module.split(".")).with_suffix(".olean")
            before = digest(artifact)
            text = run(f"replay-{number:03d}-{module}",
                       [args.lake, "env", "lean", "--run", "scripts/Replay.lean", module])
            if f"replaying {module} (exact module)" not in text or digest(artifact) != before:
                raise RuntimeError("Replay marker or artifact integrity mismatch for " + module)
            results["module_replays"].append({"module": module, "artifact_sha256": before, "passed": True})
            checkpoint()
        results["input_sha256_after"] = input_hashes()
        if results["input_sha256_before"] != results["input_sha256_after"]:
            raise RuntimeError("A proof or reproduction input changed during verification.")
        results["status"] = "passed"
        results["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        checkpoint()
        print("Verification passed for the pinned source inputs.", flush=True)
        return 0
    except Exception as error:
        results["status"] = "failed"
        results["error"] = str(error)
        results["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        checkpoint()
        print(str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
