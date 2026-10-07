#!/usr/bin/env python3
# Copyright (c) 2026 Chris Henson. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Chris Henson

"""Prepare representative kernel benchmarks without importing a built catalogue row.

Run from the repository root. Selection is deterministic and samples independent
certificate fragments by their equation, symmetry, branch and retirement density.
The benchmark retains the current generated metadata, reason proofs and retirement
bundle proofs, so their cost is measured rather than hidden in a built row import.

This tool prepares source and summarizes Lean JSON diagnostics; it does not run
Lean, remove build outputs, or claim that a sample predicts a whole-row build.
Use Lean MCP diagnostics first during development. Preparation reads the row's
Lake setup JSON and prints a command with its exact Lean options: plain
``lake env lean`` does not inherit the package's weak linter options. Use the
printed command, capturing GNU ``time -v`` separately. Full-row acceptance still
requires two complete, fresh row builds.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import shlex


DECLARATION = re.compile(
    r"^(?:(?:private|public|noncomputable) +)*(?:def|theorem) +([A-Za-z0-9_]+)", re.M)
TREE_NAME = re.compile(r"\bcertificateTree\d+\b")


def fingerprint(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def measurement_command(source: Path, output: Path, setup: Path | None = None) -> dict:
    """Reuse actual Lake options without importing the target row or its build artifacts."""
    relative_source = source.resolve().relative_to(Path.cwd().resolve())
    if setup is None:
        setup = Path(".lake/build/ir") / relative_source.with_suffix(".setup.json")
    if not setup.is_file():
        module = ".".join(relative_source.with_suffix("").parts)
        setup_output = "/tmp/cslib-ra-benchmark-setup.json"
        command = shlex.join(["lake", "--json", "query", f"+{module}:setup"])
        raise ValueError(f"missing Lake setup {setup}; build only its dependencies and setup with\n"
                         f"  {command} > {setup_output}\n"
                         f"then rerun prepare with --setup {setup_output}")
    raw = setup.read_bytes()
    options = json.loads(raw)["options"]
    if not isinstance(options, dict):
        raise ValueError(f"invalid Lean options in {setup}")
    flags = []
    for name, value in sorted(options.items()):
        if type(value) is bool:
            rendered = str(value).lower()
        elif type(value) in (int, str):
            rendered = str(value)
        else:
            raise ValueError(f"unsupported Lean option value for {name}: {value!r}")
        flags.append(f"-D{name}={rendered}")
    return {"setup_path": str(setup), "setup_sha256": fingerprint(raw),
            "lean_options": options,
            "command": ["lake", "env", "lean", "--json", *flags, str(output)],
            "note": "Use this command to retain the recorded Lake options. The prepared source "
                    "forces synchronous elaboration for declaration timing; logs alone cannot "
                    "verify which command was executed."}


def select_fragments(data: dict, chunk_size: int, samples: int) -> dict:
    """Mirror the documented fragment boundary rule, then sample its independent leaves."""
    nodes = data["nodes"]
    boundaries: set[int] = set()
    costs: list[int] = []

    def children(index: int) -> tuple[int, ...]:
        node = nodes[index]
        return ((node[4], node[5]) if node[0] == 2 else
                (node[4],) if node[0] in (3, 4) else ())

    for index in range(len(nodes)):
        descendants = children(index)
        while 1 + sum(1 if child in boundaries else costs[child]
                      for child in descendants) > chunk_size:
            boundaries.add(max((child for child in descendants if child not in boundaries),
                               key=lambda child: costs[child]))
        costs.append(1 + sum(1 if child in boundaries else costs[child]
                             for child in descendants))
    boundaries.add(data["root"])
    candidates = []
    equation_count = len(data["equations"])
    for ordinal, root in enumerate(sorted(boundaries)):
        pending, tags, equation, symmetry, references = [root], Counter(), 0, 0, 0
        while pending:
            index = pending.pop()
            if index != root and index in boundaries:
                references += 1
                continue
            node = nodes[index]
            tags[node[0]] += 1
            if node[0] == 4 and "bundles" in data:
                # One retirement node can justify several constraints in format 3.
                mask = data["bundles"][node[3]][1]
                equation += (mask & ((1 << equation_count) - 1)).bit_count()
                symmetry += (mask >> equation_count).bit_count()
            elif node[0] in (1, 3, 4):
                witness = data["reasons"][node[3]][0] if "reasons" in data else node[3]
                equation += witness < equation_count
                symmetry += witness >= equation_count
            pending.extend(children(index))
        if references:
            continue
        candidates.append({"ordinal": ordinal, "root": root, "nodes": sum(tags.values()),
                           "equation": equation, "symmetry": symmetry,
                           "branch": tags[2], "retirement": tags[4], "accept": tags[0],
                           "reject": tags[1], "force": tags[3], "result": nodes[root][6]})

    chosen, used = [], set()
    # Within each density stratum, spread the sample over the source ordering.
    for stratum_index, category in enumerate(("symmetry", "equation", "branch", "retirement")):
        quota = samples // 4 + (stratum_index < samples % 4)
        eligible = [c for c in candidates if c["ordinal"] not in used]
        eligible.sort(key=lambda c: (-c[category] / c["nodes"], c["ordinal"]))
        pool = sorted(eligible[:max(quota, len(eligible) // 4)], key=lambda c: c["ordinal"])
        for position in range(min(quota, len(pool))):
            index = position * (len(pool) - 1) // max(1, min(quota, len(pool)) - 1)
            candidate = dict(pool[index], stratum=category)
            chosen.append(candidate)
            used.add(candidate["ordinal"])
    return {"chunk_size": chunk_size, "fragments": len(boundaries),
            "independent_fragments": len(candidates), "requested_samples": samples,
            "samples": sorted(chosen, key=lambda c: c["ordinal"])}


def declaration_category(name: str, declaration: str) -> str:
    proof = "theorem " in declaration.splitlines()[0]
    if name.startswith("certificateTree"):
        return "certificate_data"
    if name.startswith("chunk"):
        if name.endswith("_checked"):
            return "chunk_kernel_check"
        if proof:
            return "chunk_semantic_proof"
        return "chunk_data"
    if name.lower().startswith("bundle"):
        return "bundle_proof" if proof else "bundle_data"
    if name.lower().startswith("reason"):
        return "reason_proof" if proof else "reason_data"
    return "metadata_proof" if proof else "metadata_data"


def prepare(source: str, selection: dict, row: str) -> tuple[str, list[dict]]:
    """Keep fresh metadata, selected chunks, and exactly their tree dependencies."""
    if "import Cslib.Foundations.RelationAlgebra.SearchBundles" not in source:
        raise ValueError("source is not the retirement-bundle backend; refusing an old-row benchmark")
    if re.search(rf"^.*import +Cslib\.Foundations\.RelationAlgebra\.Catalogue\.Counts\.{row}\b",
                 source, re.M):
        raise ValueError("benchmark source must not import the previously compiled target row")
    matches = list(DECLARATION.finditer(source))
    declarations = {match[1]: source[match.start():
                    matches[index + 1].start() if index + 1 < len(matches) else len(source)]
                    for index, match in enumerate(matches)}
    tree_start = next((match.start() for match in matches
                       if match[1].startswith("certificateTree")), None)
    if tree_start is None:
        raise ValueError("no certificate tree declarations found")
    selected, needed_trees = set(), set()
    for sample in selection["samples"]:
        prefix = f"chunk{sample['ordinal']:05d}"
        names = {name for name in declarations if name.startswith(prefix)}
        required = {prefix + suffix for suffix in
                    ("State", "Data", "References", "References_valid", "_checked", "_count")}
        if not required <= names:
            raise ValueError(f"missing numeric chunk declarations for {prefix}: {required - names}")
        references = declarations.get(prefix + "References", "")
        if re.search(r"some +chunk\d+", references):
            raise ValueError(f"{prefix} is not independent; JSON and source boundaries disagree")
        selected.update(names)
        for name in names:
            needed_trees.update(TREE_NAME.findall(declarations[name]))
    pending = list(needed_trees)
    while pending:
        name = pending.pop()
        if name not in declarations:
            raise ValueError(f"missing tree dependency {name}")
        for dependency in TREE_NAME.findall(declarations[name]):
            if dependency != name and dependency not in needed_trees:
                needed_trees.add(dependency)
                pending.append(dependency)
    selected.update(needed_trees)
    namespace = re.findall(r"^namespace +([^\n]+)$", source, re.M)
    if len(namespace) != 1:
        raise ValueError("expected a single generated row namespace")
    benchmark = source[:tree_start] + "\n".join(
        declarations[match[1]].rstrip() for match in matches if match[1] in selected)
    benchmark += f"\n\nend {namespace[0]}\n"
    # Timers are commands, so declaration doc comments cannot precede them.
    # Keep their text as ordinary comments in this temporary measurement file.
    benchmark = benchmark.replace("/--", "/-")
    # Phase options can be attached to adjacent declarations by extraction. Force
    # every phase synchronous so #time includes the corresponding kernel check.
    benchmark = re.sub(r"(set_option +Elab\.async +)true\b", r"\1false", benchmark)
    marker = "@[expose] public section"
    if marker not in benchmark:
        raise ValueError("missing generated public section")
    benchmark = benchmark.replace(marker, marker + "\n\nset_option Elab.async false", 1)
    benchmark = DECLARATION.sub(lambda match: "set_option profiler true in\n#time " + match[0],
                                benchmark)
    # The inserted #time command precedes each declaration on the same line.
    locations = []
    timed = re.compile(r"^#time +((?:(?:private|public|noncomputable) +)*"
                       r"(?:def|theorem) +([A-Za-z0-9_]+))", re.M)
    previous, line = 0, 1
    for match in timed.finditer(benchmark):
        line += benchmark.count("\n", previous, match.start())
        previous = match.start()
        locations.append({"line": line,
                          "name": match[2],
                          "category": declaration_category(match[2], match[1])})
    return benchmark, locations


def report(log: Path, manifest: dict) -> dict:
    """Summarize #time diagnostics; kernel sub-times are intentionally not double-counted."""
    declarations = manifest["declarations"]
    lines = [declaration["line"] for declaration in declarations]
    timings, errors = [], []
    for raw in log.read_text().splitlines():
        try:
            diagnostic = json.loads(raw)
        except json.JSONDecodeError:
            continue
        message = diagnostic.get("data", diagnostic.get("message", ""))
        if diagnostic.get("severity") == "error":
            errors.append(message)
        time = re.fullmatch(r"time: ([0-9.]+)(ms|s)\s*", message)
        if time is None:
            continue
        line = diagnostic.get("pos", {}).get("line", 0)
        index = bisect_right(lines, line) - 1
        if index < 0:
            raise ValueError(f"unmapped timing diagnostic at line {line}")
        milliseconds = float(time[1]) * (1000 if time[2] == "s" else 1)
        timings.append(dict(declarations[index], milliseconds=milliseconds))
    totals = Counter()
    for timing in timings:
        totals[timing["category"]] += timing["milliseconds"]
    seen = {timing["name"] for timing in timings}
    missing = [declaration["name"] for declaration in declarations
               if declaration["name"] not in seen]
    return {"source_sha256": manifest["source_sha256"], "errors": errors,
            "requested_lean_options": manifest.get("measurement", {}).get("lean_options"),
            "complete": not errors and not missing and len(timings) == len(declarations),
            "missing_declarations": missing,
            "timed_declarations": len(timings), "expected_declarations": len(declarations),
            "category_milliseconds": dict(totals), "declarations": timings,
            "note": "Synchronous declaration timings exclude parsing, command linters, imports "
                    "and final artifact emission; they are not whole-build timings."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    subparsers = parser.add_subparsers(dest="action", required=True)
    select = subparsers.add_parser("select", help="select independent fragments from certificate JSON")
    prepare_parser = subparsers.add_parser("prepare", help="prepare a benchmark of fresh generated source")
    for command in (select, prepare_parser):
        command.add_argument("--data", type=Path, required=True)
        command.add_argument("--samples", type=int, default=64)
        command.add_argument("--chunk-size", type=int, default=8000)
    prepare_parser.add_argument("--row", required=True)
    prepare_parser.add_argument("--source", type=Path, required=True)
    prepare_parser.add_argument("--output", type=Path, required=True)
    prepare_parser.add_argument("--manifest", type=Path, required=True)
    prepare_parser.add_argument("--setup", type=Path,
                                help="actual Lake setup JSON (default: infer from --source)")
    summarize = subparsers.add_parser("report", help="summarize captured Lean --json diagnostics")
    summarize.add_argument("--log", type=Path, required=True)
    summarize.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    if args.action == "report":
        print(json.dumps(report(args.log, json.loads(args.manifest.read_text())), indent=2))
        return
    if args.samples < 1 or args.chunk_size < 4:
        parser.error("--samples must be positive and --chunk-size must be at least four")
    raw = args.data.read_bytes()
    data = json.loads(raw)
    selection = select_fragments(data, args.chunk_size, args.samples)
    selection["data_sha256"] = fingerprint(raw)
    if args.action == "select":
        print(json.dumps(selection, indent=2))
        return
    if "reasons" not in data or "bundles" not in data:
        parser.error("prepare requires the cached retirement-bundle certificate format")
    source = args.source.read_bytes()
    benchmark, declarations = prepare(source.decode(), selection, args.row)
    try:
        measurement = measurement_command(args.source, args.output, args.setup)
    except (ValueError, KeyError, OSError) as error:
        parser.error(str(error))
    manifest = dict(selection, row=args.row, source_sha256=fingerprint(source),
                    benchmark_sha256=fingerprint(benchmark.encode()), declarations=declarations,
                    measurement=measurement)
    args.output.write_text(benchmark)
    args.manifest.write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Prepared {len(selection['samples'])} independent fragments "
          "and all metadata/reason/bundle proofs")
    print("Measure with the recorded Lake options (keep stderr separate from JSON diagnostics):")
    print(shlex.join(measurement["command"]) + " > benchmark.jsonl 2> benchmark.stderr")


if __name__ == "__main__":
    main()
