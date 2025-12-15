#!/usr/bin/env python3
"""
Weekly lint report generator for CSLib.

Parses Lean build output and generates a Zulip-formatted report with tables
showing grouped message counts. Output format matches Mathlib's weekly linting reports.
"""

import argparse
import re
import sys
import uuid
from collections import Counter
from dataclasses import dataclass

from tabulate import tabulate


@dataclass
class LintResults:
    """Parsed lint results from a Lean build."""

    errors: list[str]
    warnings: list[str]
    info_messages: list[str]

    @property
    def has_messages(self) -> bool:
        return bool(self.errors or self.warnings or self.info_messages)


def parse_args():
    parser = argparse.ArgumentParser(
        description="Generate a weekly lint report for posting to Zulip"
    )
    parser.add_argument("output_file", help="Path to the Lean build output file")
    parser.add_argument("--sha", required=True, help="Git commit SHA")
    parser.add_argument("--repo", required=True, help="GitHub repository (e.g., leanprover/cslib)")
    parser.add_argument("--run-id", required=True, help="GitHub Actions run ID")
    return parser.parse_args()


def filter_output(lines: list[str]) -> list[str]:
    """Filter out build progress and trace lines."""
    filtered = []
    for line in lines:
        if line.startswith("✔"):
            continue
        if line.startswith("trace:"):
            continue
        if line.startswith("info:") and "checking out revision" in line:
            continue
        filtered.append(line)
    return filtered


def extract_descriptions(lines: list[str], prefix: str) -> list[str]:
    """
    Extract message descriptions from lines starting with the given prefix.

    Strips the "prefix: file:line:col: " or "prefix: " to get just the description.
    """
    matching = [line for line in lines if line.startswith(f"{prefix}: ")]
    if not matching:
        return []

    # Pattern to match "prefix: file:line:col: description"
    pattern = re.compile(rf"^{prefix}: [^:]+:\d+:\d+: (.+)$")
    # Fallback pattern for "prefix: description" (without file:line:col)
    fallback_pattern = re.compile(rf"^{prefix}: (.+)$")

    descriptions = []
    for line in matching:
        match = pattern.match(line)
        if match:
            descriptions.append(match.group(1))
        else:
            fallback = fallback_pattern.match(line)
            if fallback:
                descriptions.append(fallback.group(1))
            else:
                descriptions.append(line)

    return descriptions


def parse_build_output(lines: list[str]) -> LintResults:
    """Parse filtered build output into structured lint results."""
    return LintResults(
        errors=extract_descriptions(lines, "error"),
        warnings=extract_descriptions(lines, "warning"),
        info_messages=extract_descriptions(lines, "info"),
    )


def format_table(descriptions: list[str], title: str, description_header: str) -> str:
    """Format descriptions as a Zulip spoiler block with a markdown table."""
    counts = Counter(descriptions)
    # Sort by count (descending), then alphabetically
    sorted_items = sorted(counts.items(), key=lambda x: (-x[1], x[0]))

    table_data = [[count, desc] for desc, count in sorted_items]
    table = tabulate(table_data, headers=["", description_header], tablefmt="github")

    return f"```spoiler {title}\n{table}\n```\n"


def format_report(results: LintResults, sha: str, repo: str, run_id: str) -> str:
    """Format lint results as a complete Zulip message."""
    short_sha = sha[:7]
    lines = [
        f"CSLib weekly lint run "
        f"[completed](https://github.com/{repo}/actions/runs/{run_id}) "
        f"([{short_sha}](https://github.com/{repo}/commit/{sha}))."
    ]

    if not results.has_messages:
        lines.append("Build completed without lint messages.")
        return "\n".join(lines)

    # Summary counts
    if results.errors:
        lines.append(f" Errors: {len(results.errors)}")
    if results.warnings:
        lines.append(f" Warnings: {len(results.warnings)}")
    if results.info_messages:
        lines.append(f" Info messages: {len(results.info_messages)}")
    lines.append("")

    # Detail tables
    if results.errors:
        lines.append(format_table(results.errors, "Error counts", "Error description"))
    if results.warnings:
        lines.append(format_table(results.warnings, "Warning counts", "Warning description"))
    if results.info_messages:
        lines.append(format_table(results.info_messages, "Info message counts", "Info message"))

    return "\n".join(lines)


def main():
    args = parse_args()

    # Read and filter the build output
    with open(args.output_file, "r") as f:
        lines = [line.rstrip("\n") for line in f]

    filtered = filter_output(lines)
    print(f"{len(filtered)} lines of output", file=sys.stderr)

    # Parse into structured results
    results = parse_build_output(filtered)

    if results.errors:
        print(f"{len(results.errors)} errors", file=sys.stderr)
    if results.warnings:
        print(f"{len(results.warnings)} warnings", file=sys.stderr)
    if results.info_messages:
        print(f"{len(results.info_messages)} info messages", file=sys.stderr)

    # Generate report
    report = format_report(results, args.sha, args.repo, args.run_id)

    # Output in GitHub Actions multiline format
    delimiter = str(uuid.uuid4())
    print(f"zulip-message<<{delimiter}")
    print(report)
    print(delimiter)


if __name__ == "__main__":
    main()
