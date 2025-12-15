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
        # Skip build progress markers
        if line.startswith("✔"):
            continue
        # Skip trace output
        if line.startswith("trace:"):
            continue
        # Skip dependency checkout messages
        if line.startswith("info:") and "checking out revision" in line:
            continue
        filtered.append(line)
    return filtered


def extract_messages(lines: list[str], prefix: str) -> tuple[list[str], list[str]]:
    """
    Extract lines starting with the given prefix and their descriptions.

    Returns (matching_lines, descriptions) where descriptions have the
    "prefix: file:line:col: " or "prefix: " removed.
    """
    matching = [line for line in lines if line.startswith(f"{prefix}: ")]
    if not matching:
        return [], []

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
                descriptions.append(line)  # Keep original if no pattern matches

    return matching, descriptions


def format_table(descriptions: list[str], header: str) -> str:
    """Format descriptions as a Zulip spoiler block with a markdown table."""
    counts = Counter(descriptions)
    # Sort by count (descending), then alphabetically
    sorted_items = sorted(counts.items(), key=lambda x: (-x[1], x[0]))

    lines = [
        f"```spoiler {header}",
        f"| | {header.replace(' counts', ' description')} |",
        "| ---: | --- |",
    ]
    for desc, count in sorted_items:
        lines.append(f"| {count} | {desc} |")
    lines.append("```")
    lines.append("")

    return "\n".join(lines)


def main():
    args = parse_args()

    # Read and filter the build output
    with open(args.output_file, "r") as f:
        lines = [line.rstrip("\n") for line in f]

    filtered = filter_output(lines)
    print(f"{len(filtered)} lines of output", file=sys.stderr)

    # Extract categorized messages
    error_lines, error_descs = extract_messages(filtered, "error")
    warning_lines, warning_descs = extract_messages(filtered, "warning")
    info_lines, info_descs = extract_messages(filtered, "info")

    if error_lines:
        print(f"{len(error_lines)} lines of errors", file=sys.stderr)
    if warning_lines:
        print(f"{len(warning_lines)} lines of warnings", file=sys.stderr)
    if info_lines:
        print(f"{len(info_lines)} lines of info", file=sys.stderr)

    # Generate output in GitHub Actions multiline format
    delimiter = str(uuid.uuid4())
    short_sha = args.sha[:7]

    print(f"zulip-message<<{delimiter}")
    print(
        f"CSLib weekly lint run "
        f"[completed](https://github.com/{args.repo}/actions/runs/{args.run_id}) "
        f"([{short_sha}](https://github.com/{args.repo}/commit/{args.sha}))."
    )

    # Summary counts
    counts = []
    if error_lines:
        counts.append(f"Errors: {len(error_lines)}")
    if warning_lines:
        counts.append(f"Warnings: {len(warning_lines)}")
    if info_lines:
        counts.append(f"Info messages: {len(info_lines)}")

    if not counts:
        print("Build completed without lint messages.")
    else:
        for count in counts:
            print(f" {count}")
        print()

        # Generate tables
        if error_lines:
            print(format_table(error_descs, "Error counts"))
        if warning_lines:
            print(format_table(warning_descs, "Warning counts"))
        if info_lines:
            print(format_table(info_descs, "Info message counts"))

    print(delimiter)


if __name__ == "__main__":
    main()
