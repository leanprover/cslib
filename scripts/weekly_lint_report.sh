#!/bin/bash
# Weekly lint report generator for CSLib.
#
# Parses Lean build output and generates a Zulip-formatted report with tables
# showing grouped message counts. Output format matches Mathlib's weekly linting reports.
#
# Usage: weekly_lint_report.sh <output_file> <sha> <repo> <run_id>

set -euo pipefail

lean_outfile=$1
sha=$2
repo=$3
run_id=$4

short_sha=${sha:0:7}

# Filter out build progress and trace lines
filtered_out=$(grep -v '^✔' "${lean_outfile}" | grep -v '^trace: ' | grep -v 'checking out revision' || true)
echo "$(echo "${filtered_out}" | grep -c '' || echo 0) lines of output" >&2

# Extract and count messages by type
error_lines=$(echo "${filtered_out}" | grep '^error: ' || true)
warning_lines=$(echo "${filtered_out}" | grep '^warning: ' || true)
info_lines=$(echo "${filtered_out}" | grep '^info: ' || true)

# Strip prefix and file:line:col to get just descriptions
error_descriptions=$(echo "${error_lines}" | sed 's/^error: [^:]*:[0-9]*:[0-9]*: //' | sed 's/^error: //' || true)
warning_descriptions=$(echo "${warning_lines}" | sed 's/^warning: [^:]*:[0-9]*:[0-9]*: //' | sed 's/^warning: //' || true)
info_descriptions=$(echo "${info_lines}" | sed 's/^info: [^:]*:[0-9]*:[0-9]*: //' | sed 's/^info: //' || true)

# Count non-empty lines
count_lines() {
    local input="$1"
    if [ -z "${input}" ]; then
        echo 0
    else
        echo "${input}" | grep -c '' || echo 0
    fi
}

# Format descriptions as markdown table rows, grouped and sorted by count
format_table_rows() {
    sort | uniq -c | sort -bgr | sed 's/^ *\([0-9][0-9]*\) \(.*\)$/| \1 | \2 |/'
}

# Print a collapsible spoiler block with a markdown table
# Usage: print_spoiler_table <spoiler_title> <column_header> <descriptions>
print_spoiler_table() {
    local title="$1"
    local header="$2"
    local descriptions="$3"
    echo "\`\`\`spoiler ${title}"
    echo "|   | ${header} |"
    echo "| ---: | --- |"
    echo "${descriptions}" | format_table_rows
    echo "\`\`\`"
    echo
}

error_count=$(count_lines "${error_lines}")
warning_count=$(count_lines "${warning_lines}")
info_count=$(count_lines "${info_lines}")

echo "${error_count} errors" >&2
echo "${warning_count} warnings" >&2
echo "${info_count} info messages" >&2

# Output in GitHub Actions multiline format
delimiter=$(uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid 2>/dev/null || echo "EOF_${RANDOM}")
echo "zulip-message<<${delimiter}"

echo "CSLib weekly lint run [completed](https://github.com/${repo}/actions/runs/${run_id}) ([${short_sha}](https://github.com/${repo}/commit/${sha}))."

if [ "${error_count}" -eq 0 ] && [ "${warning_count}" -eq 0 ] && [ "${info_count}" -eq 0 ]; then
    echo "Build completed without lint messages."
else
    # Summary counts
    if [ "${error_count}" -gt 0 ]; then
        echo " Errors: ${error_count}"
    fi
    if [ "${warning_count}" -gt 0 ]; then
        echo " Warnings: ${warning_count}"
    fi
    if [ "${info_count}" -gt 0 ]; then
        echo " Info messages: ${info_count}"
    fi
    echo

    # Detail tables
    if [ "${error_count}" -gt 0 ]; then
        print_spoiler_table "Error counts" "Error description" "${error_descriptions}"
    fi

    if [ "${warning_count}" -gt 0 ]; then
        print_spoiler_table "Warning counts" "Warning description" "${warning_descriptions}"
    fi

    if [ "${info_count}" -gt 0 ]; then
        print_spoiler_table "Info message counts" "Info message" "${info_descriptions}"
    fi
fi

echo "${delimiter}"
