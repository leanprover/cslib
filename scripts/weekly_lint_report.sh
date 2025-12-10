#!/bin/bash
# Simplified weekly lint report generator for CSLib
# Usage: weekly_lint_report.sh <output_file> <sha> <repo> <run_id>

lean_outfile=$1
SHA=$2
REPO=$3
RUN_ID=$4

# Filter out build progress lines and dependency checkout messages
filtered_out=$(grep -v '^✔' "${lean_outfile}" | grep -v '^trace: ' | grep -v '^info: .* checking out revision')

# Count message types (handle grep returning non-zero exit code when no matches)
error_count=$(grep -c '^error: ' <<<"${filtered_out}" 2>/dev/null) || error_count=0
warning_count=$(grep -c '^warning: ' <<<"${filtered_out}" 2>/dev/null) || warning_count=0
info_count=$(grep -c '^info: ' <<<"${filtered_out}" 2>/dev/null) || info_count=0

# Generate output
delimiter=$(cat /proc/sys/kernel/random/uuid)

echo "zulip-message<<${delimiter}"
echo "CSLib weekly lint run [completed](https://github.com/${REPO}/actions/runs/${RUN_ID}) ([${SHA:0:7}](https://github.com/${REPO}/commit/${SHA}))."
echo ""

if [ "$error_count" -eq 0 ] && [ "$warning_count" -eq 0 ] && [ "$info_count" -eq 0 ]; then
  echo "Build completed without lint messages."
else
  echo "Summary:"
  [ "$error_count" -gt 0 ] && echo "- Errors: ${error_count}"
  [ "$warning_count" -gt 0 ] && echo "- Warnings: ${warning_count}"
  [ "$info_count" -gt 0 ] && echo "- Info messages: ${info_count}"
fi

echo "${delimiter}"
