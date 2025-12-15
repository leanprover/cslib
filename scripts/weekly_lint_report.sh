#!/bin/bash
# Weekly lint report generator for CSLib
# Produces a table format compatible with Mathlib's weekly linting reports
# Usage: weekly_lint_report.sh <output_file> <sha> <repo> <run_id>

shopt -s extglob

lean_outfile=$1
SHA=$2
REPO=$3
RUN_ID=$4

# Filter out build progress lines and dependency checkout messages
filtered_out=$(grep -v '^✔' "${lean_outfile}" | grep -v '^trace: ' | grep -v '^info: .* checking out revision')
echo "$(wc -l <<<"${filtered_out}") lines of output" >&2

# Generate output
# Use uuidgen for portability (works on both Linux and macOS)
delimiter=$(uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid)

echo "zulip-message<<${delimiter}"
echo "CSLib weekly lint run [completed](https://github.com/${REPO}/actions/runs/${RUN_ID}) ([${SHA:0:7}](https://github.com/${REPO}/commit/${SHA}))."

# Categorize the output
counts=()

# Extract errors
if error_lines=$(grep '^error: ' <<<"${filtered_out}"); then
  # Remove the "error: file:line:col: " prefix to get just the description
  error_descriptions=$(sed 's/^error: [^:]*:[0-9]*:[0-9]*: //' <<<"${error_lines}")
  counts+=( "$(printf 'Errors: %d' "$(wc -l <<<"${error_lines}")")" )
  echo "$(wc -l <<<"${error_lines}") lines of errors" >&2
fi

# Extract warnings
if warning_lines=$(grep '^warning: ' <<<"${filtered_out}"); then
  # Remove the "warning: file:line:col: " prefix to get just the description
  warning_descriptions=$(sed 's/^warning: [^:]*:[0-9]*:[0-9]*: //' <<<"${warning_lines}")
  counts+=( "$(printf 'Warnings: %d' "$(wc -l <<<"${warning_lines}")")" )
  echo "$(wc -l <<<"${warning_lines}") lines of warnings" >&2
fi

# Extract info messages (excluding checkout messages already filtered)
if info_lines=$(grep '^info: ' <<<"${filtered_out}"); then
  # Remove the "info: file:line:col: " prefix to get just the description
  # Also handle plain "info: message" format (without file:line:col)
  info_descriptions=$(sed -e 's/^info: [^:]*:[0-9]*:[0-9]*: //' -e 's/^info: //' <<<"${info_lines}")
  counts+=( "$(printf 'Info messages: %d' "$(wc -l <<<"${info_lines}")")" )
  echo "$(wc -l <<<"${info_lines}") lines of info" >&2
fi

if (( ${#counts[@]} == 0 )); then
  echo "Build completed without lint messages."
else
  printf ' %s\n' "${counts[@]}"
  echo
fi

# Generate tables for each category
if [ -n "${error_lines}" ]; then
  echo "\`\`\`spoiler Error counts"
  echo "| | Error description |"
  echo "| ---: | --- |"
  sort <<<"${error_descriptions}" | uniq -c | sort -bgr | sed 's/^\( *[0-9][0-9]*\) \(.*\)$/| \1 | \2 |/'
  echo "\`\`\`"
  echo
fi

if [ -n "${warning_lines}" ]; then
  echo "\`\`\`spoiler Warning counts"
  echo "| | Warning description |"
  echo "| ---: | --- |"
  sort <<<"${warning_descriptions}" | uniq -c | sort -bgr | sed 's/^\( *[0-9][0-9]*\) \(.*\)$/| \1 | \2 |/'
  echo "\`\`\`"
  echo
fi

if [ -n "${info_lines}" ]; then
  echo "\`\`\`spoiler Info message counts"
  echo "| | Info message |"
  echo "| ---: | --- |"
  sort <<<"${info_descriptions}" | uniq -c | sort -bgr | sed 's/^\( *[0-9][0-9]*\) \(.*\)$/| \1 | \2 |/'
  echo "\`\`\`"
  echo
fi

echo "${delimiter}"
