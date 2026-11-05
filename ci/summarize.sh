#!/usr/bin/env bash
# Writes a table of the results of ci/test-version.sh for the given Lean versions.
#
# Usage: ci/summarize.sh TITLE VERSION...
#
# The table goes to $GITHUB_STEP_SUMMARY, or to standard output outside Actions. The script exits
# with status 1 unless every given version has a passing result, so a version that didn't run
# fails the job. Each result is deleted once it is read, so a summary only covers the runs since
# the summary before it.

set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: ci/summarize.sh TITLE VERSION..." >&2
  exit 2
fi

title="$1"
shift
work="${SUBVERSO_CI_WORK:-${RUNNER_TEMP:-${TMPDIR:-/tmp}}/subverso-ci}"
out="${GITHUB_STEP_SUMMARY:-/dev/stdout}"
ok=true

{
  echo "### $title"
  echo
  echo "| Lean | Modules | Result | Time |"
  echo "| --- | --- | --- | --- |"
} >> "$out"

for version in "$@"; do
  slot_name="$(printf '%s' "$version" | tr -c 'A-Za-z0-9.' '-')"
  result="$work/results/$slot_name.tsv"
  if [ -f "$result" ]; then
    IFS=$'\t' read -r _ modules outcome seconds < "$result"
    rm -f "$result"
    time="$((seconds / 60))m $((seconds % 60))s"
  else
    modules="?"
    outcome="did not run"
    time=""
    # A version that was stopped has a log and no result. Its log goes with the failed ones.
    if [ -f "$work/logs/$slot_name.log" ]; then
      outcome="did not finish"
      mkdir -p "$work/failed/$slot_name"
      cp "$work/logs/$slot_name.log" "$work/failed/$slot_name/"
    fi
  fi
  if [ "$outcome" = pass ]; then
    mark="pass"
  else
    mark="**FAILED** (${outcome#fail: })"
    ok=false
    if [ "$outcome" = "did not run" ] || [ "$outcome" = "did not finish" ]; then
      echo "::error title=Lean $version::No result was recorded for this version"
    fi
  fi
  echo "| $version | $modules | $mark | $time |" >> "$out"
done

[ "$ok" = true ]
