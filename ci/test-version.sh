#!/usr/bin/env bash
# Builds and tests SubVerso with one Lean version, in a directory of its own.
#
# Usage: ci/test-version.sh [VERSION [MODULES]]
#
# VERSION is a Lean release as it appears after `leanprover/lean4:`, and MODULES is `true` or
# `false`. They default to the environment variables LEAN_VERSION and LEAN_MODULES.
#
# Other environment variables:
#   SUBVERSO_CI_WORK      Work directory, shared by all versions on a machine.
#                         Default: $RUNNER_TEMP/subverso-ci, or $TMPDIR/subverso-ci outside Actions.
#   SUBVERSO_CI_PREBUILD  Directory that holds the prebuilt test projects. Each subdirectory is a
#                         build root in the layout of `.builds`, and its contents are copied into
#                         this version's `.builds`. Default: .prebuild in the repository.
#
# The script records a result line in $SUBVERSO_CI_WORK/results and a log in
# $SUBVERSO_CI_WORK/logs. The log of a failed version and the highlighted JSON it produced are
# also copied to $SUBVERSO_CI_WORK/failed.

set -euo pipefail

version="${1:-${LEAN_VERSION:-}}"
modules="${2:-${LEAN_MODULES:-}}"

if [ -z "$version" ]; then
  echo "::error title=CI configuration::No Lean version given" >&2
  exit 2
fi
case "$modules" in
  true | false) ;;
  *)
    echo "::error title=Lean $version::MODULES must be true or false, got '$modules'" >&2
    exit 2
    ;;
esac

repo="$(cd "$(dirname "$0")/.." && pwd)"
work="${SUBVERSO_CI_WORK:-${RUNNER_TEMP:-${TMPDIR:-/tmp}}/subverso-ci}"
prebuild="${SUBVERSO_CI_PREBUILD:-$repo/.prebuild}"
toolchain="leanprover/lean4:$version"
slot_name="$(printf '%s' "$version" | tr -c 'A-Za-z0-9.' '-')"
slot="$work/slots/$slot_name"
log="$work/logs/$slot_name.log"
result="$work/results/$slot_name.tsv"

mkdir -p "$work/logs" "$work/results"
rm -f "$result"

# The stage that is running, for the failure annotation.
stage="setup"

retry() {
  local attempt
  for attempt in 1 2 3; do
    if "$@"; then
      return 0
    fi
    if [ "$attempt" -lt 3 ]; then
      echo "Attempt $attempt failed, retrying in 15 seconds"
      sleep 15
    fi
  done
  return 1
}

# Runs a command and stops it after the given number of seconds.
# shellcheck disable=SC2329 # `retry` invokes it
with_time_limit() {
  local seconds="$1"
  shift
  perl -e 'alarm shift; exec @ARGV or die "exec: $!\n"' "$seconds" "$@"
}

copy_sources() {
  local f
  mkdir -p "$slot"
  # Only tracked files are copied, so local build products and scratch files stay out of the slot.
  (
    cd "$repo"
    git ls-files -z | while IFS= read -r -d '' f; do
      if [ -e "$f" ]; then printf '%s\0' "$f"; fi
    done | tar --null -T - -cf -
  ) | tar -xf - -C "$slot"
}

copy_prebuilt() {
  local root
  if [ ! -d "$prebuild" ]; then
    echo "No prebuilt test projects in $prebuild; the test driver builds them"
    return 0
  fi
  mkdir -p "$slot/.builds"
  for root in "$prebuild"/*/; do
    [ -d "$root" ] || continue
    echo "Copying prebuilt test projects from $root"
    cp -a "$root." "$slot/.builds/"
  done
}

run_checks() {
  echo "Testing SubVerso with $toolchain (module system: $modules) in $slot"

  stage="copying the sources"
  rm -rf "$slot"
  copy_sources
  cd "$slot"

  if [ "$modules" = false ]; then
    stage="removing module syntax"
    python3 demodulize.py src
  fi

  echo "Lean files:"
  find . -name "*.lean" -type f

  stage="copying the prebuilt test projects"
  copy_prebuilt

  echo "$toolchain" > lean-toolchain

  stage="installing $toolchain"
  retry with_time_limit 900 elan run --install "$toolchain" lean --version

  stage="lean --version"
  lean --version

  stage="lake build"
  lake build

  stage="lake exe subverso-tests"
  lake exe subverso-tests
}

collect_failure() {
  local dest="$work/failed/$slot_name"
  mkdir -p "$dest"
  cp "$log" "$dest/"
  if [ -d "$slot/.builds" ]; then
    (cd "$slot" && find .builds -type d -name highlighted -path '*/.lake/build/highlighted' -prune -print0 |
      while IFS= read -r -d '' d; do
        mkdir -p "$dest/$(dirname "$d")"
        cp -R "$d" "$dest/$d"
      done) || echo "Could not copy the highlighted output of $slot"
  fi
}

# Each slot has its own Lake artifact cache, so concurrent versions don't write to a shared one.
export LAKE_CACHE_DIR="$work/lake-cache/$slot_name"
mkdir -p "$LAKE_CACHE_DIR"

start="$(date +%s)"
# `run_checks` runs in a subshell that exits at the first failing command. Its stage is reported
# through a file because the subshell can't set variables of this shell.
stage_file="$work/results/$slot_name.stage"
set +e
(
  set -euo pipefail
  trap 'echo "$stage" > "$stage_file"' EXIT
  run_checks
) 2>&1 | tee "$log"
statuses=("${PIPESTATUS[@]}")
set -e
status="${statuses[0]}"
if [ "$status" -eq 0 ] && [ "${statuses[1]}" -ne 0 ]; then
  status="${statuses[1]}"
  echo "writing the log" > "$stage_file"
fi
seconds=$(($(date +%s) - start))

if [ "$status" -eq 0 ]; then
  printf '%s\t%s\tpass\t%s\n' "$version" "$modules" "$seconds" > "$result"
  rm -f "$stage_file"
  rm -rf "$slot" "$LAKE_CACHE_DIR"
  echo "Lean $version passed in ${seconds}s"
else
  failed_stage="$(cat "$stage_file" 2>/dev/null || echo unknown)"
  rm -f "$stage_file"
  printf '%s\t%s\tfail: %s\t%s\n' "$version" "$modules" "$failed_stage" "$seconds" > "$result"
  collect_failure
  echo "::error title=Lean $version::Failed at $failed_stage (exit code $status) after ${seconds}s. See the step log."
fi
exit "$status"
