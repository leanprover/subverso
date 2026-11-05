#!/usr/bin/env bash
# Builds the test projects under their own toolchains, all at the same time.
#
# Usage: ci/prebuild.sh
#
# The (project, toolchain) pairs come from ci/test-projects.sh. Each pair gets a build root of its
# own under $SUBVERSO_CI_PREBUILD (default: .prebuild in the repository), in the layout of
# `.builds`. Build roots of other pairs are deleted.
#
# The test driver must be built first, with `lake build subverso-tests`.

set -euo pipefail

cd "$(dirname "$0")/.."
prebuild="${SUBVERSO_CI_PREBUILD:-.prebuild}"

targets="$(bash ci/test-projects.sh)"

names=()
while read -r project toolchain; do
  names+=("$project-${toolchain##*:}")
done <<< "$targets"

mkdir -p "$prebuild"
for root in "$prebuild"/*/; do
  [ -d "$root" ] || continue
  keep=false
  for name in "${names[@]}"; do
    if [ "$(basename "$root")" = "$name" ]; then keep=true; fi
  done
  if [ "$keep" = false ]; then
    echo "Deleting the unused build root $root"
    rm -rf "$root"
  fi
done

logs="$(mktemp -d)"
pids=()
while read -r project toolchain; do
  name="$project-${toolchain##*:}"
  SUBVERSO_TEST_BUILD_ROOT="$prebuild/$name" \
    lake env .lake/build/bin/subverso-tests prepare "$project" "$toolchain" \
    > "$logs/$name.log" 2>&1 < /dev/null &
  pids+=("$!")
done <<< "$targets"

failed=0
for i in "${!pids[@]}"; do
  status=0
  wait "${pids[$i]}" || status=$?
  echo "::group::Prebuild ${names[$i]} (exit code $status)"
  cat "$logs/${names[$i]}.log"
  echo "::endgroup::"
  if [ "$status" -ne 0 ]; then
    echo "::warning title=Prebuild ${names[$i]}::The prebuild failed with exit code $status"
    failed=1
  fi
done
exit "$failed"
