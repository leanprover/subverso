#!/usr/bin/env bash
# Checks that the `highlighted` facet and `subverso-helper` load imports from Lake's artifact cache.
#
# Usage: ci/test-artifact-cache.sh MODULES
#
# MODULES is `true` or `false`, and says whether the test project also has module system files.
#
# The test project is created in `.builds/artifact-cache`, with the repository's Lean toolchain.
# Deleting the project's build directory leaves its imports in the cache alone, as a clean checkout
# with a populated cache does.

set -euo pipefail

modules="${1:?MODULES must be true or false}"

repo="$(cd "$(dirname "$0")/.." && pwd)"
project="$repo/.builds/artifact-cache"

export LAKE_ARTIFACT_CACHE=1
export LAKE_CACHE_DIR="$project/cache"
unset LAKE_RESTORE_ARTIFACTS

fail() {
  echo "::error title=Artifact cache test::$1" >&2
  exit 1
}

rm -rf "$project"
mkdir -p "$project/Lib"
cp "$repo/lean-toolchain" "$project/"
cd "$project"

printf 'def c : Nat := 1\n' > Lib/C.lean
printf 'import Lib.C\ndef b : Nat := c + 1\n' > Lib/B.lean
printf 'import Lib.B\ndef a : Nat := b + c\n' > Lib/A.lean
targets=(+Lib.A:highlighted)

{
  echo 'import Lake'
  echo 'open Lake DSL'
  echo 'require subverso from "../.."'
  if [ "$modules" = true ]; then
    echo 'package proj where'
    echo '  leanOptions := #[⟨`experimental.module, true⟩]'
  else
    echo 'package proj'
  fi
  echo 'lean_lib Lib where'
  echo '  roots := #[`Lib]'
  echo '  globs := #[.submodules `Lib]'
} > lakefile.lean

if [ "$modules" = true ]; then
  printf 'module\npublic def m3 : Nat := 1\n' > Lib/M3.lean
  printf 'module\npublic import Lib.M3\npublic def m2 : Nat := m3 + 1\n' > Lib/M2.lean
  printf 'module\npublic import Lib.M2\npublic def m1 : Nat := m2 + m3\n' > Lib/M1.lean
  targets+=(+Lib.M1:highlighted)
fi

echo "Populating the artifact cache"
lake build Lib subverso-extract-mod subverso-helper

echo "Highlighting with imports that are only in the cache"
rm -rf .lake/build
lake build "${targets[@]}"
if [ -e .lake/build/lib/lean/Lib/C.olean ]; then
  fail "Lib.C was restored to the build directory, so the test doesn't exercise the artifact cache"
fi
[ -s .lake/build/highlighted/Lib/A.json ] || fail "Highlighted JSON for Lib.A is missing"

echo "Fetching highlighted JSON from the cache"
rm -rf .lake/build
lake build "${targets[@]}"
[ -s .lake/build/highlighted/Lib/A.json ] || fail "Cached highlighted JSON was not restored"
if [ -e .lake/build/highlighted-setup/Lib/A.json ]; then
  fail "The extractor ran even though its output is in the cache"
fi

echo "Querying subverso-helper with imports that are only in the cache"
rm -rf .lake/build
lake build Lib subverso-helper
python3 "$repo/ci/query-helper.py" Lib.A 'b + c'
if [ "$modules" = true ]; then
  python3 "$repo/ci/query-helper.py" Lib.M1 'm3 + m2'
fi

echo "Artifact cache test passed"
