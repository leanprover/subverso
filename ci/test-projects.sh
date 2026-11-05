#!/usr/bin/env bash
# Prints the test projects and their toolchains, one "<project> <toolchain>" pair per line.
#
# Usage: ci/test-projects.sh
#
# The pairs are `demo-toml` under its own toolchain and `demo` under each Lean version in the file
# demo-toolchains. `fixedTargets` in Tests.lean computes the same pairs.

set -euo pipefail

cd "$(dirname "$0")/.."
awk '{sub(/\r$/, "")} NF {print "demo-toml " $1}' demo-toml/lean-toolchain
awk '{sub(/\r$/, "")} NF {print "demo leanprover/lean4:" $1}' demo-toolchains
