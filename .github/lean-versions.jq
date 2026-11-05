# Turns lean-versions.json and platform-versions.json into the matrix for the `test` job in
# workflows/ci.yml.
#
# Each entry of lean-versions.json describes one Lean version that CI tests on Linux:
#   version  (required) The Lean release, as written after `leanprover/lean4:` in a toolchain file.
#   modules  (default true) Whether the version supports the module system. When it is false,
#            demodulize.py strips module syntax from the SubVerso sources before the build.
#
# The Linux versions are split in file order into shards of `$shard` versions. Each shard has one
# runner with the label `$runner`.
#
# Each entry of platform-versions.json describes one Lean version that CI tests on another
# platform, on a runner of its own. These entries spot-check that running the toolchain's
# command-line tools works there. An entry has the fields above and three more, all required:
#   platform  A short name for the platform and the install method. It starts the job's name.
#   runner    The runner label.
#   install   How Elan is installed: `curl` for the official script, `brew` for Homebrew.
#
# The macOS runner is pinned to macos-15-intel, because executables that older Lean versions build
# abort in dyld on the macOS 26 arm64 image.
#
# Usage: jq -c --argjson shard 8 --arg runner LABEL --slurpfile platforms platform-versions.json \
#          -f lean-versions.jq lean-versions.json

def defaults: {modules: true};

def normalize($file; $fields):
  if type != "object" then error("\($file): each entry must be an object, got \(tojson)")
  elif (.version | type) != "string" or .version == "" then error("\($file): entry without a version: \(tojson)")
  else defaults + . end
  | if (.modules | type) != "boolean" then error("\($file): modules must be a boolean in \(tojson)") else . end
  | (keys - ["version", "modules"] - $fields) as $unknown
  | if ($unknown | length) > 0 then error("\($file): unknown field \($unknown[0]) in \(tojson)") else . end;

def require_string($file; $field):
  if (.[$field] | type) != "string" or .[$field] == "" then error("\($file): entry without \($field): \(tojson)") else . end;

# The directory name that ci/test-version.sh derives from a version.
def slot_name: gsub("[^A-Za-z0-9.]"; "-");

def chunks($n): [range(0; length; $n) as $i | .[$i:$i + $n]];

def range_name: if length == 1 then .[0].version else "\(.[0].version)–\(.[-1].version)" end;

def entry($name; $runner; $install):
  {
    name: $name,
    runner: $runner,
    install: $install,
    versions: tojson,
    expected: (map(.version) | join(" "))
  };

def platform_entries:
  if ($platforms | length) != 1 or ($platforms[0] | type) != "array" then error("platform-versions.json must hold one array") else $platforms[0] end
  | map(normalize("platform-versions.json"; ["platform", "runner", "install"])
        | require_string("platform-versions.json"; "platform")
        | require_string("platform-versions.json"; "runner")
        | if .install != "curl" and .install != "brew" then error("platform-versions.json: install must be curl or brew in \(tojson)") else . end
        | . as $e
        | [del(.platform, .runner, .install)]
        | entry("\($e.platform) \($e.version)"; $e.runner; $e.install));

if type != "array" or length == 0 then error("lean-versions.json must be a non-empty array") else . end
| map(normalize("lean-versions.json"; []))
| if (map(.version) | unique | length) != length then error("lean-versions.json lists a version twice") else . end
| (chunks($shard) | map(entry("linux \(range_name)"; $runner; "curl"))) + platform_entries
| if any(.[]; (.versions | fromjson | length) > 8) then error("a matrix entry has more versions than the test job has slots") else . end
| if any(.[]; .versions | fromjson | map(.version | slot_name) | (unique | length) != length) then error("two versions of a matrix entry have the same slot directory") else . end
| if (map(.name) | unique | length) != length then error("two matrix entries have the same name") else . end
| {include: .}
