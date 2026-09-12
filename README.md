# SubVerso - Verso's Library for Subprocesses

SubVerso is a support library that allows a
[Verso](https://github.com/leanprover/verso) document to describe Lean
code written in multiple versions of Lean. Verso itself may be tied to
new Lean versions, because it makes use of new compiler features. This
library will maintain broader compatibility with various Lean versions.

## Versions and Compatibility

SubVerso's CI currently validates it on every Lean release since
4.0.0, along with whatever version or snapshot is currently targeted
by Verso itself.

There should be no expectations of compatibility between different
versions of SubVerso, however - the specifics of its data formats is
an implementation detail, not a public API. Please use SubVerso itself
to read and write the data.

## Module System

The code in `main` uses the Lean module system. For compatibility with
older Lean versions, a "demodulized" version of the code is generated
on each commit to `main`. This is force-pushed to the `no-modules`
branch. The "demodulized" version has been rewritten by the script
`demodulize.py`. Additionally, the no-module code generated from commit
`abc123def456` on `main` is tagged with `no-modules/abc123def456` for posterity.

Versions of Lean prior to `4.25.0` or `nightly-2025-10-07` should use
the `no-modules` branch.

Projects which coordinate two Lean versions across the "module gap"
can still check that the SubVerso versions are the same in CI. The
file `.source-commit` in the `no-modules` branch contains the commit
hash of `main` that it was generated from.

## Features

### Code Examples

Presently, SubVerso supports the extraction of highlighting
information from code. There may be a many-to-many relationship
between Lean modules and documents that describe them. In these cases,
using SubVerso's examples library to indicate examples to be shown in
the text can be useful.

This feature may also be useful for other applications that require
careful presentation of Lean code.

To use this feature, first add a dependency on `subverso` to your
Lakefile:

```
require subverso from git "git@github.com:leanprover/subverso.git"
```

Examples are named in _anchors_, which are created using
specially-formatted comments. An anchor `A` is delimeted by:
```lean
-- ANCHOR: A
```
and:
```lean
-- ANCHOR_END: A
```

Within a Lean source file, anchor names should be unique. Anchors may
overlap arbitrarily.

Within an anchor, a proof state may be named `X` using the
`PROOF_STATE X` comment, which points at the source position of the
state using a `^`. Here, the proof state `after_intro` is the one
active around the `r`:

```lean
example : ∀n, n * (2 + 2) = n * 4 := by
  -- ANCHOR: proof
  intro n
  -- ^ PROOF_STATE: after_intro
  grind
  -- ANCHOR_END: proof
```

### Module Extraction

SubVerso can be used to extract a representation of a module's code
together with metadata. Run:

```
$ subverso-extract-mod MODNAME OUT.json
```

to extract metadata about module `MODNAME` into `OUT.json`. The
resulting JSON file contains an array of objects. Lean modules are
sequences of commands, and each object represents one of them. The
objects have the following keys:
 * `kind` - the syntax kind of the command
 * `defines` - names defined by the command (useful e.g. for automatic hyperlink insertion in rendered HTML)
 * `code` - the internal SubVerso JSON format for the highlighted
   code, including proof states, which is intended to be deserialized
   using the `FromJson Highlighted` instance from SubVerso.
   
The `highlighted` facet for a package, library, or module builds
highlighted sources.

### Helper Process

SubVerso can also be used as a helper for other tools that need to be
more interactive than module extraction, and yet still cross Lean
version boundaries. Verso uses this feature to attempt to highlight
code samples in Markdown module docstrings when using its "literate
Lean" blog post feature.

To start up the helper, run `subverso-helper`. It communicates with a
protocol reminiscent of JSON-RPC, but this is an implementation
detail - it should be used via the API in `SubVerso.Helper`. It can
presently be used to elaborate and highlight terms in the context of a
module.

### Docstring lookup (staging API)

`SubVerso.DocString` provides `SubVerso.findDocString`, intended for Verso to consume before
upstreaming to Lean. It returns `.found doc`, `.absent`, or `.unavailable moduleName`;
`toOption` recovers the usual optional docstring.

Successful lookups preserve Lean's rendering, builtin documentation, tactic aliases, and inherited
documentation. The API accepts the same `includeBuiltin`, `options`, `currNamespace`, and `openDecls`
arguments as Lean 4.34's `findDocString?`; arguments unsupported by older versions are ignored.

On failure, lookup follows loaded `inherit_doc` references and checks the defining module's effective
import mode, including transitive imports. `.unavailable M` means documentation might exist but its
metadata is unavailable; a batch build can load it with `import all M`. Lookup itself loads no extra
metadata. Local declarations can return `.unavailable` through inherited documentation.

Available server metadata is currently detected using declaration ranges from the same module as
conservative evidence. Missing ranges can cause a false `.unavailable`; an authoritative environment
query belongs in Lean. Versions without the module system return only `.found` or `.absent`.

### Highlighting diagnostics

All highlighting entrypoints return the output and a diagnostic summary, separate from Lean messages:

```lean
let (hl, diagnostics) ← SubVerso.Highlighting.highlight stx messages trees
```

`diagnostics.missingDocStringModules` is a `Lean.NameSet` of modules reported as unavailable for
retained hovers. Merge summaries with `++` when combining results. JSON encodes the set as a sorted
array, and decoding restores uniqueness. Individual token lookup statuses and locations are not kept.

The summary covers the entire result. Slicing highlighted output or selecting module items does not
narrow it. For warnings specific to an excerpt, collect diagnostics at that excerpt's boundary and
merge only the included pieces.

A suitable warning is “Documentation metadata is unavailable for these modules. If these names are
documented, use `import all M` to include their docstrings.” `.found` and `.absent` results produce no
suggestions, and older Lean versions without the module system return an empty summary.

Helper results, extracted modules, and saved examples include a `diagnostics` JSON field. Their
decoders accept older payloads that omit it, defaulting to empty diagnostics.
