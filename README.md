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

Then, in the modules that contain code examples to be used in
documentation, add the following to the imports list:
```
import SubVerso.Examples
```
and open the namespace within which the new (scoped) operators are defined:
```
open SubVerso.Examples
```

This library defines two new pieces of syntax. Wrapping a sequence of
commands in `%example NAME` and `%end` causes their data to be saved
under the key `NAME`. Any `%ex{NAME2}{T}` expressions within the
command are additionally saved under the key `NAME2`, with the `%ex`
annotation removed from the highlighted code.

For instance, if the module to be highlighted contains:
```
%example F
def f (n : Nat) : Nat := %ex{plus23}{$ex{N}{n} + 23}

#eval f 5
%end
```
then three pieces of highlighted code are saved, named `F` (the whole
block), `plus23` (which contains `n + 23`), and `N` (which contains
`n`).

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
 
