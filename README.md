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
