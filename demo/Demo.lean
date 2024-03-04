-- This module serves as the root of the `Demo` library.
-- Import modules here that should be built as part of the library.
import «Demo».Basic

import SubVerso.Examples

open SubVerso.Examples

%example xdef
def f (x : Nat) := %ex{add}{33 + %ex{X}{x}}
%end
