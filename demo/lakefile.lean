/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lake
open Lake DSL

-- This needs to be git rather than a filesystem path, because git
-- will clone the project. This results in a separate .lake build dir,
-- so the different versions of Lake don't stomp on each others'
-- files.
require subverso from git ".."

package «demo» where
  -- add package configuration options here

lean_lib «Demo» where
  -- add library configuration options here

@[default_target]
lean_exe «demo» where
  root := `Main
