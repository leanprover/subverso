/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lake
open Lake DSL

-- This project is never used to cross Lean versions, so no need to do anything fancy here.
require subverso from ".."

package «small» where
  -- add package configuration options here

@[default_target]
lean_lib «Small» where
  -- add library configuration options here
