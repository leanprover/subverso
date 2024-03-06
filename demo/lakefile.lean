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
