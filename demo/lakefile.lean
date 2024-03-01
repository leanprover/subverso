import Lake
open Lake DSL

require subverso from ".."

package «demo» where
  -- add package configuration options here

lean_lib «Demo» where
  -- add library configuration options here

@[default_target]
lean_exe «demo» where
  root := `Main
