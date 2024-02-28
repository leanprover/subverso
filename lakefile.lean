import Lake
open Lake DSL

package «subverso» where
  -- add package configuration options here

lean_lib «Subverso» where
  -- add library configuration options here

@[default_target]
lean_exe «subverso» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
