import Lake
open Lake DSL

package «subverso» where
  -- add package configuration options here

lean_lib SubversoHighlighting where
  srcDir := "src/highlighting"
  roots := #[`Subverso.Highlighting]

lean_lib SubversoExamples where
  srcDir := "src/examples"
  roots := #[`Subverso.Examples]

@[default_target]
lean_exe «subverso-tests» where
  root := `Tests
