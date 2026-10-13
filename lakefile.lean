import Lake
open Lake DSL

package «k1-lean» where
  -- add package configuration options here

lean_lib «K1Lean» where
  srcDir := "Src"

@[default_target]
lean_exe «k1-lean» where
  root := `Main
