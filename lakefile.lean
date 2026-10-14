import Lake
open Lake DSL

package «k1-lean» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

lean_lib «K1Lean» where
  srcDir := "Src"

@[default_target]
lean_exe «k1-lean» where
  root := `Main
