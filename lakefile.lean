import Lake
open Lake DSL

package «foo» where
  -- add package configuration options here

lean_lib «Foo» where
  -- add library configuration options here

@[default_target]
lean_exe «foo» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4/" @ "69fd837a71463d8905afbf335b908a035aa11a7e"
