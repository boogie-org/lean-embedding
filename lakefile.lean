import Lake
open Lake DSL

package "lean-boogie" where
  version := v!"0.1.0"

lean_lib «LeanBoogie» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-boogie" where
  root := `Main
