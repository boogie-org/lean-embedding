import Lake
open Lake DSL

package "lean-boogie" where
  version := v!"0.1.0"

@[default_target]
lean_lib LeanBoogie where
  require ITree from git "https://github.com/boogie-org/lean-itrees.git" @ "59c895f4f70cd84ad6c8d6524a605eaaab26fe87"
  require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "680d6d58ce2bb65d15e5711d93111b2e5b22cb1a" -- 4.12
  require Duper from git "https://github.com/leanprover-community/duper.git" @ "25c3ea88da2505158998eea07f40b07c0cdfe5ba"

lean_exe Examples where
  root := `Examples
