import Lake
open Lake DSL

package "lean-boogie" where
  version := v!"0.1.0"

@[default_target]
lean_lib LeanBoogie where
  require qpf from git "https://github.com/alexkeizer/QpfTypes.git" @ "9cfc50cfa0dc561f5b7a1bf08e693b2a52172383"
  require ITree from "../ITree"
  require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "680d6d58ce2bb65d15e5711d93111b2e5b22cb1a" -- 4.12
  require Duper from git "https://github.com/leanprover-community/duper.git" @ "25c3ea88da2505158998eea07f40b07c0cdfe5ba"
