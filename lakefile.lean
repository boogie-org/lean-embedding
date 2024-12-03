import Lake
open Lake DSL

package "lean-boogie" where
  version := v!"0.1.0"

@[default_target]
lean_lib LeanBoogie where
  -- ## for 4.12:
  require qpf from git "https://github.com/Kiiyya/QpfTypes.git" @ "67e99ac5339969f1fe220100c3c5f05ea37e20f9" -- https://github.com/alexkeizer/QpfTypes/pull/52
  require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "680d6d58ce2bb65d15e5711d93111b2e5b22cb1a" -- 4.12
  require Duper from git "https://github.com/leanprover-community/duper.git" @ "25c3ea88da2505158998eea07f40b07c0cdfe5ba"

-- @[default_target]
-- lean_exe "lean-boogie" where
--   root := `Main
