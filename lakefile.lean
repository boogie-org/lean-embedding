import Lake
open Lake DSL

package "lean-boogie" where
  version := v!"0.1.0"

@[default_target]
lean_lib LeanBoogie where
  -- ## for 4.12:
  require qpf from git "https://github.com/alexkeizer/QpfTypes.git" @ "ccb042d5260e6af8f5e81fa33db83ebf0c4e093f" -- for Lean 4.12
  require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "680d6d58ce2bb65d15e5711d93111b2e5b22cb1a" -- 4.12
  require Duper from git "https://github.com/leanprover-community/duper.git" @ "25c3ea88da2505158998eea07f40b07c0cdfe5ba"

  -- ## for 4.11 (lean-auto only supports 4.11 for now):
  -- require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "60e546ca7a9d40d508e58847a9d0630406835178" -- 4.11, breaks duper, but parses z3 output.
  -- -- require Duper from git "https://github.com/leanprover-community/duper.git" @ "v0.0.17"
  -- -- require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "2b6ed7d9f86d558d94b8d9036a637395163c4fa6" -- 4.11, works with duper, but fails to parse z3 output.
  -- require Qq from git "https://github.com/leanprover-community/quote4.git" @ "9d0bdd07bdfe53383567509348b1fe917fc08de4" -- 4.11
  -- require aesop from git "https://github.com/leanprover-community/aesop.git" @ "deb279eb7be16848d0bc8387f80d6e41bcdbe738" -- 4.11

-- @[default_target]
-- lean_exe "lean-boogie" where
--   root := `Main
