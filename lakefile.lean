import Lake
open Lake DSL

package «lambda-calculus» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Lambda where
