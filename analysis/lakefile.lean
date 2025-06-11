import Lake
open Lake DSL

package «Analysis» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- Require Mathlib (the comprehensive library of mathematics in Lean)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"
-- Needed to build book
require subverso from git
  "https://github.com/leanprover/subverso.git" @ "a3e5c4c50791e536fc7f13a7aadd6236091796f9"



@[default_target]
lean_lib «Analysis» where
  -- add any library configuration options here


meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.20.0"
