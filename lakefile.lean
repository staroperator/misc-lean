import Lake
open Lake DSL

package «misc» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib TemporalLogic
