import Lake
open Lake DSL

-- SubVerso pinned to the revision Verso v4.31.0-rc1 uses, so it builds on this toolchain.
require subverso from git
  "https://github.com/leanprover/subverso" @ "ce893b9042128037e2d3c0158b9567fab9fae268"

-- Pin Mathlib to the same commit the root TauCeti project builds against (this top-level
-- pin overrides the `master` revision TauCeti requests transitively), so the slice of the
-- library we import here compiles exactly as it does upstream.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "66748b489336a59ed4b4a4a612615c38de823e9a"

-- The real Tau Ceti library, from the repository root, so the showcased theorems are
-- type-checked against exactly the library that proves them.
require «TauCeti» from "../.."

package «examples» where

@[default_target]
lean_lib «Examples» where
