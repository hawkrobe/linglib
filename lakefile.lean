import Lake
open Lake DSL

package linglib where
  version := v!"0.44.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- Documentation generator
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib Linglib where
  globs := #[.submodules `Linglib]
