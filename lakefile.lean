import Lake
open Lake DSL

package linglib where
  version := v!"0.44.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Documentation generator; pin must match lean-toolchain version
-- Find the right commit at: https://github.com/leanprover/doc-gen4/commits/main
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "a41d5ebebfa77afe737fec8de8ad03fc8b08fdff"

-- Mathlib last so its dependency versions take precedence
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"

@[default_target]
lean_lib Linglib where
  globs := #[.submodules `Linglib]

/-- Blog essays: novel synthesis and explorations accompanying blog posts.
    These import from Linglib but are not part of the library proper. -/
lean_lib PsychVerbs where
  srcDir := "blog/lean"
  globs := #[.submodules `PsychVerbs]

lean_lib KennedyRSA where
  srcDir := "blog/lean"
  globs := #[.submodules `KennedyRSA]

lean_lib SeMarkingRSA where
  srcDir := "blog/lean"
  globs := #[.submodules `SeMarkingRSA]
