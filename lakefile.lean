import Lake
open Lake DSL

package linglib where
  version := v!"0.44.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Documentation generator; pin must match lean-toolchain version
-- Find the right commit at: https://github.com/leanprover/doc-gen4/commits/main
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "aa4c3e4e14f5b31495b7c7238762ecceddd9f52c"

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

lean_lib scratch where
  globs := #[.submodules `scratch]
