import Lake
open Lake DSL

package linglib where
  version := v!"4.34.0"
  description := "A Lean 4 library for formal linguistics: semantics, syntax, pragmatics, morphology, phonology, and processing — formalized across competing frameworks for high interconnection density."
  homepage := "https://linglib.io/"
  keywords := #["linguistics", "formal-semantics", "formal-syntax", "phonology", "pragmatics", "morphology", "lean4", "mathlib"]
  leanOptions := #[⟨`autoImplicit, false⟩,
    -- TODO(v4.33.0): remove once mathlib's strict-defeq transition completes
    -- (`DeriveFintype` enum path and simp defeq-matching break without it).
    ⟨`backward.isDefEq.respectTransparency, false⟩]

-- Documentation generator; pin must match lean-toolchain version
-- Find the right commit at: https://github.com/leanprover/doc-gen4/commits/main
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "a6521b2d0c93dcdf2d640089f95548df5dd8bf46"

-- Mathlib last so its dependency versions take precedence
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib Linglib where
  globs := #[.submodules `Linglib]

/-- Blog essays: novel synthesis and explorations accompanying blog posts.
    These import from Linglib but are not part of the library proper. -/
lean_lib PsychVerbs where
  srcDir := "blog/lean"
  globs := #[.submodules `PsychVerbs]

lean_lib scratch where
  globs := #[.submodules `scratch]
