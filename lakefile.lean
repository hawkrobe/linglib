import Lake
open Lake DSL

package «linglean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LingLean» where
  globs := #[.submodules `LingLean]
