/-!
# Russian Discourse Particles

Lexical entry for Russian *tol'ko* (только) — the discourse *only*
connective (IKW 2025). Allows all clause types as S'.

## References

- Ippolito, Kiss & Williams (2025). Discourse *only*. WCCFL 41.
-/

namespace Fragments.Russian.DiscourseParticles

/-- A discourse *only* particle entry. -/
structure DiscourseOnlyParticle where
  form : String
  nativeForm : String
  gloss : String
  deriving Repr, DecidableEq, BEq

/-- Russian *tol'ko* (только) — allows all clause types as S'. -/
def tolko : DiscourseOnlyParticle where
  form := "tol'ko"
  nativeForm := "только"
  gloss := "only"

end Fragments.Russian.DiscourseParticles
