/-!
# Russian Discourse Particles
@cite{ippolito-kiss-williams-2025}

Lexical entry for Russian *tol'ko* (только) — the discourse *only*
connective. Allows all clause types as S'.

-/

namespace Fragments.Slavic.Russian.DiscourseParticles

/-- A discourse *only* particle entry. -/
structure DiscourseOnlyParticle where
  form : String
  nativeForm : String
  gloss : String
  deriving Repr, DecidableEq

/-- Russian *tol'ko* (только) — allows all clause types as S'. -/
def tolko : DiscourseOnlyParticle where
  form := "tol'ko"
  nativeForm := "только"
  gloss := "only"

end Fragments.Slavic.Russian.DiscourseParticles
