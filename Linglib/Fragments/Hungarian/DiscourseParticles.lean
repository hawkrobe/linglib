/-!
# Hungarian Discourse Particles
@cite{ippolito-kiss-williams-2025}

Lexical entry for Hungarian *csak* — the discourse *only* connective. Allows all clause types as S'.

-/

namespace Fragments.Hungarian.DiscourseParticles

/-- A discourse *only* particle entry. -/
structure DiscourseOnlyParticle where
  form : String
  nativeForm : String
  gloss : String
  deriving Repr, DecidableEq, BEq

/-- Hungarian *csak* — allows all clause types as S'. -/
def csak : DiscourseOnlyParticle where
  form := "csak"
  nativeForm := "csak"
  gloss := "only"

end Fragments.Hungarian.DiscourseParticles
