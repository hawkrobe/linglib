/-!
# Mandarin Discourse Particles
@cite{ippolito-kiss-williams-2025}

Lexical entry for Mandarin *zhǐshì* (只是) — the discourse *only*
connective. Allows all clause types as S' except exclamatives.

-/

namespace Fragments.Mandarin.DiscourseParticles

/-- A discourse *only* particle entry. -/
structure DiscourseOnlyParticle where
  form : String
  nativeForm : String
  gloss : String
  deriving Repr, DecidableEq

/-- Mandarin *zhǐshì* (只是) — blocks exclamative S'. -/
def zhishi : DiscourseOnlyParticle where
  form := "zhǐshì"
  nativeForm := "只是"
  gloss := "only (just)"

end Fragments.Mandarin.DiscourseParticles
