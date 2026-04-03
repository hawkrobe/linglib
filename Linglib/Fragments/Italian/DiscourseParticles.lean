/-!
# Italian Discourse Particles
@cite{ippolito-kiss-williams-2025}

Lexical entry for Italian *solo che* — the discourse *only* connective. The most restrictive variant: S' must be declarative.

-/

namespace Fragments.Italian.DiscourseParticles

/-- A discourse *only* particle entry. -/
structure DiscourseOnlyParticle where
  form : String
  nativeForm : String
  gloss : String
  deriving Repr, DecidableEq

/-- Italian *solo che* — S' restricted to declaratives only. -/
def soloChe : DiscourseOnlyParticle where
  form := "solo che"
  nativeForm := "solo che"
  gloss := "only (that)"

end Fragments.Italian.DiscourseParticles
