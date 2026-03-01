/-!
# Italian Discourse Particles

Lexical entry for Italian *solo che* — the discourse *only* connective
(IKW 2025). The most restrictive variant: S' must be declarative.

## References

- Ippolito, Kiss & Williams (2025). Discourse *only*. WCCFL 41.
-/

namespace Fragments.Italian.DiscourseParticles

/-- A discourse *only* particle entry. -/
structure DiscourseOnlyParticle where
  form : String
  nativeForm : String
  gloss : String
  deriving Repr, DecidableEq, BEq

/-- Italian *solo che* — S' restricted to declaratives only. -/
def soloChe : DiscourseOnlyParticle where
  form := "solo che"
  nativeForm := "solo che"
  gloss := "only (that)"

end Fragments.Italian.DiscourseParticles
