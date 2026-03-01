/-!
# Mandarin Discourse Particles

Lexical entry for Mandarin *zhǐshì* (只是) — the discourse *only*
connective (IKW 2025). Allows all clause types as S' except exclamatives.

## References

- Ippolito, Kiss & Williams (2025). Discourse *only*. WCCFL 41.
-/

namespace Fragments.Mandarin.DiscourseParticles

/-- A discourse *only* particle entry. -/
structure DiscourseOnlyParticle where
  form : String
  nativeForm : String
  gloss : String
  deriving Repr, DecidableEq, BEq

/-- Mandarin *zhǐshì* (只是) — blocks exclamative S'. -/
def zhishi : DiscourseOnlyParticle where
  form := "zhǐshì"
  nativeForm := "只是"
  gloss := "only (just)"

end Fragments.Mandarin.DiscourseParticles
