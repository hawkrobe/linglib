import Linglib.Phenomena.Questions.Typology

/-!
# Slovenian Question Particles

Lexical entries for Slovenian interrogative particles.

## Particles

| Particle | Gloss | Layer | Bias |
|----------|-------|-------|------|
| ali | neutral PQ | CP | none |

*ali* is a clause-initial particle, optional in default PQs.
Incompatible with DeclPQs (Šimík 2024 ex. 28).

## Cross-Module Connections

- `SlavicPQStrategies.slovenian`: PQ strategy profile

## References

- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
-/

namespace Fragments.Slovenian.QuestionParticles

open Phenomena.Questions.Typology (QParticleLayer)

/-- A Slovenian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  layer : QParticleLayer
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  deriving Repr, DecidableEq, BEq

/-- ali — clause-initial PQ particle (Šimík 2024 ex. 28).
Optional; incompatible with DeclPQs. No bias requirements. -/
def ali : QParticleEntry where
  form := "ali"
  gloss := "PQ (clause-initial neutral)"
  layer := .cp
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [ali]

theorem ali_neutral :
    ali.requiresEvidentialBias = false ∧ ali.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

end Fragments.Slovenian.QuestionParticles
