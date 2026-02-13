import Linglib.Phenomena.Questions.Typology

/-!
# Macedonian Question Particles

Lexical entries for Macedonian interrogative particles.

## Particles

| Particle | Romanization | Gloss | Layer | Bias |
|----------|-------------|-------|-------|------|
| дали | dali | neutral PQ | CP | none |

Macedonian *dali* can introduce negative PQs without triggering epistemic
bias, unlike Bulgarian *li* (Šimík 2024 ex. 32). Mitkovska, Bužarovska &
Saračević (2024) contrast *dali* with biased particles *zar* and *neli*.

## Cross-Module Connections

- `SlavicPQStrategies.macedonian`: PQ strategy profile (negationTriggersBias = false)

## References

- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
- Mitkovska, Bužarovska & Saračević (2024). The role of biased polar question
  particles in discourse. Poznan Studies in Contemporary Linguistics.
-/

namespace Fragments.Macedonian.QuestionParticles

open Phenomena.Questions.Typology (QParticleLayer)

/-- A Macedonian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  romanization : String
  gloss : String
  layer : QParticleLayer
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  /-- Does adding negation to the PQ trigger epistemic bias? -/
  negationTriggersBias : Bool
  deriving Repr, DecidableEq, BEq

/-- дали dali — clause-initial PQ particle (Šimík 2024 ex. 32).
Unlike Bulgarian li, dali + negation is unbiased. -/
def dali : QParticleEntry where
  form := "дали"
  romanization := "dali"
  gloss := "PQ (clause-initial neutral)"
  layer := .cp
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false
  negationTriggersBias := false

def allQuestionParticles : List QParticleEntry := [dali]

theorem dali_neutral :
    dali.requiresEvidentialBias = false ∧ dali.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

/-- dali + negation does NOT trigger bias (unlike Bulgarian li).
This is the key Macedonian-Bulgarian contrast (Šimík 2024 ex. 32). -/
theorem dali_neg_unbiased : dali.negationTriggersBias = false := rfl

end Fragments.Macedonian.QuestionParticles
