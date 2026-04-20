/-!
# Macedonian Question Particles
@cite{simik-2024}

Lexical entries for Macedonian interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Phenomena.Questions.Studies.Simik2024`.

## Particles

| Particle | Romanization | Gloss | Bias |
|----------|-------------|-------|------|
| дали | dali | neutral PQ | none |

Macedonian *dali* can introduce negative PQs without triggering epistemic
bias, unlike Bulgarian *li* (@cite{simik-2024} ex. 32). Mitkovska, Bužarovska &
Saračević (2024) contrast *dali* with biased particles *zar* and *neli*.

## Cross-Module Connections

- `SlavicPQStrategies.macedonian`: PQ strategy profile (negationTriggersBias = false)

-/

namespace Fragments.Macedonian.QuestionParticles

/-- A Macedonian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  romanization : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  /-- Does adding negation to the PQ trigger epistemic bias? -/
  negationTriggersBias : Bool
  deriving Repr, DecidableEq

/-- дали dali — clause-initial PQ particle (@cite{simik-2024} ex. 32).
Unlike Bulgarian li, dali + negation is unbiased. -/
def dali : QParticleEntry where
  form := "дали"
  romanization := "dali"
  gloss := "PQ (clause-initial neutral)"
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
This is the key Macedonian-Bulgarian contrast (@cite{simik-2024} ex. 32). -/
theorem dali_neg_unbiased : dali.negationTriggersBias = false := rfl

end Fragments.Macedonian.QuestionParticles
