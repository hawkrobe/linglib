import Linglib.Phenomena.Questions.Typology

/-!
# Polish Question Particles

Lexical entries for Polish interrogative particles.

## Particles

| Particle | Gloss | Layer | Bias |
|----------|-------|-------|------|
| czy | neutral PQ | CP | none |
| czyżby | RAZVE (mirative) | PerspP | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.polish`: PQ strategy profile (clause-initial czy obligatory)
- Cross-Slavic RAZVE family: czyżby is the Polish member

## References

- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
-/

namespace Fragments.Polish.QuestionParticles

open Phenomena.Questions.Typology (QParticleLayer)

/-- A Polish interrogative particle entry. -/
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

/-- czy — obligatory clause-initial PQ particle (Šimík 2024 ex. 30).
Verb-initial PQs possible but unacceptable in quiz scenarios. -/
def czy : QParticleEntry where
  form := "czy"
  gloss := "PQ (clause-initial neutral)"
  layer := .cp
  polarOk := true
  declOk := false
  whOk := true
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- czyżby — mirative/dubitative particle (RAZVE family, Šimík 2024 §4.2.4).
Polish member of the cross-Slavic razve family. -/
def czyzby : QParticleEntry where
  form := "czyżby"
  gloss := "RAZVE (mirative/dubitative)"
  layer := .perspP
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := true
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [czy, czyzby]

theorem czy_neutral :
    czy.requiresEvidentialBias = false ∧ czy.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

theorem czyzby_evidential : czyzby.requiresEvidentialBias = true := rfl

/-- czy and czyżby form a neutral/evidential contrast. -/
theorem bias_contrast :
    czy.requiresEvidentialBias = false ∧ czyzby.requiresEvidentialBias = true :=
  ⟨rfl, rfl⟩

end Fragments.Polish.QuestionParticles
