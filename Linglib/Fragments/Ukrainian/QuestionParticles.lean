import Linglib.Theories.Semantics.Questions.QParticleLayer

/-!
# Ukrainian Question Particles

Lexical entries for Ukrainian interrogative particles.

## Particles

| Particle | Romanization | Gloss | Layer | Bias |
|----------|-------------|-------|-------|------|
| чи | čy | neutral PQ | CP | none |
| хіба | xiba | RAZVE (mirative) | PerspP | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.ukrainian`: PQ strategy profile (clause-initial čy obligatory)
- Cross-Slavic RAZVE family: xiba is the Ukrainian cognate of Russian razve

## References

- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
-/

namespace Fragments.Ukrainian.QuestionParticles

open Semantics.Questions (QParticleLayer)

/-- A Ukrainian interrogative particle entry. -/
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
  deriving Repr, DecidableEq, BEq

/-- чи čy — obligatory clause-initial PQ particle (Šimík 2024 ex. 29).
Neutral baseline, no bias requirements. -/
def cy : QParticleEntry where
  form := "чи"
  romanization := "čy"
  gloss := "PQ (clause-initial neutral)"
  layer := .cp
  polarOk := true
  declOk := false
  whOk := true
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- хіба xiba — mirative/dubitative particle (RAZVE family, Šimík 2024 §4.2.4).
Ukrainian cognate of Russian razve. Indicates conflict between speaker's
prior state and contextual evidence. -/
def xiba : QParticleEntry where
  form := "хіба"
  romanization := "xiba"
  gloss := "RAZVE (mirative/dubitative)"
  layer := .perspP
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := true
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [cy, xiba]

theorem cy_neutral :
    cy.requiresEvidentialBias = false ∧ cy.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

theorem xiba_evidential : xiba.requiresEvidentialBias = true := rfl

/-- čy and xiba form a neutral/evidential contrast. -/
theorem bias_contrast :
    cy.requiresEvidentialBias = false ∧ xiba.requiresEvidentialBias = true :=
  ⟨rfl, rfl⟩

end Fragments.Ukrainian.QuestionParticles
