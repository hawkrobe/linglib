/-!
# Ukrainian Question Particles
@cite{simik-2024}

Lexical entries for Ukrainian interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Phenomena.Questions.Studies.Simik2024`.

## Particles

| Particle | Romanization | Gloss | Bias |
|----------|-------------|-------|------|
| чи | čy | neutral PQ | none |
| хіба | xiba | RAZVE (mirative) | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.ukrainian`: PQ strategy profile (clause-initial čy obligatory)
- Cross-Slavic RAZVE family: xiba is the Ukrainian cognate of Russian razve

-/

namespace Fragments.Ukrainian.QuestionParticles

/-- A Ukrainian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  romanization : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  deriving Repr, DecidableEq

/-- чи čy — obligatory clause-initial PQ particle (@cite{simik-2024} ex. 29).
Neutral baseline, no bias requirements. -/
def cy : QParticleEntry where
  form := "чи"
  romanization := "čy"
  gloss := "PQ (clause-initial neutral)"
  polarOk := true
  declOk := false
  whOk := true
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- хіба xiba — mirative/dubitative particle (RAZVE family, @cite{simik-2024} §4.2.4).
Ukrainian cognate of Russian razve. Indicates conflict between speaker's
prior state and contextual evidence. -/
def xiba : QParticleEntry where
  form := "хіба"
  romanization := "xiba"
  gloss := "RAZVE (mirative/dubitative)"
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
