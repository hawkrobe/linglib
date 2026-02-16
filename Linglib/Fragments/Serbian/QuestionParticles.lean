import Linglib.Theories.Semantics.Questions.QParticleLayer

/-!
# Serbian Question Particles

Lexical entries for Serbian interrogative particles. Serbian has the richest
PQ repertoire among Slavic languages (Todorović 2023).

## Particles

| Particle | Gloss | Layer | Bias |
|----------|-------|-------|------|
| da li | neutral PQ | CP | none |
| zar | RAZVE (mirative) | PerspP | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.serbian`: PQ strategy profile (da li + verb movement)
- `SlavicPQStrategies.zar`: bias particle data (outerNeg/innerNeg)
- Bridge theorems in `SlavicPQStrategies` (Phenomena imports Fragments)

## References

- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
- Todorović, N. (2023). Serbian polar questions. Glossa.
-/

namespace Fragments.Serbian.QuestionParticles

open Semantics.Questions (QParticleLayer)

/-- A Serbian interrogative particle entry. -/
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

/-- da li — default PQ particle combination (Šimík 2024 ex. 31).
Particle + verb movement. Neutral baseline. -/
def daLi : QParticleEntry where
  form := "da li"
  gloss := "PQ (particle + movement)"
  layer := .cp
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- zar — mirative/dubitative particle (RAZVE family, Šimík 2024 §4.2.4).
Compatible with both outer and inner negation (like Russian razve). -/
def zar_ : QParticleEntry where
  form := "zar"
  gloss := "RAZVE (mirative/dubitative)"
  layer := .perspP
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := true
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [daLi, zar_]

theorem daLi_neutral :
    daLi.requiresEvidentialBias = false ∧ daLi.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

theorem zar_evidential : zar_.requiresEvidentialBias = true := rfl

/-- da li and zar form a neutral/evidential contrast. -/
theorem bias_contrast :
    daLi.requiresEvidentialBias = false ∧ zar_.requiresEvidentialBias = true :=
  ⟨rfl, rfl⟩

end Fragments.Serbian.QuestionParticles
