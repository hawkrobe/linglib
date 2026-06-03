import Linglib.Semantics.Questions.Bias.Defs
/-!
# Serbian Question Particles
[simik-2024]

Lexical entries for Serbian interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Simik2024`.

## Particles

| Particle | Gloss | Bias |
|----------|-------|------|
| da li | neutral PQ | none |
| zar | RAZVE (mirative) | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.serbian`: PQ strategy profile (da li + verb movement)
- `SlavicPQStrategies.zar`: bias particle data (outerNeg/innerNeg)
- Bridge theorems in `SlavicPQStrategies` (Phenomena imports Fragments)

-/

namespace Serbian.QuestionParticles

open Semantics.Questions.Bias (ContextualEvidence OriginalBias)

/-- A Serbian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresContextualEvidence : Option ContextualEvidence
  requiresOriginalBias : Option OriginalBias
  deriving Repr, DecidableEq

/-- da li — default PQ particle combination ([simik-2024] ex. 31).
Particle + verb movement. Neutral baseline. -/
def daLi : QParticleEntry where
  form := "da li"
  gloss := "PQ (particle + movement)"
  polarOk := true
  declOk := false
  whOk := false
  requiresContextualEvidence := none
  requiresOriginalBias := none

/-- zar — mirative/dubitative particle (RAZVE family, [simik-2024] §4.2.4).
Compatible with both outer and inner negation (like Russian razve). -/
def zar_ : QParticleEntry where
  form := "zar"
  gloss := "RAZVE (mirative/dubitative)"
  polarOk := true
  declOk := false
  whOk := false
  requiresContextualEvidence := some .forP
  requiresOriginalBias := none

def allQuestionParticles : List QParticleEntry := [daLi, zar_]

theorem daLi_neutral :
    daLi.requiresContextualEvidence = none ∧ daLi.requiresOriginalBias = none :=
  ⟨rfl, rfl⟩

theorem zar_evidential : zar_.requiresContextualEvidence = some .forP := rfl

/-- da li and zar form a neutral/evidential contrast. -/
theorem bias_contrast :
    daLi.requiresContextualEvidence = none ∧ zar_.requiresContextualEvidence = some .forP :=
  ⟨rfl, rfl⟩

end Serbian.QuestionParticles
