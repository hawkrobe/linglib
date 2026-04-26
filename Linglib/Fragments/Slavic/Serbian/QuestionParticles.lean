/-!
# Serbian Question Particles
@cite{simik-2024}

Lexical entries for Serbian interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Phenomena.Questions.Studies.Simik2024`.

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

namespace Fragments.Slavic.Serbian.QuestionParticles

/-- A Serbian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  deriving Repr, DecidableEq

/-- da li — default PQ particle combination (@cite{simik-2024} ex. 31).
Particle + verb movement. Neutral baseline. -/
def daLi : QParticleEntry where
  form := "da li"
  gloss := "PQ (particle + movement)"
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- zar — mirative/dubitative particle (RAZVE family, @cite{simik-2024} §4.2.4).
Compatible with both outer and inner negation (like Russian razve). -/
def zar_ : QParticleEntry where
  form := "zar"
  gloss := "RAZVE (mirative/dubitative)"
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

end Fragments.Slavic.Serbian.QuestionParticles
