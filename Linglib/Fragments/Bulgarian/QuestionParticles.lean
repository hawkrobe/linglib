import Linglib.Phenomena.Questions.Typology

/-!
# Bulgarian Question Particles

Lexical entries for Bulgarian interrogative particles.

## Particles

| Particle | Romanization | Gloss | Layer | Bias |
|----------|-------------|-------|-------|------|
| ли | li | neutral PQ | CP | none |
| нима | nima | RAZVE (mirative) | PerspP | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.bulgarian`: PQ strategy profile (verb-attached li)
- Cross-Slavic RAZVE family: nima is the Bulgarian member
- Dukova-Zheleva: nima expresses incredulity/surprise

## References

- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
- Dukova-Zheleva, G. Questions and Focus in Bulgarian. U. of Ottawa.
-/

namespace Fragments.Bulgarian.QuestionParticles

open Phenomena.Questions.Typology (QParticleLayer)

/-- A Bulgarian interrogative particle entry. -/
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

/-- ли li — verb-attached neutral PQ particle (Šimík 2024 ex. 33).
Encliticizes onto the focused constituent. -/
def li : QParticleEntry where
  form := "ли"
  romanization := "li"
  gloss := "PQ (verb-attached neutral)"
  layer := .cp
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- нима nima — mirative/dubitative particle (RAZVE family, Šimík 2024 §4.2.4).
Expresses incredulity: speaker encounters evidence conflicting with prior
expectations (Dukova-Zheleva). -/
def nima : QParticleEntry where
  form := "нима"
  romanization := "nima"
  gloss := "RAZVE (mirative/incredulity)"
  layer := .perspP
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := true
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [li, nima]

theorem li_neutral :
    li.requiresEvidentialBias = false ∧ li.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

theorem nima_evidential : nima.requiresEvidentialBias = true := rfl

/-- li and nima form a neutral/evidential contrast. -/
theorem bias_contrast :
    li.requiresEvidentialBias = false ∧ nima.requiresEvidentialBias = true :=
  ⟨rfl, rfl⟩

end Fragments.Bulgarian.QuestionParticles
