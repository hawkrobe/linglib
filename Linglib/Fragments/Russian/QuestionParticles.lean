import Linglib.Phenomena.Questions.Typology

/-!
# Russian Question Particles

Lexical entries for Russian interrogative particles with distributional
properties and bias profiles.

## Particles

| Particle | Romanization | Gloss | Layer | Bias |
|----------|-------------|-------|-------|------|
| ли | li | neutral PQ | CP | none |
| разве | razve | RAZVE (mirative) | PerspP | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.russian`: PQ strategy profile (intonation default, li formal)
- `SlavicPQStrategies.razve`: bias particle data (outerNeg/innerNeg)
- Bridge theorems in `SlavicPQStrategies` (Phenomena imports Fragments)

## References

- Šimík, R. (2024). Polar question semantics and bias: Lessons from Slavic/Czech.
- Esipova, M. & Romero, M. (2023). Russian IntonPQs.
- Onoeva, M. & Staňková, A. (to appear). Corpus study of PQ strategies.
-/

namespace Fragments.Russian.QuestionParticles

open Phenomena.Questions.Typology (QParticleLayer)

/-- A Russian interrogative particle entry. -/
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

/-- ли li — neutral polar question particle (formal register).
Verb-attached enclitic, cliticizes onto the focused constituent.
Rare in spoken Russian (only 6/500 PQs in Onoeva & Staňková corpus).
CP-layer: basic clause-typing function. -/
def li : QParticleEntry where
  form := "ли"
  romanization := "li"
  gloss := "PQ (neutral polar question particle)"
  layer := .cp
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- разве razve — mirative/dubitative question particle (Šimík 2024 §4.2.4).
Indicates conflict between speaker's prior epistemic state and current
contextual evidence. Compatible with both outer and inner negation
(Repp & Geist 2022). -/
def razve_ : QParticleEntry where
  form := "разве"
  romanization := "razve"
  gloss := "RAZVE (mirative/dubitative Q-particle)"
  layer := .perspP
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := true
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [li, razve_]

-- Per-datum verification

theorem li_neutral :
    li.requiresEvidentialBias = false ∧ li.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

theorem razve_evidential : razve_.requiresEvidentialBias = true := rfl
theorem razve_no_epistemic : razve_.requiresEpistemicBias = false := rfl

/-- li and razve form a neutral/evidential contrast (like Mandarin ma/nandao). -/
theorem bias_contrast :
    li.requiresEvidentialBias = false ∧ razve_.requiresEvidentialBias = true :=
  ⟨rfl, rfl⟩

end Fragments.Russian.QuestionParticles
