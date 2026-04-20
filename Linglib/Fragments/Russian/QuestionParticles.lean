/-!
# Russian Question Particles
@cite{esipova-romero-2023} @cite{simik-2024}

Lexical entries for Russian interrogative particles with distributional
properties and bias profiles. The fragment commits only to theory-neutral
lexical primitives (form, gloss, distribution, bias profile); the
left-peripheral layer assignment lives in
`Phenomena.Questions.Studies.Simik2024`.

## Particles

| Particle | Romanization | Gloss | Bias |
|----------|-------------|-------|------|
| ли | li | neutral PQ | none |
| разве | razve | RAZVE (mirative) | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.russian`: PQ strategy profile (intonation default, li formal)
- `SlavicPQStrategies.razve`: bias particle data (outerNeg/innerNeg)
- Bridge theorems in `SlavicPQStrategies` (Phenomena imports Fragments)

-/

namespace Fragments.Russian.QuestionParticles

/-- A Russian interrogative particle entry. -/
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

/-- ли li — neutral polar question particle (formal register).
Verb-attached enclitic, cliticizes onto the focused constituent.
Rare in spoken Russian (only 6/500 PQs in Onoeva & Staňková corpus). -/
def li : QParticleEntry where
  form := "ли"
  romanization := "li"
  gloss := "PQ (neutral polar question particle)"
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- разве razve — mirative/dubitative question particle (@cite{simik-2024} §4.2.4).
Indicates conflict between speaker's prior epistemic state and current
contextual evidence. Compatible with both outer and inner negation. -/
def razve_ : QParticleEntry where
  form := "разве"
  romanization := "razve"
  gloss := "RAZVE (mirative/dubitative Q-particle)"
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
