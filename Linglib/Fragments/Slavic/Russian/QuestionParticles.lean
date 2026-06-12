import Linglib.Semantics.Questions.Bias.Defs
/-!
# Russian Question Particles
[esipova-romero-2023] [simik-2024]

Lexical entries for Russian interrogative particles with distributional
properties and bias profiles. The fragment commits only to theory-neutral
lexical primitives (form, gloss, distribution, bias profile); the
left-peripheral layer assignment lives in
`Simik2024`.

## Particles

| Particle | Romanization | Gloss | Bias |
|----------|-------------|-------|------|
| ли | li | neutral PQ | none |
| разве | razve | RAZVE (mirative) | +evidential |

## Cross-Module Connections

- `Simik2024.russian` (`Studies/Simik2024`): PQ strategy profile (intonation default, li formal)
- Layer assignments and Fragment-derived bias theorems in `Studies/Simik2024`

-/

namespace Russian.QuestionParticles

open Semantics.Questions.Bias (ContextualEvidence OriginalBias)

/-- A Russian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  romanization : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresContextualEvidence : Option ContextualEvidence
  requiresOriginalBias : Option OriginalBias
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
  requiresContextualEvidence := none
  requiresOriginalBias := none

/-- разве razve — mirative/dubitative question particle ([simik-2024] §4.2.4).
Indicates conflict between speaker's prior epistemic state and current
contextual evidence. Compatible with both outer and inner negation. -/
def razve_ : QParticleEntry where
  form := "разве"
  romanization := "razve"
  gloss := "RAZVE (mirative/dubitative Q-particle)"
  polarOk := true
  declOk := false
  whOk := false
  requiresContextualEvidence := some .forP
  requiresOriginalBias := none

def allQuestionParticles : List QParticleEntry := [li, razve_]

-- Per-datum verification

theorem li_neutral :
    li.requiresContextualEvidence = none ∧ li.requiresOriginalBias = none :=
  ⟨rfl, rfl⟩

theorem razve_evidential : razve_.requiresContextualEvidence = some .forP := rfl
theorem razve_no_epistemic : razve_.requiresOriginalBias = none := rfl

/-- li and razve form a neutral/evidential contrast (like Mandarin ma/nandao). -/
theorem bias_contrast :
    li.requiresContextualEvidence = none ∧ razve_.requiresContextualEvidence = some .forP :=
  ⟨rfl, rfl⟩

end Russian.QuestionParticles
