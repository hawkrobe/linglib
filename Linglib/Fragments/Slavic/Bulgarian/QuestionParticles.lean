import Linglib.Semantics.Questions.Bias.Defs
/-!
# Bulgarian Question Particles
[simik-2024]

Lexical entries for Bulgarian interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Simik2024`.

## Particles

| Particle | Romanization | Gloss | Bias |
|----------|-------------|-------|------|
| ли | li | neutral PQ | none |
| нима | nima | RAZVE (mirative) | +evidential |

## Cross-Module Connections

- `Simik2024.bulgarian` (`Studies/Simik2024`): PQ strategy profile (verb-attached li)
- Cross-Slavic RAZVE family: nima is the Bulgarian member
- Dukova-Zheleva: nima expresses incredulity/surprise

-/

namespace Bulgarian.QuestionParticles

open Semantics.Questions.Bias (ContextualEvidence OriginalBias)

/-- A Bulgarian interrogative particle entry. -/
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

/-- ли li — verb-attached neutral PQ particle ([simik-2024] ex. 33).
Encliticizes onto the focused constituent. -/
def li : QParticleEntry where
  form := "ли"
  romanization := "li"
  gloss := "PQ (verb-attached neutral)"
  polarOk := true
  declOk := false
  whOk := false
  requiresContextualEvidence := none
  requiresOriginalBias := none

/-- нима nima — mirative/dubitative particle (RAZVE family, [simik-2024] §4.2.4).
Expresses incredulity: speaker encounters evidence conflicting with prior
expectations (Dukova-Zheleva). -/
def nima : QParticleEntry where
  form := "нима"
  romanization := "nima"
  gloss := "RAZVE (mirative/incredulity)"
  polarOk := true
  declOk := false
  whOk := false
  requiresContextualEvidence := some .forP
  requiresOriginalBias := none

def allQuestionParticles : List QParticleEntry := [li, nima]

theorem li_neutral :
    li.requiresContextualEvidence = none ∧ li.requiresOriginalBias = none :=
  ⟨rfl, rfl⟩

theorem nima_evidential : nima.requiresContextualEvidence = some .forP := rfl

/-- li and nima form a neutral/evidential contrast. -/
theorem bias_contrast :
    li.requiresContextualEvidence = none ∧ nima.requiresContextualEvidence = some .forP :=
  ⟨rfl, rfl⟩

end Bulgarian.QuestionParticles
