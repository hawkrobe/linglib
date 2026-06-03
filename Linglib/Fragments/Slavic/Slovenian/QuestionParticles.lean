import Linglib.Semantics.Questions.Bias.Defs
/-!
# Slovenian Question Particles
[simik-2024]

Lexical entries for Slovenian interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Simik2024`.

## Particles

| Particle | Gloss | Bias |
|----------|-------|------|
| ali | neutral PQ | none |

*ali* is a clause-initial particle, optional in default PQs.
Incompatible with DeclPQs ([simik-2024] ex. 28).

## Cross-Module Connections

- `SlavicPQStrategies.slovenian`: PQ strategy profile

-/

namespace Slovenian.QuestionParticles

open Semantics.Questions.Bias (ContextualEvidence OriginalBias)

/-- A Slovenian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresContextualEvidence : Option ContextualEvidence
  requiresOriginalBias : Option OriginalBias
  deriving Repr, DecidableEq

/-- ali — clause-initial PQ particle ([simik-2024] ex. 28).
Optional; incompatible with DeclPQs. No bias requirements. -/
def ali : QParticleEntry where
  form := "ali"
  gloss := "PQ (clause-initial neutral)"
  polarOk := true
  declOk := false
  whOk := false
  requiresContextualEvidence := none
  requiresOriginalBias := none

def allQuestionParticles : List QParticleEntry := [ali]

theorem ali_neutral :
    ali.requiresContextualEvidence = none ∧ ali.requiresOriginalBias = none :=
  ⟨rfl, rfl⟩

end Slovenian.QuestionParticles
