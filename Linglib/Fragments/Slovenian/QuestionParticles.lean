/-!
# Slovenian Question Particles
@cite{simik-2024}

Lexical entries for Slovenian interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Phenomena.Questions.Studies.Simik2024`.

## Particles

| Particle | Gloss | Bias |
|----------|-------|------|
| ali | neutral PQ | none |

*ali* is a clause-initial particle, optional in default PQs.
Incompatible with DeclPQs (@cite{simik-2024} ex. 28).

## Cross-Module Connections

- `SlavicPQStrategies.slovenian`: PQ strategy profile

-/

namespace Fragments.Slovenian.QuestionParticles

/-- A Slovenian interrogative particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  deriving Repr, DecidableEq

/-- ali — clause-initial PQ particle (@cite{simik-2024} ex. 28).
Optional; incompatible with DeclPQs. No bias requirements. -/
def ali : QParticleEntry where
  form := "ali"
  gloss := "PQ (clause-initial neutral)"
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [ali]

theorem ali_neutral :
    ali.requiresEvidentialBias = false ∧ ali.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

end Fragments.Slovenian.QuestionParticles
