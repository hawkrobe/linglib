/-!
# Polish Question Particles
@cite{simik-2024}

Lexical entries for Polish interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Phenomena.Questions.Studies.Simik2024`.

## Particles

| Particle | Gloss | Bias |
|----------|-------|------|
| czy | neutral PQ | none |
| czyżby | RAZVE (mirative) | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.polish`: PQ strategy profile (clause-initial czy obligatory)
- Cross-Slavic RAZVE family: czyżby is the Polish member

-/

namespace Fragments.Slavic.Polish.QuestionParticles

/-- A Polish interrogative particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  deriving Repr, DecidableEq

/-- czy — obligatory clause-initial PQ particle (@cite{simik-2024} ex. 30).
Verb-initial PQs possible but unacceptable in quiz scenarios. -/
def czy : QParticleEntry where
  form := "czy"
  gloss := "PQ (clause-initial neutral)"
  polarOk := true
  declOk := false
  whOk := true
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- czyżby — mirative/dubitative particle (RAZVE family, @cite{simik-2024} §4.2.4).
Polish member of the cross-Slavic razve family. -/
def czyzby : QParticleEntry where
  form := "czyżby"
  gloss := "RAZVE (mirative/dubitative)"
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := true
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [czy, czyzby]

theorem czy_neutral :
    czy.requiresEvidentialBias = false ∧ czy.requiresEpistemicBias = false :=
  ⟨rfl, rfl⟩

theorem czyzby_evidential : czyzby.requiresEvidentialBias = true := rfl

/-- czy and czyżby form a neutral/evidential contrast. -/
theorem bias_contrast :
    czy.requiresEvidentialBias = false ∧ czyzby.requiresEvidentialBias = true :=
  ⟨rfl, rfl⟩

end Fragments.Slavic.Polish.QuestionParticles
