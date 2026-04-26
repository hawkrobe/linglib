/-!
# Bulgarian Question Particles
@cite{simik-2024}

Lexical entries for Bulgarian interrogative particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Phenomena.Questions.Studies.Simik2024`.

## Particles

| Particle | Romanization | Gloss | Bias |
|----------|-------------|-------|------|
| ли | li | neutral PQ | none |
| нима | nima | RAZVE (mirative) | +evidential |

## Cross-Module Connections

- `SlavicPQStrategies.bulgarian`: PQ strategy profile (verb-attached li)
- Cross-Slavic RAZVE family: nima is the Bulgarian member
- Dukova-Zheleva: nima expresses incredulity/surprise

-/

namespace Fragments.Slavic.Bulgarian.QuestionParticles

/-- A Bulgarian interrogative particle entry. -/
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

/-- ли li — verb-attached neutral PQ particle (@cite{simik-2024} ex. 33).
Encliticizes onto the focused constituent. -/
def li : QParticleEntry where
  form := "ли"
  romanization := "li"
  gloss := "PQ (verb-attached neutral)"
  polarOk := true
  declOk := false
  whOk := false
  requiresEvidentialBias := false
  requiresEpistemicBias := false

/-- нима nima — mirative/dubitative particle (RAZVE family, @cite{simik-2024} §4.2.4).
Expresses incredulity: speaker encounters evidence conflicting with prior
expectations (Dukova-Zheleva). -/
def nima : QParticleEntry where
  form := "нима"
  romanization := "nima"
  gloss := "RAZVE (mirative/incredulity)"
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

end Fragments.Slavic.Bulgarian.QuestionParticles
