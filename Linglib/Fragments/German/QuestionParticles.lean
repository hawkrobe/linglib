import Linglib.Phenomena.Questions.Typology

/-!
# German Question Particles

Lexical entries for German interrogative/flavoring particles.

## Particles

| Particle | Gloss | Layer | Bias |
|----------|-------|-------|------|
| denn | highlighting-sensitive flavoring particle | PerspP | +evidential |

German *denn* parallels Mandarin *nandao*: both require contextual evidence
prompting the question. Key difference: *denn* is compatible with wh-questions
(Theiler 2021), while *nandao* is restricted to polar questions (Zheng 2026).

Theiler (2021) analyzes *denn* as highlighting-sensitive: it signals that the
question is prompted by the highlighted/salient proposition in context.
In polar questions, this creates an evidential requirement; in wh-questions,
it merely signals informational need.

## Cross-Module Connections

- `Fragments.Mandarin.QuestionParticles.nandao`: cross-linguistic parallel
- `Kernel.nandaoFelicitous`: shared felicity mechanism (evidence + unexpectedness)

## References

- Theiler, N. (2021). Denn as a highlighting-sensitive particle.
  Linguistics and Philosophy 44, 323–362.
- Zheng, A.A. (2026). nandao-Qs: When Surprise Sparks Inquiry. WCCFL 43.
-/

namespace Fragments.German.QuestionParticles

open Phenomena.Questions.Typology (QParticleLayer)

/-- A German interrogative/flavoring particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  layer : QParticleLayer
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  deriving Repr, DecidableEq, BEq

/-- denn — highlighting-sensitive flavoring particle (Theiler 2021).
Signals the question is prompted by salient contextual evidence.
Compatible with both polar and wh-questions (unlike nandao). -/
def denn : QParticleEntry where
  form := "denn"
  gloss := "DENN (highlighting-sensitive flavoring particle)"
  layer := .perspP
  polarOk := true
  declOk := false
  whOk := true
  requiresEvidentialBias := true
  requiresEpistemicBias := false

def allQuestionParticles : List QParticleEntry := [denn]

theorem denn_evidential : denn.requiresEvidentialBias = true := rfl
theorem denn_no_epistemic : denn.requiresEpistemicBias = false := rfl

/-- Unlike Mandarin nandao, German denn is compatible with wh-questions
(Theiler 2021 §3). -/
theorem denn_wh_ok : denn.whOk = true := rfl

end Fragments.German.QuestionParticles
