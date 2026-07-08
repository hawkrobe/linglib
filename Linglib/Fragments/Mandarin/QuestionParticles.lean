import Linglib.Syntax.Category.Particle.Basic

/-!
# Mandarin Question Particles
[zheng-2025]

Lexical entries for Mandarin interrogative particles as `Particle` values.
Bias profiles (ba's speaker-bias requirement, nandao's evidential
requirement) are analytical classifications and live with the analysis
that assigns them, in `Zheng2025` — alongside the left-peripheral layer
assignments.

## Particles

| Particle | Gloss | Restriction |
|----------|-------|-------------|
| 吗 ma | PQ marker | polar + wh |
| 吧 ba | TAG/confirm | polar only |
| 难道 nándào | NANDAO | polar only |

## Cross-Module Connections

- `Zheng2025`: bias profiles, layer assignments, `Kernel.nandaoFelicitous`
-/

namespace Mandarin.QuestionParticles

/-- 吗 ma — unmarked polar question particle. Sentence-final; turns a
declarative into a yes/no question. Bias-neutral (see `Zheng2025`). -/
def ma : Particle where
  form := "ma"
  script := some "吗"
  position := some .clauseFinal
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .optional }

/-- 吧 ba — confirmation-seeking particle. Speaker expects a positive
answer and seeks confirmation, comparable to English tag questions
("It's raining, isn't it?"). Its speaker-bias requirement lives in
`Zheng2025`. -/
def ba : Particle where
  form := "ba"
  script := some "吧"
  position := some .clauseFinal
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

/-- 难道 nándào — evidential question particle: marks that the speaker has
encountered unexpected contextual evidence supporting the prejacent;
compatible with a neutral epistemic state (pure inquiry use, [zheng-2025]
ex. 3). Canonically clause-initial (post-subject placement possible).
Polar-only — the contrast with wh-compatible *denn* lives in `Theiler2021`.
Its evidential requirement lives in `Zheng2025`. -/
def nandao : Particle where
  form := "nándào"
  script := some "难道"
  position := some .clauseInitial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [ma, ba, nandao]

end Mandarin.QuestionParticles
