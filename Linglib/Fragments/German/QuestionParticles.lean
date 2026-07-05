import Linglib.Syntax.Particle.Basic

/-!
# German Question Particles

Lexical entries for the German interrogative/flavoring particles *denn* and
*doch wohl*, as `Particle` values. *denn* is a highlighting-sensitive
flavoring particle ([theiler-2021]); *doch wohl* is a non-compositional
marker of rejecting questions ([seeliger-repp-2018]). Layer assignments,
bias profiles, and full analyses live in the paper-anchored studies
`Theiler2021` and `SeeligerRepp2018` — a particle's bias requirement is an
analytical classification, not consensus lexical data.
-/

namespace German.QuestionParticles

/-- *denn* — highlighting-sensitive flavoring particle ([theiler-2021]),
licensed in both polar and constituent questions (unlike *nandao*),
excluded from declaratives. Its felicity condition
(highlighting/precondition) and bias profile live in `Theiler2021`. -/
def denn : Particle where
  form := "denn"
  position := .clauseMedial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .optional }

/-- *doch wohl* — non-compositional marker of rejecting questions
([seeliger-repp-2018]): declarative-syntax polar questions (recorded under
`polarInterrogative` following the source schema's question-function
reading), not assertions and not wh-questions. The PRQ/NRQ bias profile
lives in `SeeligerRepp2018`. -/
def dochWohl : Particle where
  form := "doch wohl"
  position := .clauseMedial
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional
      constituentInterrogative := some .excluded }

def allQuestionParticles : List Particle := [denn, dochWohl]

end German.QuestionParticles
