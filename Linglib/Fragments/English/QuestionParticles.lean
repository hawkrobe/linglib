import Linglib.Syntax.Particle.Basic

/-!
# English Question Particles
[dayal-2025] [bhatt-dayal-2020]

Lexical entry for the English MQP-like adverb *quick/quickly* as a
`Particle` value with an embedding-distribution facet. The
left-peripheral layer assignment is derived from that facet in
`BhattDayal2020`.
-/

namespace English.QuestionParticles

/-- *quick / quickly* — matrix-only meta-question adverb: signals
urgency in a request for information. Ungrammatical in subordinated,
quasi-subordinated, and quotation contexts ([dayal-2025] ex. (19)). -/
def quick : Particle where
  form := "quick"
  position := some .clauseInitial
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded
      quasiSubordinated := some .excluded
      quotation := some .excluded }

def allQuestionParticles : List Particle := [quick]

end English.QuestionParticles
