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

/-- *quick / quickly* — meta-question adverb, signalling that the
addressee should answer without delay: matrix questions and quotations
only ([dayal-2025] pp. 670-671, the MQP class), ungrammatical embedded
(ex. 19a "Mary asked Sue *quick/quickly where she hid the matza"). -/
def quick : Particle where
  form := "quick"
  position := some .clauseInitial
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded
      quasiSubordinated := some .excluded
      quotation := some .optional }

def allQuestionParticles : List Particle := [quick]

end English.QuestionParticles
