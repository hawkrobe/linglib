/-!
# English Question Particles
@cite{dayal-2025} @cite{bhatt-dayal-2020}

Lexical entries for English MQP-like adverbs that participate in the
left-peripheral typology of Q-particles. The fragment commits only to
theory-neutral lexical primitives (form, gloss, distribution); the
left-peripheral layer assignment lives in
`Phenomena.Questions.Studies.BhattDayal2020`.

## Particles

| Particle | Gloss | Distribution |
|----------|-------|--------------|
| quick    | matrix-only meta-question adverb | matrix only |

English lacks dedicated Q-particles for clause typing (the language uses
syntactic inversion + *whether* for embedded polar questions). What it
does have is a small set of MQP-like adverbs (*quick*, *quickly*) that
attach to matrix questions and signal urgency / addressee-directed
information request, but are ungrammatical in any embedded position
(@cite{dayal-2025} ex. (19)).
-/

namespace Fragments.English.QuestionParticles

/-- An English MQP-like question adverb entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  /-- Compatible with matrix questions? -/
  inMatrix : Bool
  /-- Compatible with subordinated interrogatives? -/
  inSubordinated : Bool
  /-- Compatible with quasi-subordinated interrogatives? -/
  inQuasiSub : Bool
  /-- Compatible with quotation? -/
  inQuotation : Bool
  deriving Repr, DecidableEq

/-- *quick / quickly* — matrix-only meta-question adverb.

    Signals urgency in a request for information. Ungrammatical in
    subordinated, quasi-subordinated, or quotation contexts
    (@cite{dayal-2025} ex. (19)). -/
def quick : QParticleEntry where
  form := "quick"
  gloss := "MQP-adv (matrix-only urgency adverb)"
  inMatrix := true
  inSubordinated := false
  inQuasiSub := false
  inQuotation := false

def allQuestionParticles : List QParticleEntry := [quick]

theorem quick_matrix_only :
    quick.inMatrix = true ∧ quick.inSubordinated = false ∧
    quick.inQuasiSub = false ∧ quick.inQuotation = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Fragments.English.QuestionParticles
