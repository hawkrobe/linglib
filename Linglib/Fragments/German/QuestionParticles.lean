import Linglib.Semantics.Questions.Bias.Defs

/-!
# German Question Particles

Lexical entries for the German interrogative/flavoring particles *denn* and
*doch wohl*, committing only to theory-neutral lexical primitives. *denn* is a
highlighting-sensitive flavoring particle ([theiler-2021]); *doch wohl* is a
non-compositional marker of rejecting questions ([seeliger-repp-2018]). The
layer assignments and full analyses live in the paper-anchored studies
`Theiler2021` and `SeeligerRepp2018`.
-/

namespace German.QuestionParticles

open Semantics.Questions.Bias (ContextualEvidence OriginalBias)

/-- A German interrogative/flavoring particle entry. -/
structure QParticleEntry where
  /-- Orthographic form of the particle. -/
  form : String
  /-- Felicitous in polar interrogatives. -/
  polarOk : Bool
  /-- Felicitous in declarative clauses. -/
  declOk : Bool
  /-- Felicitous in wh-interrogatives. -/
  whOk : Bool
  /-- Contextual-evidence bias the particle requires, or `none` if it imposes
      no such constraint. -/
  requiresContextualEvidence : Option ContextualEvidence
  /-- Original speaker bias the particle requires, or `none` if it imposes
      no such constraint. -/
  requiresOriginalBias : Option OriginalBias
  deriving Repr, DecidableEq

/-- *denn* — highlighting-sensitive flavoring particle ([theiler-2021]),
licensed in both polar and wh-questions (unlike *nandao*). It imposes no
bias requirement: its felicity condition is the highlighting/precondition
relation analysed in `Theiler2021`, not contextual or speaker bias. -/
def denn : QParticleEntry where
  form := "denn"
  polarOk := true
  declOk := false
  whOk := true
  requiresContextualEvidence := none
  requiresOriginalBias := none

/-- *doch wohl* — non-compositional marker of rejecting questions
([seeliger-repp-2018]). The fields record the prototypical negated (NRQ)
reading — contextual evidence for p, prior speaker bias against p
([seeliger-repp-2018] Table 1) — i.e. the speaker assumed ¬p but the evidence
points to p. The positive (PRQ) reading flips both dimensions; the direction
tracks clause polarity, which a single fixed-direction entry cannot capture
(the full PRQ/NRQ analysis is in `SeeligerRepp2018`). -/
def dochWohl : QParticleEntry where
  form := "doch wohl"
  polarOk := true
  declOk := false  -- marks a question, not an assertion
  whOk := false
  requiresContextualEvidence := some .forP
  requiresOriginalBias := some .againstP

/-- All German question-particle entries. -/
def allQuestionParticles : List QParticleEntry := [denn, dochWohl]

/-- *doch wohl* requires both contextual-evidence and original-speaker bias,
whereas *denn* imposes neither — reflecting the insisting nature of rejecting
questions versus the merely highlighting nature of *denn*-questions. -/
theorem dochWohl_stricter_than_denn :
    dochWohl.requiresContextualEvidence = some .forP ∧
    dochWohl.requiresOriginalBias = some .againstP ∧
    denn.requiresContextualEvidence = none ∧
    denn.requiresOriginalBias = none := ⟨rfl, rfl, rfl, rfl⟩

end German.QuestionParticles
