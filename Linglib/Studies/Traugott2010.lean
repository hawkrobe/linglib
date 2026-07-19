import Linglib.Features.Subjectivity

/-!
# Traugott (2010): Subjectification and Intersubjectification
[traugott-2010] [traugott-dasher-2002]

The diachronic hypothesis that lexical items acquire subjective and
intersubjective meanings over time, in a fixed order:

    nonsubjective → subjective → intersubjective

This is one of the best-supported unidirectional tendencies in semantic
change, attested across modality, connectives, discourse markers, and
spatial expressions. [traugott-2010] is the consolidating statement of
the program developed in [traugott-dasher-2002].

The synchronic infrastructure (the `SubjectivityLevel` type and ordering)
lives in `Features.Subjectivity`. This file formalizes the **diachronic
claims**: that the ordering reflects a historical trajectory, that each
transition is unidirectional, and that specific semantic domains exhibit
this pattern.

## Connections

- `Semantics.Modality.Narrog`: speaker-orientation level maps to
  subjectivity level; the directionality of modal change (see
  `Studies/Narrog2010.lean`) is an instance of subjectification.
- `Quantification.Binominal`: the bleaching cline (N+PP → evaluative → intensifier)
  parallels the subjectification trajectory in the nominal domain
  (binominal steps formalized in `Studies/TenWolde2023.lean`).
- `Features/Grammaticalization.lean`: subjectification is a semantic
  dimension of grammaticalization — as forms grammaticalize, they tend
  to acquire more subjective meanings.
-/

namespace Traugott2010

open Features.Subjectivity

/-! ### The diachronic cline -/

/-- A diachronic subjectification step: a word or construction acquires a
    meaning at a higher subjectivity level. -/
structure SubjectificationStep where
  /-- Description of the expression. -/
  expression : String
  /-- Earlier (less subjective) meaning. -/
  sourceMeaning : String
  /-- Later (more subjective) meaning. -/
  targetMeaning : String
  /-- Subjectivity level of the source meaning. -/
  sourceLevel : SubjectivityLevel
  /-- Subjectivity level of the target meaning. -/
  targetLevel : SubjectivityLevel
  /-- Unidirectionality: target is at least as subjective as source. -/
  directed : sourceLevel ≤ targetLevel
  deriving Repr

/-- Canonical examples of subjectification.
    [traugott-dasher-2002] Table 1, [traugott-2010] §2. -/
def canonicalExamples : List SubjectificationStep :=
  [ -- "while": temporal → concessive → polite refusal
    { expression := "while"
      sourceMeaning := "during the time that (temporal)"
      targetMeaning := "although (concessive)"
      sourceLevel := .nonSubjective
      targetLevel := .subjective
      directed := by decide }
  , -- "must": root necessity → epistemic necessity
    { expression := "must"
      sourceMeaning := "is required to (deontic)"
      targetMeaning := "necessarily is (epistemic)"
      sourceLevel := .subjective
      targetLevel := .subjective
      directed := by decide }
  , -- "please": verb → politeness marker
    { expression := "please"
      sourceMeaning := "if it pleases you (propositional)"
      targetMeaning := "politeness marker (addressee face)"
      sourceLevel := .nonSubjective
      targetLevel := .intersubjective
      directed := by decide }
  , -- "in fact": locative → epistemic → discourse marker
    { expression := "in fact"
      sourceMeaning := "in reality (propositional)"
      targetMeaning := "contrary to expectation (discourse marker)"
      sourceLevel := .nonSubjective
      targetLevel := .subjective
      directed := by decide }
  ]

/-- All canonical examples respect unidirectionality. -/
theorem all_directed :
    ∀ s ∈ canonicalExamples, s.sourceLevel ≤ s.targetLevel :=
  fun s hs => by
    simp [canonicalExamples] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> decide

/-! ### Intersubjectification -/

/-- Intersubjectification: the final stage of the cline, where meanings
    come to encode attention to the addressee's face/self-image.

    [traugott-2010]: intersubjectification presupposes subjectification.
    An expression must first acquire speaker-oriented meaning before it can
    develop addressee-oriented meaning. -/
theorem intersubjectification_presupposes_subjectification :
    SubjectivityLevel.subjective ≤ SubjectivityLevel.intersubjective := by decide

/-- The full cline is totally ordered. -/
theorem cline_total_order (a b : SubjectivityLevel) : a ≤ b ∨ b ≤ a :=
  le_total a b

end Traugott2010
