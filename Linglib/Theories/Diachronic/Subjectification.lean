import Linglib.Features.Subjectivity

/-!
# Subjectification and Intersubjectification
@cite{traugott-dasher-2002} @cite{traugott-2010}

The diachronic hypothesis that lexical items acquire subjective and
intersubjective meanings over time, in a fixed order:

    nonsubjective → subjective → intersubjective

This is one of the best-supported unidirectional tendencies in semantic
change, attested across modality, connectives, discourse markers, and
spatial expressions.

The synchronic infrastructure (the `SubjectivityLevel` type and ordering)
lives in `Features.Subjectivity`. This module formalizes the **diachronic claims**:
that the ordering reflects a historical trajectory, that each transition is
unidirectional, and that specific semantic domains exhibit this pattern.

## Connections

- `Theories.Semantics.Modality.Narrog`: speaker-orientation level maps to
  subjectivity level; the directionality of modal change (see
  `Diachronic.ModalChange`) is an instance of subjectification.
- `Core.Lexical.Binominal`: the bleaching cline (N+PP → evaluative → intensifier)
  parallels the subjectification trajectory in the nominal domain: N₁ shifts
  from denoting objective properties to expressing speaker attitude.
- `Diachronic.Grammaticalization`: subjectification is a semantic dimension of
  grammaticalization — as forms grammaticalize, they tend to acquire
  more subjective meanings.
-/

namespace Diachronic.Subjectification

open Features.Subjectivity

-- ============================================================================
-- §1. The Diachronic Cline
-- ============================================================================

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
    @cite{traugott-dasher-2002} Table 1, @cite{traugott-2010} §2. -/
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

-- ============================================================================
-- §2. Binominal Subjectification
-- ============================================================================

/-- Subjectification steps in the binominal (N₁-of-N₂) domain.

@cite{ten-wolde-2023} §4.5: the EBNP → EM → BI transitions are driven by
subjectification — N₁ shifts from ascribing objective/physical properties
to expressing the speaker's subjective evaluation. -/
def binominalSubjectificationSteps : List SubjectificationStep :=
  [ -- N+PP/HC → EBNP: the key subjectification step in the binominal domain.
    -- N₁ shifts from denoting objective referential properties to expressing
    -- the speaker's evaluative attitude.
    { expression := "N₁ in of-binominals"
      sourceMeaning := "N₁ denotes referential property (N+PP: the beast of the field)"
      targetMeaning := "N₁ ascribes evaluative property (EBNP: that idiot of a doctor)"
      sourceLevel := .nonSubjective
      targetLevel := .subjective
      directed := by decide }
  , -- EBNP → EM: N₁ bleaches from full gradable predicate to pure
    -- speaker evaluation. Subjectivity level maintained but semantics bleached.
    { expression := "[N₁ of a] in of-binominals"
      sourceMeaning := "N₁ ascribes evaluative property (EBNP: a beast of a man)"
      targetMeaning := "N₁ expresses speaker's subjective evaluation (EM: a hell of a game)"
      sourceLevel := .subjective
      targetLevel := .subjective
      directed := by decide }
  , -- EM → BI: N₁ further bleaches to degree intensifier.
    -- Subjectivity level maintained; the change is syntactic (shifts into AdjP).
    { expression := "[N₁ of a] in of-binominals"
      sourceMeaning := "N₁ as evaluative modifier (EM: a hell of a time)"
      targetMeaning := "N₁ as degree intensifier (BI: a hell of a good time)"
      sourceLevel := .subjective
      targetLevel := .subjective
      directed := by decide }
  ]

/-- The N+PP → EBNP step is a genuine subjectification (nonSubjective → subjective);
    the later steps maintain subjectivity while bleaching semantics further. -/
theorem binominal_steps_directed :
    ∀ s ∈ binominalSubjectificationSteps, s.sourceLevel ≤ s.targetLevel :=
  fun s hs => by
    simp [binominalSubjectificationSteps] at hs
    rcases hs with rfl | rfl | rfl <;> decide

-- ============================================================================
-- §3. Intersubjectification
-- ============================================================================

/-- Intersubjectification: the final stage of the cline, where meanings
    come to encode attention to the addressee's face/self-image.

    @cite{traugott-2010}: intersubjectification presupposes subjectification.
    An expression must first acquire speaker-oriented meaning before it can
    develop addressee-oriented meaning. -/
theorem intersubjectification_presupposes_subjectification :
    SubjectivityLevel.subjective ≤ SubjectivityLevel.intersubjective := by decide

/-- The full cline is totally ordered. -/
theorem cline_total_order (a b : SubjectivityLevel) : a ≤ b ∨ b ≤ a :=
  le_total a b

end Diachronic.Subjectification
