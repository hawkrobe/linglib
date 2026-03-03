/-!
# @cite{xiang-2022}: Relativized Exhaustivity @cite{xiang-2022}

Empirical data on mention-some and uniqueness from:
@cite{xiang-2022}. Relativized Exhaustivity: mention-some and uniqueness.
*Natural Language Semantics* 30:311–362.

## Overview

@cite{xiang-2022} makes three contributions:

1. MS answers are subject to a "mention-one-only" constraint: they must name
   a single individual, not a disjunction (ex. 3–4).
2. MS is primarily *grammatically* licensed by ability *can* inside the
   question nucleus, not pragmatically by decision problems. The MS/MA
   ambiguity in *can*-questions reflects structural scope ambiguity of
   the wh-trace relative to the modal (first-order vs higher-order).
3. The RelExh presupposition (91) — exhaustivity evaluated relative to
   singleton modal bases — unifies MS licensing, avoids over-generation
   for non-*can* questions, and derives local-uniqueness effects in
   modalized singular wh-questions.

## Data points

Empirical generalizations from the paper, with exact example numbers:
1. "Who can chair the committee?" — MS available (ex. 2)
2. "Who called?" — MA required (ex. 1)
3. Mention-one-only constraint (ex. 3–4)
4. Non-*can* modals block MS: *should*, *might* (ex. 6)
5. Same question, different contexts → MS vs MA (Section 2.2)
6. Singular uniqueness effects (Section 4.3, Section 6.3)
7. Table 3 summary: RelExh vs Dayal's EP predictions
-/

namespace Phenomena.Questions.Studies.Xiang2022.Data

/-- Whether a question receives mention-some, mention-all, or is ambiguous
between the two readings. -/
inductive MSMAJudgment where
  | mentionSome
  | mentionAll
  | ambiguous
  deriving DecidableEq, Repr

/-- Type of modal in the question, which affects MS/MA availability.
Xiang's key claim: only ability *can* grammatically licenses MS. -/
inductive ModalType where
  | none
  | abilityCan
  | epistemicMight
  | deonticShould
  deriving DecidableEq, Repr

/-- A single empirical datum from @cite{xiang-2022}. -/
structure Xiang2022Datum where
  /-- The question under study -/
  question : String
  /-- What modal (if any) appears in the question -/
  modalType : ModalType
  /-- Observed MS/MA judgment -/
  judgment : MSMAJudgment
  /-- An example answer or context -/
  exampleAnswer : String
  /-- Source reference within the paper -/
  source : String
  deriving Repr

/-! ### Core data: MS licensing by modal type -/

/-- Ability *can* licenses mention-some (@cite{xiang-2022}, ex. 2).

"Who can chair the committee?" — naming a single individual is a
sufficient answer. This is the paper's central empirical observation:
MS is grammatically licensed by *can*. -/
def canQuestionMS : Xiang2022Datum :=
  { question := "Who can chair the committee?"
  , modalType := .abilityCan
  , judgment := .mentionSome
  , exampleAnswer := "Anne can. (sufficient answer)"
  , source := "Xiang 2022, ex. 2"
  }

/-- Bare wh-question requires mention-all (@cite{xiang-2022}, ex. 1).

"Who called?" — without a modal, the question demands exhaustive listing.
Non-modalized questions uniformly receive MA. -/
def bareQuestionMA : Xiang2022Datum :=
  { question := "Who called?"
  , modalType := .none
  , judgment := .mentionAll
  , exampleAnswer := "Anne and Bill called. (#Anne called, as a complete answer)"
  , source := "Xiang 2022, ex. 1"
  }

/-- Deontic *should* blocks mention-some (@cite{xiang-2022}, ex. 6b).

"Which students should pass the test?" — even though modal, deontic
modals pattern with MA. Only ability *can* licenses MS. -/
def deonticBlocksMS : Xiang2022Datum :=
  { question := "Which students should pass the test?"
  , modalType := .deonticShould
  , judgment := .mentionAll
  , exampleAnswer := "All students who should. (#Anne should, as a complete answer)"
  , source := "Xiang 2022, ex. 6b"
  }

/-- Epistemic *might* blocks mention-some (@cite{xiang-2022}, ex. 6c).

"Which students might pass the test?" — epistemics pattern with MA,
not MS. The question demands the full epistemic picture. -/
def epistemicBlocksMS : Xiang2022Datum :=
  { question := "Which students might pass the test?"
  , modalType := .epistemicMight
  , judgment := .mentionAll
  , exampleAnswer := "All students who might. (#Anne might, as a complete answer)"
  , source := "Xiang 2022, ex. 6c"
  }

/-- Non-modalized question requires MA (@cite{xiang-2022}, ex. 6a).

"Which students passed the test?" — without a modal, exhaustive. -/
def nonModalMA : Xiang2022Datum :=
  { question := "Which students passed the test?"
  , modalType := .none
  , judgment := .mentionAll
  , exampleAnswer := "All students who passed."
  , source := "Xiang 2022, ex. 6a"
  }

/-! ### Context sensitivity (Section 2.2) -/

/-- Goal-driven MS: same question, recruit-one goal (@cite{xiang-2022}, Section 2.2).

"Who can chair the committee?" with the goal of recruiting *one* person.
@cite{van-rooij-2003} models this via a decision problem where any single
committee member resolves the DP. -/
def goalDrivenMS : Xiang2022Datum :=
  { question := "Who can chair the committee?"
  , modalType := .abilityCan
  , judgment := .mentionSome
  , exampleAnswer := "Context: We need to recruit one more member. → Anne can."
  , source := "Xiang 2022, Section 2.2 (cf. van Rooij 2003)"
  }

/-- Goal-driven MA: same question, know-all goal (@cite{xiang-2022}, Section 2.2).

Same question as above, but the goal of knowing the *full* candidate list.
The DP requires complete information, so all candidates must be named. -/
def goalDrivenMA : Xiang2022Datum :=
  { question := "Who can chair the committee?"
  , modalType := .abilityCan
  , judgment := .mentionAll
  , exampleAnswer := "Context: We want a complete roster. → Anne and Bill can."
  , source := "Xiang 2022, Section 2.2 (cf. van Rooij 2003)"
  }

/-! ### Mention-one-only constraint (ex. 3–4) -/

/-- Whether an MS answer obeys the mention-one-only constraint. -/
structure MentionOneOnlyDatum where
  /-- The question -/
  question : String
  /-- The proposed MS answer -/
  answer : String
  /-- Is this answer acceptable as an MS answer? -/
  acceptable : Bool
  /-- Source -/
  source : String
  deriving Repr

/-- Valid MS answer: single individual (@cite{xiang-2022}, ex. 3a).

"Anne can." — a single-individual MS answer is acceptable. -/
def mentionOneValid : MentionOneOnlyDatum :=
  { question := "Who can chair the committee?"
  , answer := "Anne can."
  , acceptable := true
  , source := "Xiang 2022, ex. 3a"
  }

/-- Invalid MS answer: disjunction (@cite{xiang-2022}, ex. 3b).

"#Anne or Bill can." — a disjunctive MS answer is blocked by
the mention-one-only constraint. This is NOT predicted by
van Rooij's decision-theoretic account but IS predicted by
Xiang's semantic analysis. -/
def mentionOneInvalid : MentionOneOnlyDatum :=
  { question := "Who can chair the committee?"
  , answer := "#Anne or Bill can."
  , acceptable := false
  , source := "Xiang 2022, ex. 3b"
  }

/-! ### Uniqueness effects (Section 4.3, Section 6.3) -/

/-- Types of uniqueness inference observed in singular wh-questions.
Xiang distinguishes global vs local uniqueness (Table 3). -/
inductive UniquenessType where
  | global       -- exactly one individual satisfies P in every accessible world
  | local        -- in each accessible world, at most one individual satisfies P
  | existLocal   -- "existential" local uniqueness (weaker, via existential closure)
  | none
  deriving DecidableEq, Repr

/-- A datum about uniqueness effects in singular wh-questions. -/
structure UniquenessDatum where
  /-- The question -/
  question : String
  /-- Modal type -/
  modalType : ModalType
  /-- Type of uniqueness inference -/
  uniqueness : UniquenessType
  /-- Whether Dayal's EP predicts this -/
  dayalEPPredicts : Bool
  /-- Whether RelExh predicts this -/
  relExhPredicts : Bool
  /-- Source -/
  source : String
  deriving Repr

/-- Non-modalized singular: global uniqueness.
"Which child came?" — presupposes exactly one child came.
Both Dayal's EP and RelExh predict this. (Table 3, row 1) -/
def nonModalUniqueness : UniquenessDatum :=
  { question := "Which child came?"
  , modalType := .none
  , uniqueness := .global
  , dayalEPPredicts := true
  , relExhPredicts := true
  , source := "Xiang 2022, Table 3, ex. 64"
  }

/-- □-modal singular (have-to), global uniqueness.
"Which chapter do we have to assign?" — global uniqueness reading.
Both Dayal's EP and RelExh predict. (Table 3, row 3) -/
def boxModalGlobalUniq : UniquenessDatum :=
  { question := "Which chapter do we have to assign?"
  , modalType := .deonticShould
  , uniqueness := .global
  , dayalEPPredicts := true
  , relExhPredicts := true
  , source := "Xiang 2022, Table 3, ex. 99/102"
  }

/-- □-modal singular (have-to), local uniqueness.
"Which chapter do we have to assign?" — local uniqueness reading.
Dayal's EP does NOT predict this; RelExh DOES. This is a key
advantage of RelExh over Dayal's EP. (Table 3, row 4) -/
def boxModalLocalUniq : UniquenessDatum :=
  { question := "Which chapter do we have to assign?"
  , modalType := .deonticShould
  , uniqueness := .local
  , dayalEPPredicts := false
  , relExhPredicts := true
  , source := "Xiang 2022, Table 3, ex. 99/103"
  }

/-- ◇-modal singular (can), local uniqueness in MS.
"Which chapter can we assign?" — existential local uniqueness.
Dayal's EP does NOT predict; RelExh DOES. (Table 3, row 8) -/
def canModalLocalUniqMS : UniquenessDatum :=
  { question := "Which chapter can we assign?"
  , modalType := .abilityCan
  , uniqueness := .existLocal
  , dayalEPPredicts := false
  , relExhPredicts := true
  , source := "Xiang 2022, Table 3, ex. 100–101/105b"
  }

/-- ◇-modal singular (can), global uniqueness.
"Which chapter can we assign?" — global uniqueness.
Dayal's EP predicts this but RelExh does NOT — the only cell in
Table 3 where Dayal's EP has coverage that RelExh lacks. (Table 3, row 7) -/
def canModalGlobalUniq : UniquenessDatum :=
  { question := "Which chapter can we assign?"
  , modalType := .abilityCan
  , uniqueness := .global
  , dayalEPPredicts := true
  , relExhPredicts := false
  , source := "Xiang 2022, Table 3, row 7"
  }

def uniquenessData : List UniquenessDatum :=
  [ nonModalUniqueness, boxModalGlobalUniq, boxModalLocalUniq
  , canModalLocalUniqMS, canModalGlobalUniq ]

/-! ### Aggregation -/

/-- All MS/MA judgment data points from the paper. -/
def allData : List Xiang2022Datum :=
  [ canQuestionMS, bareQuestionMA, deonticBlocksMS, epistemicBlocksMS
  , nonModalMA, goalDrivenMS, goalDrivenMA ]

/-- Data points classified as mention-some. -/
def msCount : Nat :=
  allData.filter (λ d => d.judgment == .mentionSome) |>.length

/-- Data points classified as mention-all. -/
def maCount : Nat :=
  allData.filter (λ d => d.judgment == .mentionAll) |>.length

/-- Table 3 cells where RelExh has coverage that Dayal's EP lacks. -/
def relExhAdvantages : Nat :=
  uniquenessData.filter (λ d => d.relExhPredicts && !d.dayalEPPredicts) |>.length

/-- Table 3 cells where Dayal's EP has coverage that RelExh lacks. -/
def dayalAdvantages : Nat :=
  uniquenessData.filter (λ d => d.dayalEPPredicts && !d.relExhPredicts) |>.length

end Phenomena.Questions.Studies.Xiang2022.Data
