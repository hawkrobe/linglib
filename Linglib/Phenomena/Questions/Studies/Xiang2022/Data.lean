/-!
# Xiang 2022: Relativized Exhaustivity @cite{xiang-2022}

Empirical data on mention-some and uniqueness from:
Xiang, Yimei (2022). Relativized Exhaustivity: mention-some and uniqueness.
*Natural Language Semantics* 30:311–362.

## Overview

Theory-neutral data encoding Xiang's empirical generalizations about when
wh-questions receive mention-some (MS) vs mention-all (MA) interpretations.
Key factors: modal type in the question, the questioner's decision problem,
and structural conditions on the answer space (overlap, closure under ∧).

## Data Points

1. *Can*-questions license MS (ex. 32–33)
2. Bare wh-questions require MA (ex. 2b)
3. Epistemic *might* blocks MS (ex. 5)
4. Universal *must* requires MA (ex. 6)
5. Same question, different goals → MS vs MA (ex. 9–10)
6. Singular uniqueness: "Who is the chair?" (ex. 44–46)
-/

namespace Phenomena.Questions.Studies.Xiang2022.Data

/-- Whether a question receives mention-some, mention-all, or is ambiguous. -/
inductive MSMAJudgment where
  | mentionSome
  | mentionAll
  | ambiguous
  deriving DecidableEq, Repr

/-- Type of modal in the question, which affects MS/MA availability. -/
inductive ModalType where
  | none
  | abilityCanP
  | epistemicMight
  | universalMust
  deriving DecidableEq, Repr

/-- A single empirical datum from Xiang 2022. -/
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

/-! ### Data points -/

/-- *Can*-question licenses mention-some (Xiang 2022, ex. 32–33).

"Who can chair the committee?" — any single answer suffices when the
questioner's goal is to find *someone* who can serve. -/
def canQuestionMS : Xiang2022Datum :=
  { question := "Who can serve on the committee?"
  , modalType := .abilityCanP
  , judgment := .mentionSome
  , exampleAnswer := "Andy can. (sufficient answer)"
  , source := "Xiang 2022, ex. 32–33"
  }

/-- Bare wh-question requires mention-all (Xiang 2022, ex. 2b).

"Who called?" — without a modal, the question demands exhaustive listing. -/
def bareQuestionMA : Xiang2022Datum :=
  { question := "Who called?"
  , modalType := .none
  , judgment := .mentionAll
  , exampleAnswer := "Andy and Billy called. (#Andy called, as a complete answer)"
  , source := "Xiang 2022, ex. 2b"
  }

/-- Epistemic *might* blocks mention-some (Xiang 2022, ex. 5).

"Who might serve on the committee?" — even though modal, epistemics
pattern with MA because knowing one possibility doesn't resolve the DP. -/
def epistemicBlocksMS : Xiang2022Datum :=
  { question := "Who might serve on the committee?"
  , modalType := .epistemicMight
  , judgment := .mentionAll
  , exampleAnswer := "Andy might. (#incomplete — need full epistemic picture)"
  , source := "Xiang 2022, ex. 5"
  }

/-- Universal *must* requires mention-all (Xiang 2022, ex. 6).

"Who must serve?" — universal modals demand exhaustive identification. -/
def universalMA : Xiang2022Datum :=
  { question := "Who must serve on the committee?"
  , modalType := .universalMust
  , judgment := .mentionAll
  , exampleAnswer := "Andy and Billy must. (#Andy must, as a complete answer)"
  , source := "Xiang 2022, ex. 6"
  }

/-- Goal-driven MS: same question, find-someone goal (Xiang 2022, ex. 9–10).

"Who can serve?" with the goal of recruiting *one* person → MS reading. -/
def goalDrivenMS : Xiang2022Datum :=
  { question := "Who can serve on the committee?"
  , modalType := .abilityCanP
  , judgment := .mentionSome
  , exampleAnswer := "Context: We need to recruit one person. → Andy can."
  , source := "Xiang 2022, ex. 9"
  }

/-- Goal-driven MA: same question, know-all goal (Xiang 2022, ex. 9–10).

"Who can serve?" with the goal of knowing the *full* list → MA reading. -/
def goalDrivenMA : Xiang2022Datum :=
  { question := "Who can serve on the committee?"
  , modalType := .abilityCanP
  , judgment := .mentionAll
  , exampleAnswer := "Context: We need a complete roster. → Andy and Billy can."
  , source := "Xiang 2022, ex. 10"
  }

/-- Singular uniqueness: "Who is the chair?" (Xiang 2022, ex. 44–46).

Singular wh-questions with definite predicates have a uniqueness presupposition
that forces exactly one individual as the answer. -/
def singularUniqueness : Xiang2022Datum :=
  { question := "Who is the chair of the committee?"
  , modalType := .none
  , judgment := .mentionAll  -- uniqueness is a special case of exhaustivity
  , exampleAnswer := "Andy is. (unique answer presupposed)"
  , source := "Xiang 2022, ex. 44–46"
  }

/-- All data points from the paper. -/
def allData : List Xiang2022Datum :=
  [ canQuestionMS, bareQuestionMA, epistemicBlocksMS, universalMA
  , goalDrivenMS, goalDrivenMA, singularUniqueness ]

/-- Number of data points classified as mention-some. -/
def msCount : Nat :=
  allData.filter (λ d => d.judgment == .mentionSome) |>.length

/-- Number of data points classified as mention-all. -/
def maCount : Nat :=
  allData.filter (λ d => d.judgment == .mentionAll) |>.length

end Phenomena.Questions.Studies.Xiang2022.Data
