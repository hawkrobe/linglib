/-
# Questions: Basic Types and Shared Infrastructure

Theory-neutral types for question-answer phenomena.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Krifka (2011). Questions. In Semantics: An International Handbook.
- Dayal (2016). Questions. Oxford University Press.
-/

namespace Phenomena.Questions

-- ============================================================================
-- Question Types
-- ============================================================================

/-- Classification of question types -/
inductive QuestionType where
  | polar           -- Yes/no questions: "Did John leave?"
  | whSingular      -- Singular wh: "Who left?"
  | whPlural        -- Plural wh: "Which students left?"
  | alternative     -- Alternative: "Did John or Mary leave?"
  | whyHow          -- Reason/manner: "Why/How did John leave?"
  deriving DecidableEq, Repr

/-- Answer completeness -/
inductive AnswerCompleteness where
  | exhaustive      -- Complete answer to the question
  | mentionSome     -- Partial but sufficient answer
  | incomplete      -- Incomplete answer
  | overinformative -- More information than asked
  deriving DecidableEq, Repr

/-- Answer form -/
inductive AnswerForm where
  | sentential      -- Full sentence: "John left"
  | constituent     -- Short answer: "John"
  | taciturn        -- Minimal: "Yes" / "No"
  deriving DecidableEq, Repr

-- ============================================================================
-- Basic Question-Answer Datum
-- ============================================================================

/-- A question-answer pair with metadata -/
structure QAPair where
  /-- The question -/
  question : String
  /-- The answer -/
  answer : String
  /-- Type of question -/
  questionType : QuestionType
  /-- Completeness of answer -/
  completeness : AnswerCompleteness
  /-- Form of answer -/
  form : AnswerForm
  /-- Is this Q-A pair felicitous? -/
  felicitous : Bool
  /-- Source/citation -/
  source : String := ""
  deriving Repr

-- ============================================================================
-- Term Types (G&S 1984)
-- ============================================================================

/-- Term types determine exhaustive interpretation.
    Source: G&S 1984, Chapter IV.
-/
inductive TermType where
  | singular        -- "the student who left"
  | definiteNP      -- "the students who left"
  | indefinite      -- "a student who left"
  | universalNP     -- "every student who left"
  deriving DecidableEq, Repr

/-- Whether a term type gets an exhaustive interpretation -/
def TermType.exhaustive : TermType → Bool
  | .singular => true
  | .definiteNP => true
  | .indefinite => false
  | .universalNP => true

end Phenomena.Questions
