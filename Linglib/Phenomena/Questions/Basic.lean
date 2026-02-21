import Linglib.Core.Word

/-!
# Questions: Basic Types and Shared Infrastructure

Theory-neutral types for question-answer phenomena.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Krifka (2011). Questions. In Semantics: An International Handbook.
- Dayal (2016). Questions. Oxford University Press.
-/

namespace Phenomena.Questions

/-- Semantic type of a wh-phrase, classifying what domain the wh-word
    ranges over. The taxonomy is empirically motivated by distributional
    patterns in the Santa Cruz Sluicing Corpus (Anand, Hardt & McCloskey
    2021), where these types show radically different frequencies. -/
inductive WhSemanticType where
  | entity          -- who, what, which N — ranges over individuals
  | degree          -- how much, how many, how ADJ — ranges over degrees
  | reason          -- why — ranges over reasons/causes
  | manner          -- how — ranges over manners
  | temporal        -- when — ranges over times
  | locative        -- where — ranges over locations
  | classificatory  -- what kind of, what sort of — ranges over kinds
  deriving DecidableEq, BEq, Repr, Inhabited

-- Question Types

/-- Classification of question types by answer form.

    Note: this classifies the *form* of the question and expected answer,
    not the semantic type of the wh-phrase. For semantic type (entity,
    degree, reason, etc.), see `WhSemanticType`. -/
inductive QuestionType where
  | polar           -- Yes/no questions: "Did John leave?"
  | whSingular      -- Singular wh: "Who left?"
  | whPlural        -- Plural wh: "Which students left?"
  | alternative     -- Alternative: "Did John or Mary leave?"
  | whReason        -- Reason: "Why did John leave?"
  | whManner        -- Manner: "How did John leave?"
  deriving DecidableEq, Repr

/-- The semantic type of the wh-phrase, when the question is a wh-question.
    Returns `none` for polar and alternative questions. For `whSingular`
    and `whPlural`, the semantic type depends on the specific wh-word used,
    so we default to `entity` — the caller should refine if needed. -/
def QuestionType.whSemanticType : QuestionType → Option WhSemanticType
  | .polar      => none
  | .alternative => none
  | .whSingular => some .entity   -- default; could be temporal, locative, etc.
  | .whPlural   => some .entity
  | .whReason   => some .reason
  | .whManner   => some .manner

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

-- Basic Question-Answer Datum

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

-- Term Types (G&S 1984)

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
