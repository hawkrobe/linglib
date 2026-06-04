import Linglib.Core.UD.Word
import Linglib.Features.OntologicalCategory

/-!
# Questions: Basic Types and Shared Infrastructure
[dayal-2016] [groenendijk-stokhof-1984] [anand-hardt-mccloskey-2021]

Theory-neutral types for question-answer phenomena. The semantic type of a wh-phrase
(*who*/*what*/*where*/…) is the shared `Features.OntologicalCategory` axis — its
wh-side distribution is empirically motivated by the Santa Cruz Sluicing Corpus
([anand-hardt-mccloskey-2021]), where these categories show radically different
frequencies.

-/

namespace Phenomena.Questions

-- Question Types

/-- Classification of question types by answer form.

    Note: this classifies the *form* of the question and expected answer,
    not the semantic type of the wh-phrase. For semantic type (person/thing/
    amount/reason/…), see `Features.OntologicalCategory`. -/
inductive QuestionType where
  | polar           -- Yes/no questions: "Did John leave?"
  | whSingular      -- Singular wh: "Who left?"
  | whPlural        -- Plural wh: "Which students left?"
  | alternative     -- Alternative: "Did John or Mary leave?"
  | whReason        -- Reason: "Why did John leave?"
  | whManner        -- Manner: "How did John leave?"
  deriving DecidableEq, Repr

/-- The ontological category of the wh-phrase, when the question is a wh-question.
    Returns `none` for polar and alternative questions. For `whSingular`/`whPlural`
    the person/thing split depends on the specific wh-word (*who* vs *what*/*which*),
    so we default to `person` — the caller should refine per wh-word. -/
def QuestionType.whSemanticType : QuestionType → Option Features.OntologicalCategory
  | .polar       => none
  | .alternative => none
  | .whSingular  => some .person   -- default; *who* vs *what* refined per wh-word
  | .whPlural    => some .person
  | .whReason    => some .reason
  | .whManner    => some .manner

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

-- Term Types ([groenendijk-stokhof-1984])

/-- Term types determine exhaustive interpretation.
    Source: [groenendijk-stokhof-1984], Chapter IV.
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
