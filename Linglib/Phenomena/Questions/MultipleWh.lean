/-
# Multiple Wh-Questions
@cite{belnap-1982} @cite{groenendijk-stokhof-1984}

Questions with multiple wh-phrases require n-place term answers.
@cite{belnap-1982} §4 argues for simultaneous introduction of multiple
*which*-phrases (as opposed to one-at-a-time introduction) — the question
asks for a unique pair, not sequential individuals.

(Separately, @cite{belnap-1982} §5 argues that different wh-words —
*which*, *who*, *where*, *what* — should be treated as distinct syntactic
categories with different answer types, contra the assumption that all
wh-words are interchangeable.)

## Examples

- "Which man loves which woman?" → "John, Mary; and Bill, Suzy"
- Expresses: John loves Mary, Bill loves Suzy, and no other man-woman pairs

## Insight

An n-constituent interrogative asks for an n-place relation.
The answer specifies which n-tuples satisfy the relation exhaustively.

-/

import Linglib.Phenomena.Questions.Basic
import Linglib.Typology.Question

namespace Phenomena.Questions.MultipleWh

open Typology.Question


/-- A multiple wh-question with its answer patterns -/
structure MultipleWhDatum where
  /-- The question -/
  question : String
  /-- Number of wh-phrases -/
  numWh : Nat
  /-- Example constituent answer (short form) -/
  constituentAnswer : String
  /-- Example sentential answer (long form) -/
  sententialAnswer : String
  /-- The exhaustive interpretation -/
  exhaustiveReading : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 310: "Which man loves which woman?" -/
def whichManWoman : MultipleWhDatum :=
  { question := "Which man loves which woman?"
  , numWh := 2
  , constituentAnswer := "John, Suzy"
  , sententialAnswer := "John loves Suzy"
  , exhaustiveReading := "The only man-woman loving pair is ⟨John, Suzy⟩"
  , source := "G&S 1984, p. 310"
  }

/-- Conjunctive answer: multiple pairs -/
def whichManWoman_conj : MultipleWhDatum :=
  { question := "Which man loves which woman?"
  , numWh := 2
  , constituentAnswer := "John, Suzy; and Bill, Mary"
  , sententialAnswer := "John loves Suzy, and Bill loves Mary"
  , exhaustiveReading := "The only man-woman loving pairs are ⟨John, Suzy⟩ and ⟨Bill, Mary⟩"
  , source := "G&S 1984, p. 312"
  }

/-- Disjunctive answer: uncertain which pair -/
def whichManWoman_disj : MultipleWhDatum :=
  { question := "Which man loves which woman?"
  , numWh := 2
  , constituentAnswer := "John, Suzy; or Bill, Mary"
  , sententialAnswer := "John loves Suzy, or Bill loves Mary"
  , exhaustiveReading := "Either ⟨John, Suzy⟩ is the only pair, or ⟨Bill, Mary⟩ is the only pair"
  , source := "G&S 1984, p. 312"
  }

/-- Complex answer with quantifiers -/
def whichManWoman_quant : MultipleWhDatum :=
  { question := "Which man loves which woman?"
  , numWh := 2
  , constituentAnswer := "Every man, a girl"
  , sententialAnswer := "Every man loves a girl"
  , exhaustiveReading := "For each man x, there's exactly one girl y such that x loves y"
  , source := "G&S 1984, p. 313"
  }

def multipleWhExamples : List MultipleWhDatum :=
  [whichManWoman, whichManWoman_conj, whichManWoman_disj, whichManWoman_quant]


/-- Constituent and sentential answers express the same proposition.
    @cite{groenendijk-stokhof-1984}: Both derived from the same abstract + term.
-/
structure AnswerEquivalence where
  /-- The question -/
  question : String
  /-- Short (constituent) answer -/
  shortAnswer : String
  /-- Long (sentential) answer -/
  longAnswer : String
  /-- They express the same proposition -/
  equivalent : Bool := true
  deriving Repr

def johnSuzy_equiv : AnswerEquivalence :=
  { question := "Which man loves which woman?"
  , shortAnswer := "John, Suzy"
  , longAnswer := "John loves Suzy"
  }

def answerEquivalenceExamples : List AnswerEquivalence :=
  [johnSuzy_equiv]


/-- Some multiple-wh questions have both pair-list and single-pair readings.
    G&S focus on exhaustive (pair-list) readings.
-/
inductive MultiWhReading where
  | pairList    -- Lists all satisfying pairs exhaustively
  | singlePair  -- Asks for one satisfying pair (mention-some)
  deriving DecidableEq, Repr

/-- G&S: The default/semantic reading is pair-list (exhaustive).
    Single-pair readings are pragmatic/mention-some.
-/
def defaultReading : MultiWhReading := .pairList


/-- G&S define a hierarchy of term categories:
    T^0 = S/S (sentence adverbs: yes, no)
    T^1 = S/AB^1 (ordinary terms: John, everyone)
    T^2 = S/AB^2 (2-place terms: John, Mary)
    T^n = S/AB^n (n-place terms)
-/
structure TermCategory where
  /-- The arity -/
  arity : Nat
  /-- Example expressions -/
  examples : List String
  /-- Type description -/
  typeDesc : String
  deriving Repr

def t0_category : TermCategory :=
  { arity := 0
  , examples := ["yes", "no", "if Mary walks"]
  , typeDesc := "S/S (sentence adverbs)"
  }

def t1_category : TermCategory :=
  { arity := 1
  , examples := ["John", "everyone", "the student who left"]
  , typeDesc := "S/(S/e) (ordinary terms)"
  }

def t2_category : TermCategory :=
  { arity := 2
  , examples := ["John, Mary", "every man, a girl"]
  , typeDesc := "S/((S/e)/e) (2-place terms)"
  }

def termCategories : List TermCategory :=
  [t0_category, t1_category, t2_category]

-- ============================================================================
-- § Cross-linguistic MWF data (substrate in `Typology/Question.lean`)
-- ============================================================================

/-! Languages vary in whether multiple wh-specifiers at a phase edge are
tolerable at PF (@cite{rudin-1988}, @cite{citko-gracanin-yuksek-2025}).
The substrate primitives (`MWFParameter`, `PhaseEdge`, `EdgeAsterisk`,
`MWFViolation`, `EllipsisRepairsMWF`) are in `Linglib/Typology/Question.lean`
per the project layering convention; this file holds only the per-language
data + theorems consuming it.

The intra-English variety A/B split (paper-specific to
@cite{citko-gracanin-yuksek-2025}) lives in
`Phenomena/Ellipsis/Studies/CitkoGracaninYuksek2025.lean`. -/

/-- Cross-linguistic MWF datum. Records the parameter setting and an
    example question. `AllowsMultipleSluicing` is **derived** from the
    parameter via `EllipsisRepairsMWF`. -/
structure MWFLanguageDatum where
  language : String
  mwfParam : MWFParameter
  /-- Example multiple wh-question. -/
  exampleQuestion : String
  /-- Is the bare multiple-wh question grammatical? -/
  grammatical : Bool
  notes : String := ""
  deriving Repr, DecidableEq

/-- Multiple sluicing is licensed iff vP-edge ellipsis repairs the MWF
    violation for `n = 2` wh-specifiers. **Derived, not stipulated.** -/
def MWFLanguageDatum.AllowsMultipleSluicing (d : MWFLanguageDatum) : Prop :=
  EllipsisRepairsMWF d.mwfParam 2 (vpEdgeDeleted := true)

instance (d : MWFLanguageDatum) : Decidable d.AllowsMultipleSluicing := by
  unfold MWFLanguageDatum.AllowsMultipleSluicing; infer_instance

/-- Bulgarian: MWF language (@cite{rudin-1988} canonical case). -/
def bulgarian : MWFLanguageDatum :=
  { language := "Bulgarian"
  , mwfParam := .fronts
  , exampleQuestion := "Koj kakvo e kupil?"
  , grammatical := true
  , notes := "All wh-phrases front; @cite{rudin-1988} canonical MWF language" }

/-- German: non-MWF; vP-only asterisk; multiple sluicing repairs.
    @cite{citko-gracanin-yuksek-2025} ex 31a. -/
def german : MWFLanguageDatum :=
  { language := "German"
  , mwfParam := .nonFrontsVPOnly
  , exampleQuestion := "*Wer was hat gesehen?"
  , grammatical := false
  , notes := "Non-MWF; bans multiple wh-fronting in questions; "
           ++ "allows multiple sluicing (@cite{citko-gracanin-yuksek-2025} ex 31a)" }

/-- Greek: non-MWF; vP-only asterisk; multiple sluicing repairs.
    @cite{citko-gracanin-yuksek-2025} ex 31b. -/
def greek : MWFLanguageDatum :=
  { language := "Greek"
  , mwfParam := .nonFrontsVPOnly
  , exampleQuestion := "*Pços ti efere?"
  , grammatical := false
  , notes := "Non-MWF; bans multiple wh-fronting in questions; "
           ++ "allows multiple sluicing (@cite{citko-gracanin-yuksek-2025} ex 31b)" }

/-- Cross-linguistic MWF table (textbook-consensus subset). -/
def mwfLanguageTable : List MWFLanguageDatum := [bulgarian, german, greek]

/-- Bulgarian: MWF language → no violations on bare multiple wh. -/
theorem bulgarian_no_violation : ¬ MWFViolation bulgarian.mwfParam 2 := by decide

/-- German question with two wh-phrases is starred. -/
theorem german_violates_in_questions : MWFViolation german.mwfParam 2 := by decide

/-- Sluicing repairs in German and Greek (vP-only asterisk eliminated). -/
theorem german_greek_sluicing_repairs :
    german.AllowsMultipleSluicing ∧ greek.AllowsMultipleSluicing := by decide

end Phenomena.Questions.MultipleWh
