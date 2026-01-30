/-
# Multiple Wh-Questions

Questions with multiple wh-phrases require n-place term answers.

## Examples

- "Which man loves which woman?" → "John, Mary; and Bill, Suzy"
- Expresses: John loves Mary, Bill loves Suzy, and no other man-woman pairs

## Key Insight

An n-constituent interrogative asks for an n-place relation.
The answer specifies which n-tuples satisfy the relation exhaustively.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Section 3.2.
- Dayal (2016). Questions. Chapter on pair-list readings.
-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.MultipleWh

-- ============================================================================
-- PART 1: Multiple Wh-Question Data
-- ============================================================================

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

-- ============================================================================
-- PART 2: Answer Form Equivalence
-- ============================================================================

/-- Constituent and sentential answers express the same proposition.
    G&S 1984: Both derived from the same abstract + term.
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

-- ============================================================================
-- PART 3: Pair-List vs Single-Pair Readings
-- ============================================================================

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

-- ============================================================================
-- PART 4: n-Place Term Categories
-- ============================================================================

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

end Phenomena.Questions.MultipleWh
