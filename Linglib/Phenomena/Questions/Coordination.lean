/-
# Interrogative Coordination

Conjunction and disjunction of interrogatives from G&S 1984, Chapter VI.

## Conjunctive Interrogatives

"Who came and what did they bring?"

This asks for BOTH:
1. Who came (list of people)
2. What each person brought (function from people to things)

The answer must resolve both questions simultaneously.

## Disjunctive Interrogatives

"Did John come or did Mary come?"

Two readings:
1. **Alternative**: Which one came? (exclusive)
2. **Polar over disjunction**: Did at least one come? (yes/no)

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI.
- Szabolcsi (1997). Ways of Scope Taking.
-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.Coordination

-- ============================================================================
-- PART 1: Conjunctive Interrogatives
-- ============================================================================

/-- A conjunctive interrogative datum. -/
structure ConjunctiveInterrogativeDatum where
  /-- The conjoined question -/
  question : String
  /-- First conjunct -/
  conjunct1 : String
  /-- Second conjunct -/
  conjunct2 : String
  /-- Type of conjunction (and, and also, etc.) -/
  conjunctionType : String
  /-- Example complete answer -/
  completeAnswer : String
  /-- Example partial answer (answers only one conjunct) -/
  partialAnswer : Option String
  /-- Is partial answer acceptable? -/
  partialOK : Bool
  /-- Notes -/
  notes : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S: "Who came and what did they bring?" -/
def whoCameWhatBring : ConjunctiveInterrogativeDatum :=
  { question := "Who came and what did they bring?"
  , conjunct1 := "Who came?"
  , conjunct2 := "What did they bring?"
  , conjunctionType := "and"
  , completeAnswer := "John came and brought wine; Mary came and brought cheese"
  , partialAnswer := some "John and Mary came"
  , partialOK := false
  , notes := "Q2 is functionally dependent on Q1 (anaphora 'they'); requires pair-list"
  , source := "G&S 1984, p. 417"
  }

/-- "Who will be invited and who will be excluded?" -/
def whoInvitedExcluded : ConjunctiveInterrogativeDatum :=
  { question := "Who will be invited and who will be excluded?"
  , conjunct1 := "Who will be invited?"
  , conjunct2 := "Who will be excluded?"
  , conjunctionType := "and"
  , completeAnswer := "John, Mary, and Sue will be invited; Bill and Tom will be excluded"
  , partialAnswer := some "John, Mary, and Sue will be invited"
  , partialOK := false
  , notes := "Independent conjuncts; complete answer lists both sets"
  , source := "constructed"
  }

/-- "Where did John go and when did he return?" -/
def whereWhenJohn : ConjunctiveInterrogativeDatum :=
  { question := "Where did John go and when did he return?"
  , conjunct1 := "Where did John go?"
  , conjunct2 := "When did he return?"
  , conjunctionType := "and"
  , completeAnswer := "John went to Paris and returned on Monday"
  , partialAnswer := some "John went to Paris"
  , partialOK := false
  , notes := "Two separate wh-questions conjoined"
  , source := "constructed"
  }

/-- "Which students passed and which students failed?" -/
def whichPassedFailed : ConjunctiveInterrogativeDatum :=
  { question := "Which students passed and which students failed?"
  , conjunct1 := "Which students passed?"
  , conjunct2 := "Which students failed?"
  , conjunctionType := "and"
  , completeAnswer := "Alice and Bob passed; Carol and Dave failed"
  , partialAnswer := some "Alice and Bob passed"
  , partialOK := false
  , notes := "Exhaustive for both; answer fully specifies the partition"
  , source := "constructed"
  }

def conjunctiveInterrogativeExamples : List ConjunctiveInterrogativeDatum :=
  [ whoCameWhatBring
  , whoInvitedExcluded
  , whereWhenJohn
  , whichPassedFailed
  ]

-- ============================================================================
-- PART 2: Disjunctive Interrogatives
-- ============================================================================

/-- A disjunctive interrogative datum. -/
structure DisjunctiveInterrogativeDatum where
  /-- The disjoined question -/
  question : String
  /-- First disjunct -/
  disjunct1 : String
  /-- Second disjunct -/
  disjunct2 : String
  /-- Alternative reading answer -/
  alternativeAnswer : String
  /-- Polar-disjunction reading answer -/
  polarAnswer : String
  /-- Which reading is preferred in context -/
  preferredReading : String
  /-- Prosodic cues -/
  prosody : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S: "Did John come or did Mary come?" (alternative reading) -/
def didJohnOrMary_alt : DisjunctiveInterrogativeDatum :=
  { question := "Did John come or did Mary come?"
  , disjunct1 := "Did John come?"
  , disjunct2 := "Did Mary come?"
  , alternativeAnswer := "John came" -- or "Mary came" or "Neither"
  , polarAnswer := "Yes (at least one came)" -- or "No (neither came)"
  , preferredReading := "alternative"
  , prosody := "Rising on 'John', rising on 'Mary', falling at end"
  , source := "G&S 1984, p. 419"
  }

/-- Polar over disjunction reading -/
def didJohnOrMary_polar : DisjunctiveInterrogativeDatum :=
  { question := "Did John or Mary come?"
  , disjunct1 := "John came"
  , disjunct2 := "Mary came"
  , alternativeAnswer := "John" -- if alternative reading
  , polarAnswer := "Yes" -- or "No"
  , preferredReading := "polar"
  , prosody := "Rising-falling on 'Mary'"
  , source := "G&S 1984, p. 420"
  }

/-- "Is the door open or closed?" (forced alternative) -/
def doorOpenClosed : DisjunctiveInterrogativeDatum :=
  { question := "Is the door open or closed?"
  , disjunct1 := "Is it open?"
  , disjunct2 := "Is it closed?"
  , alternativeAnswer := "Open" -- or "Closed"
  , polarAnswer := "Yes" -- infelicitous; alternatives are exhaustive
  , preferredReading := "alternative"
  , prosody := "Rising on 'open', falling on 'closed'"
  , source := "constructed"
  }

/-- "Will you marry me or not?" (insistent alternative) -/
def marryMeOrNot : DisjunctiveInterrogativeDatum :=
  { question := "Will you marry me or not?"
  , disjunct1 := "Will you marry me?"
  , disjunct2 := "Will you not marry me?"
  , alternativeAnswer := "Yes, I will" -- or "No, I won't"
  , polarAnswer := "Yes" -- odd; the 'or not' makes it alternative
  , preferredReading := "alternative (insistent)"
  , prosody := "Neutral or emphatic"
  , source := "Van Rooy & Šafářová 2003"
  }

def disjunctiveInterrogativeExamples : List DisjunctiveInterrogativeDatum :=
  [ didJohnOrMary_alt
  , didJohnOrMary_polar
  , doorOpenClosed
  , marryMeOrNot
  ]

-- ============================================================================
-- PART 3: Alternative Questions
-- ============================================================================

/-- Alternative question data: exclusive choice among options. -/
structure AlternativeQuestionDatum where
  /-- The question -/
  question : String
  /-- The alternatives -/
  alternatives : List String
  /-- Are alternatives exhaustive? -/
  exhaustive : Bool
  /-- Can "yes/no" answer? -/
  yesNoOK : Bool
  /-- Expected answer type -/
  answerType : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- "Do you want tea or coffee?" -/
def teaOrCoffee : AlternativeQuestionDatum :=
  { question := "Do you want tea or coffee?"
  , alternatives := ["tea", "coffee"]
  , exhaustive := false  -- could want neither or both
  , yesNoOK := false     -- "Yes" is pragmatically odd
  , answerType := "One of the alternatives (or 'neither')"
  , source := "constructed"
  }

/-- "Is the number odd or even?" -/
def oddOrEven : AlternativeQuestionDatum :=
  { question := "Is the number odd or even?"
  , alternatives := ["odd", "even"]
  , exhaustive := true  -- mathematically exhaustive
  , yesNoOK := false    -- must choose one
  , answerType := "One alternative (forced choice)"
  , source := "constructed"
  }

/-- "Did John, Mary, or Bill do it?" -/
def johnMaryBill : AlternativeQuestionDatum :=
  { question := "Did John, Mary, or Bill do it?"
  , alternatives := ["John", "Mary", "Bill"]
  , exhaustive := false  -- someone else could have
  , yesNoOK := false
  , answerType := "One person or 'none of them'"
  , source := "constructed"
  }

def alternativeQuestionExamples : List AlternativeQuestionDatum :=
  [teaOrCoffee, oddOrEven, johnMaryBill]

-- ============================================================================
-- PART 4: Embedded Coordinated Questions
-- ============================================================================

/-- Data on coordination under attitude verbs. -/
structure EmbeddedCoordinationDatum where
  /-- The sentence -/
  sentence : String
  /-- The embedding verb -/
  verb : String
  /-- The coordinated question -/
  coordinatedQ : String
  /-- Coordination type -/
  coordType : String  -- "and" or "or"
  /-- Interpretation -/
  interpretation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- "John knows who came and what they brought" -/
def knowWhoWhatConj : EmbeddedCoordinationDatum :=
  { sentence := "John knows who came and what they brought"
  , verb := "know"
  , coordinatedQ := "who came and what they brought"
  , coordType := "and"
  , interpretation := "John knows the complete answer to both questions"
  , source := "G&S 1984, p. 418"
  }

/-- "Mary wonders whether Bill left or whether Sue arrived" -/
def wonderWhetherDisj : EmbeddedCoordinationDatum :=
  { sentence := "Mary wonders whether Bill left or whether Sue arrived"
  , verb := "wonder"
  , coordinatedQ := "whether Bill left or whether Sue arrived"
  , coordType := "or"
  , interpretation := "Mary is curious about which of the two holds"
  , source := "constructed"
  }

/-- "I don't know who won or who lost" -/
def dontKnowDisj : EmbeddedCoordinationDatum :=
  { sentence := "I don't know who won or who lost"
  , verb := "don't know"
  , coordinatedQ := "who won or who lost"
  , coordType := "or"
  , interpretation := "I don't know either answer"
  , source := "constructed"
  }

def embeddedCoordinationExamples : List EmbeddedCoordinationDatum :=
  [knowWhoWhatConj, wonderWhetherDisj, dontKnowDisj]

-- ============================================================================
-- PART 5: Sluicing with Coordinated Antecedents
-- ============================================================================

/-- Sluicing examples with coordinated antecedents. -/
structure SluicingCoordinationDatum where
  /-- The full discourse -/
  discourse : String
  /-- The antecedent clause -/
  antecedent : String
  /-- The sluiced question -/
  sluice : String
  /-- The reconstructed question -/
  reconstruction : String
  /-- Is the sluice acceptable? -/
  acceptable : Bool
  /-- Source -/
  source : String := ""
  deriving Repr

/-- "John talked to someone, and I know who" -/
def talkedSomeone : SluicingCoordinationDatum :=
  { discourse := "John talked to someone, and I know who."
  , antecedent := "John talked to someone"
  , sluice := "who"
  , reconstruction := "who John talked to"
  , acceptable := true
  , source := "constructed"
  }

/-- "John invited someone and Mary invited someone, and I know who" -/
def bothInvitedSomeone : SluicingCoordinationDatum :=
  { discourse := "John invited someone and Mary invited someone, and I know who."
  , antecedent := "John invited someone and Mary invited someone"
  , sluice := "who"
  , reconstruction := "who John invited and who Mary invited (or just one)"
  , acceptable := true
  , source := "constructed"
  }

def sluicingCoordinationExamples : List SluicingCoordinationDatum :=
  [talkedSomeone, bothInvitedSomeone]

-- ============================================================================
-- PART 6: Multiple Coordination
-- ============================================================================

/-- Data on questions with more than two conjuncts/disjuncts. -/
structure MultipleCoordinationDatum where
  /-- The question -/
  question : String
  /-- Number of coordinated elements -/
  numElements : Nat
  /-- The elements -/
  elements : List String
  /-- Coordination type -/
  coordType : String
  /-- Complete answer form -/
  answerForm : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- "Who came, what did they bring, and when did they leave?" -/
def threeConjuncts : MultipleCoordinationDatum :=
  { question := "Who came, what did they bring, and when did they leave?"
  , numElements := 3
  , elements := ["who came", "what they brought", "when they left"]
  , coordType := "and"
  , answerForm := "John came at 3pm with wine and left at 6pm; Mary came at 4pm with cheese and left at 7pm"
  , source := "constructed"
  }

/-- "Did John, Mary, Bill, or Sue win?" -/
def fourDisjuncts : MultipleCoordinationDatum :=
  { question := "Did John, Mary, Bill, or Sue win?"
  , numElements := 4
  , elements := ["John won", "Mary won", "Bill won", "Sue won"]
  , coordType := "or"
  , answerForm := "Mary won" -- one of the four
  , source := "constructed"
  }

def multipleCoordinationExamples : List MultipleCoordinationDatum :=
  [threeConjuncts, fourDisjuncts]

-- ============================================================================
-- PART 7: Conjunction vs Alternative
-- ============================================================================

/-- Minimal pairs: conjunction vs alternative interpretation. -/
structure ConjAltMinimalPair where
  /-- The ambiguous question -/
  question : String
  /-- Conjunctive interpretation -/
  conjInterpretation : String
  /-- Alternative interpretation -/
  altInterpretation : String
  /-- Prosodic disambiguation -/
  prosody : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- "Did John or Mary call?" -/
def johnOrMaryMinimal : ConjAltMinimalPair :=
  { question := "Did John or Mary call?"
  , conjInterpretation := "Did John-or-Mary (as a group) call?"
  , altInterpretation := "Which one called: John or Mary?"
  , prosody := "Rising-falling = polar; Rising-rising-falling = alternative"
  , source := "G&S 1984"
  }

def conjAltMinimalPairs : List ConjAltMinimalPair :=
  [johnOrMaryMinimal]

-- ============================================================================
-- Summary: Key Principles
-- ============================================================================

/-- G&S key principles for interrogative coordination -/
def coordinationPrinciples : List String :=
  [ "Conjoined questions require complete answer to all conjuncts"
  , "Disjoined questions (alternative reading) require choosing one"
  , "Disjoined questions (polar reading) ask yes/no about disjunction"
  , "Prosody disambiguates alternative vs polar readings"
  , "Embedded coordination under 'know' = conjunction of knowledge"
  , "'Or not' makes a question insistent (alternative reading)"
  , "Functionally dependent conjuncts require pair-list answers"
  ]

end Phenomena.Questions.Coordination
