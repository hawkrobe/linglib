import Linglib.Phenomena.Questions.Basic

/-!
# Phenomena/Questions/MentionSome.lean

Empirical data on mention-some interpretations from G&S 1984, Chapter VI, Section 5.

## Overview

This file contains theory-neutral empirical data on:
1. Mention-some vs choice reading distinctions
2. Embedded mention-some paraphrases
3. The negative answer problem (why "not in drawer" fails)
4. Verb licensing (why "depends" blocks mention-some)
5. Mention-two / cumulative quantification (Belnap examples)

## Sources

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI, Sec. 5.
- Belnap (1982). Questions and Answers in Montague Grammar.
-/

namespace Phenomena.Questions.MentionSome


/-- Data point distinguishing mention-some from choice readings.

G&S 1984, Section 5.1-5.3: Both yield non-exhaustive answers, but differ
in their semantic source and paraphrase possibilities. -/
structure MentionSomeVsChoiceDatum where
  /-- The question -/
  question : String
  /-- A valid mention-some answer -/
  mentionSomeAnswer : String
  /-- The corresponding choice answer (if applicable) -/
  choiceAnswer : Option String
  /-- How to distinguish the readings -/
  distinction : String
  /-- Source -/
  source : String := "G&S 1984, Section 5"
  deriving Repr

/-- Classic mention-some: "Where can I buy X?"

G&S 1984, p. 331: The questioner's practical goal makes a single answer sufficient. -/
def whereCanIBuy : MentionSomeVsChoiceDatum :=
  { question := "Where can I buy an Italian newspaper?"
  , mentionSomeAnswer := "At the station kiosk"
  , choiceAnswer := none  -- No choice reading (no wide-scope element)
  , distinction := "Mention-some from practical goal; choice requires wide-scope ∃/∨"
  }

/-- "Where is a pen?" - mention-some vs potential choice.

If interpreted with wide-scope ∃ over pens, could be choice. -/
def whereIsPen : MentionSomeVsChoiceDatum :=
  { question := "Where is a pen?"
  , mentionSomeAnswer := "In the study"
  , choiceAnswer := some "The blue pen is in the study; the red pen is in the kitchen"
  , distinction := "Mention-some: any single location. Choice: depends on which pen"
  }

/-- "Who has something I can write with?" -/
def whoHasSomething : MentionSomeVsChoiceDatum :=
  { question := "Who has something I can write with?"
  , mentionSomeAnswer := "Mary does"
  , choiceAnswer := some "If you want a pen, ask Mary; if pencil, ask John"
  , distinction := "Wide-scope ∃ over writing implements creates choice reading"
  }

/-- G&S's newspaper example with different contexts. -/
def newspaperContexts : MentionSomeVsChoiceDatum :=
  { question := "Where can I buy an Italian newspaper?"
  , mentionSomeAnswer := "At the station"
  , choiceAnswer := none
  , distinction := "Context determines whether questioner wants all locations or just one"
  }

def mentionSomeVsChoiceExamples : List MentionSomeVsChoiceDatum :=
  [whereCanIBuy, whereIsPen, whoHasSomething, newspaperContexts]


/-- Data on embedded mention-some questions under attitude verbs.

G&S 1984, Section 5.3: Paraphrases help identify the reading. -/
structure EmbeddedMentionSomeDatum where
  /-- The sentence with embedded question -/
  sentence : String
  /-- Paraphrase under mention-some reading -/
  mentionSomeParaphrase : String
  /-- Paraphrase under choice reading (if available) -/
  choiceParaphrase : Option String
  /-- Paraphrase under mention-all reading -/
  mentionAllParaphrase : Option String
  /-- The embedding verb -/
  verb : String
  /-- Source -/
  source : String := "G&S 1984, Section 5.3"
  deriving Repr

/-- "John knows where he can buy an Italian newspaper" (mention-some).

G&S 1984, (9)-(10): John knows of at least one place that sells them. -/
def johnKnowsWherePaper : EmbeddedMentionSomeDatum :=
  { sentence := "John knows where he can buy an Italian newspaper"
  , mentionSomeParaphrase := "There is a place that sells Italian newspapers and John knows it sells them"
  , choiceParaphrase := none
  , mentionAllParaphrase := some "For every place that sells Italian newspapers, John knows it sells them"
  , verb := "knows"
  }

/-- "John knows who has a pen" - three-way ambiguity.

G&S 1984, Section 5.3: Can be mention-some, choice (which pen), or mention-all. -/
def johnKnowsWhoHasPen : EmbeddedMentionSomeDatum :=
  { sentence := "John knows who has a pen"
  , mentionSomeParaphrase := "John knows of someone who has a pen (that they have a pen)"
  , choiceParaphrase := some "For whichever pen is relevant, John knows who has it"
  , mentionAllParaphrase := some "John knows of everyone who has a pen that they have one"
  , verb := "knows"
  }

/-- "John wonders where he can buy an Italian newspaper" (mention-some).

G&S 1984, (11)-(12): John wants to know of some place (not all places). -/
def johnWondersWherePaper : EmbeddedMentionSomeDatum :=
  { sentence := "John wonders where he can buy an Italian newspaper"
  , mentionSomeParaphrase := "John wants to know of some place that it sells Italian newspapers"
  , choiceParaphrase := none
  , mentionAllParaphrase := some "John wants to know of every place whether it sells Italian newspapers"
  , verb := "wonders"
  }

/-- "John asked who has a pen" - embedded under "ask". -/
def johnAskedWhoHasPen : EmbeddedMentionSomeDatum :=
  { sentence := "John asked who has a pen"
  , mentionSomeParaphrase := "John asked his question wanting to find out about one pen-haver"
  , choiceParaphrase := none
  , mentionAllParaphrase := some "John asked wanting to find out about all pen-havers"
  , verb := "asked"
  }

/-- "Mary told John where he can buy an Italian newspaper". -/
def maryToldJohn : EmbeddedMentionSomeDatum :=
  { sentence := "Mary told John where he can buy an Italian newspaper"
  , mentionSomeParaphrase := "Mary told John about one place where he can buy an Italian newspaper"
  , choiceParaphrase := none
  , mentionAllParaphrase := some "Mary told John about every place where he can buy an Italian newspaper"
  , verb := "told"
  }

def embeddedMentionSomeExamples : List EmbeddedMentionSomeDatum :=
  [johnKnowsWherePaper, johnKnowsWhoHasPen, johnWondersWherePaper,
   johnAskedWhoHasPen, maryToldJohn]


/-- Data illustrating why partial answerhood doesn't capture mention-some.

G&S 1984, Section 5.2: Negative answers satisfy P-ANS but are NOT acceptable
mention-some answers. This is the key problem with the P-ANS analysis. -/
structure NegativeAnswerDatum where
  /-- The question -/
  question : String
  /-- A valid positive mention-some answer -/
  positiveAnswer : String
  /-- A negative answer that satisfies P-ANS but isn't mention-some -/
  negativeAnswer : String
  /-- Why negative fails as mention-some -/
  whyNegativeFails : String
  /-- A complete "nowhere" type answer -/
  nowhereAnswer : Option String
  /-- Source -/
  source : String := "G&S 1984, Section 5.2"
  deriving Repr

/-- The pen location example.

"Not in the drawer" satisfies P-ANS but doesn't help find the pen. -/
def penLocationNegative : NegativeAnswerDatum :=
  { question := "Where is a pen?"
  , positiveAnswer := "In the study"
  , negativeAnswer := "Not in the drawer"
  , whyNegativeFails := "Doesn't provide a location where you can get a pen"
  , nowhereAnswer := some "Nowhere / There isn't one"
  }

/-- Coffee shop example with negative. -/
def coffeeNegative : NegativeAnswerDatum :=
  { question := "Where can I buy coffee?"
  , positiveAnswer := "At the Starbucks on Main Street"
  , negativeAnswer := "Not at the library"
  , whyNegativeFails := "Eliminates a non-coffee-place, doesn't provide one"
  , nowhereAnswer := some "Nowhere nearby / You can't"
  }

/-- Newspaper example.

G&S 1984: Negative answers don't satisfy the questioner's goal. -/
def newspaperNegative : NegativeAnswerDatum :=
  { question := "Where can I buy an Italian newspaper?"
  , positiveAnswer := "At the station kiosk"
  , negativeAnswer := "Not at the corner shop"
  , whyNegativeFails := "Questioner needs a location to GO to, not one to avoid"
  , nowhereAnswer := some "Nowhere in this town"
  }

def negativeAnswerExamples : List NegativeAnswerDatum :=
  [penLocationNegative, coffeeNegative, newspaperNegative]


/-- Data on which verbs allow/block mention-some readings.

G&S 1984, Section 5.4: Verbs like "depends" and "matter" BLOCK mention-some
because they require complete information about the question. -/
structure VerbLicensingDatum where
  /-- Example sentence -/
  sentence : String
  /-- The matrix verb -/
  verb : String
  /-- Does mention-some reading exist? -/
  mentionSomePossible : Bool
  /-- Explanation of why verb allows/blocks -/
  explanation : String
  /-- Source -/
  source : String := "G&S 1984, Section 5.4"
  deriving Repr

/-- "It depends on who has a pen" - BLOCKS mention-some.

G&S 1984, Section 5.4: "depends" requires knowing the complete answer. -/
def dependsBlocks : VerbLicensingDatum :=
  { sentence := "It depends on who has a pen"
  , verb := "depends"
  , mentionSomePossible := false
  , explanation := "Functional dependency requires complete answer"
  }

/-- "It matters who has a pen" - BLOCKS mention-some. -/
def matterBlocks : VerbLicensingDatum :=
  { sentence := "It matters who has a pen"
  , verb := "matter"
  , mentionSomePossible := false
  , explanation := "Relevance requires knowing the full picture"
  }

/-- "Who gets the prize is determined by who wins" - BLOCKS mention-some. -/
def determineBlocks : VerbLicensingDatum :=
  { sentence := "Who gets the prize is determined by who wins"
  , verb := "determine"
  , mentionSomePossible := false
  , explanation := "Determination relation needs complete input"
  }

/-- "John knows who has a pen" - ALLOWS mention-some. -/
def knowAllows : VerbLicensingDatum :=
  { sentence := "John knows who has a pen"
  , verb := "know"
  , mentionSomePossible := true
  , explanation := "Knowledge can be partial; knowing one suffices"
  }

/-- "John wonders who has a pen" - ALLOWS mention-some. -/
def wonderAllows : VerbLicensingDatum :=
  { sentence := "John wonders who has a pen"
  , verb := "wonder"
  , mentionSomePossible := true
  , explanation := "Can wonder about one satisfier without needing all"
  }

/-- "John found out who has a pen" - ALLOWS mention-some. -/
def findOutAllows : VerbLicensingDatum :=
  { sentence := "John found out who has a pen"
  , verb := "find out"
  , mentionSomePossible := true
  , explanation := "Finding out about one suffices for the goal"
  }

def verbLicensingExamples : List VerbLicensingDatum :=
  [dependsBlocks, matterBlocks, determineBlocks,
   knowAllows, wonderAllows, findOutAllows]


/-- Data on mention-n readings with numeral quantification.

G&S 1984, Section 5.3 (citing Belnap): Questions like "Where do two unicorns live?"
have multiple readings involving cumulative quantification. -/
structure MentionNDatum where
  /-- The question -/
  question : String
  /-- The numeral involved -/
  numeral : Nat
  /-- Mention-some answer (one place with n entities) -/
  mentionSomeAnswer : String
  /-- Mention-n/cumulative answer (multiple places covering n entities) -/
  cumulativeAnswer : String
  /-- Choice answer (identify specific entities) -/
  choiceAnswer : String
  /-- Context where cumulative is natural -/
  cumulativeContext : String
  /-- Source -/
  source : String := "G&S 1984, Section 5.3; Belnap 1982"
  deriving Repr

/-- Belnap's unicorn example.

"Where do two unicorns live?" - classic example of cumulative quantification. -/
def whereTwoUnicorns : MentionNDatum :=
  { question := "Where do two unicorns live?"
  , numeral := 2
  , mentionSomeAnswer := "In the enchanted forest (where both unicorns live)"
  , cumulativeAnswer := "One in Paris, one in Rome"
  , choiceAnswer := "The white unicorn lives in Paris; the silver one in Rome"
  , cumulativeContext := "When you want to know locations of unicorns collectively"
  }

/-- "Where do three students work?" -/
def whereThreeStudents : MentionNDatum :=
  { question := "Where do three students work?"
  , numeral := 3
  , mentionSomeAnswer := "At the library (where three students work together)"
  , cumulativeAnswer := "Two at the library, one at the café"
  , choiceAnswer := "John works at the library, Mary at the café, Bill at home"
  , cumulativeContext := "Survey of student workplaces"
  }

/-- "Who do two professors recommend?" -/
def whoTwoProfessors : MentionNDatum :=
  { question := "Who do two professors recommend?"
  , numeral := 2
  , mentionSomeAnswer := "Alice (whom both professors recommend)"
  , cumulativeAnswer := "Professor Smith recommends Alice; Professor Jones recommends Bob"
  , choiceAnswer := "Professor Smith recommends Alice and Bob; Professor Jones recommends Carol"
  , cumulativeContext := "Collecting recommendations from multiple professors"
  }

def mentionNExamples : List MentionNDatum :=
  [whereTwoUnicorns, whereThreeStudents, whoTwoProfessors]


/-- Data on how human concerns/goals license mention-some.

G&S 1984, Section 5.4: The questioner's practical goal makes partial
information sufficient. -/
structure HumanConcernDatum where
  /-- The question -/
  question : String
  /-- The underlying human concern/goal -/
  humanConcern : String
  /-- Why partial answer suffices -/
  whyPartialSuffices : String
  /-- A valid mention-some answer -/
  exampleAnswer : String
  /-- Source -/
  source : String := "G&S 1984, Section 5.4"
  deriving Repr

/-- Buying coffee - classic practical goal. -/
def buyCoffeeGoal : HumanConcernDatum :=
  { question := "Where can I buy coffee?"
  , humanConcern := "Get coffee"
  , whyPartialSuffices := "Going to one coffee shop achieves the goal"
  , exampleAnswer := "At the café on the corner"
  }

/-- Borrowing a pen - immediate practical need. -/
def borrowPenGoal : HumanConcernDatum :=
  { question := "Who has a pen I can borrow?"
  , humanConcern := "Write something down"
  , whyPartialSuffices := "One pen suffices for writing"
  , exampleAnswer := "Mary has one"
  }

/-- Finding a doctor - practical health concern. -/
def findDoctorGoal : HumanConcernDatum :=
  { question := "Where can I find a doctor?"
  , humanConcern := "Get medical attention"
  , whyPartialSuffices := "One doctor can provide treatment"
  , exampleAnswer := "There's a clinic on Main Street"
  }

/-- Getting directions - travel goal. -/
def getDirectionsGoal : HumanConcernDatum :=
  { question := "How can I get to the station?"
  , humanConcern := "Reach the station"
  , whyPartialSuffices := "One route is enough to get there"
  , exampleAnswer := "Take bus 42"
  }

def humanConcernExamples : List HumanConcernDatum :=
  [buyCoffeeGoal, borrowPenGoal, findDoctorGoal, getDirectionsGoal]


/-- Total number of mention-some phenomena examples. -/
def totalExamples : Nat :=
  mentionSomeVsChoiceExamples.length +
  embeddedMentionSomeExamples.length +
  negativeAnswerExamples.length +
  verbLicensingExamples.length +
  mentionNExamples.length +
  humanConcernExamples.length

/-- Number of verb licensing examples that BLOCK mention-some. -/
def verbsThatBlock : Nat :=
  verbLicensingExamples.filter (fun d => !d.mentionSomePossible) |>.length

/-- Number of verb licensing examples that ALLOW mention-some. -/
def verbsThatAllow : Nat :=
  verbLicensingExamples.filter (fun d => d.mentionSomePossible) |>.length

end Phenomena.Questions.MentionSome
