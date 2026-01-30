/-
# Polar Question Answers

Sentential (yes/no) interrogatives and their answer patterns.

## Key Phenomena

1. Yes/No as T⁰ terms (sentence adverbs, category S/S)
2. Conditional answers → biconditional interpretation
3. Disjunctive answers → exclusive interpretation
4. Negative interrogatives mark doxastic attitude, not semantic content

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Section 3.3.
- Krifka (2011). Questions. In Semantics: An International Handbook.
-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.PolarAnswers

-- ============================================================================
-- PART 1: Yes/No as Zero-Place Terms
-- ============================================================================

/-- G&S 1984: Yes and No are T⁰ (sentence adverbs, category S/S).
    - yes ~ λp.p(a)   (affirms the proposition)
    - no  ~ λp.¬p(a)  (negates the proposition)

    This makes sentential interrogatives derivable by the same IA-rule
    as constituent interrogatives, with AB⁰ = S and T⁰ = S/S.
-/
structure YesNoDatum where
  /-- The polar question -/
  question : String
  /-- The answer (yes/no form) -/
  answer : String
  /-- Is this positive or negative? -/
  positive : Bool
  /-- The proposition expressed by the answer -/
  meaning : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 321: "Does John walk?" -/
def doesJohnWalk_yes : YesNoDatum :=
  { question := "Does John walk?"
  , answer := "Yes"
  , positive := true
  , meaning := "John walks"
  , source := "G&S 1984, p. 321"
  }

def doesJohnWalk_no : YesNoDatum :=
  { question := "Does John walk?"
  , answer := "No"
  , positive := false
  , meaning := "John doesn't walk"
  , source := "G&S 1984, p. 322"
  }

def yesNoExamples : List YesNoDatum :=
  [doesJohnWalk_yes, doesJohnWalk_no]

-- ============================================================================
-- PART 2: Conditional Answers → Biconditional
-- ============================================================================

/-- G&S 1984, p. 324-326: A conditional answer to a polar question
    receives a BICONDITIONAL interpretation via exhaustification.

    "Does John walk?" → "If Mary walks"
    means: John walks IFF Mary walks (not just: John walks IF Mary walks)
-/
structure ConditionalAnswerDatum where
  /-- The polar question -/
  question : String
  /-- The conditional answer -/
  conditionalAnswer : String
  /-- Surface form (what was said) -/
  surfaceMeaning : String
  /-- Exhaustified meaning (what was understood) -/
  exhaustifiedMeaning : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 324: Conditional becomes biconditional in answer context -/
def ifMaryWalks : ConditionalAnswerDatum :=
  { question := "Does John walk?"
  , conditionalAnswer := "If Mary walks"
  , surfaceMeaning := "John walks if Mary walks"
  , exhaustifiedMeaning := "John walks if and only if Mary walks"
  , source := "G&S 1984, p. 324-325"
  }

/-- When the question itself is about a conditional, no strengthening occurs -/
def conditionalAsQuestion : ConditionalAnswerDatum :=
  { question := "Is it true that John walks if Mary walks?"
  , conditionalAnswer := "Yes, John walks if Mary walks"
  , surfaceMeaning := "John walks if Mary walks"
  , exhaustifiedMeaning := "John walks if Mary walks"  -- no biconditional!
  , source := "G&S 1984, p. 327"
  }

def conditionalAnswerExamples : List ConditionalAnswerDatum :=
  [ifMaryWalks, conditionalAsQuestion]

/-- The key insight: what determines conditional vs biconditional reading
    is whether the question asks about the conditional itself, or about
    its consequent.
-/
def conditionalBiconditionalPrinciple : String :=
  "Conditionals receive standard logical interpretation when answering " ++
  "a question about the conditional itself. They become biconditional " ++
  "when answering a question about their consequent."

-- ============================================================================
-- PART 3: Disjunction → Exclusive in Answers
-- ============================================================================

/-- G&S 1984, p. 327: Similar to conditionals, disjunctions in answers
    receive exclusive interpretation via exhaustification.
-/
structure DisjunctionAnswerDatum where
  /-- The polar question -/
  question : String
  /-- The disjunctive answer -/
  disjunctiveAnswer : String
  /-- Inclusive or exclusive reading? -/
  exclusive : Bool
  /-- Explanation -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Disjunction becomes exclusive when answering about disjunct -/
def cookiesOrChocolates_exclusive : DisjunctionAnswerDatum :=
  { question := "Are there cookies in the box?"
  , disjunctiveAnswer := "Yes, or chocolates"
  , exclusive := true
  , explanation := "Exclusive: either cookies or chocolates, not both"
  , source := "G&S 1984, p. 327"
  }

/-- Disjunction stays inclusive when answering about disjunction itself -/
def cookiesOrChocolates_inclusive : DisjunctionAnswerDatum :=
  { question := "Are there cookies or chocolates in the box?"
  , disjunctiveAnswer := "Yes, there are cookies or chocolates"
  , exclusive := false
  , explanation := "Inclusive: could be cookies, chocolates, or both"
  , source := "G&S 1984, p. 327"
  }

def disjunctionAnswerExamples : List DisjunctionAnswerDatum :=
  [cookiesOrChocolates_exclusive, cookiesOrChocolates_inclusive]

-- ============================================================================
-- PART 4: Negative Interrogatives (Doxastic Marking)
-- ============================================================================

/-- G&S 1984, p. 331-334: Negation in interrogatives does NOT contribute
    to semantic content. Instead, it marks a doxastic attitude:
    the questioner expects a negative answer.

    "Doesn't John walk?" asks the SAME question as "Does John walk?"
    but marks that the questioner expects "No" as the answer.
-/
structure NegativeInterrogativeDatum where
  /-- The positive form of the question -/
  positiveForm : String
  /-- The negative form of the question -/
  negativeForm : String
  /-- Do they express the same question semantically? -/
  sameQuestion : Bool
  /-- What does "No" mean as an answer to the negative form? -/
  noMeaning : String
  /-- What attitude does the negative form mark? -/
  doxasticAttitude : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 331: "Doesn't John walk?" vs "Does John walk?" -/
def doesntJohnWalk : NegativeInterrogativeDatum :=
  { positiveForm := "Does John walk?"
  , negativeForm := "Doesn't John walk?"
  , sameQuestion := true
  , noMeaning := "John doesn't walk"  -- NOT "John walks"!
  , doxasticAttitude := "Questioner expects negative answer"
  , source := "G&S 1984, p. 331"
  }

def negativeInterrogativeExamples : List NegativeInterrogativeDatum :=
  [doesntJohnWalk]

-- ============================================================================
-- PART 5: Positive vs Negative Answer Marking
-- ============================================================================

/-- When answering against the questioner's expected polarity,
    the answer must be MARKED (emphatic stress, do-support).
-/
structure MarkedAnswerDatum where
  /-- The question -/
  question : String
  /-- Expected answer polarity based on question form -/
  expectedPolarity : Bool  -- true = positive expected
  /-- Unmarked answer (goes with expectation) -/
  unmarkedAnswer : String
  /-- Marked answer (goes against expectation) -/
  markedAnswer : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Negative interrogative expects negative; positive answer needs marking -/
def negativeQuestion_positiveAnswer : MarkedAnswerDatum :=
  { question := "Doesn't John walk?"
  , expectedPolarity := false  -- negative expected
  , unmarkedAnswer := "No."
  , markedAnswer := "But yès, he dóes!"
  , source := "G&S 1984, p. 332"
  }

/-- Positive interrogative with positive marking expects positive -/
def tagQuestion_negativeAnswer : MarkedAnswerDatum :=
  { question := "John does walk, doesn't he?"
  , expectedPolarity := true  -- positive expected
  , unmarkedAnswer := "Yes."
  , markedAnswer := "But nö, he doesn't."
  , source := "G&S 1984, p. 332"
  }

def markedAnswerExamples : List MarkedAnswerDatum :=
  [negativeQuestion_positiveAnswer, tagQuestion_negativeAnswer]

-- ============================================================================
-- PART 6: "Not happy" vs "Unhappy" Distinction
-- ============================================================================

/-- G&S p. 333: Clear evidence that negation in interrogatives is not semantic:
    "Are you not happy?" vs "Are you unhappy?" have different answer patterns.
-/
structure NegationVsAntonymDatum where
  /-- Interrogative with negation -/
  negatedForm : String
  /-- Interrogative with antonym -/
  antonymForm : String
  /-- What "No" means for negated form -/
  noMeaning_negated : String
  /-- What "No" means for antonym form -/
  noMeaning_antonym : String
  /-- Are these the same question? -/
  sameQuestion : Bool
  /-- Source -/
  source : String := ""
  deriving Repr

def notHappy_vs_unhappy : NegationVsAntonymDatum :=
  { negatedForm := "Are you not happy?"
  , antonymForm := "Are you unhappy?"
  , noMeaning_negated := "I am not happy"  -- confirms lack of happiness
  , noMeaning_antonym := "I am not unhappy"  -- denies unhappiness (≈ happy)
  , sameQuestion := false
  , source := "G&S 1984, p. 333"
  }

def negationVsAntonymExamples : List NegationVsAntonymDatum :=
  [notHappy_vs_unhappy]

-- ============================================================================
-- PART 7: Theoretical Explanation
-- ============================================================================

/-- G&S's explanation for why negation can be used non-semantically:
    In the semantics of interrogatives, "Does John walk?" and
    "Does John not walk?" express the SAME question (same partition).
    This opens up negation for non-semantic (doxastic) use.
-/
def whyNegationIsDoxastic : String :=
  "Semantically, there is no difference between the question expressed by " ++
  "an interrogative formed from 'John walks' and one formed from " ++
  "'John doesn't walk'. Though these sentences have different meanings, " ++
  "the interrogatives formed from them express the same question. " ++
  "In the semantics of interrogatives, negation has no role of its own. " ++
  "This opens the possibility to use negation to mark doxastic attitudes."

end Phenomena.Questions.PolarAnswers
