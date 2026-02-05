/-
# Conditional Phenomena - Empirical Data

Theory-neutral empirical observations about conditional sentences.

This file documents well-known phenomena in the interpretation and use
of conditional sentences, without committing to any particular semantic
or pragmatic theory.

## Key Phenomena

1. **Conditional Perfection**: "If A then C" often implies "If ¬A then ¬C"
2. **Missing-Link Infelicity**: "If A then C" is odd when A and C are unrelated
3. **Indicative/Subjunctive Split**: Different morphology, different interpretation
4. **Conditional Questions**: "If A, will C?" vs "Will C if A?"

## References

- Geis & Zwicky (1971). On invited inferences.
- van der Auwera (1997). Pragmatics in the last quarter century.
- von Fintel (2011). Conditionals.
-/

import Linglib.Core.Empirical
import Mathlib.Data.Rat.Defs

namespace Phenomena.Conditionals

open Phenomena

-- Conditional Perfection

/--
**Conditional Perfection** (Geis & Zwicky 1971)

The phenomenon where "If A then C" is interpreted as "A iff C".

Example:
  "If you mow the lawn, I'll give you $5"
  → Often interpreted as: "If you DON'T mow the lawn, I WON'T give you $5"

This is an "invited inference" - not entailed, but strongly suggested.
-/
structure ConditionalPerfectionDatum where
  /-- The conditional sentence -/
  sentence : String
  /-- The perfected (biconditional) reading -/
  perfectedReading : String
  /-- Whether perfection is typically inferred -/
  perfectionObserved : Bool
  /-- Any special conditions for the inference -/
  conditions : String := ""
  deriving Repr

/-- Classic example from Geis & Zwicky -/
def lawnMowingExample : ConditionalPerfectionDatum := {
  sentence := "If you mow the lawn, I'll give you $5"
  perfectedReading := "If and only if you mow the lawn, I'll give you $5"
  perfectionObserved := true
  conditions := "Promise/threat context facilitates perfection"
}

/-- Example where perfection is NOT inferred -/
def mathExample : ConditionalPerfectionDatum := {
  sentence := "If x is even, then x is divisible by 2"
  perfectedReading := "x is even iff x is divisible by 2"
  perfectionObserved := true  -- This happens to be logically true anyway
  conditions := "Mathematical/definitional conditionals"
}

/-- Example where perfection is blocked -/
def disjunctiveAntecedent : ConditionalPerfectionDatum := {
  sentence := "If it's hot or humid, the fan will turn on"
  perfectedReading := "If it's not hot and not humid, the fan won't turn on"
  perfectionObserved := true
  conditions := "Disjunctive antecedent - perfection applies to the disjunction"
}

-- Missing-Link Infelicity

/--
**Missing-Link Infelicity**

The phenomenon where conditionals with unrelated antecedent and consequent
sound odd or unacceptable.

Example:
  "If my coffee is cold, the Eiffel Tower is in Paris"
  → True (material conditional) but pragmatically odd

This is explained by the assertability-based semantics: the conditional
is infelicitous because P(C|A) ≈ P(C), indicating no connection.
-/
structure MissingLinkDatum where
  /-- The conditional sentence -/
  sentence : String
  /-- Whether the material conditional is true -/
  materiallyTrue : Bool
  /-- Whether the sentence sounds felicitous -/
  felicitous : Bool
  /-- Explanation for the (in)felicity -/
  explanation : String
  deriving Repr

/-- Classic missing-link example -/
def coffeeEiffelExample : MissingLinkDatum := {
  sentence := "If my coffee is cold, the Eiffel Tower is in Paris"
  materiallyTrue := true  -- Consequent is true regardless
  felicitous := false
  explanation := "No causal/correlational link between antecedent and consequent"
}

/-- Another missing-link example -/
def coinPresidentExample : MissingLinkDatum := {
  sentence := "If I flip this coin and it lands heads, Biden is president"
  materiallyTrue := true
  felicitous := false
  explanation := "Antecedent and consequent are probabilistically independent"
}

/-- Felicitous conditional for comparison -/
def rainUmbrellaExample : MissingLinkDatum := {
  sentence := "If it rains, the streets will be wet"
  materiallyTrue := true  -- Assuming it does rain → wet streets
  felicitous := true
  explanation := "Clear causal link: rain causes wet streets"
}

-- Douven's Puzzle

/--
**Douven's Puzzle** (Douven 2008, discussed in Grusdt et al. 2022)

A puzzle about when conditionals are assertable.

Scenario:
  You have an almost-fair coin (51% heads).
  Is it appropriate to assert "If you flip the coin, it will land heads"?

Intuition: NO - despite P(H|flip) = 0.51 > 0.5, the conditional seems too weak.

This suggests assertability requires P(C|A) >> P(C), not just P(C|A) > 0.5.
The threshold θ ≈ 0.9 in Grusdt et al. captures this.
-/
structure DouvenPuzzleDatum where
  /-- P(C|A) in the scenario -/
  conditionalProb : ℚ
  /-- P(C) (unconditional probability of consequent) -/
  unconditionalProb : ℚ
  /-- Intuitive judgment: is the conditional assertable? -/
  intuitivelyAssertable : Bool
  /-- The conditional sentence -/
  sentence : String
  deriving Repr

/-- The original Douven scenario -/
def douvenCoinFlip : DouvenPuzzleDatum := {
  conditionalProb := 51/100
  unconditionalProb := 51/100  -- Same, since flip has probability 1
  intuitivelyAssertable := false
  sentence := "If you flip the coin, it will land heads"
}

/-- A case where assertion IS appropriate -/
def highProbCase : DouvenPuzzleDatum := {
  conditionalProb := 95/100
  unconditionalProb := 1/2
  intuitivelyAssertable := true
  sentence := "If you water the plant, it will grow"
}

/-- Edge case: P(C|A) high but P(C) also high -/
def baseRateCase : DouvenPuzzleDatum := {
  conditionalProb := 95/100
  unconditionalProb := 90/100
  intuitivelyAssertable := false  -- Unclear/debatable
  sentence := "If you use sunscreen, you won't get sunburned"
}

-- Indicative vs Subjunctive Conditionals

/--
**Indicative/Subjunctive Split**

English (and many languages) distinguish:
- Indicative: "If it rains, the game is cancelled"
- Subjunctive: "If it were to rain, the game would be cancelled"

These have different interpretations:
- Indicative: epistemic uncertainty, open whether A is true
- Subjunctive: counterfactual, A is assumed false

Example (Adams 1970):
  "If Oswald didn't kill Kennedy, someone else did" (indicative) - TRUE
  "If Oswald hadn't killed Kennedy, someone else would have" (subjunctive) - FALSE/UNCERTAIN
-/
structure IndicativeSubjunctivePair where
  /-- The indicative version -/
  indicative : String
  /-- The subjunctive/counterfactual version -/
  subjunctive : String
  /-- Judgment on indicative -/
  indicativeJudgment : String
  /-- Judgment on subjunctive -/
  subjunctiveJudgment : String
  deriving Repr

/-- Adams' Oswald example -/
def oswaldExample : IndicativeSubjunctivePair := {
  indicative := "If Oswald didn't kill Kennedy, someone else did"
  subjunctive := "If Oswald hadn't killed Kennedy, someone else would have"
  indicativeJudgment := "True (we know Kennedy was killed)"
  subjunctiveJudgment := "False or uncertain (conspiracy theory)"
}

/-- Standard minimal pair -/
def weatherExample : IndicativeSubjunctivePair := {
  indicative := "If it rains tomorrow, the picnic is cancelled"
  subjunctive := "If it were to rain tomorrow, the picnic would be cancelled"
  indicativeJudgment := "Open possibility (don't know yet)"
  subjunctiveJudgment := "Hypothetical (assuming it probably won't rain)"
}

-- Conditional Questions

/--
Conditionals in questions exhibit interesting behavior.

"If it rains, will the game be cancelled?"
vs
"Will the game be cancelled if it rains?"

These are typically equivalent, but word order can affect focus/presupposition.
-/
structure ConditionalQuestionDatum where
  /-- The conditional question -/
  question : String
  /-- The expected answer form -/
  expectedAnswer : String
  /-- Notes on interpretation -/
  notes : String
  deriving Repr

def conditionalQuestionExample : ConditionalQuestionDatum := {
  question := "If it rains, will the game be cancelled?"
  expectedAnswer := "Yes, if it rains the game will be cancelled"
  notes := "The antecedent is presupposed as a possibility being considered"
}

-- Biscuit Conditionals

/--
**Biscuit Conditionals** (Austin 1956)

Non-causal conditionals where the consequent's truth doesn't depend on
the antecedent.

Example:
  "If you're hungry, there are biscuits on the table"
  → The biscuits are there regardless of whether you're hungry

The antecedent specifies WHEN the information is relevant, not a cause.
-/
structure BiscuitConditionalDatum where
  /-- The biscuit conditional -/
  sentence : String
  /-- Paraphrase showing the structure -/
  paraphrase : String
  /-- Whether consequent depends on antecedent -/
  consequentDepends : Bool
  deriving Repr

def classicBiscuit : BiscuitConditionalDatum := {
  sentence := "If you're hungry, there are biscuits on the table"
  paraphrase := "There are biscuits on the table (relevant if you're hungry)"
  consequentDepends := false
}

def anotherBiscuit : BiscuitConditionalDatum := {
  sentence := "If you need me, I'll be in my office"
  paraphrase := "I'll be in my office (relevant if you need me)"
  consequentDepends := false
}

-- Summary Statistics

/-- Key empirical generalizations about conditionals -/
structure ConditionalGeneralizations where
  /-- Conditional perfection is observed -/
  perfectionObserved : Bool := true
  /-- Missing-link conditionals are infelicitous -/
  missingLinkInfelicitous : Bool := true
  /-- High threshold required for assertability (not just > 0.5) -/
  highThresholdRequired : Bool := true
  /-- Indicative ≠ subjunctive in truth conditions -/
  indicativeSubjunctiveDiffer : Bool := true
  /-- Biscuit conditionals exist (non-causal) -/
  biscuitConditionalsExist : Bool := true

def observedGeneralizations : ConditionalGeneralizations := {}

end Phenomena.Conditionals
