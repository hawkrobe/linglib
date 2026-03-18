/-
# @cite{thomas-2026}: A Probabilistic, Question-Based Approach to Additivity

Empirical data from @cite{thomas-2026} on additive particle felicity,
including the novel argument-building use type where antecedent and
prejacent jointly support a conclusion rather than being focus alternatives.

## Main definitions

- `ernieIree`: Argument-building "too" from COCA (ex. 1a/14a)
- `trafficTicket`: Argument-building "too" from COCA (ex. 1b/14b)
- `hotelRoom`: Argument-building "too" from COCA (ex. 1c/14c/65)
- `pizzaSpaghetti`: Standard focus-alternative "too" (ex. 5a/10/21)
- `averyInvited`: Standard additive presupposition (ex. 2/68)
- Infelicitous examples: scalar entailment (11/29a/73), conjunction
  irrelevance (25/72B), weakening/maximality (30/74),
  cross-product question (13/40/75), reversed argumentative
  orientation (15a/19a)

-/

import Linglib.Phenomena.Focus.AdditiveParticles.Data

namespace Phenomena.Focus.AdditiveParticles.Studies.Thomas2026

open Phenomena.Focus.AdditiveParticles

-- Argument-Building Examples (COCA, §1/§3)

/-- Argument-building "too" from COCA (ex. 1a/14a).
ANT = Ernie took Iree in on her own; π = it was a good thing she did.
Both jointly support the conclusion that Ernie helped Iree a great deal. -/
def ernieIree : AdditiveParticleDatum :=
  { sentence := "Ernie [...] just naturally took Iree in with no authority but her own. [...] Good thing she did too because something happened in the birthing time of Iree and she's got epilepsy [...]"
  , antecedent := "Ernie took Iree in with no authority but her own"
  , prejacent := "It was a good thing she did"
  , particle := "too"
  , resolvedQuestion := some "How much has Ernie helped Iree?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "COCA example. ANT and π jointly evidence the conclusion that Ernie helped Iree a great deal."
  , source := "Thomas (2026), ex. 1a/14a"
  }

/-- Argument-building "too" from COCA (ex. 1b/14b).
ANT = I know a couple people who have gotten tickets;
π = the fine is a hefty one.
Both jointly support the conclusion: you should worry about traffic
enforcement. -/
def trafficTicket : AdditiveParticleDatum :=
  { sentence := "i have never gotten a ticket but i know a cpl people who have.. i guess the fine is a hefty one too. depending on what im driving, i chance it."
  , antecedent := "I know a couple people who have gotten tickets"
  , prejacent := "The fine is a hefty one"
  , particle := "too"
  , resolvedQuestion := some "How much should I worry about traffic enforcement?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "COCA example. Both provide cumulative evidence that traffic enforcement is serious."
  , source := "Thomas (2026), ex. 1b/14b"
  }

/-- Argument-building "too" from COCA (ex. 1c/14c/65).
ANT = A room just opened up at this hotel;
π = It looks kind of fancy.
Both jointly support the conclusion: this hotel would be a good place
to stay. Primary worked example in §5.3. -/
def hotelRoom : AdditiveParticleDatum :=
  { sentence := "A room just opened up at this hotel. [...] It looks kind of fancy, too."
  , antecedent := "A room just opened up at this hotel"
  , prejacent := "It looks kind of fancy"
  , particle := "too"
  , resolvedQuestion := some "What would be a good hotel for us to stay at?"
  , felicity := .ok
  , useType := .argumentBuilding
  , notes := "COCA example. Primary worked example in §5.3. ANT = room available, π = fancy, RQ = good hotel?"
  , source := "Thomas (2026), ex. 1c/14c/65"
  }

/-- All argument-building examples from. -/
def argumentBuildingExamples : List AdditiveParticleDatum :=
  [ernieIree, trafficTicket, hotelRoom]

-- Standard (Focus-Alternative) Examples

/-- Standard focus-alternative "too" (ex. 5a/10/21).
ANT = "I like pizza", π = "I like spaghetti".
Both are partial answers to "What do you like?" -/
def pizzaSpaghetti : AdditiveParticleDatum :=
  { sentence := "I like [pizza]_F, and I like [spaghetti]_F, too."
  , antecedent := "I like pizza"
  , prejacent := "I like spaghetti"
  , particle := "too"
  , resolvedQuestion := some "What do you like?"
  , felicity := .ok
  , useType := .standard
  , notes := "Standard use. ANT and π are focus alternatives (same property, different objects)."
  , source := "Thomas (2026), ex. 5a/10/21"
  }

/-- Standard additive presupposition example (ex. 2/68).
Q: Who did Avery invite?
ANT = She invited Bailey (and Cameron). π = She invited Dana. -/
def averyInvited : AdditiveParticleDatum :=
  { sentence := "Q: Who did Avery invite? A: She invited Bailey. She invited Cameron, too."
  , antecedent := "Avery invited Bailey"
  , prejacent := "Avery invited Cameron"
  , particle := "too"
  , resolvedQuestion := some "Who did Avery invite?"
  , felicity := .ok
  , useType := .standard
  , notes := "Standard additive presupposition: ANT and π are both partial answers to the same question."
  , source := "Thomas (2026), ex. 2/68"
  }

/-- Standard focus-alternative examples. -/
def standardExamples : List AdditiveParticleDatum :=
  [pizzaSpaghetti, averyInvited]

-- Infelicitous Examples

/-- Infelicitous: π entails the resolution — violates non-triviality
(ex. 11/29a/73).
ANT = "Sam is happy", π = "He's ecstatic".
Since "ecstatic" entails "happy", ⟦π⟧ ⊆ RQ|_{ANT∩⟦π⟧} = |Sam is ecstatic|,
violating Def. 64c.i. -/
def happyEcstatic : AdditiveParticleDatum :=
  { sentence := "Sam is happy. #He's ecstatic, too."
  , antecedent := "Sam is happy"
  , prejacent := "Sam is ecstatic"
  , particle := "too"
  , resolvedQuestion := some "What is Sam's emotional state?"
  , felicity := .odd
  , useType := .standard
  , notes := "Infelicitous: π = 'ecstatic' entails the resolution evidenced by ANT∩π — violates Def. 64c.i (non-triviality)."
  , source := "Thomas (2026), ex. 11/29a/73"
  }

/-- Infelicitous: reversed argumentative orientation — no suitable RQ
(ex. 15a/19a).
In the context of (14a) where Ernie's actions are evaluated positively,
replacing "good thing" with "bad thing" reverses the argumentative
direction. No RQ satisfies both the Antecedent and Conjunction Conditions. -/
def badThingSheDidToo : AdditiveParticleDatum :=
  { sentence := "Ernie took Iree in with no authority but her own. It was a bad thing she did, #too."
  , antecedent := "Ernie took Iree in with no authority but her own"
  , prejacent := "It was a bad thing she did"
  , particle := "too"
  , resolvedQuestion := none
  , felicity := .odd
  , useType := .argumentBuilding
  , notes := "Infelicitous: ANT evidences a positive conclusion but π evidences a negative one — no RQ satisfies both conditions."
  , source := "Thomas (2026), ex. 15a/19a"
  }

/-- Infelicitous: conjunction provides no additional evidence — fails
Conjunction Condition (ex. 25/72B).
ANT = "She invited Bailey and Cameron", π = "Dogs are mammals".
π provides no information about who Avery invited. -/
def dogsAreMammals : AdditiveParticleDatum :=
  { sentence := "Q: Who are some people Avery invited? A: She invited Bailey and Cameron. #Dogs are mammals, too."
  , antecedent := "She invited Bailey and Cameron"
  , prejacent := "Dogs are mammals"
  , particle := "too"
  , resolvedQuestion := some "Who are some people Avery invited?"
  , felicity := .odd
  , useType := .standard
  , notes := "Infelicitous: π provides no information relevant to RQ — ANT∩⟦π⟧ does not Evidence RQ more strongly than ANT alone (fails Conjunction Condition)."
  , source := "Thomas (2026), ex. 25/72B"
  }

/-- Infelicitous: weaker alternative works just as well — violates
maximality (ex. 30/74).
ANT = "Avery plays an instrument", π = "Bailey plays the cello".
"Bailey plays an instrument" (weaker than π) gives the same evidential
boost to the resolution. -/
def instrumentCello : AdditiveParticleDatum :=
  { sentence := "Q: Who plays an instrument? A: Avery plays an instrument. #Bailey plays the cello, too."
  , antecedent := "Avery plays an instrument"
  , prejacent := "Bailey plays the cello"
  , particle := "too"
  , resolvedQuestion := some "Who plays an instrument?"
  , felicity := .odd
  , useType := .standard
  , notes := "Infelicitous: 'Bailey plays an instrument' (⊃ ⟦π⟧) evidences the resolution just as strongly — violates Def. 64c.ii (maximality). Note: swapping ANT and π yields felicitous 'too' (ex. 30A')."
  , source := "Thomas (2026), ex. 30/74"
  }

/-- Infelicitous: cross-product question — no single RQ satisfies both
conditions (ex. 13/40/75).
Q: Who ate what? ANT = "Avery ate pizza", π = "Bailey ate spaghetti".
Every resolution to "Who ate what?" specifies what BOTH Avery and Bailey
ate, so ANT alone provides no information about Bailey's food. -/
def whoAteWhat : AdditiveParticleDatum :=
  { sentence := "Q: Who ate what? A: Avery ate pizza. B: #Bailey ate spaghetti, too."
  , antecedent := "Avery ate pizza"
  , prejacent := "Bailey ate spaghetti"
  , particle := "too"
  , resolvedQuestion := some "Who ate what?"
  , felicity := .odd
  , useType := .standard
  , notes := "Infelicitous: ANT answers 'What did Avery eat?' while π answers 'What did Bailey eat?' — no single RQ has both Antecedent and Conjunction Conditions satisfied."
  , source := "Thomas (2026), ex. 13/40/75"
  }

/-- Infelicitous examples from. -/
def infelicitousExamples : List AdditiveParticleDatum :=
  [happyEcstatic, badThingSheDidToo, dogsAreMammals, instrumentCello, whoAteWhat]

-- Collected Data

/-- All examples. -/
def allExamples : List AdditiveParticleDatum :=
  argumentBuildingExamples ++ standardExamples ++ infelicitousExamples

end Phenomena.Focus.AdditiveParticles.Studies.Thomas2026
