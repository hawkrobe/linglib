/-
# Goodman & Stuhlmüller (2013) - Empirical Data

"Knowledge and Implicature: Modeling Language Understanding as Social Cognition"
Topics in Cognitive Science 5(1): 173-184

## Scalar Implicature

Scalar implicature is a pragmatic inference where using a weaker term
implicates the negation of stronger alternatives on the same scale.

Key example: "some" implicates "not all" (some-all scale)

## Background References

- Horn (1972). On the Semantic Properties of Logical Operators in English.
- Grice (1975). Logic and Conversation.
-/

import Linglib.Core.Empirical

namespace Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013

open Phenomena

-- Study Metadata

/-- Citation for this study -/
def citation : String := "Goodman, N.D. & Stuhlmüller, A. (2013). Knowledge and Implicature: Modeling Language Understanding as Social Cognition. Topics in Cognitive Science 5(1): 173-184."

/-- Listener interpretation measure: behavioral comprehension -/
def interpretationMeasure : MeasureSpec :=
  { scale := .proportion, task := .forcedChoice, unit := "probability 0-1" }

-- Scalar Implicature Data

/-- A Horn scale: ordered alternatives from weak to strong -/
structure HornScale where
  name : String
  weakTerm : String
  strongTerm : String
  deriving Repr

/-- The canonical some/all scale -/
def someAllScale : HornScale := {
  name := "Quantifier Scale"
  weakTerm := "some"
  strongTerm := "all"
}

/-- A scalar implicature datum -/
structure ScalarImplicatureDatum where
  utterance : String
  strongerAlternative : String
  literalMeaning : String
  implicatedMeaning : String
  deriving Repr

/-- The canonical "some" → "not all" example -/
def someNotAll : ScalarImplicatureDatum := {
  utterance := "Some of the students passed"
  strongerAlternative := "All of the students passed"
  literalMeaning := "At least one student passed (possibly all)"
  implicatedMeaning := "Some but not all students passed"
}

-- Knowledge State Data (Experiment 1 from the paper)

/-- Speaker's perceptual access level -/
structure AccessCondition where
  objectsSeen : Nat
  totalObjects : Nat
  deriving Repr

/-- The key experimental conditions from Experiment 1 -/
def fullAccessCondition : AccessCondition := { objectsSeen := 3, totalObjects := 3 }
def partialAccess2 : AccessCondition := { objectsSeen := 2, totalObjects := 3 }
def partialAccess1 : AccessCondition := { objectsSeen := 1, totalObjects := 3 }

/-- Experimental finding: implicature strength varies with access -/
structure KnowledgeImplicatureDatum where
  access : AccessCondition
  utterance : String
  implicatureStrength : String  -- "strong", "weak", "none"
  empiricalNote : String
  deriving Repr

/-- Full access: strong implicature -/
def fullAccessResult : KnowledgeImplicatureDatum := {
  access := fullAccessCondition
  utterance := "Some of the apples are red"
  implicatureStrength := "strong"
  empiricalNote := "Bets on 3 were less than bets on 2 (p < .001)"
}

/-- Partial access (1 object): no implicature -/
def partialAccess1Result : KnowledgeImplicatureDatum := {
  access := partialAccess1
  utterance := "Some of the apples are red"
  implicatureStrength := "none"
  empiricalNote := "Bets on 2 did not exceed bets on 3 (p = .78)"
}

-- The Core Empirical Phenomenon (Experiment 2: Number Words)

/--
**The Empirical Phenomenon**

From Experiment 2: Number word interpretation varies with speaker access.
- Full access + "two" → interpreted as "exactly 2"
- Partial access + "two" → interpreted as "≥2" (weaker)

This is CANCELLATION: the exact interpretation is canceled with partial knowledge.
-/
structure ImplicatureCancellationPhenomenon where
  /-- Cancellation was observed in the experiment -/
  cancellation_observed : Bool
  /-- Statistical significance -/
  significant : Bool
  /-- Citation -/
  citation : String

/-- The empirical finding from Experiment 2 -/
def numberWordCancellation : ImplicatureCancellationPhenomenon := {
  cancellation_observed := true
  significant := true
  citation := "Goodman & Stuhlmüller (2013), Experiment 2, p. 180"
}

-- What This Phenomenon Requires of Semantic Theories

/--
**Semantic Constraint from Empirical Data**

If cancellation is observed, then:
1. An implicature must exist (something to cancel)
2. The implicature must be PRAGMATIC, not semantic (otherwise can't vary)
3. The literal meaning must be WEAKER than the pragmatic interpretation

For number words:
- Pragmatic: "two" → exactly 2
- Literal must be: "two" → ≥2 (weaker, allows cancellation)
- NOT: "two" → exactly 2 (no room for cancellation)
-/
structure SemanticRequirement where
  /-- Literal meaning must allow multiple states -/
  requires_ambiguity : Bool
  /-- Exact interpretation must emerge pragmatically -/
  exact_is_pragmatic : Bool

/-- What the cancellation phenomenon requires -/
def cancellationRequires : SemanticRequirement := {
  requires_ambiguity := true
  exact_is_pragmatic := true
}

/--
**The Inconsistency Claim**

Any semantic theory where "two" literally means exactly 2 is
INCONSISTENT with the observed cancellation phenomenon.

This is because:
- If literal meaning is already exact, there's no implicature
- If there's no implicature, there's nothing to cancel
- But cancellation IS observed
- Contradiction
-/
def exactSemanticsInconsistent : Bool := true

end Phenomena.ScalarImplicatures.Studies.GoodmanStuhlmuller2013
