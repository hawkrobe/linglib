/-
# Inference Preservation: Empirical Data

Theory-neutral empirical patterns for how imprecision is blocked when it
would fail to preserve certain inferences.

## Phenomena Covered

1. **Numeral alternatives**: 99 vs 100 asymmetry
2. **Conjunction entailments**: "A and B are P" |= "A is P"
3. **Numeral-modified definites**: "the four doors" lacks non-maximality

## Key Insight (INFERENCE PRESERVATION)

An imprecise construal of φ is blocked if it would fail to preserve
inferences about alternatives of φ that hold on the precise construal.

This explains:
- Why 99 can't be imprecise (100 is an alternative; 99 entails ¬100)
- Why conjunctions resist non-maximality (conjuncts are alternatives)
- Why "the four doors" is precise (sub-numerals are alternatives)

## Key References

- Dissertation Chapters 6-7
- Sauerland & Stateva (2007): Numeral alternatives
- Križ (2015): Conjunctions and homogeneity
-/

namespace Phenomena.Imprecision.InferencePreservation

-- ============================================================================
-- PART 1: Alternative Sets
-- ============================================================================

/--
Type of alternative relationship.
-/
inductive AlternativeType where
  | scalar       -- Horn scale alternatives (some/all)
  | subdomain    -- Subdomain alternatives (the books → the book a)
  | conjunct     -- Conjunct alternatives (A and B → A, B)
  | numeral      -- Numeral alternatives (99 → 100, 98, ...)
  deriving Repr, DecidableEq

/--
Inference relation between expression and alternative.
-/
inductive InferenceRelation where
  | entails         -- φ |= ψ
  | contradicts     -- φ |= ¬ψ
  | independent     -- neither
  deriving Repr, DecidableEq

-- ============================================================================
-- PART 2: Numeral Alternatives and Blocking
-- ============================================================================

/--
Numeral alternative blocking datum.

Key idea: The alternatives of a numeral n include nearby numerals.
If n contradicts m on precise reading, imprecise construal can't
be compatible with m.

Source: Dissertation Chapter 6, Sauerland & Stateva (2007)
-/
structure NumeralBlockingDatum where
  /-- The numeral -/
  numeral : Nat
  /-- Is it round? -/
  round : Bool
  /-- Key alternative -/
  alternative : Nat
  /-- Is alternative in the alternative set? -/
  alternativeInSet : Bool
  /-- Inference relation (precise reading) -/
  inferenceRelation : InferenceRelation
  /-- Is imprecision blocked? -/
  imprecisionBlocked : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

def ninetyNineBlocked : NumeralBlockingDatum :=
  { numeral := 99
  , round := false
  , alternative := 100
  , alternativeInSet := true  -- 100 is obligatorily an alternative of 99
  , inferenceRelation := .contradicts  -- "99 cars" entails "NOT 100 cars"
  , imprecisionBlocked := true
  , explanation := "If 99 could mean 'approximately 99' (including 100), it would fail to preserve the inference that the 100-alternative is false. Since 100 is obligatorily in the alternative set of 99, imprecision is blocked."
  }

def hundredNotBlocked : NumeralBlockingDatum :=
  { numeral := 100
  , round := true
  , alternative := 99
  , alternativeInSet := false  -- 99 is NOT obligatorily an alternative of 100
  , inferenceRelation := .contradicts
  , imprecisionBlocked := false
  , explanation := "99 is not obligatorily an alternative of 100 due to 100's roundness. The alternative set of 100 might include {200, 50, ...} but not necessarily {99, 101, ...}. So imprecision doesn't violate inference preservation."
  }

/--
The asymmetry depends on conventionalized alternative sets.

Round numbers have "coarse" alternative sets.
Non-round numbers have "fine" alternative sets that include round neighbors.

Source: Dissertation Chapter 6
-/
structure AlternativeSetAsymmetry where
  /-- Round numeral -/
  roundNumeral : Nat
  /-- Its alternative set (simplified) -/
  roundAlternatives : List Nat
  /-- Non-round numeral -/
  nonRoundNumeral : Nat
  /-- Its alternative set (simplified) -/
  nonRoundAlternatives : List Nat
  /-- Asymmetry explanation -/
  explanation : String
  deriving Repr

def hundredNinetyNineAsymmetry : AlternativeSetAsymmetry :=
  { roundNumeral := 100
  , roundAlternatives := [50, 200, 500, 1000]  -- other round numbers
  , nonRoundNumeral := 99
  , nonRoundAlternatives := [100, 98, 97, 101]  -- includes neighboring round
  , explanation := "100's alternatives are other round numbers (coarse scale). 99's alternatives include 100 (the nearest round number). This asymmetry in alternative sets explains why 99 must be exact."
  }

-- ============================================================================
-- PART 3: Conjunction Blocking
-- ============================================================================

/--
Conjunction blocking datum.

Conjunctions have conjuncts as alternatives.
"A and B are P" entails "A is P" and "B is P".
Non-maximal reading would fail to preserve these entailments.

Source: Dissertation Chapter 7
-/
structure ConjunctionBlockingDatum where
  /-- The conjunction sentence -/
  sentence : String
  /-- The conjuncts -/
  conjuncts : List String
  /-- Alternatives (the conjuncts as sentences) -/
  alternatives : List String
  /-- Entailment holds on precise reading? -/
  entailmentHolds : Bool
  /-- Would non-max preserve entailment? -/
  nonMaxPreservesEntailment : Bool
  /-- Is non-max blocked? -/
  nonMaxBlocked : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

def annBertConjunction : ConjunctionBlockingDatum :=
  { sentence := "Ann and Bert have red hair."
  , conjuncts := ["Ann", "Bert"]
  , alternatives := ["Ann has red hair.", "Bert has red hair."]
  , entailmentHolds := true  -- "A and B have P" |= "A has P", "B has P"
  , nonMaxPreservesEntailment := false  -- "only Ann has P" wouldn't entail both
  , nonMaxBlocked := true
  , explanation := "If 'Ann and Bert have red hair' could be true when only Ann has red hair, it would fail to entail 'Bert has red hair', violating inference preservation."
  }

def threeStudentsConjunction : ConjunctionBlockingDatum :=
  { sentence := "Bert, Claire, and Dora went there."
  , conjuncts := ["Bert", "Claire", "Dora"]
  , alternatives := ["Bert went there.", "Claire went there.", "Dora went there."]
  , entailmentHolds := true
  , nonMaxPreservesEntailment := false
  , nonMaxBlocked := true
  , explanation := "Same pattern: explicit list of conjuncts creates entailments that non-maximal reading would violate."
  }

-- ============================================================================
-- PART 4: Numeral-Modified Definites
-- ============================================================================

/--
Numeral-modified definites: "the four doors"

These have homogeneity gaps but resist non-maximality.
The numeral creates subdomain alternatives.

Source: Brisson (1998), Križ (2015), dissertation Chapter 7
-/
structure NumeralDefiniteBlockingDatum where
  /-- The sentence -/
  sentence : String
  /-- The numeral -/
  numeral : Nat
  /-- Sub-numeral alternatives -/
  subNumeralAlternatives : List Nat
  /-- Does sentence entail sub-numeral alternatives? -/
  entailsSubNumerals : Bool
  /-- Is non-max blocked? -/
  nonMaxBlocked : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

def fourDoorsBlocking : NumeralDefiniteBlockingDatum :=
  { sentence := "The four doors are open."
  , numeral := 4
  , subNumeralAlternatives := [1, 2, 3]  -- "the one door", "the two doors", etc.
  , entailsSubNumerals := true  -- if 4 are open, then 3 are, 2 are, 1 is
  , nonMaxBlocked := true
  , explanation := "'The four doors are open' with only 3 open would fail to entail 'The three doors are open' (which requires all 3 in a contextually salient group of 3 to be open). But wait - this is subtle. The blocking actually works through a different mechanism involving the numeral's own alternatives."
  }

-- ============================================================================
-- PART 5: Exceptions - Collective/Cumulative Predicates
-- ============================================================================

/--
Collective and cumulative predicates sometimes permit non-maximality
even with conjunctions.

This is an exception that inference preservation needs to handle.

Source: Dissertation Chapter 7
-/
structure CollectiveCumulativeException where
  /-- The sentence -/
  sentence : String
  /-- Predicate type -/
  predicateType : String  -- "collective" or "cumulative"
  /-- Is non-max possible? -/
  nonMaxPossible : Bool
  /-- Why? -/
  explanation : String
  deriving Repr

def collectiveMeetException : CollectiveCumulativeException :=
  { sentence := "Ann, Bert, and Claire met."
  , predicateType := "collective"
  , nonMaxPossible := true  -- marginally possible
  , explanation := "Collective predicates may exceptionally permit non-max because the entailment pattern is different: 'A, B, C met' doesn't straightforwardly entail 'A met' (meeting requires multiple participants)."
  }

def cumulativeCarryException : CollectiveCumulativeException :=
  { sentence := "Ann, Bert, and Claire carried the piano upstairs."
  , predicateType := "cumulative"
  , nonMaxPossible := true
  , explanation := "Cumulative readings involve a many-to-many relation. The inference pattern is more complex, potentially allowing non-max."
  }

-- ============================================================================
-- PART 6: The Blocking Constraint
-- ============================================================================

/--
INFERENCE PRESERVATION constraint (informal statement).

For an imprecise construal of φ to be available:
- For all alternatives ψ of φ:
  - If precise(φ) |= ψ, then imprecise(φ) |= ψ
  - If precise(φ) |= ¬ψ, then imprecise(φ) |= ¬ψ

Source: Dissertation Chapters 6-7
-/
structure InferencePreservationConstraint where
  /-- Name of constraint -/
  name : String
  /-- Informal statement -/
  statement : String
  /-- Applies to entailments? -/
  appliesToEntailments : Bool
  /-- Applies to contradictions? -/
  appliesToContradictions : Bool
  /-- Applies to all alternatives? -/
  appliesToAllAlternatives : Bool
  deriving Repr

def inferencePreservation : InferencePreservationConstraint :=
  { name := "INFERENCE PRESERVATION"
  , statement := "An imprecise construal of φ must preserve the inferential relations (entailment, contradiction) between φ and its alternatives that hold on the precise construal."
  , appliesToEntailments := true
  , appliesToContradictions := true
  , appliesToAllAlternatives := true  -- but see exceptions
  }

-- ============================================================================
-- PART 7: Predictions
-- ============================================================================

/--
Predictions of INFERENCE PRESERVATION.
-/
structure InferencePreservationPrediction where
  /-- Construction -/
  construction : String
  /-- Prediction -/
  prediction : String
  /-- Is prediction borne out? -/
  confirmed : Bool
  deriving Repr

def prediction1 : InferencePreservationPrediction :=
  { construction := "Non-round numerals"
  , prediction := "Non-round numerals can't be imprecise because they contradict round alternatives"
  , confirmed := true
  }

def prediction2 : InferencePreservationPrediction :=
  { construction := "Explicit conjunctions"
  , prediction := "Explicit conjunctions resist non-max because they entail conjunct alternatives"
  , confirmed := true
  }

def prediction3 : InferencePreservationPrediction :=
  { construction := "Numeral-modified definites"
  , prediction := "'The N Xs' resists non-max due to sub-numeral alternatives"
  , confirmed := true
  }

def prediction4 : InferencePreservationPrediction :=
  { construction := "Collective predicates with conjunctions"
  , prediction := "May permit non-max because entailment pattern differs"
  , confirmed := true  -- at least marginally
  }

-- ============================================================================
-- PART 8: Open Questions
-- ============================================================================

/--
Open questions for INFERENCE PRESERVATION.
-/
structure OpenQuestion where
  /-- The question -/
  question : String
  /-- Why it's open -/
  difficulty : String
  deriving Repr

def question1 : OpenQuestion :=
  { question := "What exactly are the alternatives for conjunctions?"
  , difficulty := "Need precise theory of alternative sets for plural expressions"
  }

def question2 : OpenQuestion :=
  { question := "Why do collective predicates behave differently?"
  , difficulty := "Need to understand how entailment patterns interact with the constraint"
  }

def question3 : OpenQuestion :=
  { question := "How does this interact with the QUD?"
  , difficulty := "The constraint seems to apply regardless of QUD, but formalization unclear"
  }

-- ============================================================================
-- PART 9: Key Generalizations
-- ============================================================================

/--
Core empirical generalizations about inference preservation.
-/
structure InferencePreservationGeneralizations where
  /-- Non-round numerals exact due to round alternatives -/
  nonRoundExactDueToAlternatives : Bool
  /-- Conjunctions resist non-max due to conjunct alternatives -/
  conjunctionsResistDueToAlternatives : Bool
  /-- Collective predicates exceptional -/
  collectivesExceptional : Bool
  /-- Constraint is about alternatives, not monotonicity -/
  alternativesBased : Bool
  deriving Repr

def mainGeneralizations : InferencePreservationGeneralizations :=
  { nonRoundExactDueToAlternatives := true
  , conjunctionsResistDueToAlternatives := true
  , collectivesExceptional := true
  , alternativesBased := true
  }

-- ============================================================================
-- Collections
-- ============================================================================

def numeralBlockingExamples : List NumeralBlockingDatum :=
  [ninetyNineBlocked, hundredNotBlocked]

def conjunctionBlockingExamples : List ConjunctionBlockingDatum :=
  [annBertConjunction, threeStudentsConjunction]

def collectiveExceptions : List CollectiveCumulativeException :=
  [collectiveMeetException, cumulativeCarryException]

def predictions : List InferencePreservationPrediction :=
  [prediction1, prediction2, prediction3, prediction4]

def openQuestions : List OpenQuestion :=
  [question1, question2, question3]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `NumeralBlockingDatum`: Why non-round numerals are exact
- `AlternativeSetAsymmetry`: Round vs non-round alternative sets
- `ConjunctionBlockingDatum`: Why conjunctions resist non-max
- `NumeralDefiniteBlockingDatum`: "The four doors" pattern
- `CollectiveCumulativeException`: Exceptions for collective predicates
- `InferencePreservationConstraint`: The blocking constraint

### Key Finding: INFERENCE PRESERVATION
Imprecise construals must preserve inferential relations with alternatives:
- If precise(φ) |= ψ, then imprecise(φ) |= ψ
- If precise(φ) |= ¬ψ, then imprecise(φ) |= ¬ψ

### Applications
1. 99 can't mean "approximately 99" because it would then be compatible
   with 100, but 99 must contradict 100 (an alternative).
2. "Ann and Bert are P" can't mean "Ann or Bert is P" because it would
   then fail to entail "Ann is P" (an alternative).

### Key References
- Dissertation Chapters 6-7
- Sauerland & Stateva (2007)
- Križ (2015), Brisson (1998)
-/

end Phenomena.Imprecision.InferencePreservation
