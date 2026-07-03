import Linglib.Semantics.Quantification.Numerals.Roundness

/-!
# [haslinger-2025-diss]: Imprecision and homogeneity

Empirical data from Nina Haslinger (2025), "Pragmatic constraints on imprecision
and homogeneity," Doctoral Dissertation, Georg-August-Universität Göttingen
(doi:10.53846/goediss-11395). The Sinn und Bedeutung 28 paper [haslinger-2024]
is the published version of dissertation chapters 3 and 5.

## Two constraints

1. **NO NEEDLESS MANNER VIOLATIONS** (Ch 3-4): a tradeoff between structural
   complexity and semantic precision — more complex expressions must be more
   precise. The competition relation is **potential p-equivalence** (def (68),
   §3.3.3): two sentences compete iff there is *some* choice of issue
   parameter making their p-truth conditions equivalent.

2. **INFERENCE PRESERVATION** (Ch 6-7): an imprecise construal of φ must
   preserve the inferential relations between φ and its alternatives that hold
   on the precise construal.

## Sub-namespaces

- `Numerals` (Ch 2, Ch 4) — round/non-round asymmetry, `exactly`/`approximately`
  modifiers, the German game-show paradigm.
- `FormMeaning` (Ch 3) — complexity-precision pairs: the/all-the, and/both,
  100/exactly-100, blue/completely-blue.
- `InferencePreservation` (Ch 6, 7) — alternative-set blocking for non-round
  numerals, conjunctions, and numeral definites.

-/

namespace Haslinger2025

-- ============================================================================
-- §1. Numeral Imprecision
-- ============================================================================

namespace Numerals

open Semantics.Numerals.Roundness

/--
Numeral imprecision datum: context-dependent exactness.
-/
structure NumeralImprecisionDatum where
  /-- The numeral -/
  numeral : Nat
  /-- Roundness grade (from `Semantics.Numerals.Roundness`) -/
  roundness : RoundnessGrade
  /-- Sentence frame -/
  sentenceFrame : String
  /-- Context favoring exact reading -/
  exactContext : String
  /-- Context favoring inexact reading -/
  inexactContext : String
  /-- Actual value in scenario -/
  actualValue : Nat
  /-- Acceptable in exact context? -/
  acceptableExact : Bool
  /-- Acceptable in inexact context? -/
  acceptableInexact : Bool
  deriving Repr

/--
The cars scenario from [haslinger-2025-diss] Ch 2.1.2 ex. (19) `CARS(EXACT)`
and ex. (20) `CARS(INEXACT)`, pp. 71-72.
-/
def carsExact : NumeralImprecisionDatum :=
  { numeral := 100
  , roundness := .high       -- score 6 (all 6 k-ness properties)
  , sentenceFrame := "This guy owns _ cars."
  , exactContext := "Tax rate depends on owning exactly 100+ cars"
  , inexactContext := "Discussing extreme wealth (exact count irrelevant)"
  , actualValue := 98
  , acceptableExact := false   -- misleading about tax status
  , acceptableInexact := true  -- 98 ≈ 100 for wealth signaling
  }

def carsNonRound : NumeralImprecisionDatum :=
  { numeral := 99
  , roundness := .none        -- score 0 (no k-ness properties)
  , sentenceFrame := "This guy owns _ cars."
  , exactContext := "Tax rate depends on owning exactly 100+ cars"
  , inexactContext := "Discussing extreme wealth (exact count irrelevant)"
  , actualValue := 98
  , acceptableExact := false
  , acceptableInexact := false  -- 99 requires exact reading even here
  }


/--
Minimal pair showing round/non-round asymmetry.
-/
structure RoundnessAsymmetryDatum where
  /-- Round numeral -/
  roundNumeral : Nat
  /-- Non-round numeral -/
  nonRoundNumeral : Nat
  /-- Context (same for both) -/
  context : String
  /-- Actual value -/
  actualValue : Nat
  /-- Round numeral acceptable? -/
  roundAcceptable : Bool
  /-- Non-round acceptable? -/
  nonRoundAcceptable : Bool
  deriving Repr

def hundredVsNinetyNine : RoundnessAsymmetryDatum :=
  { roundNumeral := 100
  , nonRoundNumeral := 99
  , context := "Casual conversation about someone's car collection"
  , actualValue := 98
  , roundAcceptable := true    -- "100 cars" OK when actual is 98
  , nonRoundAcceptable := false -- "99 cars" requires exactly 99
  }

def fiftyVsFortyNine : RoundnessAsymmetryDatum :=
  { roundNumeral := 50
  , nonRoundNumeral := 49
  , context := "Estimating crowd size at event"
  , actualValue := 47
  , roundAcceptable := true
  , nonRoundAcceptable := false
  }


/--
The game show scenario tests for homogeneity gaps.

Context makes both exact and inexact readings relevant.
If numerals had gaps like plurals, neither sentence should be clearly true.

Source: [haslinger-2025-diss] Ch 2.4.1 ex. (164), p. 72.
-/
structure GameShowDatum where
  /-- The sentence -/
  sentence : String
  /-- Scenario description -/
  scenario : String
  /-- Exact reading true? -/
  exactReadingTrue : Bool
  /-- Inexact reading true? -/
  inexactReadingTrue : Bool
  /-- Judgment: is sentence acceptable? -/
  acceptable : Bool
  /-- Do speakers agree? -/
  speakersAgree : Bool
  /-- Notes -/
  notes : String
  deriving Repr

def gameShowPositive : GameShowDatum :=
  { sentence := "Bei diesem Spiel hat heute jeder 200 Münzen gesammelt."
              -- "In this game, everyone collected 200 coins today."
  , scenario := "Game: collect exactly 200 coins → €250 prize; approximately 200 → €50. All participants collected amounts like 195, 198, 203, 205 (close but not exact). All won €50."
  , exactReadingTrue := false   -- no one got exactly 200
  , inexactReadingTrue := true  -- everyone got approximately 200
  , acceptable := true          -- some speakers accept (inexact reading)
  , speakersAgree := false      -- speakers disagree on judgment
  , notes := "Unlike plurals, speakers don't report 'neither true nor false' - they pick exact or inexact reading"
  }

def gameShowNegative : GameShowDatum :=
  { sentence := "Bei diesem Spiel hat heute niemand 200 Münzen gesammelt."
              -- "In this game, nobody collected 200 coins today."
  , scenario := "Same as above"
  , exactReadingTrue := true    -- no one got exactly 200
  , inexactReadingTrue := false -- everyone got approximately 200
  , acceptable := true          -- some speakers accept (exact reading)
  , speakersAgree := false
  , notes := "Complementary to positive - one is true depending on reading"
  }


/--
"Exactly" removes imprecision, parallel to "all" for plurals.

Source: [haslinger-2025-diss] Ch 4.2.1 ex. (4) and (9), pp. 174-176.
-/
structure ExactlyModifierDatum where
  /-- Bare numeral sentence -/
  bareSentence : String
  /-- Modified sentence -/
  exactlySentence : String
  /-- Context -/
  context : String
  /-- Actual value -/
  actualValue : Nat
  /-- Bare acceptable? -/
  bareAcceptable : Bool
  /-- Exactly acceptable? -/
  exactlyAcceptable : Bool
  deriving Repr

def exactlyRemovesImprecision : ExactlyModifierDatum :=
  { bareSentence := "Ann owns 100 cars."
  , exactlySentence := "Ann owns exactly 100 cars."
  , context := "Casual conversation about wealth"
  , actualValue := 98
  , bareAcceptable := true     -- imprecise reading available
  , exactlyAcceptable := false -- "exactly" forces precise reading
  }


/--
"Approximately" reduces imprecision by binding out the exact reading: bare
`100` has both exact and inexact readings; `approximately 100` has only
inexact, so the set of available construals shrinks.

Source: [haslinger-2025-diss] §4.2.1 ex. (4) and (10), p. 174-176;
non-round case developed in §4.2.2 ex. (25)-(26).
-/
structure ApproximatelyDatum where
  /-- Bare sentence -/
  bareSentence : String
  /-- Approximately sentence -/
  approxSentence : String
  /-- Roundness grade (from `Semantics.Numerals.Roundness`) -/
  roundness : RoundnessGrade
  /-- Is approximately acceptable with this numeral? -/
  approxNatural : Bool
  /-- Notes -/
  notes : String
  deriving Repr

def approximatelyWithRound : ApproximatelyDatum :=
  { bareSentence := "Ann owns 100 cars."
  , approxSentence := "Ann owns approximately 100 cars."
  , roundness := .high       -- 100: score 6
  , approxNatural := true
  , notes := "Natural: makes existing imprecision explicit"
  }

def approximatelyWithNonRound : ApproximatelyDatum :=
  { bareSentence := "Ann owns 99 cars."
  , approxSentence := "Ann owns approximately 99 cars."
  , roundness := .none      -- 99: score 0
  , approxNatural := false  -- or at least marked
  , notes := "Odd/marked: why approximate to a non-round number?"
  }


/--
Core empirical generalizations about numeral imprecision.
-/
structure Generalizations where
  /-- Round numerals permit imprecision -/
  roundPermitsImprecision : Bool
  /-- Non-round require exactness -/
  nonRoundRequiresExact : Bool
  /-- "Exactly" removes imprecision -/
  exactlyRemoves : Bool
  /-- Negation requires polar questions -/
  negationRequiresPolar : Bool
  /-- No clear homogeneity gaps (unlike plurals) -/
  noHomogeneityGaps : Bool
  /-- Imprecision is context-sensitive -/
  contextSensitive : Bool
  deriving Repr

def generalizations : Generalizations :=
  { roundPermitsImprecision := true
  , nonRoundRequiresExact := true
  , exactlyRemoves := true
  , negationRequiresPolar := true
  , noHomogeneityGaps := true  -- disputed, but apparent
  , contextSensitive := true
  }

-- Collections

def carsExamples : List NumeralImprecisionDatum :=
  [carsExact, carsNonRound]

def roundnessAsymmetryExamples : List RoundnessAsymmetryDatum :=
  [hundredVsNinetyNine, fiftyVsFortyNine]

def gameShowExamples : List GameShowDatum :=
  [gameShowPositive, gameShowNegative]

end Numerals


-- ============================================================================
-- §2. Form/Meaning Correspondences
-- ============================================================================

namespace FormMeaning

/--
A pair of expressions showing the complexity-precision tradeoff.

The `potentiallyPEquivalent` field encodes Haslinger's notion of **potential
p-equivalence** (definition (68), §3.3.3): two sentences count as competitors
for NO NEEDLESS MANNER VIOLATIONS iff there exists *some* choice of issue
parameter making their p-truth conditions equivalent. This is weaker than raw
truth-conditional equivalence and is **not transitive** (footnote on p. 88).
-/
structure ComplexityPrecisionPair where
  /-- Less complex expression -/
  lessComplexExpr : String
  /-- More complex expression -/
  moreComplexExpr : String
  /-- What makes it more complex -/
  complexitySource : String
  /-- Does less complex permit imprecision? -/
  lessComplexImprecise : Bool
  /-- Does more complex permit imprecision? -/
  moreComplexImprecise : Bool
  /-- Potential p-equivalence (Haslinger def 68): some issue-parameter choice
      makes the two p-truth-conditionally equivalent. NOT TC-equivalence. -/
  potentiallyPEquivalent : Bool
  /-- Construction type -/
  constructionType : String
  deriving Repr

/--
Plural definites: "the doors" vs "all the doors". The German parallel
(`die Türen` / `alle Türen`) holds, and §3.2.2 (Table 3.1) surveys 12+
language families showing the absence of the inverse pattern.

Source: [haslinger-2025-diss] Ch 3.1.1 ex. (3), p. 86; gap-removal
contrast ex. (4).
-/
def doorsAllDoors : ComplexityPrecisionPair :=
  { lessComplexExpr := "The doors are open."
  , moreComplexExpr := "All the doors are open."
  , complexitySource := "Addition of 'all'"
  , lessComplexImprecise := true   -- permits non-maximal
  , moreComplexImprecise := false  -- requires maximal
  , potentiallyPEquivalent := true  -- §3.3.3 def (68); some issue-param assignment makes p-truth-conditions match
  , constructionType := "Plural definites"
  }

/--
Conjunctions: "Ann and Bert" vs "both Ann and Bert"

Source: [haslinger-2025-diss] Ch 3.3 ex. (48), p. 104; further developed
in §3.5.1 (p. 126).
-/
def andBoth : ComplexityPrecisionPair :=
  { lessComplexExpr := "Ann and Bert have red hair."
  , moreComplexExpr := "Both Ann and Bert have red hair."
  , complexitySource := "Addition of 'both'"
  , lessComplexImprecise := true   -- has homogeneity gap
  , moreComplexImprecise := false  -- gap-less
  , potentiallyPEquivalent := true  -- §3.3.3 def (68)
  , constructionType := "Conjunctions"
  }

/--
Numerals: "100 cars" vs "exactly 100 cars"

Source: [haslinger-2025-diss] Ch 4.2 ex. (4), p. 174 + ex. (9), p. 176
(`CARS(EXACT)` scenario).
-/
def numeralExactly : ComplexityPrecisionPair :=
  { lessComplexExpr := "Ann owns 100 cars."
  , moreComplexExpr := "Ann owns exactly 100 cars."
  , complexitySource := "Addition of 'exactly'"
  , lessComplexImprecise := true   -- permits inexact
  , moreComplexImprecise := false  -- requires exact
  , potentiallyPEquivalent := true  -- §3.3.3 def (68)
  , constructionType := "Numerals"
  }

/--
Summative predicates: "blue" vs "completely blue"

Source: [haslinger-2025-diss] on summative predicates.
-/
def blueCompletely : ComplexityPrecisionPair :=
  { lessComplexExpr := "The flag is blue."
  , moreComplexExpr := "The flag is completely blue."
  , complexitySource := "Addition of 'completely'"
  , lessComplexImprecise := true   -- permits partial coverage
  , moreComplexImprecise := false  -- requires full coverage
  , potentiallyPEquivalent := true  -- §2.4.1 ex. (169a), summative singular predication
  , constructionType := "Summative predicates"
  }

def attestedPairs : List ComplexityPrecisionPair :=
  [doorsAllDoors, andBoth, numeralExactly, blueCompletely]

end FormMeaning


-- ============================================================================
-- §3. Inference Preservation
-- ============================================================================

namespace InferencePreservation

/-- Inference relation between expression and alternative. -/
inductive InferenceRelation where
  | entails         -- φ |= ψ
  | contradicts     -- φ |= ¬ψ
  | independent     -- neither
  deriving Repr, DecidableEq



/--
Numeral alternative blocking datum.

The alternatives of a numeral n include nearby numerals.
If n contradicts m on precise reading, imprecise construal can't
be compatible with m.

Source: [haslinger-2025-diss] Chapter 6, [sauerland-stateva-2007]
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
  , alternativeInSet := true
  , inferenceRelation := .independent
  , imprecisionBlocked := true
  , explanation := "100 is obligatorily in 99's alternative set; an imprecise construal of '99 cars' that included 100 would fail Inference Preservation."
  }

def hundredNotBlocked : NumeralBlockingDatum :=
  { numeral := 100
  , round := true
  , alternative := 99
  , alternativeInSet := false
  , inferenceRelation := .independent
  , imprecisionBlocked := false
  , explanation := "100's coarse-scale alternative set {50, 200, 500, 1000} excludes 99; no alternative to fail against."
  }

/--
The asymmetry depends on conventionalized alternative sets.

Round numbers have "coarse" alternative sets.
Non-round numbers have "fine" alternative sets that include round neighbors.

Source: [haslinger-2025-diss] Chapter 6
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


/--
Conjunction blocking datum.

Conjunctions have conjuncts as alternatives.
"A and B are P" entails "A is P" and "B is P".
Non-maximal reading would fail to preserve these entailments.

Source: [haslinger-2025-diss] Chapter 7
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


/--
Numeral-modified definites: "the four doors"

These have homogeneity gaps but resist non-maximality.
The structural alternative is the numeral *indefinite* (not sub-numerals).

Source: [haslinger-2025-diss] §7.2.3, eq. (11)-(16), p. 305; ftn. 7 p. 309
on the numeral indefinite's lack of homogeneity gap.
-/
structure NumeralDefiniteBlockingDatum where
  /-- The sentence -/
  sentence : String
  /-- The numeral -/
  numeral : Nat
  /-- The structural alternative (numeral indefinite, no definite article) -/
  indefiniteAlternative : String
  /-- Does precise definite reading entail the indefinite alternative? -/
  entailsIndefiniteAlternative : Bool
  /-- Would non-max definite reading entail the indefinite alternative? -/
  nonMaxEntailsAlternative : Bool
  /-- Is non-max blocked? -/
  nonMaxBlocked : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

def fourDoorsBlocking : NumeralDefiniteBlockingDatum :=
  { sentence := "The four doors are open."
  , numeral := 4
  , indefiniteAlternative := "Four doors are open."
  , entailsIndefiniteAlternative := true   -- precise definite ⇒ indefinite
  , nonMaxEntailsAlternative := false      -- 3-of-4 doesn't entail it
  , nonMaxBlocked := true
  , explanation := "Numeral indefinite alternative has no homogeneity gap (covert ∃ binds it); precise definite entails it but non-maximal definite would not."
  }


/--
Collective and cumulative predicates sometimes permit non-maximality
even with conjunctions.

This is an exception that inference preservation needs to handle.

Source: [haslinger-2025-diss] Chapter 7
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
  , nonMaxPossible := true
  , explanation := "'A, B, C met' doesn't entail 'A met' (meeting needs ≥2 participants), so the entailment pattern Inference Preservation tracks does not arise."
  }

def cumulativeCarryException : CollectiveCumulativeException :=
  { sentence := "Ann, Bert, and Claire carried the piano upstairs."
  , predicateType := "cumulative"
  , nonMaxPossible := true
  , explanation := "Many-to-many cumulative readings have weaker entailment patterns than distributive readings."
  }

def numeralBlockingExamples : List NumeralBlockingDatum :=
  [ninetyNineBlocked, hundredNotBlocked]

def conjunctionBlockingExamples : List ConjunctionBlockingDatum :=
  [annBertConjunction, threeStudentsConjunction]

def collectiveExceptions : List CollectiveCumulativeException :=
  [collectiveMeetException, cumulativeCarryException]

end InferencePreservation

end Haslinger2025
