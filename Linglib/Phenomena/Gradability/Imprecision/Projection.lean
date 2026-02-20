/-
# Projection Patterns: Empirical Data

Theory-neutral empirical patterns for how homogeneity/imprecision projects
under embedding operators.

## Phenomena Covered

1. Under `every`: strong (maximal) reading.
2. Under `no`: strong reading, limited non-maximality.
3. Under `exactly one`: strong reading.
4. Under `not every`: permits non-maximality (asymmetric with `no`).

## Puzzle

Different embedding operators show different patterns for:
- Whether homogeneity gaps project
- Whether non-maximal readings are available

The `no` vs `not every` asymmetry is particularly important.

## References

- Križ & Chemla (2015): Experimental investigation
- Bar-Lev (2021a): Exhaustification approach predictions
- Augurzky et al. (2023): every/no/not every asymmetry
- Križ (2015): Trivalent projection
-/

namespace Phenomena.Gradability.Imprecision.Projection


/--
Types of embedding operators for projection.
-/
inductive EmbeddingOperator where
  | every        -- upward monotonic
  | no           -- downward monotonic
  | exactlyOne   -- non-monotonic
  | exactlyTwo   -- non-monotonic
  | notEvery     -- downward component + scalar implicature
  | atLeastOne   -- upward monotonic
  deriving Repr, DecidableEq

/--
Monotonicity of an operator.
-/
inductive Monotonicity where
  | upward
  | downward
  | nonMonotonic
  deriving Repr, DecidableEq

def monotonicity : EmbeddingOperator → Monotonicity
  | .every => .upward
  | .no => .downward
  | .exactlyOne => .nonMonotonic
  | .exactlyTwo => .nonMonotonic
  | .notEvery => .downward  -- but with implicature making it non-monotonic
  | .atLeastOne => .upward


/--
Projection pattern for a plural under an embedding operator.
-/
structure ProjectionDatum where
  /-- The embedding operator -/
  operator : EmbeddingOperator
  /-- Example sentence -/
  sentence : String
  /-- Gap scenario description -/
  gapScenario : String
  /-- Strong (maximal) reading available? -/
  strongReadingAvailable : Bool
  /-- Weak (existential) reading available? -/
  weakReadingAvailable : Bool
  /-- Homogeneity gap detectable? -/
  gapDetectable : Bool
  /-- Non-maximal reading available? -/
  nonMaximalAvailable : Bool
  deriving Repr


/--
Križ & Chemla (2015) tested these conditions experimentally.

Task: Trivalent truth-value judgment
- "completely true"
- "completely false"
- "neither completely true nor completely false"

Source: Križ & Chemla (2015), Experiments C1-C3
-/

def everyProjection : ProjectionDatum :=
  { operator := .every
  , sentence := "Every boy found his presents."
  , gapScenario := "Every boy found some presents, but not every boy found all"
  , strongReadingAvailable := true   -- "every boy found all his presents"
  , weakReadingAvailable := true     -- "every boy found some presents"
  , gapDetectable := true            -- many "neither" responses
  , nonMaximalAvailable := true      -- some "completely true" in gap scenario
  }

def noProjection : ProjectionDatum :=
  { operator := .no
  , sentence := "No boy found his presents."
  , gapScenario := "Some boys found some presents, no boy found all"
  , strongReadingAvailable := true   -- "no boy found any presents"
  , weakReadingAvailable := true     -- "no boy found all presents"
  , gapDetectable := false           -- few "neither" responses
  , nonMaximalAvailable := false     -- almost no "completely true" in gap
  }

def exactlyTwoProjection : ProjectionDatum :=
  { operator := .exactlyTwo
  , sentence := "Exactly two of the four boys found their presents."
  , gapScenario := "Exactly two found all; more than two found some"
  , strongReadingAvailable := true
  , weakReadingAvailable := true
  , gapDetectable := true
  , nonMaximalAvailable := true
  }


/--
Augurzky et al. (2023) manipulated QUD between participants.

Strict context: QUD targets strongest reading.
Lax context: QUD targets weakest reading.

`no` is less sensitive to QUD manipulation than `every`.

Source: Augurzky et al. (2023), Experiments 1-2
-/
structure QUDManipulationDatum where
  /-- The embedding operator -/
  operator : EmbeddingOperator
  /-- Sentence -/
  sentence : String
  /-- Strict reading (QUD = strong) -/
  strictReading : String
  /-- Lax reading (QUD = weak) -/
  laxReading : String
  /-- Gap scenario -/
  gapScenario : String
  /-- Acceptance rate in STRICT context (gap scenario) -/
  strictContextAcceptance : String  -- "low", "medium", "high"
  /-- Acceptance rate in LAX context (gap scenario) -/
  laxContextAcceptance : String
  /-- Is there an interaction (context effect differs by operator)? -/
  contextEffect : Bool
  deriving Repr

def everyQUDEffect : QUDManipulationDatum :=
  { operator := .every
  , sentence := "Every boy opened his presents."
  , strictReading := "Every boy opened all his presents"
  , laxReading := "Every boy opened some of his presents"
  , gapScenario := "Every boy opened some, not all opened all"
  , strictContextAcceptance := "low"   -- strict QUD → reject in gap
  , laxContextAcceptance := "high"     -- lax QUD → accept in gap
  , contextEffect := true              -- big effect of QUD
  }

def noQUDEffect : QUDManipulationDatum :=
  { operator := .no
  , sentence := "No boy opened his presents."
  , strictReading := "No boy opened any presents"
  , laxReading := "No boy opened all his presents"
  , gapScenario := "Some boys opened some, none opened all"
  , strictContextAcceptance := "low"
  , laxContextAcceptance := "low"      -- still low
  , contextEffect := false             -- small effect of QUD
  }

def notEveryQUDEffect : QUDManipulationDatum :=
  { operator := .notEvery
  , sentence := "Not every boy opened his presents."
  , strictReading := "At least one boy opened none"
  , laxReading := "At least one boy didn't open all"
  , gapScenario := "Some boys opened some but not all"
  , strictContextAcceptance := "low"
  , laxContextAcceptance := "high"     -- unlike `no`
  , contextEffect := true              -- big effect of QUD
  }


/--
`no` resists non-maximality but `not every` permits it,
which is surprising because both are downward-entailing.

Source: Augurzky et al. (2023), Bar-Lev (2021a)
-/
structure NoNotEveryAsymmetryDatum where
  /-- `no` sentence -/
  noSentence : String
  /-- `not every` sentence -/
  notEverySentence : String
  /-- Gap scenario -/
  gapScenario : String
  /-- `no` permits weak reading in gap? -/
  noPermitsWeak : Bool
  /-- `not every` permits weak reading in gap? -/
  notEveryPermitsWeak : Bool
  /-- Theoretical explanation -/
  explanation : String
  deriving Repr

def noNotEveryAsymmetry : NoNotEveryAsymmetryDatum :=
  { noSentence := "No boy opened his presents."
  , notEverySentence := "Not every boy opened his presents."
  , gapScenario := "Half opened all, half opened some but not all"
  , noPermitsWeak := false      -- "no boy opened ALL" reading unavailable
  , notEveryPermitsWeak := true -- "not every boy opened ALL" available
  , explanation := "On exhaustification account: `not every` triggers scalar implicature ('some did'), creating non-monotonic context where exhaustification can strengthen embedded plural. `no` lacks this implicature, so embedded exhaustification has no effect."
  }


/--
Predicted truth conditions for embedded plurals.

Source: Križ & Chemla (2015), Križ (2015)
-/
structure EmbeddedTruthConditions where
  /-- Operator -/
  operator : EmbeddingOperator
  /-- Sentence -/
  sentence : String
  /-- Truth conditions (informal) -/
  truthConditions : String
  /-- Falsity conditions (informal) -/
  falsityConditions : String
  /-- Gap conditions (informal) -/
  gapConditions : String
  deriving Repr

def everyTruthConditions : EmbeddedTruthConditions :=
  { operator := .every
  , sentence := "Every student read the books."
  , truthConditions := "Every student read all the books"
  , falsityConditions := "Some student read none of the books"
  , gapConditions := "Every student read some, at least one didn't read all"
  }

def noTruthConditions : EmbeddedTruthConditions :=
  { operator := .no
  , sentence := "No student read the books."
  , truthConditions := "No student read any of the books"
  , falsityConditions := "Some student read all the books"
  , gapConditions := "Some students read some, none read all"
  }

def exactlyOneTruthConditions : EmbeddedTruthConditions :=
  { operator := .exactlyOne
  , sentence := "Exactly one student read the books."
  , truthConditions := "One student read all, no more than one read any"
  , falsityConditions := "Either no student read all, or more than one read some"
  , gapConditions := "Various mixed scenarios"
  }


/--
Plurals in restrictor vs nuclear scope behave differently.

Source: Mayr & Sudo (2022), Križ (2015)
-/
structure RestrictorScopeDatum where
  /-- Sentence -/
  sentence : String
  /-- Position of plural -/
  pluralPosition : String  -- "restrictor" or "scope"
  /-- Reading available -/
  universalReading : Bool
  /-- Existential reading? -/
  existentialReading : Bool
  /-- Notes -/
  notes : String
  deriving Repr

def pluralInRestrictor : RestrictorScopeDatum :=
  { sentence := "Every immigrant who lives in the five Nordic countries is worried."
  , pluralPosition := "restrictor"
  , universalReading := true  -- "lives in all five"
  , existentialReading := true -- "lives in one of the five"
  , notes := "Existential reading: quantify over immigrants living in at least one Nordic country"
  }

def pluralInScope : RestrictorScopeDatum :=
  { sentence := "Every student read the books."
  , pluralPosition := "scope"
  , universalReading := true
  , existentialReading := false  -- not a default reading
  , notes := "Default is universal; existential requires special context"
  }


/--
Core empirical generalizations about projection.
-/
structure ProjectionGeneralizations where
  /-- Upward monotonic operators: gaps project -/
  upwardMonotonicGapsProject : Bool
  /-- Downward monotonic operators: gaps don't project (for `no`) -/
  noResistsGaps : Bool
  /-- `not every` different from `no` -/
  notEveryDifferentFromNo : Bool
  /-- Non-monotonic operators: gaps project -/
  nonMonotonicGapsProject : Bool
  /-- Strong readings in all cases -/
  strongReadingsUniversal : Bool
  deriving Repr

def mainGeneralizations : ProjectionGeneralizations :=
  { upwardMonotonicGapsProject := true
  , noResistsGaps := true
  , notEveryDifferentFromNo := true
  , nonMonotonicGapsProject := true
  , strongReadingsUniversal := true
  }

-- Collections

def krizChemlaData : List ProjectionDatum :=
  [everyProjection, noProjection, exactlyTwoProjection]

def augurzkyData : List QUDManipulationDatum :=
  [everyQUDEffect, noQUDEffect, notEveryQUDEffect]

def truthConditionsData : List EmbeddedTruthConditions :=
  [everyTruthConditions, noTruthConditions, exactlyOneTruthConditions]

end Phenomena.Gradability.Imprecision.Projection
