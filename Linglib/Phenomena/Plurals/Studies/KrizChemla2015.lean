/-!
# @cite{kriz-chemla-2015}: Trivalent truth-value judgments for embedded plurals

Empirical data from Manuel Križ and Emmanuel Chemla (2015), "Two methods to
find truth-value gaps and their application to the projection problem of
homogeneity," *Natural Language Semantics*. Križ & Chemla introduce a trivalent
judgment task ("completely true" / "completely false" / "neither completely
true nor completely false") and use it to test how homogeneity gaps for plural
definites project under embedding operators (`every`, `no`, `exactly N`).

## Empirical contribution

For sentences embedding plural definites under quantifiers:

- **`every` (upward monotonic)**: gaps DETECTABLE — many "neither" responses
  in scenarios where every boy found *some* but not *all* his presents.
- **`no` (downward monotonic)**: gaps NOT detectable — few "neither" responses
  in scenarios where some boys found some but no boy found all presents.
- **`exactly N` (non-monotonic)**: gaps DETECTABLE — pattern matches `every`.

The `no`/`every` asymmetry is the empirical puzzle that motivates Križ's later
formal work (`@cite{kriz-2016}`) and the extension by `@cite{bar-lev-2021}` and
`@cite{augurzky-etal-2023}`.

## Provenance

This data was previously bundled inside `Phenomena/Imprecision/Projection.lean`
and then `Studies/Haslinger2025.lean`. Moved here at
0.230.521 because the empirical anchor is Križ & Chemla 2015 — Haslinger 2025
discusses these data points in Ch 7 but as a published-result substrate, not as
her own original observation.

-/

namespace Phenomena.Plurals.Studies.KrizChemla2015

/--
Types of embedding operators for projection studies.
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

Source: @cite{kriz-chemla-2015}, Experiments C1-C3.
Task: trivalent truth-value judgment ("completely true" / "completely false" /
"neither").
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
  /-- Homogeneity gap detectable (many "neither" responses)? -/
  gapDetectable : Bool
  /-- Non-maximal reading available (some "completely true" in gap)? -/
  nonMaximalAvailable : Bool
  deriving Repr

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
Predicted truth conditions for embedded plurals.

Source: @cite{kriz-chemla-2015} + Križ (2015) dissertation.
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


-- Collections

def projectionData : List ProjectionDatum :=
  [everyProjection, noProjection, exactlyTwoProjection]

def truthConditionsData : List EmbeddedTruthConditions :=
  [everyTruthConditions, noTruthConditions, exactlyOneTruthConditions]

end Phenomena.Plurals.Studies.KrizChemla2015
