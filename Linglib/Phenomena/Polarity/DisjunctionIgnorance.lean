/-
# Disjunction Ignorance: Empirical Data

Theory-neutral empirical patterns for ignorance inferences from disjunction.

## The Pattern

"Harry is in Antwerp or Brussels" implicates:
1. Speaker doesn't know Harry is in Antwerp
2. Speaker doesn't know Harry is in Brussels

This is different from scalar implicature:
- Scalar: "some" → speaker KNOWS not all
- Ignorance: "A or B" → speaker DOESN'T KNOW which

## Key References

- Gazdar, G. (1979). Pragmatics: Implicature, Presupposition, and Logical Form.
- Sauerland, U. (2004). Scalar Implicatures in Complex Sentences.
- Geurts, B. (2010). Quantity Implicatures. Ch. 3.3.
-/

namespace Phenomena.Polarity.DisjunctionIgnorance


/--
Empirical pattern: Disjunction and speaker ignorance.

"Harry is in Antwerp or Brussels" implicates:
1. Speaker doesn't know Harry is in Antwerp
2. Speaker doesn't know Harry is in Brussels

Source: Gazdar (1979), Geurts (2010) Ch. 3.3
-/
structure DisjunctionIgnoranceDatum where
  /-- The disjunctive statement -/
  disjunction : String
  /-- First disjunct -/
  disjunctA : String
  /-- Second disjunct -/
  disjunctB : String
  /-- Ignorance inference about A -/
  inferenceA : String
  /-- Ignorance inference about B -/
  inferenceB : String
  deriving Repr

/--
Classic example: Harry's location.
Source: Geurts (2010) p.61
-/
def harryLocation : DisjunctionIgnoranceDatum :=
  { disjunction := "Harry is in Antwerp or Brussels"
  , disjunctA := "Harry is in Antwerp"
  , disjunctB := "Harry is in Brussels"
  , inferenceA := "Speaker doesn't know Harry is in Antwerp"
  , inferenceB := "Speaker doesn't know Harry is in Brussels"
  }

/--
Location example with Mary.
-/
def maryLocation : DisjunctionIgnoranceDatum :=
  { disjunction := "Mary went to Paris or London"
  , disjunctA := "Mary went to Paris"
  , disjunctB := "Mary went to London"
  , inferenceA := "Speaker doesn't know Mary went to Paris"
  , inferenceB := "Speaker doesn't know Mary went to London"
  }

/--
Activity example.
-/
def johnActivity : DisjunctionIgnoranceDatum :=
  { disjunction := "John is reading or sleeping"
  , disjunctA := "John is reading"
  , disjunctB := "John is sleeping"
  , inferenceA := "Speaker doesn't know John is reading"
  , inferenceB := "Speaker doesn't know John is sleeping"
  }

/--
All basic ignorance examples.
-/
def disjunctionIgnoranceExamples : List DisjunctionIgnoranceDatum :=
  [harryLocation, maryLocation, johnActivity]


/--
Comparison between ignorance and scalar implicatures.

Key difference:
- Scalar: Speaker KNOWS the stronger alternative is false
- Ignorance: Speaker DOESN'T KNOW which disjunct is true
-/
structure IgnoranceVsScalarDatum where
  /-- The utterance -/
  utterance : String
  /-- Type of inference -/
  inferenceType : String
  /-- The inference -/
  inference : String
  /-- Is speaker claiming knowledge? -/
  speakerClaimsKnowledge : Bool
  deriving Repr

/--
"Some" triggers scalar implicature (speaker knows).
-/
def someScalar : IgnoranceVsScalarDatum :=
  { utterance := "Some students passed"
  , inferenceType := "scalar"
  , inference := "Speaker believes not all students passed"
  , speakerClaimsKnowledge := true  -- Speaker KNOWS not all
  }

/--
"Or" triggers ignorance (speaker doesn't know).
-/
def orIgnorance : IgnoranceVsScalarDatum :=
  { utterance := "John passed or Mary passed"
  , inferenceType := "ignorance"
  , inference := "Speaker doesn't know which one passed"
  , speakerClaimsKnowledge := false  -- Speaker DOESN'T KNOW
  }

/--
All comparison examples.
-/
def comparisonExamples : List IgnoranceVsScalarDatum :=
  [someScalar, orIgnorance]


/--
Ignorance extends to long disjunctions (n > 2).

For "A or B or C", we get ignorance about each disjunct:
- Speaker doesn't know A
- Speaker doesn't know B
- Speaker doesn't know C

Source: Geurts (2010) p.61-64
-/
structure LongDisjunctionIgnoranceDatum where
  /-- The disjunctive statement -/
  disjunction : String
  /-- List of disjuncts -/
  disjuncts : List String
  /-- Ignorance inferences (one per disjunct) -/
  ignoranceInferences : List String
  deriving Repr

/--
Three-way disjunction example.
Source: Geurts (2010) p.61
-/
def threeWayLocation : LongDisjunctionIgnoranceDatum :=
  { disjunction := "Harry is in Antwerp, Brussels, or Copenhagen"
  , disjuncts := ["Antwerp", "Brussels", "Copenhagen"]
  , ignoranceInferences :=
      [ "Speaker doesn't know Harry is in Antwerp"
      , "Speaker doesn't know Harry is in Brussels"
      , "Speaker doesn't know Harry is in Copenhagen"
      ]
  }

/--
Four-way disjunction example.
-/
def fourWayActivity : LongDisjunctionIgnoranceDatum :=
  { disjunction := "John is reading, writing, sleeping, or eating"
  , disjuncts := ["reading", "writing", "sleeping", "eating"]
  , ignoranceInferences :=
      [ "Speaker doesn't know John is reading"
      , "Speaker doesn't know John is writing"
      , "Speaker doesn't know John is sleeping"
      , "Speaker doesn't know John is eating"
      ]
  }

/--
All long disjunction examples.
-/
def longDisjunctionExamples : List LongDisjunctionIgnoranceDatum :=
  [threeWayLocation, fourWayActivity]


/--
Cases where ignorance inference is blocked or cancelled.
-/
structure IgnoranceBlockingDatum where
  /-- The context or construction -/
  context : String
  /-- Example sentence -/
  sentence : String
  /-- Is ignorance blocked? -/
  ignoranceBlocked : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

/--
Explicit knowledge blocks ignorance.
-/
def explicitKnowledge : IgnoranceBlockingDatum :=
  { context := "Speaker has explicit knowledge"
  , sentence := "Harry is in Antwerp or Brussels — I know it's Antwerp"
  , ignoranceBlocked := true
  , explanation := "Explicit assertion of knowledge cancels ignorance inference"
  }

/--
Rhetorical questions don't trigger ignorance.
-/
def rhetoricalQuestion : IgnoranceBlockingDatum :=
  { context := "Rhetorical/exam question"
  , sentence := "Is the capital of France Paris or London?"
  , ignoranceBlocked := true
  , explanation := "Speaker (examiner) knows the answer; no genuine ignorance"
  }

/--
Embedded disjunction under belief.
-/
def embeddedBelief : IgnoranceBlockingDatum :=
  { context := "Embedded under belief verb"
  , sentence := "John believes Harry is in Antwerp or Brussels"
  , ignoranceBlocked := true
  , explanation := "Ignorance is about John's epistemic state, not speaker's"
  }

/--
All blocking examples.
-/
def blockingExamples : List IgnoranceBlockingDatum :=
  [explicitKnowledge, rhetoricalQuestion, embeddedBelief]


/--
Interaction between disjunction ignorance and quantifiers.
-/
structure QuantifiedIgnoranceDatum where
  /-- The sentence -/
  sentence : String
  /-- Quantifier scope -/
  quantifierScope : String
  /-- Ignorance inference -/
  inference : String
  /-- Notes on the reading -/
  notes : String
  deriving Repr

/--
Disjunction in scope of universal.
-/
def universalScopeDisj : QuantifiedIgnoranceDatum :=
  { sentence := "Every student read Moby Dick or Huckleberry Finn"
  , quantifierScope := "∀ > ∨"
  , inference := "Speaker doesn't know which book each student read"
  , notes := "Ignorance is about the distribution, not existence"
  }

/--
Disjunction scoping over universal.
-/
def disjScopeUniversal : QuantifiedIgnoranceDatum :=
  { sentence := "Every student read Moby Dick, or every student read Huckleberry Finn"
  , quantifierScope := "∨ > ∀"
  , inference := "Speaker doesn't know which book ALL students read"
  , notes := "Global ignorance about which alternative"
  }

/--
All quantified ignorance examples.
-/
def quantifiedIgnoranceExamples : List QuantifiedIgnoranceDatum :=
  [universalScopeDisj, disjScopeUniversal]


/-!
## Positional Asymmetry in Disjunction Interpretation

Chierchia (2013) "Logic in Grammar" Ch.1 observes that the SAME lexical
material yields different PREFERRED readings based on structural position:

| Position | Polarity | Preferred Reading |
|----------|----------|-------------------|
| Consequent of conditional | UE | Exclusive |
| Antecedent of conditional | DE | Inclusive |
| Scope of "every" | UE | Exclusive |
| Restrictor of "every" | DE | Inclusive |
| Positive sentence | UE | Exclusive |
| Negative sentence | DE | Inclusive |

### The Core Pattern

**UE contexts**: Exclusive reading preferred
- "If everything goes well, we'll hire Mary or Sue"
- Default: we'll hire exactly one of them

**DE contexts**: Inclusive reading preferred
- "If we hire Mary or Sue, everything will go well"
- Default: hiring either or both leads to success

### Explanation via Maximize Strength

The asymmetry follows from the Maximize Strength principle:
- In UE: Adding "not both" STRENGTHENS → compute SI
- In DE: Adding "not both" would WEAKEN → don't compute SI

When the exclusive SI is not computed, the inclusive reading emerges.

### References

- Chierchia (2013). Logic in Grammar. Cambridge. Ch.1.
- See also: Theories/NeoGricean/Exhaustivity/Basic.lean (Maximize Strength)
-/

/--
Type of disjunction interpretation.
-/
inductive DisjunctionReading where
  | inclusive   -- p ∨ q (possibly both)
  | exclusive   -- (p ∨ q) ∧ ¬(p ∧ q) (not both)
  deriving DecidableEq, BEq, Repr

/--
Structural position of the disjunction.
-/
inductive DisjunctionPosition where
  | matrix            -- Main clause
  | conditional_cons  -- Consequent of conditional (UE)
  | conditional_ant   -- Antecedent of conditional (DE)
  | every_scope       -- Scope of "every" (UE)
  | every_restrictor  -- Restrictor of "every" (DE)
  | negation_scope    -- Under negation (DE)
  deriving DecidableEq, BEq, Repr

/--
Context polarity: upward-entailing or downward-entailing.
-/
inductive ContextPolarity' where
  | upward    -- ∀: if φ ⊆ ψ then C(φ) ⊆ C(ψ)
  | downward  -- ∀: if φ ⊆ ψ then C(ψ) ⊆ C(φ)
  deriving DecidableEq, BEq, Repr

/--
Determine context polarity from position.
-/
def positionPolarity : DisjunctionPosition → ContextPolarity'
  | .matrix => .upward
  | .conditional_cons => .upward
  | .conditional_ant => .downward
  | .every_scope => .upward
  | .every_restrictor => .downward
  | .negation_scope => .downward

/--
Predict preferred reading from polarity.
UE → exclusive (SI computed), DE → inclusive (SI not computed).
-/
def predictReading : ContextPolarity' → DisjunctionReading
  | .upward => .exclusive
  | .downward => .inclusive

/--
Example showing exclusive/inclusive asymmetry.
-/
structure ExclusiveInclusiveExample where
  /-- The sentence -/
  sentence : String
  /-- Position of disjunction -/
  position : DisjunctionPosition
  /-- Polarity of that position -/
  polarity : ContextPolarity'
  /-- Preferred reading -/
  preferredReading : DisjunctionReading
  /-- Can the other reading be forced with context? -/
  canForceOther : Bool
  /-- Source -/
  source : String
  deriving Repr

-- Chierchia (2013) examples (1a,b)
def hiring_consequent : ExclusiveInclusiveExample :=
  { sentence := "If everything goes well, we'll hire Mary or Sue"
  , position := .conditional_cons
  , polarity := .upward
  , preferredReading := .exclusive
  , canForceOther := true
  , source := "Chierchia (2013) p.2 (1a)"
  }

def hiring_antecedent : ExclusiveInclusiveExample :=
  { sentence := "If we hire Mary or Sue, everything will go well"
  , position := .conditional_ant
  , polarity := .downward
  , preferredReading := .inclusive
  , canForceOther := true
  , source := "Chierchia (2013) p.2 (1b)"
  }

-- Matrix clause example
def matrix_exclusive : ExclusiveInclusiveExample :=
  { sentence := "We'll hire Mary or Sue"
  , position := .matrix
  , polarity := .upward
  , preferredReading := .exclusive
  , canForceOther := true
  , source := "Standard observation"
  }

-- Universal restrictor vs scope
def every_scope : ExclusiveInclusiveExample :=
  { sentence := "Everyone likes Mary or Sue"
  , position := .every_scope
  , polarity := .upward
  , preferredReading := .exclusive
  , canForceOther := true
  , source := "Chierchia (2013) discussion"
  }

def every_restrictor : ExclusiveInclusiveExample :=
  { sentence := "Everyone who likes Mary or Sue will be happy"
  , position := .every_restrictor
  , polarity := .downward
  , preferredReading := .inclusive
  , canForceOther := true
  , source := "Chierchia (2013) discussion"
  }

-- Negation scope
def negation_scope : ExclusiveInclusiveExample :=
  { sentence := "We won't hire Mary or Sue"
  , position := .negation_scope
  , polarity := .downward
  , preferredReading := .inclusive
  , canForceOther := true
  , source := "De Morgan reading: ¬M ∧ ¬S"
  }

/--
All exclusive/inclusive examples.
-/
def exclusiveInclusiveExamples : List ExclusiveInclusiveExample :=
  [ hiring_consequent, hiring_antecedent
  , matrix_exclusive
  , every_scope, every_restrictor
  , negation_scope
  ]

-- Verify predictions match data
#guard exclusiveInclusiveExamples.all (fun ex =>
  predictReading ex.polarity == ex.preferredReading)


/-!
## Forcing Non-Preferred Readings

While polarity determines the DEFAULT reading, context can FORCE the
non-preferred interpretation:

### Forcing Inclusive in UE (harder)
"If everything goes well, we'll hire Mary or Sue, or both."
- Explicit "or both" forces inclusive

### Forcing Exclusive in DE (harder)
"If we hire Mary or Sue but not both, everything will go well."
- Explicit "but not both" forces exclusive

The key observation: forcing requires EXPLICIT marking.
The unmarked reading follows from Maximize Strength.
-/

/--
Example of forcing a non-preferred reading.
-/
structure ForcedReadingExample where
  /-- The base sentence -/
  baseSentence : String
  /-- Position (determines default) -/
  position : DisjunctionPosition
  /-- Default reading -/
  defaultReading : DisjunctionReading
  /-- Forcing phrase -/
  forcingPhrase : String
  /-- Resulting reading -/
  forcedReading : DisjunctionReading
  /-- Notes -/
  notes : String
  deriving Repr

def force_inclusive_ue : ForcedReadingExample :=
  { baseSentence := "If everything goes well, we'll hire Mary or Sue"
  , position := .conditional_cons
  , defaultReading := .exclusive
  , forcingPhrase := "or both"
  , forcedReading := .inclusive
  , notes := "Adding 'or both' explicitly licenses inclusive reading"
  }

def force_exclusive_de : ForcedReadingExample :=
  { baseSentence := "If we hire Mary or Sue, everything will go well"
  , position := .conditional_ant
  , defaultReading := .inclusive
  , forcingPhrase := "but not both"
  , forcedReading := .exclusive
  , notes := "Adding 'but not both' explicitly restricts to exclusive"
  }

/--
All forced reading examples.
-/
def forcedReadingExamples : List ForcedReadingExample :=
  [force_inclusive_ue, force_exclusive_de]

-- Summary

/-
## What This Module Provides

### Data Types
- `DisjunctionIgnoranceDatum`: Basic ignorance pattern
- `IgnoranceVsScalarDatum`: Comparison with scalar implicatures
- `LongDisjunctionIgnoranceDatum`: Ignorance with n>2 disjuncts
- `IgnoranceBlockingDatum`: Cases where ignorance is blocked
- `QuantifiedIgnoranceDatum`: Interaction with quantifiers

### Example Collections
- `disjunctionIgnoranceExamples`: 3 basic examples
- `comparisonExamples`: 2 scalar vs ignorance examples
- `longDisjunctionExamples`: 2 long disjunction examples
- `blockingExamples`: 3 blocking contexts
- `quantifiedIgnoranceExamples`: 2 quantifier interactions
- `exclusiveInclusiveExamples`: 6 polarity-dependent reading examples
- `forcedReadingExamples`: 2 context-forcing examples

### Exclusive/Inclusive Asymmetry (Chierchia 2013)
- `DisjunctionReading`: inclusive vs exclusive
- `DisjunctionPosition`: structural position types
- `positionPolarity`: map position to polarity
- `predictReading`: predict reading from polarity
- `ExclusiveInclusiveExample`: empirical data structure

### Key Predictions
- UE contexts → exclusive (SI computed)
- DE contexts → inclusive (SI not computed)
- Non-preferred readings require explicit marking

### Key References
- Gazdar (1979): Original observation
- Sauerland (2004): Compositional analysis
- Geurts (2010): Modern synthesis
- Chierchia (2013): Exclusive/inclusive asymmetry
-/

end Phenomena.Polarity.DisjunctionIgnorance
