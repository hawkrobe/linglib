/-
# Degree/Vagueness Fragments

Building blocks for RSA scenarios with gradable adjectives and vagueness.

## Architecture

Semantic primitives (Degree, Threshold, NegationType, HasDegree) live in
`Montague/Lexicon/Degrees.lean`. This module provides:

- **Concrete RSA domains**: Price.World, Height.World, Temperature.World
- **RSA infrastructure**: AdjUtt, DegreeWorld, scenario builders

## Components

- `AdjUtt`: Standard gradable adjective utterances (positive/negative/silent)
- `DegreeWorld`: Joint world state (Degree x Threshold)
- `tallShort`: Scenario builder for height domain
- `Price`, `Height`, `Temperature`: Concrete RSA domains

## The Pattern

Vagueness RSA involves:
1. **Degrees**: The underlying scale (height, temperature, etc.)
2. **Thresholds**: Contextual cutoff for "tall", "hot", etc.
3. **Joint inference**: Listener infers both degree and threshold

Key insight: The threshold is a *free variable* that listeners infer.
This explains context-sensitivity and borderline cases.

## Usage

```lean
import Linglib.Theories.Pragmatics.RSA.Domains.Degrees

-- Height domain with 11 degrees (0..10)
def scenario := Degrees.tallShort 10

#eval RSAL.L1_world scenario .tall
-- Infers both height and threshold jointly
```

## References

- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
- Kennedy (2007). Vagueness and grammar.
- Tessler & Franke (2020). Not unreasonable.
- Cruse (1986). Lexical Semantics.
- Horn (1989). A Natural History of Negation.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Mathlib.Data.Rat.Defs

namespace RSA.Domains.Degrees

open Core.Scale (Degree Threshold Degree.ofNat Degree.toNat Threshold.toNat
  deg thr allDegrees allThresholds HasDegree)
open TruthConditional.Adjective (positiveMeaning negativeMeaning)
open TruthConditional.Numeral (numeralExact)

-- Utterances

/-- Standard gradable adjective utterances -/
inductive AdjUtt where
  | positive  -- "tall", "hot", etc.
  | negative  -- "short", "cold", etc.
  | silent    -- say nothing
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Meaning under threshold -/
def adjMeaning {max : Nat} (u : AdjUtt) (d : Degree max) (t : Threshold max) : Bool :=
  match u with
  | .positive => positiveMeaning d t
  | .negative => negativeMeaning d t
  | .silent => true

-- Joint World: Degree x Threshold

/--
Joint world state for vagueness: both degree and threshold.

The key insight from Lassiter & Goodman (2017): listeners jointly infer
both the degree value AND the contextual threshold.
-/
abbrev DegreeWorld (max : Nat) := Degree max × Threshold max

/-- All joint worlds -/
def allDegreeWorlds (max : Nat) (h : 0 < max := by omega) : List (DegreeWorld max) :=
  (allDegrees max).flatMap λ d =>
    (allThresholds max h).map λ t => (d, t)

instance {n : Nat} (h : 0 < n := by omega) : BEq (DegreeWorld n) := instBEqProd

-- Scenario Builders

/--
Tall/short scenario with threshold inference.

The listener jointly infers:
- The degree (how tall is the person?)
- The threshold (what counts as "tall" in this context?)
-/
def tallShort (max : Nat) (h : 0 < max := by omega) (u : AdjUtt) : List (DegreeWorld max × ℚ) :=
  RSA.Eval.basicL1
    [AdjUtt.positive, .negative, .silent]
    (allDegreeWorlds max h)
    (λ utt (d, t) => boolToRat (adjMeaning utt d t))
    (λ _ => 1) 1 (λ _ => 0) u

/--
Scenario with custom prior over degrees.

Often degrees have a prior (e.g., height is roughly normal).
-/
def withDegreePrior (max : Nat) (h : 0 < max := by omega)
    (degreePrior : Degree max → ℚ)
    (thresholdPrior : Threshold max → ℚ := λ _ => 1)
    (u : AdjUtt)
    : List (DegreeWorld max × ℚ) :=
  let worldPrior : DegreeWorld max → ℚ := λ (d, t) => degreePrior d * thresholdPrior t
  RSA.Eval.basicL1
    [AdjUtt.positive, .negative, .silent]
    (allDegreeWorlds max h)
    (λ utt (d, t) => boolToRat (adjMeaning utt d t))
    worldPrior 1 (λ _ => 0) u

-- Graded (Non-Boolean) Semantics

/--
Graded meaning: returns a value in [0, 1] instead of Bool.

For fuzzy boundaries, the meaning can be probabilistic:
- P("tall" | d, theta) could be a sigmoid around theta

This is for more sophisticated models; the Boolean version suffices for many cases.
-/
def gradedPositive {max : Nat} (d : Degree max) (t : Threshold max) : ℚ :=
  if d.toNat > t.toNat then 1 else 0  -- Step function (simplest)

/--
Sigmoid-like graded meaning (discrete approximation).

Smoother transition around threshold.
-/
def sigmoidMeaning {max : Nat} (d : Degree max) (t : Threshold max) (_sharpness : ℚ := 2)
    : ℚ :=
  let diff : Int := d.toNat - t.toNat
  if diff > 2 then 1
  else if diff < -2 then 0
  else (diff + 3) / 6  -- Linear approximation in transition zone

-- Comparison Class Pattern

/--
Comparison class: the relevant population for determining threshold.

"John is tall for a basketball player" vs "John is tall for a jockey"
have different thresholds based on comparison class.
-/
structure ComparisonClass (max : Nat) where
  name : String
  /-- Prior over degrees in this class -/
  prior : Degree max → ℚ
  /-- Typical threshold for this class -/
  typicalThreshold : Threshold max

-- Examples

-- Height domain 0..10
#eval tallShort 10 (by omega) .positive
-- Infers high degree values more likely

-- Check semantics
#eval positiveMeaning (Degree.ofNat 10 8) (⟨⟨5, by omega⟩⟩ : Threshold 10)  -- true
#eval positiveMeaning (Degree.ofNat 10 3) (⟨⟨5, by omega⟩⟩ : Threshold 10)  -- false

-- Domain: Prices (for Kao et al. 2014 hyperbole)

namespace Price

/-- A world characterized by its price -/
structure World where
  value : ℚ
  deriving Repr, DecidableEq, BEq

instance : HasDegree World where
  degree := World.value

/-- Common price levels -/
def low : World := ⟨50⟩
def medium : World := ⟨500⟩
def high : World := ⟨10000⟩

/-- Price utterances (stated dollar amounts) -/
inductive Utterance where
  | fifty       -- "$50"
  | fiveHundred -- "$500"
  | tenThousand -- "$10,000"
  | million     -- "$1,000,000" (typically hyperbolic)
  deriving Repr, DecidableEq, BEq

def Utterance.value : Utterance → ℚ
  | .fifty => 50
  | .fiveHundred => 500
  | .tenThousand => 10000
  | .million => 1000000

/-- Literal semantics: stated amount = actual price -/
def meaning (u : Utterance) (w : World) : Bool :=
  numeralExact u.value w

def standardWorlds : List World := [low, medium, high]
def standardUtterances : List Utterance := [.fifty, .fiveHundred, .tenThousand, .million]

/-- Run L1 inference for a price utterance -/
def runL1 (u : Utterance) : List (World × ℚ) :=
  RSA.Eval.basicL1 standardUtterances standardWorlds
    (λ utt w => boolToRat (meaning utt w)) (λ _ => 1) 1 (λ _ => 0) u

end Price

-- Domain: Heights

namespace Height

/-- A world characterized by height (in cm) -/
structure World where
  value : ℚ
  deriving Repr, DecidableEq, BEq

instance : HasDegree World where
  degree := World.value

/-- Height utterances -/
inductive Utterance where
  | fiveFeet    -- ~152 cm
  | sixFeet     -- ~183 cm
  | sevenFeet   -- ~213 cm
  | tenFeet     -- ~305 cm (hyperbolic for humans)
  deriving Repr, DecidableEq, BEq

def Utterance.value : Utterance → ℚ
  | .fiveFeet => 152
  | .sixFeet => 183
  | .sevenFeet => 213
  | .tenFeet => 305

def meaning (u : Utterance) (w : World) : Bool :=
  numeralExact u.value w

end Height

-- Domain: Temperature

namespace Temperature

/-- A world characterized by temperature (in C) -/
structure World where
  value : ℚ
  deriving Repr, DecidableEq, BEq

instance : HasDegree World where
  degree := World.value

end Temperature

-- Grounding Theorems

/-- Price meaning uses the HasDegree instance -/
theorem price_uses_degree (u : Price.Utterance) (w : Price.World) :
    Price.meaning u w = (HasDegree.degree w == u.value) := rfl

/-- "Million dollars" never literally matches standard prices -/
theorem million_never_literal :
    ∀ w ∈ Price.standardWorlds, Price.meaning .million w = false := by
  intro w hw
  simp [Price.standardWorlds] at hw
  rcases hw with rfl | rfl | rfl <;> native_decide

-- RSA Convenience (Prices)

def Price.l0 (u : Price.Utterance) : List (Price.World × ℚ) :=
  RSA.Eval.basicL0 Price.standardUtterances Price.standardWorlds
    (λ utt w => boolToRat (Price.meaning utt w)) (λ _ => 1) u

def Price.s1 (w : Price.World) : List (Price.Utterance × ℚ) :=
  RSA.Eval.basicS1 Price.standardUtterances Price.standardWorlds
    (λ utt world => boolToRat (Price.meaning utt world)) (λ _ => 1) 1 (λ _ => 0) w

def Price.l1 (u : Price.Utterance) : List (Price.World × ℚ) :=
  Price.runL1 u

#eval Price.l0 .fifty        -- Only low price matches
#eval Price.l0 .million      -- Empty (never literally true)
#eval Price.s1 Price.high    -- Prefers "ten thousand"

end RSA.Domains.Degrees
