/-
# Degree/Vagueness Fragments

Building blocks for RSA scenarios with gradable adjectives and vagueness.

## Architecture

Semantic primitives (Degree, Threshold, NegationType, HasDegree) live in
`Montague/Lexicon/Degrees.lean`. This module provides:

- **Concrete RSA domains**: Price.World, Height.World, Temperature.World
- **RSA infrastructure**: AdjUtt, DegreeWorld

## Components

- `AdjUtt`: Standard gradable adjective utterances (positive/negative/silent)
- `DegreeWorld`: Joint world state (Degree x Threshold)
- `Price`, `Height`, `Temperature`: Concrete RSA domains

## The Pattern

Vagueness RSA involves:
1. **Degrees**: The underlying scale (height, temperature, etc.)
2. **Thresholds**: Contextual cutoff for "tall", "hot", etc.
3. **Joint inference**: Listener infers both degree and threshold

Key insight: The threshold is a *free variable* that listeners infer.
This explains context-sensitivity and borderline cases.

## References

- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
- Kennedy (2007). Vagueness and grammar.
- Tessler & Franke (2020). Not unreasonable.
- Cruse (1986). Lexical Semantics.
- Horn (1989). A Natural History of Negation.
-/

import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics

namespace RSA.Domains.Degrees

open Core.Scale (Degree Threshold Degree.ofNat Degree.toNat Threshold.toNat
  deg thr allDegrees allThresholds HasDegree)
open Semantics.Lexical.Adjective (positiveMeaning negativeMeaning)
open Semantics.Lexical.Numeral (numeralExact)

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

instance {n : Nat} (_h : 0 < n := by omega) : BEq (DegreeWorld n) := instBEqProd

-- Comparison Class Pattern

/--
Comparison class: the relevant population for determining threshold.

"John is tall for a basketball player" vs "John is tall for a jockey"
have different thresholds based on comparison class.
-/
structure ComparisonClass (max : Nat) where
  name : String
  /-- Typical threshold for this class -/
  typicalThreshold : Threshold max

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
  rcases hw with rfl | rfl | rfl <;> sorry

end RSA.Domains.Degrees
