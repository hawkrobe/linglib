/-
# Degree/Vagueness Fragments

Building blocks for RSA scenarios with gradable adjectives and vagueness.

## Components

- `Degree n`: Discretized degree scale (0..n)
- `Threshold`: Cutoff for positive/negative form
- `NegationType`: Contradictory vs. contrary negation
- `gradedMeaning`: Threshold-relative semantics
- `thresholdScenario`: Joint inference over degrees and thresholds

## The Pattern

Vagueness RSA involves:
1. **Degrees**: The underlying scale (height, temperature, etc.)
2. **Thresholds**: Contextual cutoff for "tall", "hot", etc.
3. **Joint inference**: Listener infers both degree and threshold

Key insight: The threshold is a *free variable* that listeners infer.
This explains context-sensitivity and borderline cases.

## Negation: Contradictory vs. Contrary

This module provides infrastructure for modeling both types of negation:

**Contradictory negation** (logical complement):
- "not happy" = degree ≤ θ (everything that's not happy)
- P and ¬P partition the space: exactly one must be true
- No gap: every degree is either "happy" or "not happy"

**Contrary negation** (polar opposite):
- "unhappy" = degree < θ_neg where θ_neg < θ_pos
- P and Q can both be false: the gap region
- Gap: θ_neg ≤ degree ≤ θ_pos is "neither happy nor unhappy"

This distinction explains why "not unhappy" ≠ "happy":
- "not unhappy" = degree ≥ θ_neg (includes gap + happy region)
- "happy" = degree > θ_pos (only happy region)

## Usage

```lean
import Linglib.Fragments.Degrees

-- Height domain with 11 degrees (0..10)
def scenario := Degrees.tallShort 10

#eval RSA.L1_world scenario .tall
-- Infers both height and threshold jointly
```

## References

- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
- Kennedy (2007). Vagueness and grammar.
- Tessler & Franke (2020). Not unreasonable: Why two negatives don't make a positive.
- Cruse (1986). Lexical Semantics (contraries vs. contradictories).
- Horn (1989). A Natural History of Negation.
-/

import Linglib.Theories.RSA.Core.Basic
import Mathlib.Data.Rat.Defs

namespace Degrees

-- ============================================================================
-- Degree Values
-- ============================================================================

/--
A degree on a scale from 0 to max.

Represents discretized continuous values like height, temperature, etc.
-/
structure Degree (max : Nat) where
  value : Fin (max + 1)
  deriving Repr, DecidableEq, BEq

instance {n : Nat} : Inhabited (Degree n) := ⟨⟨0, Nat.zero_lt_succ n⟩⟩

/-- All degrees from 0 to max -/
def allDegrees (max : Nat) : List (Degree max) :=
  List.finRange (max + 1) |>.map (⟨·⟩)

/-- Degree from Nat (clamped) -/
def Degree.ofNat (max : Nat) (n : Nat) : Degree max :=
  ⟨⟨min n max, by omega⟩⟩

/-- Get numeric value -/
def Degree.toNat {max : Nat} (d : Degree max) : Nat := d.value.val

-- ============================================================================
-- Thresholds
-- ============================================================================

/--
A threshold for a gradable adjective.

x is "tall" iff degree(x) > threshold
-/
structure Threshold (max : Nat) where
  value : Fin max  -- threshold < max (so at least one thing can be tall)
  deriving Repr, DecidableEq, BEq

instance {n : Nat} (h : 0 < n := by omega) : Inhabited (Threshold n) := ⟨⟨0, h⟩⟩

/-- All thresholds from 0 to max-1 -/
def allThresholds (max : Nat) (h : 0 < max := by omega) : List (Threshold max) :=
  List.finRange max |>.map (⟨·⟩)

/-- Get numeric value -/
def Threshold.toNat {max : Nat} (t : Threshold max) : Nat := t.value.val

-- ============================================================================
-- Negation Types: Contradictory vs. Contrary
-- ============================================================================

/--
Types of negation for gradable adjectives.

From traditional logic (Square of Opposition) and lexical semantics:

**Contradictories** (e.g., "happy" / "not happy"):
- Cannot both be true AND cannot both be false
- Exactly one must hold for any degree
- "not happy" = ¬(degree > θ) = degree ≤ θ

**Contraries** (e.g., "happy" / "unhappy"):
- Cannot both be true BUT can both be false
- Gap region where neither holds
- "happy" = degree > θ_pos, "unhappy" = degree < θ_neg, gap = θ_neg ≤ d ≤ θ_pos

The key insight: morphological antonyms ("unhappy") are typically CONTRARY,
not contradictory. This is why "not unhappy" ≠ "happy".

References:
- Cruse (1986). Lexical Semantics.
- Horn (1989). A Natural History of Negation.
- Tessler & Franke (2020). Not unreasonable: Why two negatives don't make a positive.
-/
inductive NegationType where
  /-- Contradictory: logical complement, no gap. ¬(d > θ) = d ≤ θ -/
  | contradictory
  /-- Contrary: polar opposite with gap. d < θ_neg where θ_neg < θ_pos -/
  | contrary
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Two-Threshold Model for Contrary Antonyms
-- ============================================================================

/--
A threshold pair for contrary antonyms.

For contrary pairs like happy/unhappy:
- θ_pos: threshold for positive form (degree > θ_pos → "happy")
- θ_neg: threshold for negative form (degree < θ_neg → "unhappy")
- Constraint: θ_neg ≤ θ_pos (gap exists when θ_neg < θ_pos)

The gap region θ_neg ≤ degree ≤ θ_pos is "neither happy nor unhappy".
-/
structure ThresholdPair (max : Nat) where
  /-- Threshold for positive form ("happy") -/
  pos : Threshold max
  /-- Threshold for negative form ("unhappy") -/
  neg : Threshold max
  /-- Gap constraint: neg threshold ≤ pos threshold -/
  gap_exists : neg.toNat ≤ pos.toNat := by decide
  deriving Repr

instance {n : Nat} (h : 0 < n := by omega) : Inhabited (ThresholdPair n) :=
  ⟨{ pos := ⟨⟨0, h⟩⟩, neg := ⟨⟨0, h⟩⟩, gap_exists := le_refl _ }⟩

/-- Threshold pair equality (ignore proof) -/
instance {n : Nat} : BEq (ThresholdPair n) where
  beq t1 t2 := t1.pos == t2.pos && t1.neg == t2.neg

instance {n : Nat} : DecidableEq (ThresholdPair n) :=
  fun t1 t2 =>
    if h : t1.pos = t2.pos ∧ t1.neg = t2.neg then
      isTrue (by cases t1; cases t2; simp_all)
    else
      isFalse (by intro heq; cases heq; simp_all)

-- ============================================================================
-- Negation Semantics
-- ============================================================================

/--
Contradictory negation: the logical complement.

"not happy" = degree ≤ θ (everything that fails to be happy).
This is standard Boolean negation.
-/
def contradictoryNeg {max : Nat} (d : Degree max) (θ : Threshold max) : Bool :=
  d.toNat ≤ θ.toNat

/--
Contrary negation: the polar opposite.

"unhappy" = degree < θ_neg (the opposite pole, not just "not happy").
This creates a gap where θ_neg ≤ degree ≤ θ_pos.
-/
def contraryNeg {max : Nat} (d : Degree max) (θ_neg : Threshold max) : Bool :=
  d.toNat < θ_neg.toNat

/--
Check if a degree is in the gap region (neither positive nor negative).

The gap is the region where:
- degree ≤ θ_pos (not positive/happy)
- degree ≥ θ_neg (not negative/unhappy under contrary reading)

Someone in the gap is "not unhappy" but also "not happy".
-/
def inGapRegion {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  tp.neg.toNat ≤ d.toNat && d.toNat ≤ tp.pos.toNat

/--
Positive meaning with two-threshold model.
Same as single threshold: degree > θ_pos.
-/
def positiveMeaning' {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  d.toNat > tp.pos.toNat

/--
Negative meaning with contrary semantics.
"unhappy" = degree < θ_neg.
-/
def contraryNegMeaning {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  d.toNat < tp.neg.toNat

/--
Negation of contrary negative: "not unhappy".
"not unhappy" = degree ≥ θ_neg (includes gap AND positive region).

This is why "not unhappy" ≠ "happy":
- "not unhappy" includes the gap region
- "happy" excludes it
-/
def notContraryNegMeaning {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  d.toNat ≥ tp.neg.toNat

-- ============================================================================
-- Gradable Adjective Semantics
-- ============================================================================

/-- Positive form: degree > threshold -/
def positiveMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  d.toNat > t.toNat

/-- Negative form: degree < threshold (or ≤ for some analyses) -/
def negativeMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  d.toNat < t.toNat

/-- Antonym reverses the comparison -/
def antonymMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  d.toNat ≤ t.toNat

-- ============================================================================
-- Utterances
-- ============================================================================

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

-- ============================================================================
-- Joint World: Degree × Threshold
-- ============================================================================

/--
Joint world state for vagueness: both degree and threshold.

The key insight from Lassiter & Goodman (2017): listeners jointly infer
both the degree value AND the contextual threshold.
-/
abbrev DegreeWorld (max : Nat) := Degree max × Threshold max

/-- All joint worlds -/
def allDegreeWorlds (max : Nat) (h : 0 < max := by omega) : List (DegreeWorld max) :=
  (allDegrees max).flatMap fun d =>
    (allThresholds max h).map fun t => (d, t)

instance {n : Nat} (h : 0 < n := by omega) : BEq (DegreeWorld n) := instBEqProd

-- ============================================================================
-- Scenario Builders
-- ============================================================================

/--
Tall/short scenario with threshold inference.

The listener jointly infers:
- The degree (how tall is the person?)
- The threshold (what counts as "tall" in this context?)
-/
def tallShort (max : Nat) (h : 0 < max := by omega) : RSAScenario :=
  RSAScenario.basicBool
    [AdjUtt.positive, .negative, .silent]
    (allDegreeWorlds max h)
    (fun (d, t) u => adjMeaning u d t)

/--
Scenario with custom prior over degrees.

Often degrees have a prior (e.g., height is roughly normal).
-/
def withDegreePrior (max : Nat) (h : 0 < max := by omega)
    (degreePrior : Degree max → ℚ)
    (thresholdPrior : Threshold max → ℚ := fun _ => 1)
    : RSAScenario :=
  let worldPrior : DegreeWorld max → ℚ := fun (d, t) => degreePrior d * thresholdPrior t
  RSAScenario.basicBool
    [AdjUtt.positive, .negative, .silent]
    (allDegreeWorlds max h)
    (fun (d, t) u => adjMeaning u d t)
    worldPrior

-- ============================================================================
-- Graded (Non-Boolean) Semantics
-- ============================================================================

/--
Graded meaning: returns a value in [0, 1] instead of Bool.

For fuzzy boundaries, the meaning can be probabilistic:
- P("tall" | d, θ) could be a sigmoid around θ

This is for more sophisticated models; the Boolean version suffices for many cases.
-/
def gradedPositive {max : Nat} (d : Degree max) (t : Threshold max) : ℚ :=
  if d.toNat > t.toNat then 1 else 0  -- Step function (simplest)

/--
Sigmoid-like graded meaning (discrete approximation).

Smoother transition around threshold.
-/
def sigmoidMeaning {max : Nat} (d : Degree max) (t : Threshold max) (sharpness : ℚ := 2)
    : ℚ :=
  let diff : Int := d.toNat - t.toNat
  if diff > 2 then 1
  else if diff < -2 then 0
  else (diff + 3) / 6  -- Linear approximation in transition zone

-- ============================================================================
-- Comparison Class Pattern
-- ============================================================================

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

-- ============================================================================
-- Examples
-- ============================================================================

-- Height domain 0..10
#eval RSA.L1_world (tallShort 10) .positive
-- Infers high degree values more likely

-- Check semantics
#eval positiveMeaning (Degree.ofNat 10 8) (⟨⟨5, by omega⟩⟩ : Threshold 10)  -- true
#eval positiveMeaning (Degree.ofNat 10 3) (⟨⟨5, by omega⟩⟩ : Threshold 10)  -- false

-- ============================================================================
-- HasDegree Typeclass (for Measure Functions)
-- ============================================================================

/--
Typeclass for entities that have a degree/magnitude on some scale.

This is the formal semantics "measure function" μ : Entity → Degree.
"John is tall" and "John is 6 feet" both involve μ_height(John).

Examples:
- μ_height(John) = 183 cm
- μ_price(laptop) = $500
- μ_temperature(room) = 22°C
-/
class HasDegree (E : Type) where
  degree : E → ℚ

-- ============================================================================
-- Numeral Expression Semantics
-- ============================================================================

/--
Literal/exact semantics for numeral expressions.

"six feet" is true of x iff μ_height(x) = 183 (approximately).
This is the strict reading; hyperbole arises when speakers use
literally false expressions pragmatically.
-/
def numeralExact {E : Type} [HasDegree E] (stated : ℚ) (entity : E) : Bool :=
  HasDegree.degree entity == stated

/--
"At least n" semantics (lower-bound reading).
-/
def numeralAtLeast {E : Type} [HasDegree E] (threshold : ℚ) (entity : E) : Bool :=
  HasDegree.degree entity ≥ threshold

/--
Approximate match with tolerance (for vagueness/imprecision).
-/
def numeralApprox {E : Type} [HasDegree E] (stated : ℚ) (tolerance : ℚ) (entity : E) : Bool :=
  let actual := HasDegree.degree entity
  (stated - tolerance ≤ actual) && (actual ≤ stated + tolerance)

-- ============================================================================
-- Domain: Prices (for Kao et al. 2014 hyperbole)
-- ============================================================================

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

def toScenario : RSAScenario :=
  RSAScenario.basicBool standardUtterances standardWorlds (fun w u => meaning u w)

end Price

-- ============================================================================
-- Domain: Heights
-- ============================================================================

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

-- ============================================================================
-- Domain: Temperature
-- ============================================================================

namespace Temperature

/-- A world characterized by temperature (in °C) -/
structure World where
  value : ℚ
  deriving Repr, DecidableEq, BEq

instance : HasDegree World where
  degree := World.value

end Temperature

-- ============================================================================
-- Grounding Theorems
-- ============================================================================

/-- Price meaning uses the HasDegree instance -/
theorem price_uses_degree (u : Price.Utterance) (w : Price.World) :
    Price.meaning u w = (HasDegree.degree w == u.value) := rfl

/-- "Million dollars" never literally matches standard prices -/
theorem million_never_literal :
    ∀ w ∈ Price.standardWorlds, Price.meaning .million w = false := by
  intro w hw
  simp [Price.standardWorlds] at hw
  rcases hw with rfl | rfl | rfl <;> native_decide

-- ============================================================================
-- RSA Convenience (Prices)
-- ============================================================================

def Price.l0 (u : Price.Utterance) : List (Price.World × ℚ) :=
  RSA.L0 Price.toScenario u () () () ()

def Price.s1 (w : Price.World) : List (Price.Utterance × ℚ) :=
  RSA.S1 Price.toScenario w () () () ()

def Price.l1 (u : Price.Utterance) : List (Price.World × ℚ) :=
  RSA.L1_world Price.toScenario u

#eval Price.l0 .fifty        -- Only low price matches
#eval Price.l0 .million      -- Empty (never literally true)
#eval Price.s1 Price.high    -- Prefers "ten thousand"

end Degrees
