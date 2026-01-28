/-
# Degree/Vagueness Fragments

Building blocks for RSA scenarios with gradable adjectives and vagueness.

## Components

- `Degree n`: Discretized degree scale (0..n)
- `Threshold`: Cutoff for positive/negative form
- `gradedMeaning`: Threshold-relative semantics
- `thresholdScenario`: Joint inference over degrees and thresholds

## The Pattern

Vagueness RSA involves:
1. **Degrees**: The underlying scale (height, temperature, etc.)
2. **Thresholds**: Contextual cutoff for "tall", "hot", etc.
3. **Joint inference**: Listener infers both degree and threshold

Key insight: The threshold is a *free variable* that listeners infer.
This explains context-sensitivity and borderline cases.

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
-/

import Linglib.Theories.RSA.Core
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

end Degrees
