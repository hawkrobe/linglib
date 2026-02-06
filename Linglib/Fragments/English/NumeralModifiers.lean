/-
# English Numeral Modifiers

Fragment entries for numeral modification expressions: "around", "between",
"exactly", "approximately".

These modifiers interact with numeral imprecision (Phenomena/Imprecision/)
and are formalized in RSA/Implementations/EgreEtAl2023.lean.

## Entries

- `around`: tolerance-based approximation (Égré et al. 2023)
- `between`: interval-based specification
- `exactly`: precision enforcer
- `approximately`: explicit imprecision marker

## References

- Égré, P., Spector, B., Mortier, A., & Verheyen, S. (2023). On the optimality
  of vagueness. Linguistics and Philosophy, 46, 1101–1130.
- Krifka, M. (2007). Approximate interpretation of number words.
- Solt, S. (2014). An alternative theory of imprecision.
-/

import Linglib.Core.Basic
import Mathlib.Data.Rat.Defs

namespace Fragments.English.NumeralModifiers

/--
Semantic type of a numeral modifier.

Modifiers can be:
- Tolerance-based: "around n" = λx. |n-x| ≤ y (with hidden tolerance y)
- Interval-based: "between a b" = λx. a ≤ x ≤ b
- Exactifier: "exactly n" = λx. x = n
-/
inductive ModifierType where
  | tolerance    -- "around", "approximately", "roughly"
  | interval     -- "between ... and ..."
  | exactifier   -- "exactly", "precisely"
  deriving Repr, DecidableEq, BEq

/--
Pragmatic function of a numeral modifier.

Following Égré et al. (2023): modifiers signal the shape of the speaker's
private distribution over the true value.
-/
inductive PragmaticFunction where
  | peakedSignal    -- Signals peaked distribution (around, approximately)
  | flatSignal      -- Signals flat/uniform distribution (between)
  | pointSignal     -- Signals point distribution (exactly)
  deriving Repr, DecidableEq, BEq

/-- Lexical entry for a numeral modifier. -/
structure NumeralModifierEntry where
  /-- Surface form -/
  form : String
  /-- Modifier type -/
  modType : ModifierType
  /-- Pragmatic function -/
  pragFunction : PragmaticFunction
  /-- Requires round numeral? -/
  requiresRound : Bool := false
  /-- Is the modifier vague (tolerance-based)? -/
  isVague : Bool
  /-- Does it convey shape information beyond support? -/
  conveysShape : Bool
  /-- Can it license sorites chains? -/
  soritesSusceptible : Bool
  /-- Notes -/
  notes : String := ""
  deriving Repr, BEq

/--
"around": tolerance-based approximation.

⟦around n⟧ = λy.λx. |n-x| ≤ y
Pragmatically signals peaked private distribution centered on n.

Source: Égré et al. 2023
-/
def around : NumeralModifierEntry :=
  { form := "around"
  , modType := .tolerance
  , pragFunction := .peakedSignal
  , requiresRound := false  -- "around 47" is grammatical though marked
  , isVague := true
  , conveysShape := true    -- Key result of Égré et al.
  , soritesSusceptible := true
  }

/--
"approximately": explicit tolerance marker.

Similar to "around" but more formal register.
Interacts with roundness: "approximately 100" natural,
"approximately 99" marked.

Source: Phenomena/Imprecision/Numerals.lean
-/
def approximately : NumeralModifierEntry :=
  { form := "approximately"
  , modType := .tolerance
  , pragFunction := .peakedSignal
  , requiresRound := false  -- Grammatical but marked with non-round
  , isVague := true
  , conveysShape := true
  , soritesSusceptible := true
  , notes := "More formal register than 'around'"
  }

/--
"roughly": informal tolerance marker.

Behaves like "around" pragmatically.
-/
def roughly : NumeralModifierEntry :=
  { form := "roughly"
  , modType := .tolerance
  , pragFunction := .peakedSignal
  , isVague := true
  , conveysShape := true
  , soritesSusceptible := true
  , notes := "Informal register"
  }

/--
"between ... and ...": interval specification.

⟦between a and b⟧ = λx. a ≤ x ≤ b
Pragmatically signals flat distribution over [a,b].
Does NOT convey shape information (only support).

Source: Égré et al. 2023
-/
def between : NumeralModifierEntry :=
  { form := "between"
  , modType := .interval
  , pragFunction := .flatSignal
  , isVague := false
  , conveysShape := false   -- Only conveys support, not shape
  , soritesSusceptible := false
  }

/--
"exactly": precision enforcer.

⟦exactly n⟧ = λx. x = n
Removes imprecision. Point signal.

Source: Phenomena/Imprecision/Numerals.lean (ExactlyModifierDatum)
-/
def exactly : NumeralModifierEntry :=
  { form := "exactly"
  , modType := .exactifier
  , pragFunction := .pointSignal
  , isVague := false
  , conveysShape := false  -- Trivially: point has no shape
  , soritesSusceptible := false
  , notes := "Removes imprecision from bare numerals"
  }

/--
"precisely": formal exactifier.

Behaves like "exactly" semantically.
-/
def precisely : NumeralModifierEntry :=
  { form := "precisely"
  , modType := .exactifier
  , pragFunction := .pointSignal
  , isVague := false
  , conveysShape := false
  , soritesSusceptible := false
  , notes := "Formal register variant of 'exactly'"
  }

-- ============================================================================
-- Scale Structure
-- ============================================================================

/--
Informativity scale for numeral modifiers.

Ordered by how much information about the true value they convey:
  exactly > around > between

"Exactly" gives the most information (point), "around" gives shape,
"between" gives only support.
-/
structure ModifierScale where
  /-- More informative (stronger) -/
  stronger : NumeralModifierEntry
  /-- Less informative (weaker) -/
  weaker : NumeralModifierEntry
  /-- Scalar relation holds -/
  isScalarPair : Bool
  deriving Repr

/-- "Exactly" is more informative than "around" -/
def exactlyAroundScale : ModifierScale :=
  { stronger := exactly
  , weaker := around
  , isScalarPair := true
  }

/-- "Around" is more informative than "between" (conveys shape) -/
def aroundBetweenScale : ModifierScale :=
  { stronger := around
  , weaker := between
  , isScalarPair := true
  }

-- Collections

def toleranceModifiers : List NumeralModifierEntry :=
  [around, approximately, roughly]

def intervalModifiers : List NumeralModifierEntry :=
  [between]

def exactifiers : List NumeralModifierEntry :=
  [exactly, precisely]

def allModifiers : List NumeralModifierEntry :=
  toleranceModifiers ++ intervalModifiers ++ exactifiers

def modifierScales : List ModifierScale :=
  [exactlyAroundScale, aroundBetweenScale]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All tolerance modifiers convey shape information. -/
theorem tolerance_modifiers_convey_shape :
    toleranceModifiers.all (·.conveysShape) = true := by native_decide

/-- No interval or exact modifiers convey shape information. -/
theorem non_tolerance_no_shape :
    (intervalModifiers ++ exactifiers).all (·.conveysShape == false) = true := by native_decide

/-- Only tolerance modifiers are sorites-susceptible. -/
theorem only_tolerance_sorites :
    toleranceModifiers.all (·.soritesSusceptible) = true ∧
    (intervalModifiers ++ exactifiers).all (·.soritesSusceptible == false) = true := by
  constructor <;> native_decide

end Fragments.English.NumeralModifiers
