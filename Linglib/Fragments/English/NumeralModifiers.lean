/-
# English Numeral Modifiers

Fragment entries for numeral modification expressions, covering:
- **Tolerance modifiers**: "around", "approximately", "roughly"
- **Interval modifiers**: "between ... and ..."
- **Exactifiers**: "exactly", "precisely"
- **Bound-setting modifiers**: "at least", "at most", "more than", "fewer than",
  "up to", "from ... on"

The bound-setting modifiers are classified following Kennedy (2015):
- Class A (strict: >, <): "more than", "fewer than" — no ignorance implicature
- Class B (non-strict: ≥, ≤): "at least", "at most", "up to", "from...on" — ignorance

Evaluative valence (Blok 2015, Claus & Walch 2024) distinguishes "at most" (negative)
from "up to" (positive), predicting divergent framing effects.

## References

- Égré, P., Spector, B., Mortier, A., & Verheyen, S. (2023). On the optimality
  of vagueness. Linguistics and Philosophy, 46, 1101–1130.
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
- Blok, D. (2015). The semantics and pragmatics of directional numeral modifiers.
- Claus, B. & Walch, V. (2024). Evaluative valence distinguishes at most from up to.
- Krifka, M. (2007). Approximate interpretation of number words.
- Solt, S. (2014). An alternative theory of imprecision.
-/

import Linglib.Core.Basic
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Mathlib.Data.Rat.Defs

namespace Fragments.English.NumeralModifiers

open Semantics.Lexical.Numeral

/--
Semantic type of a numeral modifier.

Modifiers can be:
- Tolerance-based: "around n" = λx. |n-x| ≤ y (with hidden tolerance y)
- Interval-based: "between a b" = λx. a ≤ x ≤ b
- Exactifier: "exactly n" = λx. x = n
- Bound-setting: "at least n", "more than n", etc. (Kennedy 2015)
-/
inductive ModifierType where
  | tolerance    -- "around", "approximately", "roughly"
  | interval     -- "between ... and ..."
  | exactifier   -- "exactly", "precisely"
  | bound        -- "at least", "at most", "more than", "fewer than", "up to", "from...on"
  | approximator -- "almost", "nearly": proximal + polar (Nouwen 2006)
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
  | boundSignal     -- Signals bound on the distribution (at least, at most, etc.)
  deriving Repr, DecidableEq, BEq

/-- Evaluative valence of a bound-setting modifier (Blok 2015, Claus & Walch 2024).

Distinguishes modifiers with the same truth conditions but different framing:
- "at most 100" (negative valence) → reversed framing (endorsed more in negative contexts)
- "up to 100" (positive valence) → standard framing (endorsed more in positive contexts)
-/
inductive EvaluativeValence where
  | positive   -- "up to", "from...on": invites positive evaluation
  | negative   -- "at most": invites negative evaluation
  | neutral    -- "at least", "more than", "fewer than": no evaluative bias
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
  /-- Bound direction (for bound-setting modifiers) -/
  boundDir : Option BoundDirection := none
  /-- Modifier class (for bound-setting modifiers) -/
  modClass : Option ModifierClass := none
  /-- Evaluative valence (Blok 2015 / Claus & Walch 2024) -/
  evaluativeValence : EvaluativeValence := .neutral
  /-- Does this modifier generate ignorance implicatures? -/
  generatesIgnorance : Bool := false
  /-- Notes -/
  notes : String := ""
  deriving Repr, BEq

-- ============================================================================
-- Tolerance Modifiers (Égré et al. 2023)
-- ============================================================================

/--
"about": tolerance-based approximation.

The most common English approximator. Used in BSB2022's stimuli:
"about fifty minutes" vs "fifty minutes" vs "forty-nine minutes."

⟦about n⟧ = λy.λx. |n-x| ≤ y
Pragmatically signals peaked private distribution centered on n.

Source: Beltrama, Solt & Burnett (2022)
-/
def about : NumeralModifierEntry :=
  { form := "about"
  , modType := .tolerance
  , pragFunction := .peakedSignal
  , requiresRound := false
  , isVague := true
  , conveysShape := true
  , soritesSusceptible := true
  }

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

Source: Phenomena/Gradability/Imprecision/Numerals.lean
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

-- ============================================================================
-- Interval Modifiers
-- ============================================================================

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

-- ============================================================================
-- Exactifiers
-- ============================================================================

/--
"exactly": precision enforcer.

⟦exactly n⟧ = λx. x = n
Removes imprecision. Point signal.

Source: Phenomena/Gradability/Imprecision/Numerals.lean (ExactlyModifierDatum)
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
-- Bound-Setting Modifiers (Kennedy 2015)
-- ============================================================================

/-- "at least n": Class B lower bound (max ≥ n).

Generates ignorance implicatures because compatible with the bare reading.
Neutral evaluative valence. -/
def atLeast : NumeralModifierEntry :=
  { form := "at least"
  , modType := .bound
  , pragFunction := .boundSignal
  , isVague := false
  , conveysShape := false
  , soritesSusceptible := false
  , boundDir := some .lower
  , modClass := some .classB
  , evaluativeValence := .neutral
  , generatesIgnorance := true
  }

/-- "at most n": Class B upper bound (max ≤ n).

Generates ignorance implicatures. NEGATIVE evaluative valence (Blok 2015):
"at most" is endorsed more in negative contexts. Claus & Walch (2024) show
this produces reversed framing effects. -/
def atMost : NumeralModifierEntry :=
  { form := "at most"
  , modType := .bound
  , pragFunction := .boundSignal
  , isVague := false
  , conveysShape := false
  , soritesSusceptible := false
  , boundDir := some .upper
  , modClass := some .classB
  , evaluativeValence := .negative
  , generatesIgnorance := true
  }

/-- "more than n": Class A lower bound (max > n).

Does NOT generate ignorance implicatures (excludes the bare-numeral world).
Neutral evaluative valence. -/
def moreThan : NumeralModifierEntry :=
  { form := "more than"
  , modType := .bound
  , pragFunction := .boundSignal
  , isVague := false
  , conveysShape := false
  , soritesSusceptible := false
  , boundDir := some .lower
  , modClass := some .classA
  , evaluativeValence := .neutral
  , generatesIgnorance := false
  }

/-- "fewer than n": Class A upper bound (max < n).

Does NOT generate ignorance implicatures (excludes the bare-numeral world).
Neutral evaluative valence. -/
def fewerThan : NumeralModifierEntry :=
  { form := "fewer than"
  , modType := .bound
  , pragFunction := .boundSignal
  , isVague := false
  , conveysShape := false
  , soritesSusceptible := false
  , boundDir := some .upper
  , modClass := some .classA
  , evaluativeValence := .neutral
  , generatesIgnorance := false
  }

/-- "up to n": Class B upper bound (max ≤ n).

Same truth conditions as "at most n", but POSITIVE evaluative valence
(Blok 2015). Claus & Walch (2024) show "up to" follows standard framing
(endorsed more in positive contexts), unlike "at most". -/
def upTo : NumeralModifierEntry :=
  { form := "up to"
  , modType := .bound
  , pragFunction := .boundSignal
  , isVague := false
  , conveysShape := false
  , soritesSusceptible := false
  , boundDir := some .upper
  , modClass := some .classB
  , evaluativeValence := .positive
  , generatesIgnorance := true
  }

/-- "from n on": Class B lower bound (max ≥ n).

Positive evaluative valence: invites positive evaluation of the quantity.
Generates ignorance implicatures (compatible with bare reading). -/
def fromOn : NumeralModifierEntry :=
  { form := "from ... on"
  , modType := .bound
  , pragFunction := .boundSignal
  , isVague := false
  , conveysShape := false
  , soritesSusceptible := false
  , boundDir := some .lower
  , modClass := some .classB
  , evaluativeValence := .positive
  , generatesIgnorance := true
  }

-- ============================================================================
-- Approximators (Nouwen 2006)
-- ============================================================================

/--
"almost": proximal approximation with polar exclusion.

⟦almost n⟧ = λx. close(x, n) ∧ ¬(x = n)  [or ¬(x ≥ n) under LB]

Unlike tolerance modifiers ("around"), "almost" EXCLUDES the target value
(the polar component). This creates a key LB/BL divergence:
- Under LB: "almost three" = close to 3 AND <3 → only values below 3
- Under BL: "almost three" = close to 3 AND ≠3 → values above OR below 3

Empirically, "almost three" means ~2 (below only), favoring LB.

Source: Nouwen (2006) "Remarks on the Polar Orientation of Almost";
  Penka (2006); Sadock (1981).
-/
def almost : NumeralModifierEntry :=
  { form := "almost"
  , modType := .approximator
  , pragFunction := .peakedSignal
  , isVague := true
  , conveysShape := true
  , soritesSusceptible := false
  , notes := "Polar component excludes target value (Nouwen 2006)"
  }

/--
"nearly": synonym of "almost" with slight register difference.

Same proximal + polar semantics as "almost".
-/
def nearly : NumeralModifierEntry :=
  { form := "nearly"
  , modType := .approximator
  , pragFunction := .peakedSignal
  , isVague := true
  , conveysShape := true
  , soritesSusceptible := false
  , notes := "Register variant of 'almost'"
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
  [about, around, approximately, roughly]

def intervalModifiers : List NumeralModifierEntry :=
  [between]

def exactifiers : List NumeralModifierEntry :=
  [exactly, precisely]

def boundModifiers : List NumeralModifierEntry :=
  [atLeast, atMost, moreThan, fewerThan, upTo, fromOn]

def classAModifiers : List NumeralModifierEntry :=
  [moreThan, fewerThan]

def classBModifiers : List NumeralModifierEntry :=
  [atLeast, atMost, upTo, fromOn]

def approximatorModifiers : List NumeralModifierEntry :=
  [almost, nearly]

def allModifiers : List NumeralModifierEntry :=
  toleranceModifiers ++ intervalModifiers ++ exactifiers ++ boundModifiers
    ++ approximatorModifiers

def modifierScales : List ModifierScale :=
  [exactlyAroundScale, aroundBetweenScale]

-- ============================================================================
-- Verification: Original Properties
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

-- ============================================================================
-- Verification: Kennedy 2015 Class A/B Properties
-- ============================================================================

/-- All Class B modifiers generate ignorance implicatures. -/
theorem classB_all_generate_ignorance :
    classBModifiers.all (·.generatesIgnorance) = true := by native_decide

/-- No Class A modifiers generate ignorance implicatures. -/
theorem classA_no_ignorance :
    classAModifiers.all (·.generatesIgnorance == false) = true := by native_decide

/-- "at most" and "up to" differ only in evaluative valence.

Same modType, modClass, boundDir, but different evaluativeValence.
This is the key Blok (2015) / Claus & Walch (2024) observation. -/
theorem atMost_upTo_differ_only_in_valence :
    atMost.modType = upTo.modType ∧
    atMost.modClass = upTo.modClass ∧
    atMost.boundDir = upTo.boundDir ∧
    atMost.evaluativeValence ≠ upTo.evaluativeValence := by
  constructor; · native_decide
  constructor; · native_decide
  constructor; · native_decide
  · native_decide

/-- All bound modifiers are classified as bound type. -/
theorem bound_modifiers_all_bound :
    boundModifiers.all (·.modType == .bound) = true := by native_decide

/-- No bound modifiers are vague. -/
theorem bound_modifiers_not_vague :
    boundModifiers.all (·.isVague == false) = true := by native_decide

/-- Approximators are not sorites-susceptible (unlike tolerance modifiers). -/
theorem approximators_not_sorites :
    approximatorModifiers.all (·.soritesSusceptible == false) = true := by native_decide

/-- Approximators have polar exclusion (distinguished from tolerance modifiers by type). -/
theorem approximators_distinct_from_tolerance :
    approximatorModifiers.all (·.modType == .approximator) = true ∧
    toleranceModifiers.all (·.modType == .tolerance) = true := by
  constructor <;> native_decide

end Fragments.English.NumeralModifiers
