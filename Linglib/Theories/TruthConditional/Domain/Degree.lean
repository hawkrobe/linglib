/-
# Degree Semantics for Gradable Adjectives

Semantic primitives for gradable adjective theories:
- `Degree`: Position on a scale (height, price, happiness, etc.)
- `Threshold`: Contextual cutoff for positive/negative forms
- `NegationType`: Contradictory vs. contrary negation
- `HasDegree`: Measure function typeclass

This module provides the semantic infrastructure that Montague-style
theories need for gradable adjectives. Concrete RSA domains (like
Price.World, Height.World) that use these primitives live in
`Fragments/Degrees.lean`.

## Architecture

```
Montague/Lexicon/Degrees.lean (this file - semantic primitives)
    ^
Fragments/Degrees.lean (concrete RSA domains)
    ^
RSA implementations (Kao, TesslerFranke, etc.)
```

## The Pattern

Vagueness in gradable adjectives involves:
1. **Degrees**: The underlying scale (height, temperature, etc.)
2. **Thresholds**: Contextual cutoff for "tall", "hot", etc.
3. **Negation type**: Contradictory ("not tall") vs. contrary ("short")

## Negation: Contradictory vs. Contrary

**Contradictory negation** (logical complement):
- "not happy" = degree <= theta (everything that's not happy)
- P and not-P partition the space: exactly one must be true
- No gap: every degree is either "happy" or "not happy"

**Contrary negation** (polar opposite):
- "unhappy" = degree < theta_neg where theta_neg < theta_pos
- P and Q can both be false: the gap region
- Gap: theta_neg <= degree <= theta_pos is "neither happy nor unhappy"

This distinction explains why "not unhappy" != "happy":
- "not unhappy" = degree >= theta_neg (includes gap + happy region)
- "happy" = degree > theta_pos (only happy region)

## References

- Kennedy (2007). Vagueness and grammar.
- Kennedy & McNally (2005). Scale structure, degree modification.
- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
- Tessler & Franke (2020). Not unreasonable.
- Cruse (1986). Lexical Semantics.
- Horn (1989). A Natural History of Negation.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Core.Roundness

namespace TruthConditional.Domain.Degrees

-- Degree Values

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

-- Thresholds

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

-- Negation Types: Contradictory vs. Contrary

/--
Types of negation for gradable adjectives.

From traditional logic (Square of Opposition) and lexical semantics:

**Contradictories** (e.g., "happy" / "not happy"):
- Cannot both be true AND cannot both be false
- Exactly one must hold for any degree
- "not happy" = not(degree > theta) = degree <= theta

**Contraries** (e.g., "happy" / "unhappy"):
- Cannot both be true BUT can both be false
- Gap region where neither holds
- "happy" = degree > theta_pos, "unhappy" = degree < theta_neg, gap = theta_neg <= d <= theta_pos

The key insight: morphological antonyms ("unhappy") are typically CONTRARY,
not contradictory. This is why "not unhappy" != "happy".

References:
- Cruse (1986). Lexical Semantics.
- Horn (1989). A Natural History of Negation.
- Tessler & Franke (2020). Not unreasonable.
-/
inductive NegationType where
  /-- Contradictory: logical complement, no gap. not(d > theta) = d <= theta -/
  | contradictory
  /-- Contrary: polar opposite with gap. d < theta_neg where theta_neg < theta_pos -/
  | contrary
  deriving Repr, DecidableEq, BEq

-- Two-Threshold Model for Contrary Antonyms

/--
A threshold pair for contrary antonyms.

For contrary pairs like happy/unhappy:
- theta_pos: threshold for positive form (degree > theta_pos -> "happy")
- theta_neg: threshold for negative form (degree < theta_neg -> "unhappy")
- Constraint: theta_neg <= theta_pos (gap exists when theta_neg < theta_pos)

The gap region theta_neg <= degree <= theta_pos is "neither happy nor unhappy".
-/
structure ThresholdPair (max : Nat) where
  /-- Threshold for positive form ("happy") -/
  pos : Threshold max
  /-- Threshold for negative form ("unhappy") -/
  neg : Threshold max
  /-- Gap constraint: neg threshold <= pos threshold -/
  gap_exists : neg.toNat ≤ pos.toNat := by decide
  deriving Repr

instance {n : Nat} (h : 0 < n := by omega) : Inhabited (ThresholdPair n) :=
  ⟨{ pos := ⟨⟨0, h⟩⟩, neg := ⟨⟨0, h⟩⟩, gap_exists := le_refl _ }⟩

/-- Threshold pair equality (ignore proof) -/
instance {n : Nat} : BEq (ThresholdPair n) where
  beq t1 t2 := t1.pos == t2.pos && t1.neg == t2.neg

instance {n : Nat} : DecidableEq (ThresholdPair n) :=
  λ t1 t2 =>
    if h : t1.pos = t2.pos ∧ t1.neg = t2.neg then
      isTrue (by cases t1; cases t2; simp_all)
    else
      isFalse (by intro heq; cases heq; simp_all)

-- Negation Semantics

/--
Contradictory negation: the logical complement.

"not happy" = degree <= theta (everything that fails to be happy).
This is standard Boolean negation.
-/
def contradictoryNeg {max : Nat} (d : Degree max) (θ : Threshold max) : Bool :=
  d.toNat ≤ θ.toNat

/--
Contrary negation: the polar opposite.

"unhappy" = degree < theta_neg (the opposite pole, not just "not happy").
This creates a gap where theta_neg <= degree <= theta_pos.
-/
def contraryNeg {max : Nat} (d : Degree max) (θ_neg : Threshold max) : Bool :=
  d.toNat < θ_neg.toNat

/--
Check if a degree is in the gap region (neither positive nor negative).

The gap is the region where:
- degree <= theta_pos (not positive/happy)
- degree >= theta_neg (not negative/unhappy under contrary reading)

Someone in the gap is "not unhappy" but also "not happy".
-/
def inGapRegion {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  tp.neg.toNat ≤ d.toNat && d.toNat ≤ tp.pos.toNat

/--
Positive meaning with two-threshold model.
Same as single threshold: degree > theta_pos.
-/
def positiveMeaning' {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  d.toNat > tp.pos.toNat

/--
Negative meaning with contrary semantics.
"unhappy" = degree < theta_neg.
-/
def contraryNegMeaning {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  d.toNat < tp.neg.toNat

/--
Negation of contrary negative: "not unhappy".
"not unhappy" = degree >= theta_neg (includes gap AND positive region).

This is why "not unhappy" != "happy":
- "not unhappy" includes the gap region
- "happy" excludes it
-/
def notContraryNegMeaning {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  d.toNat ≥ tp.neg.toNat

-- Gradable Adjective Semantics (Single Threshold)

/-- Positive form: degree > threshold -/
def positiveMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  d.toNat > t.toNat

/-- Negative form: degree < threshold (or <= for some analyses) -/
def negativeMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  d.toNat < t.toNat

/-- Antonym reverses the comparison -/
def antonymMeaning {max : Nat} (d : Degree max) (t : Threshold max) : Bool :=
  d.toNat ≤ t.toNat

-- HasDegree Typeclass (for Measure Functions)

/--
Typeclass for entities that have a degree/magnitude on some scale.

This is the formal semantics "measure function" mu : Entity -> Degree.
"John is tall" and "John is 6 feet" both involve mu_height(John).

Examples:
- mu_height(John) = 183 cm
- mu_price(laptop) = $500
- mu_temperature(room) = 22 C
-/
class HasDegree (E : Type) where
  degree : E → ℚ

-- Numeral Expression Semantics

/--
Literal/exact semantics for numeral expressions.

"six feet" is true of x iff mu_height(x) = 183 (approximately).
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

-- Pragmatic Halo: Rounding Semantics (Lasersohn 1999, Krifka 2007)

/-!
## Pragmatic Halo and Round Number Interpretation

Round numbers (100, 1000) are interpreted imprecisely; sharp numbers (103, 1001)
are interpreted precisely. This is the "pragmatic halo" effect.

Following Kao et al. (2014), we model this via rounding projections:
- f_e(s) = s           -- exact: no rounding
- f_a(s) = Round(s)    -- approximate: round to nearest multiple of base

Two values are "equivalent under rounding" if they round to the same number.
This creates equivalence classes: {50, 51, 52, ...} all map to 50.

References:
- Lasersohn, P. (1999). Pragmatic halos. Language 75(3): 522-551.
- Krifka, M. (2007). Approximate interpretation of number words.
- Kao et al. (2014). Nonliteral understanding of number words. PNAS.
-/

/--
Round a rational number to the nearest multiple of `base`.

Examples (base = 10):
- Round(51) = 50
- Round(55) = 60  (round half up)
- Round(1001) = 1000
-/
def roundToNearest (n : ℚ) (base : ℚ := 10) : ℚ :=
  if base == 0 then n
  else
    let scaled := n / base
    let rounded := (scaled + 1/2).floor
    rounded * base

/--
Check if a number is "round" (divisible by base).
Round numbers have pragmatic slack; sharp numbers are interpreted precisely.
-/
def isRoundNumber (n : ℚ) (base : ℚ := 10) : Bool :=
  roundToNearest n base == n

/--
Rounding equivalence: two values are equivalent if they round to the same number.

This is the equivalence relation induced by the approximate projection f_a.
-/
def roundingEquiv (n₁ n₂ : ℚ) (base : ℚ := 10) : Bool :=
  roundToNearest n₁ base == roundToNearest n₂ base

/--
Precision mode for numeral interpretation.

From Kao et al. (2014):
- Exact: speaker wants to communicate the precise value
- Approximate: speaker is okay with "close enough" (rounding)
-/
inductive PrecisionMode where
  | exact       -- f_e(s) = s
  | approximate -- f_a(s) = Round(s)
  deriving Repr, DecidableEq, BEq

/--
Project a value according to precision mode.

f_e(s) = s
f_a(s) = Round(s, base)
-/
def projectPrecision (mode : PrecisionMode) (n : ℚ) (base : ℚ := 10) : ℚ :=
  match mode with
  | .exact => n
  | .approximate => roundToNearest n base

/--
Check if stated and actual values match under a given precision mode.

Under exact mode: must be equal
Under approximate mode: must round to the same value
-/
def matchesPrecision (mode : PrecisionMode) (stated actual : ℚ) (base : ℚ := 10) : Bool :=
  projectPrecision mode stated base == projectPrecision mode actual base

/--
Numeral semantics with precision mode.

"1000 dollars" under exact mode: true iff cost = 1000
"1000 dollars" under approximate mode: true iff Round(cost) = 1000
-/
def numeralWithPrecision {E : Type} [HasDegree E]
    (stated : ℚ) (entity : E) (mode : PrecisionMode) (base : ℚ := 10) : Bool :=
  matchesPrecision mode stated (HasDegree.degree entity) base

-- Measure Predicates (Compositional Sentence Semantics)

/-!
## Compositional Semantics for Measure Sentences

Sentences like "The X cost 1000 dollars" have compositional structure:

  ⟦The X cost u dollars⟧ = measure(X) = u

where:
- `measure : Entity → ℚ` is a measure function (cost, height, weight, etc.)
- `u : ℚ` is the degree denoted by the numeral phrase "u dollars"

This section provides the infrastructure to derive such meanings compositionally,
connecting to the `HasDegree` typeclass which provides measure functions.
-/

/--
A measure predicate maps entities to degrees along some dimension.

Examples:
- cost : Item → ℚ (price in dollars)
- height : Person → ℚ (height in cm)
- temperature : Room → ℚ (temperature in °C)

This is the denotation of measure verbs like "cost", "weigh", "measure".
-/
structure MeasurePredicate (E : Type) where
  /-- The dimension being measured (for documentation) -/
  dimension : String
  /-- The measure function μ : E → ℚ -/
  μ : E → ℚ

/-- Construct a MeasurePredicate from a HasDegree instance -/
def MeasurePredicate.fromHasDegree (E : Type) [HasDegree E] (dim : String) : MeasurePredicate E :=
  { dimension := dim, μ := HasDegree.degree }

/--
A degree phrase denotes a specific degree value.

"1000 dollars" denotes the degree 1000 (in dollar units).
"six feet" denotes the degree ~183 (in cm units).

This is the semantic value of numeral + unit expressions.
-/
structure DegreePhrase where
  /-- The denoted degree value -/
  value : ℚ
  /-- Optional unit (for documentation) -/
  unit : String := ""
  deriving Repr, DecidableEq, BEq

/-- Construct a degree phrase from a rational number -/
def DegreePhrase.ofRat (n : ℚ) (unit : String := "") : DegreePhrase :=
  { value := n, unit := unit }

/-- Construct a degree phrase from a natural number -/
def DegreePhrase.ofNat (n : Nat) (unit : String := "") : DegreePhrase :=
  { value := n, unit := unit }

/--
Compositional semantics for measure sentences.

⟦X measure-pred degree-phrase⟧ = μ(X) = d

"The kettle cost 1000 dollars" is true iff cost(kettle) = 1000.

This is the core composition rule for measure sentences:
- The measure predicate provides μ : E → ℚ
- The degree phrase provides d : ℚ
- The sentence is true iff μ(entity) = d
-/
def measureSentence {E : Type} (pred : MeasurePredicate E) (entity : E) (deg : DegreePhrase) : Bool :=
  pred.μ entity == deg.value

/--
Compositional semantics using HasDegree directly.

This is a convenience that avoids constructing MeasurePredicate explicitly.
-/
def measureSentence' {E : Type} [HasDegree E] (entity : E) (deg : DegreePhrase) : Bool :=
  HasDegree.degree entity == deg.value

-- Grounding Theorems

/--
The compositional measure sentence semantics equals the simple numeral check.

This theorem shows that `measureSentence` (compositional) and `numeralExact`
(direct) compute the same truth value.
-/
theorem measureSentence_eq_numeralExact {E : Type} [HasDegree E]
    (entity : E) (deg : DegreePhrase) :
    measureSentence' entity deg = numeralExact deg.value entity := rfl

/--
MeasurePredicate.fromHasDegree produces the HasDegree measure function.
-/
theorem fromHasDegree_μ {E : Type} [HasDegree E] (dim : String) :
    (MeasurePredicate.fromHasDegree E dim).μ = HasDegree.degree := rfl

/--
Measure sentences compose correctly with HasDegree-derived predicates.
-/
theorem measureSentence_fromHasDegree {E : Type} [HasDegree E]
    (dim : String) (entity : E) (deg : DegreePhrase) :
    measureSentence (MeasurePredicate.fromHasDegree E dim) entity deg =
    numeralExact deg.value entity := rfl

-- ============================================================================
-- Degree Modifiers (Kennedy & McNally 2005; Israel 2011; Machino et al. 2025)
-- ============================================================================

/-- Degree modifier direction — same axis as NPI scalar direction.

    - **Amplifiers** (very, extremely) raise the threshold → stronger assertion.
    - **Downtoners** (slightly, kind of) lower the threshold → weaker assertion.

    This is the truth-conditional reflex of Israel's (2011) strengthening/attenuating
    axis: amplifiers strengthen gradable predicate meanings, downtoners attenuate them.

    Kennedy & McNally (2005). Scale structure, degree modification.
    Israel (2011). The Grammar of Polarity. CUP. -/
inductive ModifierDirection where
  | amplifier   -- very, extremely: θ + δ → strengthens
  | downtoner   -- slightly, kind of: θ - δ → attenuates
  deriving DecidableEq, BEq, Repr

/-- A degree modifier that shifts the threshold of a gradable predicate.

    Gradable predicate P holds of x iff degree(x) > θ.
    A modifier M transforms P so that M(P) holds iff degree(x) > θ', where:
    - Amplifier:  θ' = θ + δ  (raises the bar → harder to satisfy → stronger)
    - Downtoner:  θ' = θ - δ  (lowers the bar → easier to satisfy → weaker) -/
structure DegreeModifier (max : Nat) where
  /-- Surface form -/
  form : String
  /-- Direction: amplifier or downtoner -/
  direction : ModifierDirection
  /-- How much to shift the threshold (always positive; direction determines sign) -/
  shift : Fin (max + 1)
  /-- Strength rank within same direction (higher = more extreme) -/
  rank : Nat
  deriving Repr

/-- Apply a modifier to a threshold.
    Amplifiers add shift (θ + δ), downtoners subtract shift (θ - δ).
    Result is clamped to [0, max). -/
def DegreeModifier.applyToThreshold {max : Nat} (m : DegreeModifier max)
    (θ : Threshold max) : Threshold max :=
  have hθ := θ.value.isLt  -- θ.value.val < max
  have hm := m.shift.isLt  -- m.shift.val < max + 1
  match m.direction with
  | .amplifier =>
    ⟨⟨min (θ.value.val + m.shift.val) (max - 1), by omega⟩⟩
  | .downtoner =>
    ⟨⟨θ.value.val - m.shift.val, by omega⟩⟩

/-- A modified gradable predicate: degree(x) > M(θ). -/
def modifiedMeaning {max : Nat} (m : DegreeModifier max)
    (d : Degree max) (θ : Threshold max) : Bool :=
  positiveMeaning d (m.applyToThreshold θ)

-- Modifier Instances (Machino et al. 2025 hierarchy)

section ModifierInstances

variable (max : Nat)

/-- "slightly" — minimal downtoner -/
def slightly (h : 1 ≤ max := by omega) : DegreeModifier max :=
  { form := "slightly", direction := .downtoner
  , shift := ⟨1, by omega⟩, rank := 1 }

/-- "kind of" — moderate downtoner -/
def kindOf (h : 2 ≤ max := by omega) : DegreeModifier max :=
  { form := "kind of", direction := .downtoner
  , shift := ⟨2, by omega⟩, rank := 2 }

/-- "quite" — can be amplifier (AmE) or downtoner (BrE).
    Default: amplifier with small shift (AmE reading). -/
def quite (h : 1 ≤ max := by omega) : DegreeModifier max :=
  { form := "quite", direction := .amplifier
  , shift := ⟨1, by omega⟩, rank := 1 }

/-- "very" — strong amplifier -/
def very (h : 2 ≤ max := by omega) : DegreeModifier max :=
  { form := "very", direction := .amplifier
  , shift := ⟨2, by omega⟩, rank := 2 }

/-- "extremely" — maximal amplifier -/
def extremely (h : 3 ≤ max := by omega) : DegreeModifier max :=
  { form := "extremely", direction := .amplifier
  , shift := ⟨3, by omega⟩, rank := 3 }

end ModifierInstances

-- Strength Hierarchy Verification

-- Amplifier rank order: quite < very < extremely
#guard Nat.blt (quite 10).rank (very 10).rank
#guard Nat.blt (very 10).rank (extremely 10).rank

-- Downtoner rank order: slightly < kindOf
#guard Nat.blt (slightly 10).rank (kindOf 10).rank

-- Amplifiers raise threshold: very(θ=3) → θ'=5 > 3
#guard Nat.blt 3 ((very 10).applyToThreshold (⟨⟨3, by omega⟩⟩ : Threshold 10) |>.toNat)

-- Downtoners lower threshold: slightly(θ=5) → θ'=4 < 5
#guard Nat.blt ((slightly 10).applyToThreshold (⟨⟨5, by omega⟩⟩ : Threshold 10) |>.toNat) 5

-- ============================================================================
-- Adaptive Pragmatic Halo (Woodin et al. 2024, Krifka 2007, Lasersohn 1999)
-- ============================================================================

/-!
## Adaptive Rounding Base and Pragmatic Halo Width

The fixed `base` parameter in `roundToNearest` and `isRoundNumber` above treats
all numerals uniformly: 100 and 1000 both round to the nearest 10. But empirically,
higher-magnitude and rounder numbers permit wider imprecision (Krifka 2007).

Using `roundnessScore` from `Core.Roundness`, we derive:
- `adaptiveBase`: rounding base scales with k-ness score
- `haloWidth`: pragmatic halo width as a function of roundness
- `inferPrecisionMode`: k-ness score grounds the binary exact/approximate distinction

These connect to:
- `roundToNearest` (line 314): `adaptiveBase` replaces fixed base
- `PrecisionMode` (line 343): `inferPrecisionMode` derives from k-ness
- Kao et al. 2014's `Goal.approxPrice`: grounded by `inferPrecisionMode`

References:
- Lasersohn (1999). Pragmatic halos. Language 75(3): 522-551.
- Krifka (2007). Approximate interpretation of number words.
- Kao et al. (2014). Nonliteral understanding of number words. PNAS.
- Woodin, Winter & Bhatt (2024). Numeral frequency and roundness.
-/

open Core.Roundness in

/--
Adaptive rounding base: rounder numbers get a coarser base.

Uses `RoundnessGrade` to avoid duplicating score-binning logic:
- `.none` (e.g., 7): base 1 (no rounding slack)
- `.low` (e.g., 110): base 5
- `.moderate` (e.g., 50): base 10
- `.high` (e.g., 100, 1000): base matching their magnitude

This captures Woodin et al.'s magnitude effect: higher k-ness score
correlates with larger acceptable deviations.
-/
def adaptiveBase (n : Nat) : ℚ :=
  match Core.Roundness.roundnessGrade n with
  | .high =>
    if n % 1000 == 0 then 100
    else 10
  | .moderate => 10
  | .low => 5
  | .none => 1

open Core.Roundness in

/--
Adaptive tolerance: scales a base tolerance by the roundness score.

Rounder numbers permit more imprecision. A base tolerance of 5% becomes:
- 5% for non-round (score 0)
- up to 15% for maximally round (score 6)
-/
def adaptiveTolerance (n : Nat) (baseTol : ℚ) : ℚ :=
  let score := Core.Roundness.roundnessScore n
  baseTol * (1 + score / 6)

open Core.Roundness in

/--
Pragmatic halo width as a function of roundness score.

Lasersohn (1999): the pragmatic halo of an expression is the set of
objects "close enough" to its literal denotation. For numerals, the
halo width varies with roundness.

Connects to `roundToNearest` above: `base` is now derived from roundness
rather than being a constant.
-/
def haloWidth (n : Nat) : ℚ :=
  let score := Core.Roundness.roundnessScore n
  let magnitudeFactor : ℚ := if n ≥ 1000 then 50
                              else if n ≥ 100 then 10
                              else if n ≥ 10 then 5
                              else 1
  magnitudeFactor * score / 6

open Core.Roundness in

/--
Infer precision mode from k-ness score.

roundnessScore ≥ 2 → `.approximate` (pragmatic slack available)
roundnessScore < 2 → `.exact` (precise reading required)

This grounds Kao et al. (2014)'s binary `Goal.approxPrice` in the k-ness
model: the `approxPrice` goal uses `Round(s, 10)`, which implicitly assumes
the numeral is round enough for approximate interpretation. The k-ness score
makes this condition explicit.
-/
def inferPrecisionMode (n : Nat) : PrecisionMode :=
  if Core.Roundness.roundnessScore n ≥ 2 then .approximate
  else .exact

-- Verification

#guard inferPrecisionMode 100 == .approximate  -- score 6 ≥ 2
#guard inferPrecisionMode 50 == .approximate   -- score 4 ≥ 2
#guard inferPrecisionMode 110 == .approximate  -- score 2 ≥ 2
#guard inferPrecisionMode 7 == .exact          -- score 0 < 2
#guard inferPrecisionMode 99 == .exact         -- score 0 < 2
#guard inferPrecisionMode 15 == .exact         -- score 1 < 2

/-- Multiples of 10 have adaptive base ≥ 5 (at least `.low` grade).
    Multiples of 100 get `.moderate` or `.high` grade with base ≥ 10. -/
theorem adaptive_base_ge_five_of_div10 (n : Nat) (h10 : n % 10 = 0) :
    adaptiveBase n ≥ 5 := by
  unfold adaptiveBase
  have hs := Core.Roundness.score_ge_two_of_div10 n h10
  split
  · split <;> decide
  · decide
  · decide
  · exact absurd ‹_› (Core.Roundness.grade_ne_none_of_score_ge_one n (by omega))

end TruthConditional.Domain.Degrees
