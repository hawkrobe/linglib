/-!
# Physical Dimension
[bale-schwarz-2026] [scontras-2014] [zabbal-2005]

Per-entry feature taxonomy of physical measurement dimensions: the typed tag
that classifies what a measure function measures (mass, volume, distance,
time, cardinality, ...) and the corresponding quotient dimensions (density,
speed, pressure) that ratios of simplex dimensions give rise to.

## Scope

`Dimension` is the simplex feature: directly-measurable properties accessible
to compositional semantics. `QuotientDimension` is the parallel taxonomy of
derived ratios. Per [bale-schwarz-2026]'s No Division Hypothesis
(eq. (5), p. 135), the grammar does not compositionally produce values in
quotient dimensions; references to them go through extra-grammatical
"math speak".

`DimensionType` is the binary tag (simplex/quotient) used by paper-anchored
studies that need to label values without committing to a specific dimension.

## Consumers

- `Semantics/Measurement/Basic.lean`: `DimensionedMeasure` carries `Dimension`
- `Fragments/English/MeasurePhrases.lean`: `MeasureTermEntry` carries `Dimension`
- `Studies/{BaleSchwarz2022, BaleSchwarz2026, Scontras2014}.lean`
- `Semantics/{Noun/Binominal, Gradability/Hierarchy, Verb/VerbEntry, Events/MeasurePhrases}.lean`

-/

namespace Features.Dimension

-- ============================================================================
-- § 1. Simplex Dimensions
-- ============================================================================

/-- Physical dimensions that measure functions can target.

Simplex dimensions are directly measurable properties of entities and are
accessible to compositional semantics. The `cardinality` constructor names
the dimension of [zabbal-2005]'s CARD (the Num-head behind cardinal
numerals), aligned by [scontras-2014] with measure terms. -/
inductive Dimension where
  | mass         -- weight (grams, kilos, pounds)
  | volume       -- volume (milliliters, liters, gallons)
  | distance     -- distance (miles, kilometers, meters)
  | time         -- duration (hours, seconds, minutes)
  | cardinality  -- counting via μ_CARD
  | temperature  -- temperature (degrees Celsius, Fahrenheit)
  | area         -- area (square meters, acres)
  | force        -- force (newtons, pound-force)
  deriving Repr, DecidableEq

-- ============================================================================
-- § 2. Quotient Dimensions
-- ============================================================================

/-- Quotient dimensions: ratios of simplex dimensions.

These exist in the quantity calculus but are not compositionally derivable
within the grammar ([bale-schwarz-2026]'s No Division Hypothesis). -/
inductive QuotientDimension where
  | density      -- mass / volume
  | speed        -- distance / time
  | pressure     -- force / area
  deriving Repr, DecidableEq

/-- The simplex components of a quotient dimension.

Decomposition follows physical convention: density is mass per volume,
speed is distance per time, pressure is force per area. -/
def QuotientDimension.components : QuotientDimension → Dimension × Dimension
  | .density  => (.mass, .volume)
  | .speed    => (.distance, .time)
  | .pressure => (.force, .area)

-- ============================================================================
-- § 3. Dimension Type Tag
-- ============================================================================

/-- Binary tag distinguishing the two dimension taxonomies.

All `Dimension` constructors are simplex by definition; `QuotientDimension`
is always quotient. Studies that need to label values without committing
to a specific dimension use this tag. -/
inductive DimensionType where
  | simplex
  | quotient
  deriving Repr, DecidableEq

-- ============================================================================
-- § 4. Structural Theorems
-- ============================================================================

/-- Every quotient dimension's components are distinct simplex dimensions.

There is no "self-ratio" quotient — `mass/mass`, `time/time` etc. would be
dimensionless and don't appear in `QuotientDimension`. -/
theorem quotient_components_distinct (q : QuotientDimension) :
    q.components.1 ≠ q.components.2 := by
  cases q <;> decide

end Features.Dimension
