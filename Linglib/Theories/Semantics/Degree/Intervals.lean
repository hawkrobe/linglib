import Linglib.Core.Scales.Extent
import Linglib.Theories.Semantics.Degree.Core

/-!
# Schwarzschild's Interval Semantics
@cite{schwarzschild-2005} @cite{schwarzschild-2008} @cite{schwarzschild-wilkinson-2002}

@cite{schwarzschild-2008} "The Semantics of Comparatives and Other Degree
Constructions": degrees are reified as **intervals** on a scale, and
degree morphology manipulates these intervals.

## Key Ideas

1. **Degrees as intervals**: Rather than points on a scale, degrees are
   intervals [0, d] (for "tall") or [d, max] (for "short"). The measure
   function maps entities to intervals.

2. **Than-clause**: Denotes the interval associated with the standard
   entity. The comparative asserts that the matrix interval properly
   contains the standard interval.

3. **Subcomparatives**: The interval approach naturally handles
   subcomparatives ("longer than the desk is wide") because intervals
   from different scales can be compared when they share a common
   unit of measurement.

4. **Differential comparatives**: "3 inches taller" specifies the
   difference between intervals, natural in the interval framework.

-/

namespace Semantics.Degree.Intervals

open Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Intervals as Degrees
-- ════════════════════════════════════════════════════

/-- An interval on a linearly ordered scale.
    Schwarzschild treats degrees as intervals rather than points.
    For a positive adjective like "tall", the interval is [0, μ(x)]. -/
structure Interval (D : Type*) [Preorder D] where
  lower : D
  upper : D
  valid : lower ≤ upper

/-- The positive interval for entity x: [⊥, μ(x)].
    This is the "extent to which x is tall" — the interval from
    the bottom of the scale to x's degree. -/
def positiveInterval {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (x : Entity) : Interval D :=
  { lower := ⊥, upper := μ x, valid := bot_le }

-- ════════════════════════════════════════════════════
-- § 2. Comparative as Interval Comparison
-- ════════════════════════════════════════════════════

/-- Schwarzschild's comparative: the matrix interval properly extends
    beyond the standard interval. For positive adjectives, this means
    [0, μ(a)] properly contains [0, μ(b)], i.e., μ(a) > μ(b). -/
def intervalComparative {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  (positiveInterval μ b).upper < (positiveInterval μ a).upper

/-- Interval comparative reduces to Kennedy/Heim point comparison.
    This is expected: for positive intervals [0, μ(x)], comparing
    upper bounds IS comparing degrees. -/
theorem interval_eq_point {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) :
    intervalComparative μ a b ↔ μ b < μ a :=
  Iff.rfl

-- ════════════════════════════════════════════════════
-- § 3. Differential Comparatives
-- ════════════════════════════════════════════════════

/-- Differential comparative: "A is d-much taller than B" asserts
    that the gap between intervals has extent d.

    In Schwarzschild's framework, the differential is the interval
    [μ(b), μ(a)] — the gap between the standard and matrix intervals. -/
def differentialInterval {Entity D : Type*} [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (a b : Entity) (h : μ b ≤ μ a) : Interval D :=
  { lower := μ b, upper := μ a, valid := h }

-- ════════════════════════════════════════════════════
-- § 4. Subcomparatives
-- ════════════════════════════════════════════════════

/-- Subcomparative: "The table is longer than it is wide."

    Both matrix and standard provide intervals on DIFFERENT scales,
    but the intervals are compared via a shared unit of measurement
    (inches, centimeters, etc.).

    Schwarzschild: subcomparatives require that the two scales be
    **commensurable** — measurable in the same units. -/
def subcomparative {Entity D : Type*} [LinearOrder D]
    (μ₁ μ₂ : Entity → D) (a b : Entity) : Prop :=
  μ₁ a > μ₂ b

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Extent Functions
-- ════════════════════════════════════════════════════

/-- The positive interval's membership predicate is exactly `posExt`:
    d is in the interval [⊥, μ(x)] iff d ∈ posExt(μ, x).
    This connects Schwarzschild's interval semantics to the algebraic
    extent functions in `Core.Scale`. -/
theorem positiveInterval_iff_posExt {Entity D : Type*}
    [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (x : Entity) (d : D) :
    (positiveInterval μ x).lower ≤ d ∧ d ≤ (positiveInterval μ x).upper ↔
      d ∈ Core.Scale.posExt μ x := by
  simp [positiveInterval, Core.Scale.posExt]

end Semantics.Degree.Intervals
