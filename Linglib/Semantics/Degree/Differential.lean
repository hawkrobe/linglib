import Linglib.Semantics.Degree.Defs
import Linglib.Semantics.Degree.Discrete
import Mathlib.Tactic.Linarith

/-!
# Differential Comparative Semantics
[schwarzschild-2005] [solt-2015] [winter-2005]

Compositional semantics for measure phrase differentials in comparatives:
"3 inches taller", "twice as tall as".

## Measure Phrase Composition

[schwarzschild-2005]: measure phrases modify the degree argument of the
comparative, specifying the gap between matrix and standard degrees.

    "A is 3 inches taller than B" iff height(A) - height(B) = 3 inches

This requires a **ratio scale** (with a meaningful zero point and unit),
not just an ordinal or interval scale. Hence "3 inches taller" ✓ but
"*3 units more beautiful" ✗.

-/

namespace Degree.Differential

/-! ### Differential Semantics -/

/-- Differential comparative: "A is d-much Adj-er than B" iff the
    difference μ(A) - μ(B) = d.

    Requires a type with subtraction (ring-like structure), not just
    ordering. This is what makes measure phrase differentials more
    restrictive than bare comparatives. -/
def differentialComparative {Entity D : Type*} [Sub D]
    (μ : Entity → D) (a b : Entity) (diff : D) : Prop :=
  μ a - μ b = diff

/-- The differential is positive iff the comparative holds. Stated on ℚ;
generalizing requires ordered-group machinery (`[AddCommGroup D] [LinearOrder D]
[IsStrictOrderedAddMonoid D]`) that mathlib's current taxonomy splits across
multiple unbundled classes — see e.g. `Mathlib/Algebra/Order/Field/Defs.lean`
for the analogous LinearOrderedField → Field + LinearOrder + IsStrictOrderedRing
migration. Consumers (Intensional, VonStechow1984) instantiate at ℚ. -/
theorem differential_positive_iff {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (diff : ℚ) (hdiff : 0 < diff) :
    differentialComparative μ a b diff → μ b < μ a := by
  intro h
  simp only [differentialComparative] at h
  linarith

/-! ### Scale Type Restrictions -/

/-- Measurement level: what kind of scale an adjective's degrees live on.
    Measure phrase differentials require at least interval scale;
    factor phrases require ratio scale. -/
inductive MeasurementLevel where
  | ordinal    -- only ordering (ranking, not distance)
  | interval   -- meaningful distances (temperature in °C/°F)
  | ratio      -- meaningful zero + distances (height, weight)
  deriving DecidableEq, Repr

/-- Measure-phrase differentials ("10 degrees warmer") require at least
    interval scale ("*3 units more beautiful" is ordinal). -/
def AdmitsMeasurePhrase (l : MeasurementLevel) : Prop := l ≠ .ordinal

instance : DecidablePred AdmitsMeasurePhrase :=
  fun l => inferInstanceAs (Decidable (l ≠ .ordinal))

/-- Factor phrases ("twice as tall") require ratio scale — a meaningful
    zero point ("*twice as hot" in °C is interval). -/
def AdmitsFactorPhrase (l : MeasurementLevel) : Prop := l = .ratio

instance : DecidablePred AdmitsFactorPhrase :=
  fun l => inferInstanceAs (Decidable (l = .ratio))

/-! ### Factor Phrases -/

/-- Factor phrase equative: "A is n times as tall as B" iff μ(A) = n × μ(B).
    Requires ratio scale: a meaningful zero point. -/
def factorEquative {Entity D : Type*} [Mul D]
    (μ : Entity → D) (a b : Entity) (factor : D) : Prop :=
  μ a = factor * μ b

/-! ### Extensive Scales and Cross-Dimensional Comparison -/

/-- **Extensive measurement level**: a ratio scale that additionally
    permits cross-dimensional comparison. Spatial extent is the
    canonical example: height, width, length, and depth all map onto
    the same underlying extensive scale (cm, inches, etc.), so
    "the ladder is shorter than the house is high" is meaningful.

    [buring-2007] (p. 2, footnote 2): "spatial extent is the only
    scale I know of that has measurements in different dimensions
    mapped onto it." This makes cross-polar nomalies possible — they
    require comparing two different measure functions on a shared scale.

    Temperature (°C vs °F) has meaningful differences (interval) and
    no meaningful zero (not ratio). Beauty has only ordering (ordinal).
    Spatial extent has all three: ordering, differences, ratios, AND
    cross-dimensional commensurability. -/
inductive MeasurementLevelExt where
  | ordinal    -- only ordering
  | interval   -- meaningful distances
  | ratio      -- meaningful zero + distances
  | extensive  -- ratio + cross-dimensional commensurability
  deriving DecidableEq, Repr

/-- Cross-dimensional comparison (subcomparative) requires extensive
    commensurability. Two measure functions μ₁, μ₂ must share a
    common extensive unit for "μ₁(a) > μ₂(b)" to be meaningful.

    This explains why "shorter than high" ✓ (both spatial extent),
    "??hotter than expensive" ✗ (temperature ≠ price). -/
def AdmitsSubcomparative (l : MeasurementLevelExt) : Prop := l = .extensive

instance : DecidablePred AdmitsSubcomparative :=
  fun l => inferInstanceAs (Decidable (l = .extensive))

/-- Ratio scales admit both differential constructions. -/
theorem ratio_admits_measure : AdmitsMeasurePhrase .ratio := by decide
theorem ratio_admits_factor : AdmitsFactorPhrase .ratio := rfl

end Degree.Differential
