import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core
import Mathlib.Tactic.Linarith

/-!
# Differential Comparative Semantics
@cite{schwarzschild-2005} @cite{solt-2015} @cite{winter-2005}

Compositional semantics for measure phrase differentials in comparatives:
"3 inches taller", "twice as tall as".

## Measure Phrase Composition

@cite{schwarzschild-2005}: measure phrases modify the degree argument of the
comparative, specifying the gap between matrix and standard degrees.

    "A is 3 inches taller than B" iff height(A) - height(B) = 3 inches

This requires a **ratio scale** (with a meaningful zero point and unit),
not just an ordinal or interval scale. Hence "3 inches taller" ✓ but
"*3 units more beautiful" ✗.

-/

namespace Semantics.Degree.Differential

-- ════════════════════════════════════════════════════
-- § 1. Differential Semantics
-- ════════════════════════════════════════════════════

/-- Differential comparative: "A is d-much Adj-er than B" iff the
    difference μ(A) - μ(B) = d.

    Requires a type with subtraction (ring-like structure), not just
    ordering. This is what makes measure phrase differentials more
    restrictive than bare comparatives. -/
def differentialComparative {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (diff : ℚ) : Prop :=
  μ a - μ b = diff

/-- The differential is positive iff the comparative holds. -/
theorem differential_positive_iff {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (diff : ℚ) (hdiff : diff > 0) :
    differentialComparative μ a b diff → μ a > μ b := by
  intro h
  simp [differentialComparative] at h
  linarith

-- ════════════════════════════════════════════════════
-- § 2. Scale Type Restrictions
-- ════════════════════════════════════════════════════

/-- Measurement level: what kind of scale an adjective's degrees live on.
    Measure phrase differentials require at least interval scale;
    factor phrases require ratio scale. -/
inductive MeasurementLevel where
  | ordinal    -- only ordering (ranking, not distance)
  | interval   -- meaningful distances (temperature in °C/°F)
  | ratio      -- meaningful zero + distances (height, weight)
  deriving DecidableEq, Repr

/-- Does this measurement level admit measure phrase differentials? -/
def admitsMeasurePhrase : MeasurementLevel → Bool
  | .ratio    => true
  | .interval => true   -- "10 degrees warmer"
  | .ordinal  => false  -- "*3 units more beautiful"

/-- Does this measurement level admit factor phrases ("twice as tall")? -/
def admitsFactorPhrase : MeasurementLevel → Bool
  | .ratio    => true   -- "twice as tall" (zero point meaningful)
  | .interval => false  -- "*twice as hot" (in °C; no meaningful zero)
  | .ordinal  => false

-- ════════════════════════════════════════════════════
-- § 3. Factor Phrases
-- ════════════════════════════════════════════════════

/-- Factor phrase equative: "A is n times as tall as B" iff μ(A) = n × μ(B).
    Requires ratio scale: a meaningful zero point. -/
def factorEquative {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (factor : ℚ) : Prop :=
  μ a = factor * μ b

-- ════════════════════════════════════════════════════
-- § 4. Extensive Scales and Cross-Dimensional Comparison
-- ════════════════════════════════════════════════════

/-- **Extensive measurement level**: a ratio scale that additionally
    permits cross-dimensional comparison. Spatial extent is the
    canonical example: height, width, length, and depth all map onto
    the same underlying extensive scale (cm, inches, etc.), so
    "the ladder is shorter than the house is high" is meaningful.

    @cite{buring-2007} (p. 2, footnote 2): "spatial extent is the only
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
def admitsSubcomparative : MeasurementLevelExt → Bool
  | .extensive => true
  | _          => false

/-- Extensive scales admit everything lower scales do. -/
theorem extensive_admits_measure : admitsMeasurePhrase .ratio = true := rfl
theorem extensive_admits_factor : admitsFactorPhrase .ratio = true := rfl

/-- Cross-dimensional comparison data: only spatial extent (extensive
    scale) licenses subcomparatives. -/
structure SubcomparativeAdmissibilityDatum where
  matrixAdj : String
  embeddedAdj : String
  sharedScale : String
  level : MeasurementLevelExt
  acceptable : Bool
  deriving Repr

def subcomparativeAdmissibility : List SubcomparativeAdmissibilityDatum :=
  [ ⟨"long", "wide", "spatial extent", .extensive, true⟩
  , ⟨"tall", "wide", "spatial extent", .extensive, true⟩
  , ⟨"deep", "tall", "spatial extent", .extensive, true⟩
  , ⟨"hot", "expensive", "(none)", .ordinal, false⟩
  , ⟨"smart", "tall", "(none)", .ordinal, false⟩
  ]

-- Subcomparative acceptability tracks extensive level.
#guard subcomparativeAdmissibility.all (λ d =>
  d.acceptable == admitsSubcomparative d.level)

end Semantics.Degree.Differential
