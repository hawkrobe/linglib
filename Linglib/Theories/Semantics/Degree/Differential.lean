import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core
import Mathlib.Tactic.Linarith

/-!
# Differential Comparative Semantics
@cite{schwarzschild-2005} @cite{solt-2015} @cite{winter-2005}

Compositional semantics for measure phrase differentials in comparatives:
"3 inches taller", "twice as tall as".

## Measure Phrase Composition

Schwarzschild (2005): measure phrases modify the degree argument of the
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
  deriving DecidableEq, BEq, Repr

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

end Semantics.Degree.Differential
