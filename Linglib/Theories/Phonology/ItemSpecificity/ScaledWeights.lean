import Linglib.Theories.Phonology.LexicalFrequency.Defs
import Linglib.Core.Constraint.OT.Basic

/-!
# Frequency-Scaled Weights
@cite{coetzee-pater-2008} @cite{coetzee-kawahara-2013}

The "frequency lives in the grammar, continuously" theory:
constraint weights themselves vary as a linear function of an item's
log-frequency. Unlike `IndexedConstraints` (discontinuous, two
strata), scaled-weights produce a *gradient* response to frequency
within a single grammar.

The schema:

  `effectiveWeight(c, item) = baseWeight(c) + slope(c) · tokenLogFreq(item)`

Different alternations / constraints can have different slopes:
positive slope means "high-frequency items are more strongly subject
to the constraint" (the empirical pattern in
@cite{coetzee-kawahara-2013} for Japanese geminate devoicing); negative
slope means the opposite (high-frequency items more lenient — closer
to representation-strength predictions).

## Empirical signature

Scaled-weights theories predict a **continuous monotonic** dependence
of violation force on log-frequency. Where the empirical distribution
shows two distinct distributions and no gradience, `IndexedConstraints`
under-fits *less*. Where the distribution is continuous and monotonic
but **always in the same direction across constraints sharing the same
target**, scaled-weights is the better fit. Where direction *flips*
across constraints (e.g., compound-frequency raises nasalisation but
N2-frequency lowers it, as in
`Phenomena/Phonology/Studies/BreissKatsudaKawahara2026.lean`), this
theory needs separate slopes per constraint — which it has, and so
remains a viable account.
-/

namespace Phonology.LexicalFrequency.Scaled

open Phonology.LexicalFrequency
open Core.Constraint.OT (NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: Scaled weight
-- ============================================================================

/-- The effective weight of a constraint at a given item: a linear
    function of the item's log-frequency. -/
def scaledWeight {α : Type} [HasTokenFreq α]
    (baseWeight slope : ℝ) (a : α) : ℝ :=
  baseWeight + slope * tokenLogFreq a

/-- Build a frequency-scaled NamedConstraint. The `eval` field returns
    a `Nat`, so we cannot directly store a scaled `ℝ` weight there.
    Instead, this constructor returns a *weighted* constraint
    representation — see `Theories/Phonology/OptimalityTheory/Constraints.lean`
    for the weighted-constraint type. The implementation here is the
    *abstract scaled-weight rule*; the OT-side wiring is supplied by
    the consumer. -/
structure ScaledConstraint (α : Type) [HasTokenFreq α] where
  base : NamedConstraint α
  baseWeight : ℝ
  slope : ℝ

namespace ScaledConstraint

variable {α : Type} [HasTokenFreq α]

/-- The harmony contribution of a scaled constraint at a candidate:
    `scaledWeight × violations`. The harmony is the negative of the
    cost; consumers minimising cost equivalently maximise harmony. -/
def harmony (s : ScaledConstraint α) (a : α) : ℝ :=
  scaledWeight s.baseWeight s.slope a * (s.base.eval a : ℝ)

end ScaledConstraint

-- ============================================================================
-- § 2: Continuity (the empirical signature of the theory)
-- ============================================================================

/-- Linear monotonicity: when the slope is positive, the scaled weight
    is monotonically non-decreasing in token log-frequency. The
    contrast with indexed constraints' constant-within-stratum is
    direct. -/
theorem scaledWeight_monotone_in_freq
    {α : Type} [HasTokenFreq α] (baseWeight slope : ℝ) (h : 0 ≤ slope)
    (a b : α) (hab : tokenLogFreq a ≤ tokenLogFreq b) :
    scaledWeight baseWeight slope a ≤ scaledWeight baseWeight slope b := by
  unfold scaledWeight
  exact (add_le_add_iff_left baseWeight).mpr (mul_le_mul_of_nonneg_left hab h)

end Phonology.LexicalFrequency.Scaled
