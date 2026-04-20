import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

/-!
# Yang's Tolerance Principle @cite{yang-2016}

A productivity criterion for rule learning. Given a rule with `n` items in its
scope and `e` exceptions (items in scope that fail to obey the rule), the rule
is **tolerated** (treated as productive) iff

  `e ≤ n / ln n`.

Below this threshold, the cost of memorizing exceptions is outweighed by the
generality of the rule; above it, the learner abandons the rule and treats the
items as lexically listed. The threshold `θ_N = N / ln N` is derived in
@cite{yang-2016} from a sufficiency condition for the Elsewhere Condition under
serial rule access.

This module defines the threshold and the productivity predicate. It is
deliberately minimal — actual numerical certificates for specific `(n, e)`
pairs are deferred to the study files that need them.

@cite{belth-2026} invokes the principle as the productivity gate inside
the D2L tier-learner; see
`Phenomena/Phonology/Studies/Belth2026.lean`. Other potential
consumers (Yang's morphological productivity, infant rule generalization
@cite{emond-shi-2021}) are not yet wired in.
-/

namespace Theories.Learning.TolerancePrinciple

/-- The tolerance threshold for a vocabulary of size `n`. When `n ≤ 1`,
    `Real.log n ≤ 0` and the threshold collapses (mathlib's convention
    makes division by zero return zero) — productivity in the trivial
    case is governed by `tolerates`'s pointwise definition, not by
    interpreting the threshold as a positive bound. -/
noncomputable def threshold (n : ℕ) : ℝ := (n : ℝ) / Real.log n

/-- A rule with `n` items in scope and `e` exceptions is **tolerated** iff
    the exception count fits under Yang's threshold. -/
def tolerates (n e : ℕ) : Prop := (e : ℝ) ≤ threshold n

/-- The threshold is nonnegative for every `n`. For `n ≥ 1`, both numerator
    and denominator are nonnegative; for `n = 0`, mathlib's `Real.log 0 = 0`
    makes the quotient `0 / 0 = 0`. -/
theorem threshold_nonneg (n : ℕ) : 0 ≤ threshold n := by
  unfold threshold
  apply div_nonneg (Nat.cast_nonneg n)
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- A rule with no exceptions is always tolerated. -/
theorem tolerates_zero (n : ℕ) : tolerates n 0 := by
  simpa [tolerates] using threshold_nonneg n

end Theories.Learning.TolerancePrinciple
