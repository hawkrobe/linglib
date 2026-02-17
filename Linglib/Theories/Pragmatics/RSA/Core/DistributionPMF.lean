import Linglib.Theories.Pragmatics.RSA.Core.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.ENNReal.Basic

/-!
# ExactDist ↔ Mathlib PMF Bridge

Noncomputable bridge connecting `ExactDist` (exact rational distributions)
to Mathlib's `PMF` type. Separated from `Distribution.lean` to keep
heavy Mathlib imports (measure theory, ENNReal) out of the main RSA chain.

Import this file only when you need to connect RSA computations to
Mathlib's probability infrastructure.
-/

namespace ExactDist

variable {α : Type*} [Fintype α]

/-- Convert ExactDist to Mathlib's PMF. Noncomputable; use for proofs. -/
noncomputable def toPMF (d : ExactDist α) : PMF α :=
  PMF.ofFintype (λ x => ENNReal.ofReal (d.mass x : ℝ)) (by
    simp only [← ENNReal.ofReal_sum_of_nonneg (λ x _ => Rat.cast_nonneg.mpr (d.nonneg x))]
    simp only [← Rat.cast_sum, d.sum_one, Rat.cast_one, ENNReal.ofReal_one])

/-- PMF probability agrees with ExactDist probability. -/
theorem toPMF_apply (d : ExactDist α) (x : α) :
    d.toPMF x = ENNReal.ofReal (d.mass x : ℝ) := by
  simp only [toPMF, PMF.ofFintype_apply]

end ExactDist
