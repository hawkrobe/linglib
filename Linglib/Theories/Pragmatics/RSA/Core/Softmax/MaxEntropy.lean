import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Basic

/-!
# Softmax as Maximum Entropy Distribution (Re-export)

Re-exports entropy and maximum entropy results from `Core.RationalAction`.
-/

namespace Softmax

open Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable abbrev shannonEntropy (p : ι → ℝ) : ℝ := Core.shannonEntropy p
noncomputable abbrev entropyRegObjective (s : ι → ℝ) (α : ℝ) (p : ι → ℝ) : ℝ :=
  Core.entropyRegObjective s α p
noncomputable abbrev freeEnergy (s : ι → ℝ) (α : ℝ) (p : ι → ℝ) : ℝ :=
  Core.freeEnergy s α p

theorem shannonEntropy_nonneg (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    0 ≤ shannonEntropy p :=
  Core.shannonEntropy_nonneg p hp_nonneg hp_sum

theorem shannonEntropy_uniform :
    shannonEntropy (λ _ : ι => 1 / Fintype.card ι) = Real.log (Fintype.card ι) :=
  Core.shannonEntropy_uniform

theorem shannonEntropy_softmax (s : ι → ℝ) (α : ℝ) :
    shannonEntropy (softmax s α) =
    Real.log (partitionFn s α) - α * ∑ i : ι, softmax s α i * s i :=
  Core.shannonEntropy_softmax s α

theorem entropyRegObjective_softmax (s : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    entropyRegObjective s α (softmax s α) = (1 / α) * Real.log (partitionFn s α) :=
  Core.entropyRegObjective_softmax s α hα

theorem max_entropy_duality (s : ι → ℝ) (c : ℝ)
    (α : ℝ) (hα : 0 < α) (h_constraint : ∑ i : ι, softmax s α i * s i = c) :
    shannonEntropy (softmax s α) = Real.log (partitionFn s α) - α * c :=
  Core.max_entropy_duality s c α hα h_constraint

-- Sorry'd theorems (re-exported with sorry)

noncomputable abbrev klDiv (p q : ι → ℝ) : ℝ := Core.klFinite p q

theorem shannonEntropy_le_log_card (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card ι) :=
  Core.shannonEntropy_le_log_card p hp_nonneg hp_sum

theorem softmax_maximizes_entropyReg (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    entropyRegObjective s α p ≤ entropyRegObjective s α (softmax s α) :=
  Core.softmax_maximizes_entropyReg s α hα p hp_nonneg hp_sum

theorem softmax_minimizes_freeEnergy (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    freeEnergy s α (softmax s α) ≤ freeEnergy s α p :=
  Core.softmax_minimizes_freeEnergy s α hα p hp_nonneg hp_sum

theorem logSumExp_convex (s : ι → ℝ) :
    ConvexOn ℝ Set.univ (λ α => logSumExp s α) :=
  Core.logSumExp_convex s

theorem deriv_logSumExp (s : ι → ℝ) (α : ℝ) :
    deriv (λ α => logSumExp s α) α = ∑ i : ι, softmax s α i * s i :=
  Core.deriv_logSumExp s α

end Softmax
