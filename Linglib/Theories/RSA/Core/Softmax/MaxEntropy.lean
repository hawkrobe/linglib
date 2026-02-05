import Linglib.Theories.RSA.Core.Softmax.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Softmax as Maximum Entropy Distribution

Softmax maximizes entropy-regularized objective: argmax_p [⟨s, p⟩ + (1/α) H(p)].
-/

namespace Softmax

open Real BigOperators Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Shannon entropy: H(p) = -Σᵢ pᵢ log pᵢ. -/
noncomputable def shannonEntropy (p : ι → ℝ) : ℝ :=
  -∑ i : ι, if p i = 0 then 0 else p i * log (p i)

/-- Entropy is non-negative for probability distributions. -/
theorem shannonEntropy_nonneg (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    0 ≤ shannonEntropy p := by
  simp only [shannonEntropy]
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : p i = 0
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    have hp_pos : 0 < p i := (hp_nonneg i).lt_of_ne' hi
    have hp_le : p i ≤ 1 := by
      calc p i ≤ ∑ j : ι, p j := Finset.single_le_sum (λ j _ => hp_nonneg j) (Finset.mem_univ i)
        _ = 1 := hp_sum
    have hlog : log (p i) ≤ 0 := log_nonpos (le_of_lt hp_pos) hp_le
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hp_pos) hlog

/-- Maximum entropy is achieved by uniform distribution. -/
theorem shannonEntropy_le_log_card (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    shannonEntropy p ≤ log (Fintype.card ι) := by
  sorry

/-- Entropy of uniform distribution. -/
theorem shannonEntropy_uniform :
    shannonEntropy (λ _ : ι => 1 / Fintype.card ι) = log (Fintype.card ι) := by
  simp only [shannonEntropy]
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard
  have hunif_pos : (0 : ℝ) < 1 / Fintype.card ι := by positivity
  have hunif_ne : (1 : ℝ) / Fintype.card ι ≠ 0 := ne_of_gt hunif_pos
  simp only [hunif_ne, ↓reduceIte, log_div one_ne_zero hne, log_one, zero_sub]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Entropy of softmax: H(softmax(s, α)) = log Z - α · 𝔼[s]. -/
theorem shannonEntropy_softmax (s : ι → ℝ) (α : ℝ) :
    shannonEntropy (softmax s α) =
    log (partitionFn s α) - α * ∑ i : ι, softmax s α i * s i := by
  simp only [shannonEntropy, softmax, partitionFn]
  have hZ : 0 < ∑ j : ι, exp (α * s j) := partitionFn_pos s α
  have hne : (∑ j : ι, exp (α * s j)) ≠ 0 := ne_of_gt hZ
  -- Each softmax(i) > 0, so the if-then-else simplifies
  have hsm_pos : ∀ i, exp (α * s i) / ∑ j : ι, exp (α * s j) ≠ 0 := by
    intro i; exact ne_of_gt (div_pos (exp_pos _) hZ)
  simp only [hsm_pos, ↓reduceIte]
  -- log(exp(α·sᵢ)/Z) = α·sᵢ - log Z
  have hlog : ∀ i, log (exp (α * s i) / ∑ j : ι, exp (α * s j)) =
                   α * s i - log (∑ j : ι, exp (α * s j)) := by
    intro i; rw [log_div (ne_of_gt (exp_pos _)) hne, log_exp]
  simp_rw [hlog]
  -- Σ(exp/Z)·(αs - log Z) = Σ(exp/Z)·αs - Σ(exp/Z)·log Z = α·𝔼[s] - log Z
  have hsum1 : ∑ i : ι, exp (α * s i) / ∑ j : ι, exp (α * s j) = 1 := by
    rw [← Finset.sum_div, div_self hne]
  calc -∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i - log (∑ j : ι, exp (α * s j)))
      = -∑ i : ι, ((exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) -
                   (exp (α * s i) / ∑ j : ι, exp (α * s j)) * log (∑ j : ι, exp (α * s j))) := by
        congr 1; apply Finset.sum_congr rfl; intros; ring
    _ = -(∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) -
          ∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * log (∑ j : ι, exp (α * s j))) := by
        rw [Finset.sum_sub_distrib]
    _ = -(∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) -
          (∑ i : ι, exp (α * s i) / ∑ j : ι, exp (α * s j)) * log (∑ j : ι, exp (α * s j))) := by
        rw [← Finset.sum_mul]
    _ = -(∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) - 1 * log (∑ j : ι, exp (α * s j))) := by
        rw [hsum1]
    _ = log (∑ j : ι, exp (α * s j)) - ∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * (α * s i) := by ring
    _ = log (∑ j : ι, exp (α * s j)) - ∑ i : ι, α * ((exp (α * s i) / ∑ j : ι, exp (α * s j)) * s i) := by
        congr 1; apply Finset.sum_congr rfl; intros; ring
    _ = log (∑ j : ι, exp (α * s j)) - α * ∑ i : ι, (exp (α * s i) / ∑ j : ι, exp (α * s j)) * s i := by
        rw [← Finset.mul_sum]

/-- Alternative form using log-sum-exp. -/
theorem shannonEntropy_softmax' (s : ι → ℝ) (α : ℝ) :
    shannonEntropy (softmax s α) =
    logSumExp s α - α * ∑ i : ι, softmax s α i * s i := by
  simp only [logSumExp]
  exact shannonEntropy_softmax s α

/-- Entropy-regularized objective: G_α(p, s) = ⟨s, p⟩ + (1/α) H(p). -/
noncomputable def entropyRegObjective (s : ι → ℝ) (α : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i : ι, p i * s i + (1 / α) * shannonEntropy p

/-- Fact 5: Softmax maximizes the entropy-regularized objective. -/
theorem softmax_maximizes_entropyReg (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    entropyRegObjective s α p ≤ entropyRegObjective s α (softmax s α) := by
  sorry

/-- The maximum value of the entropy-regularized objective. -/
theorem entropyRegObjective_softmax (s : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    entropyRegObjective s α (softmax s α) = (1 / α) * log (partitionFn s α) := by
  simp only [entropyRegObjective, shannonEntropy_softmax]
  have hne : α ≠ 0 := ne_of_gt hα
  field_simp
  ring

/-- Softmax is the unique maximizer. -/
theorem softmax_unique_maximizer (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1)
    (h_max : entropyRegObjective s α p = entropyRegObjective s α (softmax s α)) :
    p = softmax s α := by
  sorry

/-- KL divergence from q to p. -/
noncomputable def klDiv (p q : ι → ℝ) : ℝ :=
  ∑ i : ι, if p i = 0 then 0 else p i * log (p i / q i)

/-- KL divergence is non-negative. -/
theorem klDiv_nonneg (p q : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i : ι, p i = 1) (hq_sum : ∑ i : ι, q i = 1) :
    0 ≤ klDiv p q := by
  sorry

/-- KL divergence is zero iff distributions are equal. -/
theorem klDiv_eq_zero_iff (p q : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i : ι, p i = 1) (hq_sum : ∑ i : ι, q i = 1) :
    klDiv p q = 0 ↔ p = q := by
  sorry

/-- Softmax minimizes KL divergence from prior weighted by scores. -/
theorem softmax_minimizes_kl_plus_energy (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    klDiv p (λ _ => 1 / Fintype.card ι) - α * ∑ i, p i * s i ≥
    klDiv (softmax s α) (λ _ => 1 / Fintype.card ι) - α * ∑ i, softmax s α i * s i := by
  sorry

/-- Free energy (from statistical mechanics). -/
noncomputable def freeEnergy (s : ι → ℝ) (α : ℝ) (p : ι → ℝ) : ℝ :=
  -∑ i : ι, p i * s i - (1 / α) * shannonEntropy p

/-- Softmax is the Boltzmann distribution: minimizes free energy. -/
theorem softmax_minimizes_freeEnergy (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    freeEnergy s α (softmax s α) ≤ freeEnergy s α p := by
  -- This is equivalent to softmax_maximizes_entropyReg (negation)
  simp only [freeEnergy]
  have h := softmax_maximizes_entropyReg s α hα p hp_nonneg hp_sum
  simp only [entropyRegObjective] at h
  linarith

/-- Softmax is an exponential family distribution. -/
theorem softmax_exponential_family (s : ι → ℝ) (α : ℝ) (i : ι) :
    softmax s α i = exp (α * s i - logSumExp s α) := by
  simp only [softmax, logSumExp]
  rw [exp_sub]
  have h : exp (log (∑ j : ι, exp (α * s j))) = ∑ j : ι, exp (α * s j) :=
    exp_log (partitionFn_pos s α)
  rw [h]

/-- The log-partition function is convex in α. -/
theorem logSumExp_convex (s : ι → ℝ) :
    ConvexOn ℝ Set.univ (λ α => logSumExp s α) := by
  sorry

/-- Derivative of log-partition gives expected value. -/
theorem deriv_logSumExp (s : ι → ℝ) (α : ℝ) :
    deriv (λ α => logSumExp s α) α = ∑ i : ι, softmax s α i * s i := by
  -- TODO: Requires calculus lemmas for sum of exp derivatives
  -- d/dα log(Z) = Z'/Z where Z = ∑ exp(α * s_j), Z' = ∑ s_j * exp(α * s_j)
  sorry

/-- Strong duality: max entropy = min free energy. -/
theorem max_entropy_duality (s : ι → ℝ) (c : ℝ)
    (α : ℝ) (hα : 0 < α) (h_constraint : ∑ i : ι, softmax s α i * s i = c) :
    shannonEntropy (softmax s α) = log (partitionFn s α) - α * c := by
  rw [shannonEntropy_softmax, h_constraint]

end Softmax
