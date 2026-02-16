import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field

/-!
# Softmax Function: Basic Properties

Following Franke & Degen "The softmax function."
-/

namespace Softmax

open Real BigOperators Finset

variable {ι : Type*} [Fintype ι]

/-- The softmax function: softmax(s, α)ᵢ = exp(α · sᵢ) / Σⱼ exp(α · sⱼ). -/
noncomputable def softmax (s : ι → ℝ) (α : ℝ) : ι → ℝ :=
  λ i => exp (α * s i) / ∑ j : ι, exp (α * s j)

/-- The partition function (normalizing constant) Z = Σⱼ exp(α · sⱼ) -/
noncomputable def partitionFn (s : ι → ℝ) (α : ℝ) : ℝ :=
  ∑ j : ι, exp (α * s j)

/-- Log-sum-exp: log of partition function -/
noncomputable def logSumExp (s : ι → ℝ) (α : ℝ) : ℝ :=
  log (∑ j : ι, exp (α * s j))

/-- The partition function is always positive. -/
theorem partitionFn_pos [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    0 < partitionFn s α := by
  apply Finset.sum_pos
  · intro i _
    exact exp_pos _
  · exact Finset.univ_nonempty

theorem partitionFn_ne_zero [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    partitionFn s α ≠ 0 :=
  ne_of_gt (partitionFn_pos s α)

/-- Each softmax probability is positive. (Fact 1, part 1) -/
theorem softmax_pos [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    0 < softmax s α i := by
  simp only [softmax]
  exact div_pos (exp_pos _) (partitionFn_pos s α)

/-- Softmax probabilities sum to 1. (Fact 1, part 2) -/
theorem softmax_sum_eq_one [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    ∑ i : ι, softmax s α i = 1 := by
  simp only [softmax]
  have h : ∑ x : ι, exp (α * s x) / ∑ j : ι, exp (α * s j) =
           (∑ x : ι, exp (α * s x)) / ∑ j : ι, exp (α * s j) := by
    rw [Finset.sum_div]
  rw [h]
  exact div_self (partitionFn_ne_zero s α)

/-- Softmax is non-negative. -/
theorem softmax_nonneg [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    0 ≤ softmax s α i :=
  le_of_lt (softmax_pos s α i)

/-- Softmax is at most 1. -/
theorem softmax_le_one [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    softmax s α i ≤ 1 := by
  have h := softmax_sum_eq_one s α
  have hpos : ∀ j, 0 ≤ softmax s α j := λ j => softmax_nonneg s α j
  calc softmax s α i
      ≤ ∑ j : ι, softmax s α j := Finset.single_le_sum (λ j _ => hpos j) (Finset.mem_univ i)
    _ = 1 := h

/-- Fact 2: Odds are determined by score differences: pᵢ/pⱼ = exp(α(sᵢ - sⱼ)). -/
theorem softmax_odds [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    softmax s α i / softmax s α j = exp (α * (s i - s j)) := by
  simp only [softmax]
  have hZ : (∑ k : ι, exp (α * s k)) ≠ 0 := partitionFn_ne_zero s α
  have hj : exp (α * s j) ≠ 0 := ne_of_gt (exp_pos _)
  field_simp
  have key : α * s j + α * (s i - s j) = α * s i := by ring
  rw [← exp_add, key]

/-- Log-odds equal scaled score difference. -/
theorem log_softmax_odds [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    log (softmax s α i / softmax s α j) = α * (s i - s j) := by
  rw [softmax_odds, log_exp]

/-- Ratio form of Fact 2. -/
theorem softmax_ratio [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i j : ι) :
    softmax s α i = softmax s α j * exp (α * (s i - s j)) := by
  have h := softmax_odds s α i j
  have hne : softmax s α j ≠ 0 := ne_of_gt (softmax_pos s α j)
  field_simp at h ⊢
  linarith [h]

/-- The logistic (sigmoid) function. -/
noncomputable def logistic (x : ℝ) : ℝ := 1 / (1 + exp (-x))

/-- Fact 3: For n = 2, softmax reduces to logistic. -/
theorem softmax_binary (s : Fin 2 → ℝ) (α : ℝ) :
    softmax s α 0 = logistic (α * (s 0 - s 1)) := by
  simp only [softmax, logistic, Fin.sum_univ_two]
  have key : α * s 0 + (-(α * (s 0 - s 1))) = α * s 1 := by ring
  have h : exp (α * s 0) + exp (α * s 1) =
           exp (α * s 0) * (1 + exp (-(α * (s 0 - s 1)))) := by
    rw [mul_add, mul_one, ← exp_add, key]
  rw [h, ← div_div, div_self (ne_of_gt (exp_pos _))]

/-- Fact 6: Softmax is translation invariant. -/
theorem softmax_add_const (s : ι → ℝ) (α c : ℝ) :
    softmax (λ i => s i + c) α = softmax s α := by
  funext i
  simp only [softmax]
  have hexp : ∀ j, exp (α * (s j + c)) = exp (α * s j) * exp (α * c) := by
    intro j
    rw [← exp_add]
    ring_nf
  simp_rw [hexp, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (ne_of_gt (exp_pos _))]

/-- Fact 8: Multiplicative scaling can be absorbed into α. -/
theorem softmax_scale (s : ι → ℝ) (α a : ℝ) (ha : a ≠ 0) :
    softmax (λ i => a * s i) (α / a) = softmax s α := by
  funext i
  simp only [softmax]
  congr 1
  · congr 1
    field_simp
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    field_simp

/-- Higher scores get higher probabilities (for α > 0). -/
theorem softmax_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : 0 < α) (i j : ι)
    (hij : s i ≤ s j) :
    softmax s α i ≤ softmax s α j := by
  simp only [softmax]
  apply div_le_div_of_nonneg_right _ (le_of_lt (partitionFn_pos s α))
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hij (le_of_lt hα)

/-- Strict monotonicity. -/
theorem softmax_strict_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : 0 < α)
    (i j : ι) (hij : s i < s j) :
    softmax s α i < softmax s α j := by
  simp only [softmax]
  apply div_lt_div_of_pos_right _ (partitionFn_pos s α)
  apply exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left hij hα

/-- At α = 0, softmax is uniform. -/
theorem softmax_zero [Nonempty ι] (s : ι → ℝ) :
    softmax s 0 = λ _ => 1 / (Fintype.card ι : ℝ) := by
  funext i
  simp only [softmax, zero_mul, exp_zero, Finset.sum_const, Finset.card_univ,
             nsmul_eq_mul, mul_one]

/-- For α < 0, lower scores get higher probabilities. -/
theorem softmax_neg_mono [Nonempty ι] (s : ι → ℝ) {α : ℝ} (hα : α < 0) (i j : ι)
    (hij : s i ≤ s j) :
    softmax s α j ≤ softmax s α i := by
  simp only [softmax]
  apply div_le_div_of_nonneg_right _ (le_of_lt (partitionFn_pos s α))
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hij (le_of_lt hα)

/-- Softmax with default α = 1. -/
noncomputable def softmax1 (s : ι → ℝ) : ι → ℝ := softmax s 1

/-- Temperature form: τ = 1/α. -/
noncomputable def softmaxTemp (s : ι → ℝ) (τ : ℝ) : ι → ℝ :=
  softmax s (1 / τ)

-- ============================================================================
-- KL Divergence and Gibbs Variational Principle
-- ============================================================================

/-!
## KL Divergence and the Gibbs Variational Principle

The softmax distribution uniquely maximizes entropy + expected score
on the probability simplex. This is the mathematical foundation for
RSA convergence (Zaslavsky et al. 2020, Proposition 1).

### Proof strategy

The Gibbs VP reduces to KL non-negativity via three identities:

1. H(p) + KL(p‖q) = -∑ pᵢ log qᵢ          (negMulLog + KL term telescope)
2. -∑ pᵢ log qᵢ = -α⟨p,s⟩ + log Z          (substitute log qᵢ = α sᵢ - log Z)
3. H(q) + α⟨q,s⟩ = log Z                    (softmax self-information)

Combining: H(p) + α⟨p,s⟩ + KL = log Z = H(q) + α⟨q,s⟩, so KL ≥ 0 ⟹ LHS ≤ RHS.

KL ≥ 0 follows from log(x) ≤ x - 1 (Mathlib: `Real.log_le_sub_one_of_pos`).

### References

- Cover & Thomas (2006), Elements of Information Theory, Ch. 2
- Zaslavsky et al. (2020), A Rate-Distortion view of RSA, SM §B
-/

/-- Finite KL divergence: KL(p ‖ q) = Σ pᵢ · log(pᵢ / qᵢ).
    Convention: 0 · log(0/q) = 0. -/
noncomputable def klFinite (p q : ι → ℝ) : ℝ :=
  ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i)

/-- KL divergence is non-negative for finite distributions.

    Proof: log(qᵢ/pᵢ) ≤ qᵢ/pᵢ - 1, so pᵢ log(pᵢ/qᵢ) ≥ pᵢ - qᵢ.
    Summing: KL(p‖q) ≥ Σ(pᵢ - qᵢ) = 1 - 1 = 0. -/
theorem kl_nonneg [Nonempty ι] {p q : ι → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    0 ≤ klFinite p q := by
  -- Each term ≥ pᵢ - qᵢ; sum to 0
  suffices h : ∀ i, (if p i = 0 then (0 : ℝ) else p i * Real.log (p i / q i)) ≥ p i - q i by
    have hge : klFinite p q ≥ ∑ i, (p i - q i) :=
      Finset.sum_le_sum (fun i _ => h i)
    simp only [Finset.sum_sub_distrib, hp_sum, hq_sum, sub_self] at hge
    linarith
  intro i
  by_cases hpi : p i = 0
  · simp only [hpi, ↓reduceIte, zero_sub]
    linarith [hq_pos i]
  · simp only [hpi, ↓reduceIte]
    have hpi_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)
    have hqi_pos : 0 < q i := hq_pos i
    -- From log(q/p) ≤ q/p - 1, multiply by -p (flip):
    -- p · log(p/q) = -p · log(q/p) ≥ -p · (q/p - 1) = p - q
    have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hqi_pos hpi_pos)
    rw [Real.log_div (ne_of_gt hpi_pos) (ne_of_gt hqi_pos)]
    -- Goal: p i * (log(p i) - log(q i)) ≥ p i - q i
    -- From hlog: log(q i) - log(p i) ≤ q i / p i - 1
    rw [Real.log_div (ne_of_gt hqi_pos) (ne_of_gt hpi_pos)] at hlog
    nlinarith [mul_div_cancel₀ (q i) (ne_of_gt hpi_pos)]

-- Softmax log identity

/-- Log of softmax = score minus log partition function. -/
theorem log_softmax [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    Real.log (softmax s α i) = α * s i - Real.log (partitionFn s α) := by
  simp only [softmax, partitionFn]
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Finset.sum_pos
    (fun j _ => Real.exp_pos _) Finset.univ_nonempty))]
  rw [Real.log_exp]

-- Gibbs Variational Principle

/-- **Gibbs Variational Principle**: softmax maximizes entropy + expected score.

    For any distribution p on ι and scores s : ι → ℝ:
      H(p) + α·⟨p, s⟩ ≤ H(q) + α·⟨q, s⟩
    where q = softmax(s, α) and H(p) = Σ negMulLog(pᵢ).

    The proof reduces to KL non-negativity via three identities:
    1. H(p) + KL(p‖q) = -∑ pᵢ log qᵢ  (negMulLog + KL term telescope)
    2. -∑ pᵢ log qᵢ = -α⟨p,s⟩ + log Z  (substitute log qᵢ = α sᵢ - log Z)
    3. H(q) + α⟨q,s⟩ = log Z            (softmax self-information)
    Combining: H(p) + α⟨p,s⟩ + KL = log Z = H(q) + α⟨q,s⟩, so KL ≥ 0 ⟹ LHS ≤ RHS. -/
theorem gibbs_variational [Nonempty ι] (s : ι → ℝ) (α : ℝ) (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) + α * ∑ i, p i * s i ≤
    (∑ i, Real.negMulLog (softmax s α i)) + α * ∑ i, softmax s α i * s i := by
  set q := softmax s α
  set logZ := Real.log (partitionFn s α)
  have hq_pos : ∀ i, 0 < q i := fun i => softmax_pos s α i
  have hq_sum : ∑ i, q i = 1 := softmax_sum_eq_one s α
  have hkl := kl_nonneg hp_nonneg hq_pos hp_sum hq_sum
  have h_logq : ∀ i, Real.log (q i) = α * s i - logZ := fun i => log_softmax s α i
  -- Identity 1: negMulLog(pᵢ) + KL_term(i) = -(pᵢ log qᵢ)  [per-term telescope]
  have h_combine : ∀ i,
      Real.negMulLog (p i) +
        (if p i = 0 then (0 : ℝ) else p i * Real.log (p i / q i)) =
      -(p i * Real.log (q i)) := by
    intro i
    by_cases hpi : p i = 0
    · simp [hpi, Real.negMulLog]
    · simp only [hpi, ↓reduceIte, Real.negMulLog]
      have hpi_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)
      rw [Real.log_div (ne_of_gt hpi_pos) (ne_of_gt (hq_pos i))]
      ring
  -- Sum of Identity 1: H(p) + KL(p‖q) = -∑ pᵢ log qᵢ
  have h1 : (∑ i, Real.negMulLog (p i)) + klFinite p q =
      -(∑ i, p i * Real.log (q i)) := by
    unfold klFinite
    rw [← Finset.sum_add_distrib]
    simp_rw [h_combine, Finset.sum_neg_distrib]
  -- Identity 2: -∑ pᵢ log qᵢ = -α⟨p,s⟩ + logZ  [via log qᵢ = α sᵢ - logZ]
  have h2 : -(∑ i, p i * Real.log (q i)) = -(α * ∑ i, p i * s i) + logZ := by
    have : ∑ i, p i * Real.log (q i) = α * ∑ i, p i * s i - logZ := by
      simp_rw [h_logq]
      rw [show ∑ i : ι, p i * (α * s i - logZ) =
          ∑ i, (α * (p i * s i) - logZ * p i) from
        Finset.sum_congr rfl fun i _ => by ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp_sum, mul_one]
    linarith
  -- Identity 3: H(q) + α⟨q,s⟩ = logZ  [softmax self-information]
  have h3 : (∑ i, Real.negMulLog (q i)) + α * ∑ i, q i * s i = logZ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show ∑ i : ι, (Real.negMulLog (q i) + α * (q i * s i)) = ∑ i, logZ * q i from
      Finset.sum_congr rfl fun i _ => by simp only [Real.negMulLog, h_logq i]; ring]
    rw [← Finset.mul_sum, hq_sum, mul_one]
  -- Combine: from h1+h2, H(p) + α⟨p,s⟩ + KL = logZ = H(q) + α⟨q,s⟩ (by h3).
  -- Since KL ≥ 0 (hkl), H(p) + α⟨p,s⟩ ≤ H(q) + α⟨q,s⟩.
  linarith

/-- The Bayesian posterior maximizes expected log-likelihood.

    For any distribution L and weight function w ≥ 0 with Σw > 0,
    the normalized w maximizes Σ (wᵢ/Σw) · log Lᵢ over distributions L.
    This is KL(w_norm ‖ L) ≥ 0 rearranged.

    This is the listener half of RSA convergence: the Bayesian update
    L(m|u) ∝ P(m)·S(u|m) maximizes E[log L]. -/
theorem bayesian_maximizes_expected_log [Nonempty ι] (w : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum_pos : 0 < ∑ i, w i)
    (L : ι → ℝ) (hL_pos : ∀ i, 0 < L i) (hL_sum : ∑ i, L i = 1) :
    ∑ i, (w i / ∑ j, w j) * Real.log (L i) ≤
    ∑ i, (w i / ∑ j, w j) * Real.log (w i / ∑ j, w j) := by
  set S := ∑ j, w j
  -- w/S is a distribution
  have hp_nonneg : ∀ i, 0 ≤ w i / S := fun i =>
    div_nonneg (hw_nonneg i) (le_of_lt hw_sum_pos)
  have hp_sum : ∑ i, w i / S = 1 := by
    rw [← Finset.sum_div]; exact div_self (ne_of_gt hw_sum_pos)
  -- KL(w/S ‖ L) ≥ 0
  have hkl := kl_nonneg hp_nonneg hL_pos hp_sum hL_sum
  -- KL = ∑ (w/S) log((w/S)/L) = ∑ (w/S) log(w/S) - ∑ (w/S) log L
  have h_expand : klFinite (fun i => w i / S) L =
      (∑ i, (w i / S) * Real.log (w i / S)) -
      (∑ i, (w i / S) * Real.log (L i)) := by
    unfold klFinite
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      by_cases hpi : w i / S = 0
      · simp [hpi]
      · simp only [hpi, ↓reduceIte]
        rw [Real.log_div (ne_of_gt (lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi)))
          (ne_of_gt (hL_pos i))]
        ring
  linarith

end Softmax
