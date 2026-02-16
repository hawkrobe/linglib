/-
# Gibbs Variational Principle

The Gibbs distribution (softmax) uniquely maximizes entropy plus expected utility
over the probability simplex. This is the key lemma for RSA convergence:
it shows that each speaker/listener update step improves the G_α objective.

## Main Results

1. `kl_finite_nonneg`: Finite KL divergence is non-negative (Gibbs' inequality)
2. `gibbs_maximizes`: Softmax maximizes H(s) + α·E_s[v] on the simplex
3. `bayesian_maximizes`: The Bayesian posterior maximizes E_w[log L] on the simplex

## Proof Strategy

Both optimality results reduce to KL non-negativity:

- **Speaker optimality** (Gibbs variational principle):
  For s* = softmax(v, α), the difference f(s*) - f(s) = KL(s || s*) ≥ 0.

- **Listener optimality** (Bayesian optimality):
  For L* ∝ w (normalized weights), the difference E[log L*] - E[log L] ∝ KL(L* || L) ≥ 0.

KL non-negativity follows from Mathlib's `klFun_nonneg`:
  klFun(x) = x · log(x) + 1 - x ≥ 0 for x ≥ 0

## References

- Cover, T. M. & Thomas, J. A. (2006). Elements of Information Theory, Theorem 2.6.3
- Zaslavsky, N., Hu, J., & Levy, R. (2020). Proposition 1 (alternating maximization)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Basic

namespace RSA.GibbsVariational

open Real Finset Softmax InformationTheory

variable {ι : Type*} [Fintype ι]


-- ============================================================================
-- Finite KL Divergence
-- ============================================================================

/-- Finite KL divergence: KL(p || q) = Σᵢ pᵢ · log(pᵢ / qᵢ).

    Convention: 0 · log(0/q) = 0, matching the continuous extension. -/
noncomputable def klFinite (p q : ι → ℝ) : ℝ :=
  ∑ i, if p i = 0 then 0 else p i * log (p i / q i)

/-- When q > 0, each KL term can be written via klFun:
    p · log(p/q) = q · klFun(p/q) + (p - q) -/
private theorem kl_term_eq_klFun {p_i q_i : ℝ} (hq : 0 < q_i) (_hp : 0 ≤ p_i) :
    (if p_i = 0 then (0 : ℝ) else p_i * log (p_i / q_i)) =
    q_i * klFun (p_i / q_i) + (p_i - q_i) := by
  by_cases hp0 : p_i = 0
  · -- When p = 0: LHS = 0, RHS = q · klFun(0) + (0 - q) = q · 1 + (-q) = 0
    simp only [hp0, ↓reduceIte, zero_div, klFun_zero, mul_one, zero_sub, add_neg_cancel]
  · -- When p > 0: LHS = p · log(p/q), RHS = q · (p/q · log(p/q) + 1 - p/q) + p - q
    simp only [hp0, ↓reduceIte]
    unfold klFun
    have hq_ne : q_i ≠ 0 := ne_of_gt hq
    field_simp
    ring

/-- Finite KL divergence equals Σ qᵢ · klFun(pᵢ/qᵢ) when Σpᵢ = Σqᵢ.

    This is the f-divergence representation of KL divergence. -/
theorem kl_eq_sum_klFun (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    klFinite p q = ∑ i, q i * klFun (p i / q i) := by
  unfold klFinite
  -- Each term: (if p i = 0 then 0 else p i * log(p i / q i)) = q i * klFun(p i / q i) + (p i - q i)
  have hterm : ∀ i, (if p i = 0 then (0 : ℝ) else p i * log (p i / q i)) =
      q i * klFun (p i / q i) + (p i - q i) :=
    λ i => kl_term_eq_klFun (hq i) (hp i)
  simp_rw [hterm]
  -- Sum: Σ [q · klFun(p/q) + (p - q)] = Σ q · klFun(p/q) + (Σp - Σq)
  rw [Finset.sum_add_distrib]
  -- Σ(p - q) = Σp - Σq = 0
  have hcancel : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  linarith

/-- **Gibbs' inequality (finite form)**: KL(p || q) ≥ 0.

    For distributions p, q on a finite type with qᵢ > 0, pᵢ ≥ 0, and Σpᵢ = Σqᵢ:
      Σᵢ pᵢ · log(pᵢ/qᵢ) ≥ 0

    Proof: KL = Σ qᵢ · klFun(pᵢ/qᵢ), and each term is non-negative since
    qᵢ > 0 and klFun(x) ≥ 0 for x ≥ 0 (Mathlib: `klFun_nonneg`). -/
theorem kl_finite_nonneg (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    0 ≤ klFinite p q := by
  rw [kl_eq_sum_klFun p q hq hp hsum]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (le_of_lt (hq i))
  exact klFun_nonneg (div_nonneg (hp i) (le_of_lt (hq i)))


-- ============================================================================
-- Gibbs Variational Principle
-- ============================================================================

/-- The per-meaning speaker objective: f(s) = Σᵤ [negMulLog(sᵤ) + α · sᵤ · vᵤ].

    This is the function that the speaker maximizes for each meaning m,
    where vᵤ = log L(m|u) is the listener utility of utterance u. -/
noncomputable def speakerObj (v : ι → ℝ) (α : ℝ) (s : ι → ℝ) : ℝ :=
  ∑ u, (negMulLog (s u) + α * s u * v u)

/-- The softmax achieves f(s*) = log Z, where Z is the partition function.

    Proof: log(s*_u) = α·v_u - log Z, so:
      negMulLog(s*_u) + α·s*_u·v_u = s*_u · log Z
    Summing over u: f(s*) = (Σ s*_u) · log Z = log Z -/
theorem speakerObj_at_softmax [Nonempty ι] (v : ι → ℝ) (α : ℝ) :
    speakerObj v α (softmax v α) = logSumExp v α := by
  unfold speakerObj logSumExp
  -- For softmax s*: negMulLog(s*_u) + α·s*_u·v_u = s*_u · log Z
  have hZ_pos : 0 < partitionFn v α := partitionFn_pos v α
  have hZ_ne : partitionFn v α ≠ 0 := ne_of_gt hZ_pos
  -- Key identity: log(s*_u) = α·v_u - log Z
  have hlog_softmax : ∀ u, log (softmax v α u) = α * v u - log (partitionFn v α) := by
    intro u
    simp only [softmax, partitionFn]
    rw [log_div (ne_of_gt (exp_pos _)) (ne_of_gt (Finset.sum_pos
      (fun j _ => exp_pos _) Finset.univ_nonempty)), log_exp]
  -- Therefore: negMulLog(s*_u) + α·s*_u·v_u = s*_u · log Z
  have hterm : ∀ u, negMulLog (softmax v α u) + α * softmax v α u * v u =
      softmax v α u * log (partitionFn v α) := by
    intro u
    unfold negMulLog
    rw [hlog_softmax]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, softmax_sum_eq_one, one_mul]
  rfl

/-- Key identity: speakerObj(s) + KL(s || s*) = logSumExp (= speakerObj(s*)).

    For each u, the combined term reduces to sᵤ · log Z:
    - When sᵤ > 0: negMulLog(sᵤ) + α·sᵤ·vᵤ + sᵤ·log(sᵤ/s*ᵤ)
                    = sᵤ·(-log sᵤ + α·vᵤ + log sᵤ - log s*ᵤ)
                    = sᵤ·(α·vᵤ - log s*ᵤ)
                    = sᵤ · log Z   [since log s*ᵤ = α·vᵤ - log Z]
    - When sᵤ = 0: contributes 0 = 0 · log Z -/
private theorem speakerObj_plus_kl [Nonempty ι] (v : ι → ℝ) (α : ℝ)
    (s : ι → ℝ) (_hs_nonneg : ∀ i, 0 ≤ s i) (hs_sum : ∑ i, s i = 1) :
    speakerObj v α s + klFinite s (softmax v α) = logSumExp v α := by
  unfold speakerObj klFinite logSumExp
  rw [← Finset.sum_add_distrib]
  -- Each term reduces to s_u · log Z
  have hZ_pos : 0 < ∑ j : ι, exp (α * v j) := partitionFn_pos v α
  have hZ_ne : (∑ j : ι, exp (α * v j)) ≠ 0 := ne_of_gt hZ_pos
  have hterm : ∀ u, (negMulLog (s u) + α * s u * v u) +
      (if s u = 0 then (0 : ℝ) else s u * log (s u / softmax v α u)) =
      s u * log (∑ j : ι, exp (α * v j)) := by
    intro u
    by_cases hs0 : s u = 0
    · simp [hs0, negMulLog]
    · simp only [hs0, ↓reduceIte]
      have hs_pos : 0 < softmax v α u := softmax_pos v α u
      rw [log_div hs0 (ne_of_gt hs_pos)]
      -- log(softmax v α u) = α·v_u - log Z
      have hlog_sm : log (softmax v α u) = α * v u - log (∑ j : ι, exp (α * v j)) := by
        simp only [softmax]
        rw [log_div (ne_of_gt (exp_pos _)) (ne_of_gt (Finset.sum_pos
          (fun j _ => exp_pos _) Finset.univ_nonempty)), log_exp]
      rw [hlog_sm]
      unfold negMulLog
      ring
  simp_rw [hterm, ← Finset.sum_mul, hs_sum, one_mul]

/-- **Gibbs Variational Principle**: The softmax distribution maximizes
    entropy plus expected utility on the probability simplex.

    For any distribution s on the simplex (sᵢ ≥ 0, Σsᵢ = 1):
      speakerObj v α s ≤ speakerObj v α (softmax v α)

    Proof: speakerObj(s) = speakerObj(s*) - KL(s || s*) ≤ speakerObj(s*)
    since KL(s || s*) ≥ 0 by Gibbs' inequality. -/
theorem gibbs_maximizes [Nonempty ι] (v : ι → ℝ) (α : ℝ)
    (s : ι → ℝ) (hs_nonneg : ∀ i, 0 ≤ s i) (hs_sum : ∑ i, s i = 1) :
    speakerObj v α s ≤ speakerObj v α (softmax v α) := by
  have hkl := kl_finite_nonneg s (softmax v α)
    (λ i => softmax_pos v α i) hs_nonneg
    (by rw [hs_sum, softmax_sum_eq_one])
  have heq := speakerObj_plus_kl v α s hs_nonneg hs_sum
  rw [← speakerObj_at_softmax] at heq
  linarith


-- ============================================================================
-- Bayesian Optimality
-- ============================================================================

/-- **Bayesian optimality**: The normalized posterior maximizes weighted log-likelihood
    on the probability simplex.

    For weights wᵢ ≥ 0 with C = Σwᵢ > 0, and any distribution L on the simplex
    (Lᵢ > 0, Σ Lᵢ = 1), the normalized posterior p*ᵢ = wᵢ/C satisfies:

      Σᵢ wᵢ · log(Lᵢ) ≤ Σᵢ wᵢ · log(p*ᵢ)

    Proof: The difference equals C · KL(p* || L) ≥ 0.

    This is used for listener optimality: with wᵢ = P(m) · S(u|m), the
    Bayesian listener L*(m|u) = wᵢ/C maximizes Σ_m P(m)·S(u|m)·log L(m|u). -/
theorem bayesian_maximizes [Nonempty ι] (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hC_pos : 0 < ∑ i, w i)
    (L : ι → ℝ) (hL_pos : ∀ i, 0 < L i) (hL_sum : ∑ i, L i = 1) :
    ∑ i, w i * log (L i) ≤ ∑ i, w i * log (w i / ∑ j, w j) := by
  -- Let C = Σw, p* = w/C (normalized posterior)
  set C := ∑ i, w i with hC_def
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  -- Step 1: KL(p* || L) ≥ 0 where p* = w/C
  have hp_nonneg : ∀ i, 0 ≤ w i / C := λ i => div_nonneg (hw_nonneg i) (le_of_lt hC_pos)
  have hp_sum : ∑ i, w i / C = 1 := by rw [← Finset.sum_div, div_self hC_ne]
  have hkl : 0 ≤ klFinite (λ i => w i / C) L :=
    kl_finite_nonneg _ L hL_pos hp_nonneg (by rw [hp_sum, hL_sum])
  -- Step 2: klFinite(w/C, L) = Σ (w/C) · log((w/C)/L)
  -- Step 3: Σ w · log(w/C) - Σ w · log(L) = C · klFinite(w/C, L) ≥ 0
  -- We prove the inequality by showing the difference is non-negative
  -- C · KL(w/C ‖ L) = ∑ w log(w/C) - ∑ w log L ≥ 0
  suffices h : (∑ i, w i * log (w i / C)) - (∑ i, w i * log (L i)) =
      C * klFinite (fun i => w i / C) L by
    linarith [mul_nonneg (le_of_lt hC_pos) hkl]
  unfold klFinite
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hwi : w i = 0
  · simp [hwi]
  · have hwC_ne : w i / C ≠ 0 := div_ne_zero hwi hC_ne
    simp only [hwC_ne, ↓reduceIte]
    have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
    rw [show C * (w i / C * log (w i / C / L i)) = w i * log (w i / C / L i) from by
      rw [← mul_assoc]; congr 1; field_simp]
    rw [log_div (ne_of_gt (div_pos hwi_pos hC_pos)) (ne_of_gt (hL_pos i))]
    ring


-- ============================================================================
-- RSA-Specific Forms
-- ============================================================================

/-- Speaker optimality for RSA: The softmax speaker S(u|m) ∝ L(m|u)^α
    maximizes G_α for fixed listener, per meaning m.

    Given listener utilities v_u = log L(m|u), the softmax distribution
    s*(u) = exp(α·v_u)/Z uniquely maximizes:
      Σ_u [negMulLog(s_u) + α · s_u · v_u]
    over all distributions s on U. -/
theorem speaker_optimal_per_meaning [Nonempty ι] (v : ι → ℝ) (α : ℝ)
    (s : ι → ℝ) (hs_nonneg : ∀ i, 0 ≤ s i) (hs_sum : ∑ i, s i = 1) :
    ∑ u, (negMulLog (s u) + α * s u * v u) ≤
    ∑ u, (negMulLog (softmax v α u) + α * softmax v α u * v u) :=
  gibbs_maximizes v α s hs_nonneg hs_sum

/-- Listener optimality for RSA: The Bayesian listener L(m|u) ∝ P(m)·S(u|m)
    maximizes E[log L] for fixed speaker, per utterance u.

    Given weights w_m = P(m)·S(u|m) ≥ 0, the normalized distribution
    L*(m) = w_m / Σw maximizes:
      Σ_m w_m · log(L_m)
    over all distributions L on M. -/
theorem listener_optimal_per_utterance [Nonempty ι] (w : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hC_pos : 0 < ∑ i, w i)
    (L : ι → ℝ) (hL_pos : ∀ i, 0 < L i) (hL_sum : ∑ i, L i = 1) :
    ∑ i, w i * log (L i) ≤ ∑ i, w i * log (w i / ∑ j, w j) :=
  bayesian_maximizes w hw_nonneg hC_pos L hL_pos hL_sum


end RSA.GibbsVariational
