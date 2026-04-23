import Linglib.Core.Agent.RationalAction
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Softmax Function: Limit Behavior

§1. Pointwise limits: α → 0 (uniform), α → ∞ (argmax), α → -∞ (argmin).
§2. BToM observer: `softmaxObserver_tendsto_one` — an observer watching a
    softmax agent concentrates on the uniquely optimal state as α → ∞.
    This is the RSA–exhaustivity bridge: L1 at α → ∞ computes exh.
-/

namespace Softmax

open Core Real BigOperators Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set of indices achieving the maximum score. -/
def argmaxSet (s : ι → ℝ) : Set ι :=
  {i | ∀ j, s j ≤ s i}

/-- The set of indices achieving the minimum score. -/
def argminSet (s : ι → ℝ) : Set ι :=
  {i | ∀ j, s i ≤ s j}

/-- Maximum score value. -/
noncomputable def maxScore [Nonempty ι] (s : ι → ℝ) : ℝ :=
  ⨆ i, s i

/-- Minimum score value. -/
noncomputable def minScore [Nonempty ι] (s : ι → ℝ) : ℝ :=
  ⨅ i, s i

/-- Fact 4: As α → 0, softmax converges to uniform distribution. -/
theorem tendsto_softmax_zero [Nonempty ι] (s : ι → ℝ) (i : ι) :
    Tendsto (λ α => softmax s α i) (𝓝 0) (𝓝 (1 / Fintype.card ι)) := by
  have h : softmax s 0 i = 1 / Fintype.card ι := by
    have := softmax_zero s
    simp only [this]
  rw [← h]
  apply Continuous.tendsto
  -- softmax α i = exp(α * s i) / Σⱼ exp(α * s j) is continuous in α
  -- Numerator: exp is continuous, mul is continuous
  -- Denominator: finite sum of continuous functions, always positive
  simp only [softmax]
  apply Continuous.div
  · exact continuous_exp.comp (continuous_mul_right (s i))
  · apply continuous_finset_sum
    intro j _
    exact continuous_exp.comp (continuous_mul_right (s j))
  · intro α
    exact partitionFn_ne_zero s α

/-- The ratio of non-max to max probability vanishes as α → ∞. -/
theorem softmax_ratio_tendsto_zero [Nonempty ι] (s : ι → ℝ)
    (i j : ι) (hij : s i < s j) :
    Tendsto (λ α => softmax s α i / softmax s α j) atTop (𝓝 0) := by
  simp only [softmax_odds]
  -- exp(α * (s_i - s_j)) → 0 when s_i < s_j
  have h : s i - s j < 0 := by linarith
  -- Use Mathlib: exp(x) → 0 as x → -∞, and c * α → -∞ when c < 0
  have hconv : Tendsto (λ α => (s i - s j) * α) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg h
  -- Rewrite to match: α * (s i - s j) = (s i - s j) * α
  have heq : (λ α => exp (α * (s i - s j))) = (λ α => exp ((s i - s j) * α)) := by
    ext α; ring_nf
  rw [heq]
  exact tendsto_exp_atBot.comp hconv

/-- At the maximum, softmax → 1 as α → ∞. Helper lemma. -/
theorem tendsto_softmax_infty_at_max [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) :
    Tendsto (λ α => softmax s α i_max) atTop (𝓝 1) := by
  -- Simple proof: softmax sums to 1, and all non-max terms → 0
  -- So: softmax_max = 1 - Σ_{j≠max} softmax_j → 1 - 0 = 1
  set S := Finset.univ.filter (λ j : ι => j ≠ i_max) with hS
  have hsum : ∀ α, softmax s α i_max = 1 - ∑ j ∈ S, softmax s α j := by
    intro α
    have h := softmax_sum_eq_one s α
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· = i_max))] at h
    have hsimp : Finset.filter (· = i_max) Finset.univ = {i_max} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hsimp, Finset.sum_singleton] at h
    have hne : Finset.filter (λ x => ¬x = i_max) Finset.univ = S := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, hS]
    rw [hne] at h
    linarith
  -- First show each softmax_j → 0 for j ≠ max
  have heach : ∀ j ∈ S, Tendsto (λ α => softmax s α j) atTop (𝓝 0) := by
    intro j hj
    rw [hS, Finset.mem_filter] at hj
    -- softmax_j ≤ (softmax_j / softmax_max) because softmax_max ≤ 1
    have hratio := softmax_ratio_tendsto_zero s j i_max (h_unique j hj.2)
    have hbound : ∀ α, softmax s α j ≤ softmax s α j / softmax s α i_max := by
      intro α
      have h1 : softmax s α i_max ≤ 1 := softmax_le_one s α i_max
      have hpos : 0 < softmax s α i_max := softmax_pos s α i_max
      have hinv : 1 ≤ 1 / softmax s α i_max := (one_le_div hpos).mpr h1
      calc softmax s α j = softmax s α j * 1 := by ring
        _ ≤ softmax s α j * (1 / softmax s α i_max) :=
            mul_le_mul_of_nonneg_left hinv (softmax_nonneg s α j)
        _ = softmax s α j / softmax s α i_max := by ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio
      (λ α => softmax_nonneg s α j) hbound
  -- Sum of terms each → 0 is → 0
  have hsum_zero : Tendsto (λ α => ∑ j ∈ S, softmax s α j) atTop (𝓝 0) := by
    have h := tendsto_finset_sum S (λ j hj => heach j hj)
    simp only [Finset.sum_const_zero] at h
    exact h
  -- 1 - sum → 1 - 0 = 1
  have hmain : Tendsto (λ α => 1 - ∑ j ∈ S, softmax s α j) atTop (𝓝 (1 : ℝ)) := by
    have htend : Tendsto (λ α => (1 : ℝ) - ∑ j ∈ S, softmax s α j) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hsum_zero
    simp only [sub_zero] at htend
    exact htend
  exact hmain.congr (λ α => (hsum α).symm)

/-- When there's a unique maximum, softmax concentrates on it as α → ∞. -/
theorem tendsto_softmax_infty_unique_max [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) (i : ι) :
    Tendsto (λ α => softmax s α i) atTop
      (𝓝 (if i = i_max then 1 else 0)) := by
  by_cases h : i = i_max
  · -- i = i_max, so we need softmax → 1
    rw [if_pos h, h]
    exact tendsto_softmax_infty_at_max s i_max h_unique
  · -- i ≠ i_max, so we need softmax → 0
    rw [if_neg h]
    have hi : s i < s i_max := h_unique i h
    have hratio := softmax_ratio_tendsto_zero s i i_max hi
    have hbound : ∀ α, softmax s α i ≤ softmax s α i / softmax s α i_max := by
      intro α
      have h1 : softmax s α i_max ≤ 1 := softmax_le_one s α i_max
      have hpos : 0 < softmax s α i_max := softmax_pos s α i_max
      have hinv : 1 ≤ 1 / softmax s α i_max := (one_le_div hpos).mpr h1
      calc softmax s α i = softmax s α i * 1 := by ring
        _ ≤ softmax s α i * (1 / softmax s α i_max) :=
            mul_le_mul_of_nonneg_left hinv (softmax_nonneg s α i)
        _ = softmax s α i / softmax s α i_max := by ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio
      (λ α => softmax_nonneg s α i) hbound

/-- Log-probability difference grows unboundedly. -/
theorem log_softmax_ratio_tendsto [Nonempty ι] (s : ι → ℝ)
    (i j : ι) (hij : s i < s j) :
    Tendsto (λ α => log (softmax s α j / softmax s α i)) atTop atTop := by
  simp only [log_softmax_odds]
  -- α * (s_j - s_i) → ∞ when s_j > s_i
  have h : 0 < s j - s i := by linarith
  -- Rewrite: α * (s j - s i) = (s j - s i) * α
  have heq : (λ α => α * (s j - s i)) = (λ α => (s j - s i) * α) := by
    ext α; ring
  rw [heq]
  exact tendsto_id.const_mul_atTop h

/-- As α → -∞, softmax concentrates on the minimum. -/
theorem tendsto_softmax_neg_infty_unique_min [Nonempty ι] (s : ι → ℝ)
    (i_min : ι) (h_unique : ∀ j, j ≠ i_min → s i_min < s j) (i : ι) :
    Tendsto (λ α => softmax s α i) atBot
      (𝓝 (if i = i_min then 1 else 0)) := by
  -- Use: softmax(s, α) = softmax(-s, -α)
  -- As α → -∞, this is like softmax(-s, β) as β → ∞
  -- And -s has unique max at i_min (where s has unique min)
  have hconv : ∀ α, softmax s α = softmax (λ j => -s j) (-α) := by
    intro α
    funext j
    unfold Core.softmax
    congr 1
    · congr 1; ring
    · apply Finset.sum_congr rfl; intro k _; congr 1; ring
  simp_rw [hconv]
  have hneg : ∀ j, j ≠ i_min → -s j < -s i_min := by
    intro j hj
    exact neg_lt_neg (h_unique j hj)
  have := tendsto_softmax_infty_unique_max (λ j => -s j) i_min hneg i
  exact this.comp tendsto_neg_atBot_atTop

/-- The IBR limit: hardmax selector. -/
noncomputable def hardmax [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) : ι → ℝ :=
  λ i => if i = i_max then 1 else 0

/-- Softmax converges to hardmax as α → ∞ (when maximum is unique). -/
theorem softmax_tendsto_hardmax [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) :
    ∀ i, Tendsto (λ α => softmax s α i) atTop
      (𝓝 (hardmax s i_max h_unique i)) := by
  intro i
  simp only [hardmax]
  exact tendsto_softmax_infty_unique_max s i_max h_unique i

/-- Shannon entropy of a distribution. -/
noncomputable def entropy [Nonempty ι] (p : ι → ℝ) : ℝ :=
  -∑ i : ι, p i * log (p i)

/-- Maximum possible entropy (uniform distribution). -/
noncomputable def maxEntropy (ι : Type*) [Fintype ι] : ℝ :=
  log (Fintype.card ι)

/-- As α → 0, entropy of softmax approaches maximum. -/
theorem entropy_tendsto_max [Nonempty ι] (s : ι → ℝ) :
    Tendsto (λ α => entropy (softmax s α)) (𝓝 0) (𝓝 (maxEntropy ι)) := by
  -- entropy ∘ softmax is continuous in α, so the limit equals the value at α = 0
  have hval : entropy (softmax s 0) = maxEntropy ι := by
    unfold entropy maxEntropy
    simp_rw [softmax_zero s]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div,
               Real.log_inv, neg_neg]
    have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  rw [← hval]
  apply Continuous.tendsto
  -- entropy(softmax s α) = -∑ i, softmax(i) * log(softmax(i))
  -- Each softmax component is continuous in α, and x * log x is continuous
  unfold entropy
  apply Continuous.neg; apply continuous_finset_sum; intro i _
  have hcont_sm : Continuous (fun α => softmax s α i) := by
    simp only [softmax]
    exact (continuous_exp.comp (continuous_mul_right (s i))).div
      (continuous_finset_sum _ (fun j _ => continuous_exp.comp (continuous_mul_right (s j))))
      (fun α => partitionFn_ne_zero s α)
  have hcont_log : Continuous (fun α => Real.log (softmax s α i)) :=
    Real.continuousOn_log.comp_continuous hcont_sm (fun α => ne_of_gt (softmax_pos s α i))
  exact hcont_sm.mul hcont_log

/-- As α → ∞ (with unique max), entropy approaches 0. -/
theorem entropy_tendsto_zero [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) :
    Tendsto (λ α => entropy (softmax s α)) atTop (𝓝 0) := by
  -- entropy p = ∑ i, negMulLog(p i), and negMulLog is continuous
  -- softmax(i) → (if i = i_max then 1 else 0), negMulLog(0) = negMulLog(1) = 0
  -- So each term → 0, and the finite sum → 0
  have hrewrite : (fun α => entropy (softmax s α)) =
      fun α => ∑ i, Real.negMulLog (softmax s α i) := by
    ext α; unfold entropy Real.negMulLog
    simp only [neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [hrewrite, show (0 : ℝ) = ∑ _i : ι, (0 : ℝ) from by simp]
  apply tendsto_finset_sum; intro i _
  -- negMulLog(softmax s α i) → negMulLog(limit_i) = 0
  have hlim := tendsto_softmax_infty_unique_max s i_max h_unique i
  have hval : Real.negMulLog (if i = i_max then 1 else 0) = 0 := by
    split_ifs <;> simp
  rw [← hval]
  exact (Real.continuous_negMulLog.tendsto _).comp hlim

/-- Exponential rate of concentration. -/
theorem softmax_exponential_decay [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_max : ∀ j, s j ≤ s i_max) (i : ι) (hi : s i < s i_max) :
    ∃ C > 0, ∀ α > 0, softmax s α i ≤ C * exp (-α * (s i_max - s i)) := by
  use 1
  constructor
  · exact one_pos
  · intro α _
    -- softmax i = softmax i_max * exp(α(s_i - s_i_max))
    have hratio := softmax_ratio s α i i_max
    rw [hratio]
    have hle : softmax s α i_max ≤ 1 := softmax_le_one s α i_max
    calc softmax s α i_max * exp (α * (s i - s i_max))
        ≤ 1 * exp (α * (s i - s i_max)) := by
            apply mul_le_mul_of_nonneg_right hle (le_of_lt (exp_pos _))
      _ = exp (α * (s i - s i_max)) := one_mul _
      _ = exp (-(α * (s i_max - s i))) := by ring_nf
      _ = exp (-α * (s i_max - s i)) := by ring_nf
      _ = 1 * exp (-α * (s i_max - s i)) := (one_mul _).symm

/-- For practical computation: when is softmax close enough to hardmax? -/
theorem softmax_negligible [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_max : ∀ j, s j ≤ s i_max) (ε : ℝ) (hε : 0 < ε)
    (gap : ℝ) (hgap : 0 < gap) (h_gap_bound : ∀ j, j ≠ i_max → s i_max - s j ≥ gap) :
    ∀ α, α > (1/gap) * |log ε| →
      ∀ j, j ≠ i_max → softmax s α j < ε := by
  intro α hα j hj
  have hgap_j : s i_max - s j ≥ gap := h_gap_bound j hj
  have hsj : s j < s i_max := by linarith
  have hα_pos : 0 < α := by
    have h : 0 ≤ (1/gap) * |log ε| := by positivity
    linarith
  -- Direct bound: softmax j = softmax i_max * exp(α(s_j - s_i_max)) ≤ exp(-α * gap)
  have hratio := softmax_ratio s α j i_max
  have hle_max : softmax s α i_max ≤ 1 := softmax_le_one s α i_max
  have hbound : softmax s α j ≤ exp (-α * (s i_max - s j)) := by
    rw [hratio]
    calc softmax s α i_max * exp (α * (s j - s i_max))
        ≤ 1 * exp (α * (s j - s i_max)) := by
            apply mul_le_mul_of_nonneg_right hle_max (le_of_lt (exp_pos _))
      _ = exp (α * (s j - s i_max)) := one_mul _
      _ = exp (-α * (s i_max - s j)) := by ring_nf
  -- softmax j ≤ exp(-α * (s i_max - s j)) ≤ exp(-α * gap)
  have hexp_mono : exp (-α * (s i_max - s j)) ≤ exp (-α * gap) := by
    apply exp_le_exp.mpr
    have : -α * (s i_max - s j) ≤ -α * gap := by
      apply mul_le_mul_of_nonpos_left hgap_j
      linarith
    exact this
  -- exp(-α * gap) < ε when α > (1/gap) * |log ε|
  have hexp_lt : exp (-α * gap) < ε := by
    rw [← exp_log hε]
    apply exp_lt_exp.mpr
    have h1 : α * gap > |log ε| := by
      have : α > (1/gap) * |log ε| := hα
      calc α * gap > (1/gap) * |log ε| * gap := by nlinarith
        _ = |log ε| := by field_simp
    by_cases hε1 : ε < 1
    · have hlog_neg : log ε < 0 := log_neg hε hε1
      have habs : |log ε| = -log ε := abs_of_neg hlog_neg
      rw [habs] at h1
      linarith
    · push_neg at hε1
      have hlog_nonneg : 0 ≤ log ε := log_nonneg hε1
      have habs : |log ε| = log ε := abs_of_nonneg hlog_nonneg
      rw [habs] at h1
      have : -α * gap < 0 := by linarith
      linarith
  calc softmax s α j ≤ exp (-α * (s i_max - s j)) := hbound
    _ ≤ exp (-α * gap) := hexp_mono
    _ < ε := hexp_lt

-- ============================================================================
-- §2. BToM Observer Inference (Exhaustivity Limit)
-- ============================================================================

/-- If action j has strictly higher score than i, softmax(i, α) → 0 as α → ∞.
    Weaker than `tendsto_softmax_infty_unique_max`: does not require a unique
    maximum, just that i is beaten by some j. -/
theorem tendsto_softmax_infty_not_max [Nonempty ι] (s : ι → ℝ)
    (i j : ι) (hij : s i < s j) :
    Tendsto (fun α => softmax s α i) atTop (nhds 0) := by
  have hratio := softmax_ratio_tendsto_zero s i j hij
  have hbound : ∀ α, softmax s α i ≤ softmax s α i / softmax s α j := by
    intro α
    have h1 : softmax s α j ≤ 1 := softmax_le_one s α j
    have hpos : 0 < softmax s α j := softmax_pos s α j
    have hinv : 1 ≤ 1 / softmax s α j := (one_le_div hpos).mpr h1
    calc softmax s α i = softmax s α i * 1 := by ring
      _ ≤ softmax s α i * (1 / softmax s α j) :=
          mul_le_mul_of_nonneg_left hinv (softmax_nonneg s α i)
      _ = softmax s α i / softmax s α j := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio
    (fun α => softmax_nonneg s α i) hbound

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Observer posterior for a softmax agent: BToM inference about the state.

    An observer sees a softmax agent choose action i, and infers the state:
    P(s | i, α) = softmax(score(·,s), α)(i) · prior(s) / Σ_{s'} ...

    In RSA: the pragmatic listener L1 observes the speaker's utterance u and
    infers the world w. This is `L1(w | u)` parameterized by α for limits. -/
noncomputable def softmaxObserver [Nonempty ι]
    (score : ι → σ → ℝ) (prior : σ → ℝ) (α : ℝ) (i : ι) (s : σ) : ℝ :=
  softmax (fun j => score j s) α i * prior s /
  ∑ s' : σ, softmax (fun j => score j s') α i * prior s'

/-- BToM inference about a softmax agent concentrates on the optimal state.

    An observer watches a softmax agent and infers the hidden state.
    If action i₀ is the unique best action at state s₀, and is not the best
    at any other state, the observer's posterior P(s₀ | i₀, α) → 1 as α → ∞.

    **RSA–exhaustivity bridge**: the pragmatic listener (L1) observes a softmax
    speaker (S1) and does Bayesian inversion. At α → ∞, L1 concentrates on
    worlds where the heard utterance was the speaker's uniquely optimal choice.
    This IS the exhaustivity operator: L1 at α → ∞ computes exh(u).

    For a simple scale {some, all} with worlds {someNotAll, all}:
    - "all" is more informative at the "all" world → S1 says "all" there
    - "some" is the only true utterance at "someNotAll" → S1 says "some" there
    - L1 hearing "some" → concentrates on "someNotAll" → exh(some) = some ∧ ¬all -/
theorem softmaxObserver_tendsto_one [Nonempty ι] [Nonempty σ]
    (score : ι → σ → ℝ) (prior : σ → ℝ)
    (i₀ : ι) (s₀ : σ)
    (h_opt : ∀ j, j ≠ i₀ → score j s₀ < score i₀ s₀)
    (h_nonopt : ∀ s, s ≠ s₀ → ∃ j, score i₀ s < score j s)
    (h_prior : 0 < prior s₀) :
    Tendsto (fun α => softmaxObserver score prior α i₀ s₀) atTop (nhds 1) := by
  simp only [softmaxObserver]
  -- Step 1: numerator → prior(s₀)
  have hnum : Tendsto (fun α => softmax (fun j => score j s₀) α i₀ * prior s₀)
      atTop (nhds (1 * prior s₀)) :=
    (tendsto_softmax_infty_at_max _ i₀ h_opt).mul tendsto_const_nhds
  rw [one_mul] at hnum
  -- Step 2: each term in the sum converges
  have hterm : ∀ s : σ, Tendsto (fun α => softmax (fun j => score j s) α i₀ * prior s)
      atTop (nhds (if s = s₀ then prior s₀ else 0)) := by
    intro s
    by_cases hs : s = s₀
    · rw [if_pos hs, hs]; exact hnum
    · rw [if_neg hs]
      obtain ⟨j, hj⟩ := h_nonopt s hs
      have : Tendsto (fun α => softmax (fun k => score k s) α i₀) atTop (nhds 0) :=
        tendsto_softmax_infty_not_max _ i₀ j hj
      have := this.mul tendsto_const_nhds (b := prior s)
      simp only [zero_mul] at this
      exact this
  -- Step 3: denominator → prior(s₀)
  have hden : Tendsto (fun α => ∑ s : σ, softmax (fun j => score j s) α i₀ * prior s)
      atTop (nhds (prior s₀)) := by
    have h := tendsto_finset_sum Finset.univ (fun s _ => hterm s)
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  -- Step 4: ratio → prior(s₀) / prior(s₀) = 1
  have h1 : prior s₀ / prior s₀ = 1 := div_self (ne_of_gt h_prior)
  rw [← h1]
  exact hnum.div hden (ne_of_gt h_prior)

/-- softmaxObserver is invariant under state-dependent constant shifts.

    Adding `c(s)` to all action scores at state `s` doesn't change the
    observer's posterior, because softmax is translation-invariant
    (`softmax_add_const`). -/
theorem softmaxObserver_add_const [Nonempty ι]
    (score : ι → σ → ℝ) (prior : σ → ℝ) (c : σ → ℝ)
    (α : ℝ) (i : ι) (s : σ) :
    softmaxObserver (fun j t => score j t + c t) prior α i s =
    softmaxObserver score prior α i s := by
  simp only [softmaxObserver]
  have h : ∀ (t : σ) (k : ι), softmax (fun j => score j t + c t) α k =
      softmax (fun j => score j t) α k :=
    fun t k => congr_fun (softmax_add_const (fun j => score j t) α (c t)) k
  simp_rw [h]

/-! ## Open conjectures

Four open questions about the algebraic and emergent properties of RSA
(previously stubbed in the deleted `Core/Conjectures.lean`).

`TODO`: **Fixed-point uniqueness** — RSA iteration converges to a
unique fixed point for any rationality `α > 0`.

`TODO`: **Lexicon-refinement monotonicity** — if `meaning₂` refines
`meaning₁` (i.e., `meaning₂ u w → meaning₁ u w`), then
`L1 meaning₂ u w ≤ L1 meaning₁ u w`. Refining lexical meanings can only
strengthen pragmatic inferences, never weaken them.

`TODO`: **Tropical limit** — in the `α → ∞` limit, soft-max S1
converges to iterated best response (argmax / tropical semiring): for
every `ε > 0`, `(S1 α u w − bestResponse u w)² < ε` eventually.

`TODO`: **Neural-symbolic emergence** — there exists a coarsening map
from a language model's token-level predictions to world-level
predictions such that the result approximates L1 to arbitrary
ε-precision. Bridges next-token modeling to Gricean reasoning. -/

end Softmax
