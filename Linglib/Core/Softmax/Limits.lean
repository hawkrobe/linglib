import Linglib.Core.Softmax.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Softmax Function: Limit Behavior

α → 0: uniform, α → ∞: argmax, α → -∞: argmin.
-/

namespace Softmax

open Real BigOperators Finset Filter Topology

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
    Tendsto (fun α => softmax s α i) (𝓝 0) (𝓝 (1 / Fintype.card ι)) := by
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
    Tendsto (fun α => softmax s α i / softmax s α j) atTop (𝓝 0) := by
  simp only [softmax_odds]
  -- exp(α * (s_i - s_j)) → 0 when s_i < s_j
  have h : s i - s j < 0 := by linarith
  -- Use Mathlib: exp(x) → 0 as x → -∞, and c * α → -∞ when c < 0
  have hconv : Tendsto (fun α => (s i - s j) * α) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg h
  -- Rewrite to match: α * (s i - s j) = (s i - s j) * α
  have heq : (fun α => exp (α * (s i - s j))) = (fun α => exp ((s i - s j) * α)) := by
    ext α; ring_nf
  rw [heq]
  exact tendsto_exp_atBot.comp hconv

/-- At the maximum, softmax → 1 as α → ∞. Helper lemma. -/
theorem tendsto_softmax_infty_at_max [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) :
    Tendsto (fun α => softmax s α i_max) atTop (𝓝 1) := by
  -- Simple proof: softmax sums to 1, and all non-max terms → 0
  -- So: softmax_max = 1 - Σ_{j≠max} softmax_j → 1 - 0 = 1
  set S := Finset.univ.filter (fun j : ι => j ≠ i_max) with hS
  have hsum : ∀ α, softmax s α i_max = 1 - ∑ j ∈ S, softmax s α j := by
    intro α
    have h := softmax_sum_eq_one s α
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· = i_max))] at h
    have hsimp : Finset.filter (· = i_max) Finset.univ = {i_max} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hsimp, Finset.sum_singleton] at h
    have hne : Finset.filter (fun x => ¬x = i_max) Finset.univ = S := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, hS]
    rw [hne] at h
    linarith
  -- First show each softmax_j → 0 for j ≠ max
  have heach : ∀ j ∈ S, Tendsto (fun α => softmax s α j) atTop (𝓝 0) := by
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
      (fun α => softmax_nonneg s α j) hbound
  -- Sum of terms each → 0 is → 0
  have hsum_zero : Tendsto (fun α => ∑ j ∈ S, softmax s α j) atTop (𝓝 0) := by
    have h := tendsto_finset_sum S (fun j hj => heach j hj)
    simp only [Finset.sum_const_zero] at h
    exact h
  -- 1 - sum → 1 - 0 = 1
  have hmain : Tendsto (fun α => 1 - ∑ j ∈ S, softmax s α j) atTop (𝓝 (1 : ℝ)) := by
    have htend : Tendsto (fun α => (1 : ℝ) - ∑ j ∈ S, softmax s α j) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hsum_zero
    simp only [sub_zero] at htend
    exact htend
  exact hmain.congr (fun α => (hsum α).symm)

/-- When there's a unique maximum, softmax concentrates on it as α → ∞. -/
theorem tendsto_softmax_infty_unique_max [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) (i : ι) :
    Tendsto (fun α => softmax s α i) atTop
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
      (fun α => softmax_nonneg s α i) hbound

/-- Log-probability difference grows unboundedly. -/
theorem log_softmax_ratio_tendsto [Nonempty ι] (s : ι → ℝ)
    (i j : ι) (hij : s i < s j) :
    Tendsto (fun α => log (softmax s α j / softmax s α i)) atTop atTop := by
  simp only [log_softmax_odds]
  -- α * (s_j - s_i) → ∞ when s_j > s_i
  have h : 0 < s j - s i := by linarith
  -- Rewrite: α * (s j - s i) = (s j - s i) * α
  have heq : (fun α => α * (s j - s i)) = (fun α => (s j - s i) * α) := by
    ext α; ring
  rw [heq]
  exact tendsto_id.const_mul_atTop h

/-- As α → -∞, softmax concentrates on the minimum. -/
theorem tendsto_softmax_neg_infty_unique_min [Nonempty ι] (s : ι → ℝ)
    (i_min : ι) (h_unique : ∀ j, j ≠ i_min → s i_min < s j) (i : ι) :
    Tendsto (fun α => softmax s α i) atBot
      (𝓝 (if i = i_min then 1 else 0)) := by
  -- Use: softmax(s, α) = softmax(-s, -α)
  -- As α → -∞, this is like softmax(-s, β) as β → ∞
  -- And -s has unique max at i_min (where s has unique min)
  have hconv : ∀ α, softmax s α = softmax (fun j => -s j) (-α) := by
    intro α
    funext j
    simp only [softmax]
    congr 1
    · congr 1; ring
    · apply Finset.sum_congr rfl; intro k _; congr 1; ring
  simp_rw [hconv]
  have hneg : ∀ j, j ≠ i_min → -s j < -s i_min := by
    intro j hj
    exact neg_lt_neg (h_unique j hj)
  have := tendsto_softmax_infty_unique_max (fun j => -s j) i_min hneg i
  exact this.comp tendsto_neg_atBot_atTop

/-- The IBR limit: hardmax selector. -/
noncomputable def hardmax [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) : ι → ℝ :=
  fun i => if i = i_max then 1 else 0

/-- Softmax converges to hardmax as α → ∞ (when maximum is unique). -/
theorem softmax_tendsto_hardmax [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) :
    ∀ i, Tendsto (fun α => softmax s α i) atTop
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
    Tendsto (fun α => entropy (softmax s α)) (𝓝 0) (𝓝 (maxEntropy ι)) := by
  sorry

/-- As α → ∞ (with unique max), entropy approaches 0. -/
theorem entropy_tendsto_zero [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_unique : ∀ j, j ≠ i_max → s j < s i_max) :
    Tendsto (fun α => entropy (softmax s α)) atTop (𝓝 0) := by
  sorry

/-- Exponential rate of concentration. -/
theorem softmax_exponential_decay [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_max : ∀ j, s j ≤ s i_max) (i : ι) (hi : s i < s i_max) :
    ∃ C > 0, ∀ α > 0, softmax s α i ≤ C * exp (-α * (s i_max - s i)) := by
  sorry

/-- For practical computation: when is softmax close enough to hardmax? -/
theorem softmax_negligible [Nonempty ι] (s : ι → ℝ)
    (i_max : ι) (h_max : ∀ j, s j ≤ s i_max) (ε : ℝ) (hε : 0 < ε)
    (gap : ℝ) (hgap : 0 < gap) (h_gap_bound : ∀ j, j ≠ i_max → s i_max - s j ≥ gap) :
    ∀ α, α > (1/gap) * |log ε| →
      ∀ j, j ≠ i_max → softmax s α j < ε := by
  sorry

end Softmax
