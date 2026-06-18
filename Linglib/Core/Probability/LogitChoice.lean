import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field

/-!
# The softmax function (logit choice rule)

`softmax sᵢ = exp sᵢ / Σⱼ exp sⱼ`: the normalized exponential of a score vector
over a `Fintype`, with partition function `partitionFn` and `logSumExp`. This is
the **logit** choice rule — the exponential parameterization of Luce's choice
rule and the Gibbs/Boltzmann distribution. The inverse-temperature / rationality
parameter enters by scaling the argument (`softmax (α • s)`); elementary
properties are surveyed in [franke-degen-2023].

It is the domain-neutral logit core shared across the library: RSA speakers and
listeners (pragmatics), MaxEnt / Noisy HG (phonology), and rational-action agents
(`Core.RationalAction`) all build on it. With the Gumbel→softmax result
(`mcfaddenIntegral_eq_softmax`) it is the logit sibling of the probit choice rule
(`gaussianChoiceProb`).

`[UPSTREAM]`: Mathlib has `Real.exp` / `Real.sigmoid` but no `softmax` /
log-sum-exp layer. Quality-and-role marker: pure-math foundation, no linguistics.

## Main definitions

* `softmax`, `partitionFn`, `logSumExp` — the normalized exponential and its
  normalizing constant.
* `logit` — the inverse of `Real.sigmoid`.

## Main results

* `softmax_sum_eq_one`, `softmax_pos` — softmax is a probability distribution.
* `softmax_odds`, `log_softmax_odds`, `softmax_ratio` — log-odds are score
  differences (the defining IIA property).
* `softmax_binary` — the two-element case is `Real.sigmoid`.
* `rpow_luce_eq_softmax` — Luce's `f^α` power rule is softmax of log-scores.
-/

namespace Core

open Real Finset

/-! ### The softmax function

The softmax function `σ(s, α)ᵢ = exp(α · sᵢ) / Σⱼ exp(α · sⱼ)` is the
exponential parameterization of the Luce choice rule; its elementary properties
are surveyed in [franke-degen-2023].
-/

/-- The softmax function: `softmax(s)ᵢ = exp(sᵢ) / Σⱼ exp(sⱼ)`. The
inverse-temperature / rationality parameter enters by scaling the argument:
`softmax (α • s)`. -/
noncomputable def softmax {ι : Type*} [Fintype ι] (s : ι → ℝ) : ι → ℝ :=
  λ i => exp (s i) / ∑ j : ι, exp (s j)

/-- The partition function (normalizing constant) `Z = Σⱼ exp(sⱼ)`. -/
noncomputable def partitionFn {ι : Type*} [Fintype ι] (s : ι → ℝ) : ℝ :=
  ∑ j : ι, exp (s j)

/-- Log-sum-exp: log of the partition function. -/
noncomputable def logSumExp {ι : Type*} [Fintype ι] (s : ι → ℝ) : ℝ :=
  log (∑ j : ι, exp (s j))

section SoftmaxBasic

variable {ι : Type*} [Fintype ι]

/-- The partition function is always positive. -/
theorem partitionFn_pos [Nonempty ι] (s : ι → ℝ) :
    0 < partitionFn s := by
  apply Finset.sum_pos
  · intro i _; exact exp_pos _
  · exact Finset.univ_nonempty

theorem partitionFn_ne_zero [Nonempty ι] (s : ι → ℝ) :
    partitionFn s ≠ 0 :=
  ne_of_gt (partitionFn_pos s)

/-- Each softmax probability is positive. -/
theorem softmax_pos [Nonempty ι] (s : ι → ℝ) (i : ι) :
    0 < softmax s i := by
  simp only [softmax]
  exact div_pos (exp_pos _) (partitionFn_pos s)

/-- Softmax probabilities sum to 1. -/
theorem softmax_sum_eq_one [Nonempty ι] (s : ι → ℝ) :
    ∑ i : ι, softmax s i = 1 := by
  simp only [softmax]
  rw [← Finset.sum_div]
  exact div_self (partitionFn_ne_zero s)

/-- Softmax is non-negative. -/
theorem softmax_nonneg [Nonempty ι] (s : ι → ℝ) (i : ι) :
    0 ≤ softmax s i :=
  le_of_lt (softmax_pos s i)

/-- Softmax is at most 1. -/
theorem softmax_le_one [Nonempty ι] (s : ι → ℝ) (i : ι) :
    softmax s i ≤ 1 := by
  calc softmax s i
      ≤ ∑ j : ι, softmax s j :=
        Finset.single_le_sum (λ j _ => softmax_nonneg s j) (Finset.mem_univ i)
    _ = 1 := softmax_sum_eq_one s

/-- Odds are determined by score differences: `pᵢ/pⱼ = exp(sᵢ - sⱼ)`. -/
theorem softmax_odds [Nonempty ι] (s : ι → ℝ) (i j : ι) :
    softmax s i / softmax s j = exp (s i - s j) := by
  simp only [softmax]
  have hZ : (∑ k : ι, exp (s k)) ≠ 0 := partitionFn_ne_zero s
  have hj : exp (s j) ≠ 0 := ne_of_gt (exp_pos _)
  field_simp
  have key : s j + (s i - s j) = s i := by ring
  rw [← exp_add, key]

/-- Log-odds equal the score difference. -/
theorem log_softmax_odds [Nonempty ι] (s : ι → ℝ) (i j : ι) :
    log (softmax s i / softmax s j) = s i - s j := by
  rw [softmax_odds, log_exp]

/-- Ratio form of the odds identity. -/
theorem softmax_ratio [Nonempty ι] (s : ι → ℝ) (i j : ι) :
    softmax s i = softmax s j * exp (s i - s j) := by
  have h := softmax_odds s i j
  have hne : softmax s j ≠ 0 := ne_of_gt (softmax_pos s j)
  field_simp at h ⊢
  linarith [h]

/-- The logit function `L(p) = log(p / (1 - p))` — the inverse of `Real.sigmoid`
    on `(0, 1)` (mathlib provides `Real.sigmoid` but not its inverse). -/
noncomputable def logit (p : ℝ) : ℝ := log (p / (1 - p))

/-- `logit` inverts `Real.sigmoid`. -/
theorem logit_sigmoid (x : ℝ) : logit (Real.sigmoid x) = x := by
  rw [Real.sigmoid_def, ← one_div]
  simp only [logit]
  have hdenom_ne : (1 + exp (-x)) ≠ 0 := ne_of_gt (by linarith [exp_pos (-x)])
  have hexp_ne : exp (-x) ≠ 0 := ne_of_gt (exp_pos _)
  have key : 1 / (1 + exp (-x)) / (1 - 1 / (1 + exp (-x))) = exp x := by
    field_simp
    ring_nf
    rw [← Real.exp_add]; simp
  rw [key, Real.log_exp]

/-- `Real.sigmoid` inverts `logit` for `0 < p < 1`. -/
theorem sigmoid_logit {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.sigmoid (logit p) = p := by
  rw [Real.sigmoid_def, ← one_div]
  simp only [logit]
  have h1mp : 0 < 1 - p := by linarith
  have hfrac : 0 < p / (1 - p) := div_pos hp0 h1mp
  have hinv : 0 < (p / (1 - p))⁻¹ := inv_pos.mpr hfrac
  rw [show -Real.log (p / (1 - p)) = Real.log (p / (1 - p))⁻¹
    from (Real.log_inv _).symm]
  rw [Real.exp_log hinv]
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  field_simp
  linarith

/-- For `n = 2`, softmax reduces to `Real.sigmoid`. -/
theorem softmax_binary (s : Fin 2 → ℝ) (α : ℝ) :
    softmax (α • s) 0 = Real.sigmoid (α * (s 0 - s 1)) := by
  rw [Real.sigmoid_def, ← one_div]
  simp only [softmax, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  have key : α * s 0 + (-(α * (s 0 - s 1))) = α * s 1 := by ring
  have h : exp (α * s 0) + exp (α * s 1) =
           exp (α * s 0) * (1 + exp (-(α * (s 0 - s 1)))) := by
    rw [mul_add, mul_one, ← exp_add, key]
  rw [h, ← div_div, div_self (ne_of_gt (exp_pos _))]

/-- Softmax log-odds equals `logit` of the binary softmax probability
    (when there are exactly two alternatives). -/
theorem logit_softmax_binary (s : Fin 2 → ℝ) (α : ℝ) :
    logit (softmax (α • s) 0) = α * (s 0 - s 1) := by
  rw [softmax_binary, logit_sigmoid]

/-- Softmax is translation invariant. -/
theorem softmax_add_const (s : ι → ℝ) (c : ℝ) :
    softmax (λ i => s i + c) = softmax s := by
  funext i
  simp only [softmax]
  have hexp : ∀ j, exp (s j + c) = exp (s j) * exp c := fun j => by rw [exp_add]
  simp_rw [hexp, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (ne_of_gt (exp_pos _))]

/-- Higher scores get higher probabilities. -/
theorem softmax_mono [Nonempty ι] (s : ι → ℝ) (i j : ι) (hij : s i ≤ s j) :
    softmax s i ≤ softmax s j := by
  simp only [softmax]
  apply div_le_div_of_nonneg_right _ (le_of_lt (partitionFn_pos s))
  exact exp_le_exp.mpr hij

/-- Strict monotonicity. -/
theorem softmax_strict_mono [Nonempty ι] (s : ι → ℝ) (i j : ι) (hij : s i < s j) :
    softmax s i < softmax s j := by
  simp only [softmax]
  apply div_lt_div_of_pos_right _ (partitionFn_pos s)
  exact exp_lt_exp.mpr hij

/-- Constant scores give the uniform distribution (the `α = 0` case of
`softmax (α • s)`). -/
theorem softmax_zero : softmax (0 : ι → ℝ) = λ _ => 1 / (Fintype.card ι : ℝ) := by
  funext i
  simp only [softmax, Pi.zero_apply, exp_zero, Finset.sum_const, Finset.card_univ,
             nsmul_eq_mul, mul_one]

/-- Log of softmax = score minus log partition function. -/
theorem log_softmax [Nonempty ι] (s : ι → ℝ) (i : ι) :
    Real.log (softmax s i) = s i - Real.log (partitionFn s) := by
  simp only [softmax, partitionFn]
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Finset.sum_pos
    (fun j _ => Real.exp_pos _) Finset.univ_nonempty))]
  rw [Real.log_exp]

/-- Softmax is an exponential family distribution. -/
theorem softmax_exponential_family [Nonempty ι] (s : ι → ℝ) (i : ι) :
    softmax s i = exp (s i - logSumExp s) := by
  simp only [softmax, logSumExp]
  rw [exp_sub, exp_log (Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty)]

/-- Luce choice with rpow scores equals softmax over scaled log scores:
    `f(i)^α / Σⱼ f(j)^α = softmax (α • (log ∘ f)) i` when all `f(i) > 0`. This
    connects belief-based RSA (which uses `rpow`) to the softmax framework. -/
theorem rpow_luce_eq_softmax [Nonempty ι] (f : ι → ℝ) (α : ℝ)
    (hf : ∀ i, 0 < f i) (i : ι) :
    f i ^ α / ∑ j : ι, f j ^ α =
    softmax (α • (fun j => log (f j))) i := by
  simp only [softmax, Pi.smul_apply, smul_eq_mul]
  congr 1
  · rw [rpow_def_of_pos (hf i), mul_comm]
  · apply Finset.sum_congr rfl
    intro j _
    rw [rpow_def_of_pos (hf j), mul_comm]

end SoftmaxBasic

end Core
