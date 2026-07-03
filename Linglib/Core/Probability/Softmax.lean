import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Softmax distribution on PMFs

The **softmax distribution** with `EReal`-valued score is the PMF with mass
proportional to `exp(score)`:

  `softmax score a ∝ exp(score a)`

Working with `score : α → EReal` (rather than `score : α → ℝ`) is essential:
the natural RSA score `score = β · log(speakerWeight)` is `-∞` exactly when
the speaker weight is 0, and `EReal.exp (-∞) = 0` makes such utterances
correctly receive 0 mass. By contrast, `Real.log 0 = 0` in mathlib, so a
ℝ-valued softmax-of-log construction would silently assign weight 1 to
impossible utterances — the bug the `EReal` substrate prevents at the root.

The inverse-temperature factor `β` lives inside the score on the consumer
side: write `softmax (fun a => (β : EReal) * scoreReal a)`. This keeps the
substrate generic over score-construction patterns
([kao-etal-2014-metaphor]'s `λ · log Σ L0`, [frank-goodman-2012]'s
`α · log L0`, [herbstritt-franke-2019]'s `λ · (-Hellinger)`, etc.).

## Main definitions

* `PMF.softmax score h_no_top h_some_finite` — softmax PMF for an
  `EReal`-valued score function bounded above and bounded-below somewhere.

## Main statements

* `softmax_apply` — closed form.
* `softmax_pos_iff_score_ne_bot` — atom has positive softmax mass iff its
  score is not `⊥`.
* `softmax_lt_iff_score_lt` — the **structural-decomposition lemma**:
  comparing softmax values reduces to comparing scores. Direct
  via `EReal.exp_lt_exp_iff` — no positivity-of-temperature side
  condition needed because the temperature is folded into `score`.

## Connection to `MeasureTheory.Measure.tilted`

The general exponential-tilting construction is mathlib's `Measure.tilted`
over arbitrary base measures. The softmax PMF is the uniform-prior case at
the PMF level. The PMF-level Esscher transform (tilting an arbitrary PMF)
is not yet defined; add it when a consumer needs `prior · exp(score)`
shape that doesn't reduce to softmax.

## Architectural role

Substrate for RSA-style speaker constructions across `Studies/`:
[frank-goodman-2012], [goodman-stuhlmuller-2013],
[kao-etal-2014-metaphor], [lassiter-goodman-2017],
[herbstritt-franke-2019], [yoon-etal-2020], etc. Replaces
the per-paper inline `PMF.normalize ∘ exp ∘ score` pattern with a
named primitive backed by the structural-decomposition lemma.
-/

set_option autoImplicit false

open scoped ENNReal

namespace PMF

variable {α : Type*}

/-! ## Definition -/

/-- The unnormalised softmax weight at `a`: `EReal.exp (score a) : ℝ≥0∞`.
Returns `0` when `score a = ⊥` and `∞` when `score a = ⊤`. -/
noncomputable def softmaxWeight (score : α → EReal) (a : α) : ℝ≥0∞ :=
  EReal.exp (score a)

@[simp] theorem softmaxWeight_apply (score : α → EReal) (a : α) :
    softmaxWeight score a = EReal.exp (score a) := rfl

theorem softmaxWeight_ne_zero_iff (score : α → EReal) (a : α) :
    softmaxWeight score a ≠ 0 ↔ score a ≠ ⊥ := by
  unfold softmaxWeight; rw [ne_eq, EReal.exp_eq_zero_iff]

theorem softmaxWeight_ne_top_iff (score : α → EReal) (a : α) :
    softmaxWeight score a ≠ ∞ ↔ score a ≠ ⊤ := by
  unfold softmaxWeight; rw [ne_eq, EReal.exp_eq_top_iff]

/-- **Softmax distribution** for an `EReal`-valued score function.

For a finite type, the partition function `Z = ∑ b, exp(score b)` is
non-zero iff some atom has score `≠ ⊥` (`h_some_finite`) and finite iff
no atom has score `= ⊤` (`h_no_top`).

The inverse-temperature factor `β` lives inside `score` on the consumer
side. Typical pattern: `score a = (β : EReal) * scoreReal a` with
`scoreReal : α → ℝ` (or ℝ embedded in EReal). -/
noncomputable def softmax [Fintype α] (score : α → EReal)
    (h_no_top : ∀ a, score a ≠ ⊤) (h_some_finite : ∃ a, score a ≠ ⊥) :
    PMF α :=
  PMF.normalize (softmaxWeight score)
    (by
      obtain ⟨a₀, ha₀⟩ := h_some_finite
      exact ENNReal.summable.tsum_ne_zero_iff.mpr
        ⟨a₀, (softmaxWeight_ne_zero_iff score a₀).mpr ha₀⟩)
    (by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr fun a _ =>
        (softmaxWeight_ne_top_iff score a).mpr (h_no_top a))

/-! ## Apply formula and basic API -/

/-- Closed form of the softmax value at `a`. -/
@[simp]
theorem softmax_apply [Fintype α] (score : α → EReal)
    (h_no_top : ∀ a, score a ≠ ⊤) (h_some_finite : ∃ a, score a ≠ ⊥) (a : α) :
    softmax score h_no_top h_some_finite a =
      softmaxWeight score a / ∑ b, softmaxWeight score b := by
  rw [softmax, PMF.normalize_apply, tsum_fintype, ENNReal.div_eq_inv_mul, mul_comm]

/-- The partition function is non-zero. -/
theorem softmax_partition_ne_zero [Fintype α] (score : α → EReal)
    (h_some_finite : ∃ a, score a ≠ ⊥) :
    (∑ b, softmaxWeight score b) ≠ 0 := by
  obtain ⟨a₀, ha₀⟩ := h_some_finite
  intro h_sum
  exact (softmaxWeight_ne_zero_iff score a₀).mpr ha₀
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le) |>.mp h_sum a₀
      (Finset.mem_univ _))

/-- The partition function is finite. -/
theorem softmax_partition_ne_top [Fintype α] (score : α → EReal)
    (h_no_top : ∀ a, score a ≠ ⊤) :
    (∑ b, softmaxWeight score b) ≠ ∞ :=
  ENNReal.sum_ne_top.mpr fun a _ =>
    (softmaxWeight_ne_top_iff score a).mpr (h_no_top a)

/-- **Softmax positivity criterion**: an atom has positive softmax mass iff
its score is not `⊥`. The score-`⊥` atoms are exactly the impossible
utterances (e.g., utterances where the literal listener has 0 support along
the QUD-projection in [kao-etal-2014-metaphor]). -/
theorem softmax_pos_iff_score_ne_bot [Fintype α] (score : α → EReal)
    (h_no_top : ∀ a, score a ≠ ⊤) (h_some_finite : ∃ a, score a ≠ ⊥) (a : α) :
    0 < softmax score h_no_top h_some_finite a ↔ score a ≠ ⊥ := by
  rw [softmax_apply, ENNReal.div_pos_iff]
  refine ⟨fun ⟨hw, _⟩ => (softmaxWeight_ne_zero_iff score a).mp hw,
          fun h => ⟨(softmaxWeight_ne_zero_iff score a).mpr h,
                    softmax_partition_ne_top score h_no_top⟩⟩

/-- **The softmax support is exactly the score-finite-below atoms**. -/
@[simp]
theorem support_softmax [Fintype α] (score : α → EReal)
    (h_no_top : ∀ a, score a ≠ ⊤) (h_some_finite : ∃ a, score a ≠ ⊥) :
    (softmax score h_no_top h_some_finite).support = {a | score a ≠ ⊥} := by
  ext a
  rw [PMF.mem_support_iff, Set.mem_setOf_eq, ← pos_iff_ne_zero]
  exact softmax_pos_iff_score_ne_bot score h_no_top h_some_finite a

/-! ## Comparison decomposition (RSA workhorse) -/

/-- **Structural-decomposition lemma**: comparing softmax values at two
atoms reduces to comparing their scores. Direct via the strict monotonicity
of `EReal.exp` (mathlib's `EReal.exp_lt_exp_iff`).

Foundation lemma for "speaker prefers utterance u₂ over u₁ at world w" claims
in RSA: the partition function depends on `w` but not on the utterance being
compared, so it cancels exactly. The score function bundles the
inverse-temperature factor (`β · log L0` for [kao-etal-2014-metaphor],
`λ · -hellingerDist` for [herbstritt-franke-2019], etc.). -/
theorem softmax_lt_iff_score_lt [Fintype α] (score : α → EReal)
    (h_no_top : ∀ a, score a ≠ ⊤) (h_some_finite : ∃ a, score a ≠ ⊥)
    (a₁ a₂ : α) :
    softmax score h_no_top h_some_finite a₁ <
        softmax score h_no_top h_some_finite a₂ ↔
      score a₁ < score a₂ := by
  rw [softmax_apply, softmax_apply,
      ENNReal.div_lt_div_iff_left
        (softmax_partition_ne_zero score h_some_finite)
        (softmax_partition_ne_top score h_no_top)]
  unfold softmaxWeight
  exact EReal.exp_lt_exp_iff

/-- **`≤` companion** of `softmax_lt_iff_score_lt`. -/
theorem softmax_le_iff_score_le [Fintype α] (score : α → EReal)
    (h_no_top : ∀ a, score a ≠ ⊤) (h_some_finite : ∃ a, score a ≠ ⊥)
    (a₁ a₂ : α) :
    softmax score h_no_top h_some_finite a₁ ≤
        softmax score h_no_top h_some_finite a₂ ↔
      score a₁ ≤ score a₂ := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact softmax_lt_iff_score_lt score h_no_top h_some_finite a₂ a₁

/-- **`=` companion** of `softmax_lt_iff_score_lt`: score symmetry. -/
theorem softmax_eq_iff_score_eq [Fintype α] (score : α → EReal)
    (h_no_top : ∀ a, score a ≠ ⊤) (h_some_finite : ∃ a, score a ≠ ⊥)
    (a₁ a₂ : α) :
    softmax score h_no_top h_some_finite a₁ =
        softmax score h_no_top h_some_finite a₂ ↔
      score a₁ = score a₂ := by
  simp only [le_antisymm_iff, softmax_le_iff_score_le]

/-! ## Degenerate cases -/

/-- **Constant-score softmax is uniform**: a constant score gives no
preference signal. -/
theorem softmax_const [Fintype α] [Nonempty α] (c : EReal) (hc_ne_top : c ≠ ⊤)
    (hc_ne_bot : c ≠ ⊥) :
    softmax (fun _ : α => c) (fun _ => hc_ne_top) ⟨Classical.arbitrary α, hc_ne_bot⟩
      = PMF.uniformOfFintype α := by
  ext a
  rw [softmax_apply, PMF.uniformOfFintype_apply]
  simp only [softmaxWeight]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Goal: exp(c) / (N * exp(c)) = N⁻¹
  have h_pos : (0 : ℝ≥0∞) < EReal.exp c := by
    rw [pos_iff_ne_zero, ne_eq, EReal.exp_eq_zero_iff]; exact hc_ne_bot
  have h_ne_top : EReal.exp c ≠ ∞ := by rw [ne_eq, EReal.exp_eq_top_iff]; exact hc_ne_top
  nth_rewrite 1 [show EReal.exp c = 1 * EReal.exp c from (one_mul _).symm]
  rw [ENNReal.mul_div_mul_right _ _ h_pos.ne' h_ne_top, one_div]

/-! ## Bridge to nat-power form

For natural exponent `n`, the EReal-softmax of `n · log w` is the
natural-power softmax of `w` — a finite ratio of `w(a)^n` over the
partition `Σ_b w(b)^n`. Mathlib's `ENNReal.rpow_eq_exp_mul_log` and
`ENNReal.rpow_natCast` together give the per-weight identity.

Pivotal for RSA findings discharged via `gcongr`/`norm_num`/`bound`:
the EReal form makes the substrate paper-faithful, but the rpow form
makes the values computable rationals when `w` is. -/

/-! ## Finite-coefficient times log: finiteness lemmas

The score `(α : EReal) * ENNReal.log x` is the canonical RSA speaker score
shape. It is finite (`∈ (⊥, ⊤)`) under the natural side conditions: `α`
real-valued (so neither `⊤` nor `⊥`), `α ≥ 0`, and `x` either non-zero or
non-top respectively. -/

/-- For `α : ℝ` non-negative and `x : ℝ≥0∞` with `x ≠ ⊤`, the EReal
product `(α : EReal) * ENNReal.log x` is bounded above (≠ ⊤). -/
theorem coe_mul_log_ne_top {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx_ne_top : x ≠ ⊤) :
    ((α : EReal) * ENNReal.log x) ≠ ⊤ := by
  rw [EReal.mul_ne_top]
  refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (EReal.coe_nonneg.mpr hα),
          Or.inl (EReal.coe_ne_top _),
          Or.inr (fun h => hx_ne_top (ENNReal.log_eq_top_iff.mp h))⟩

/-- For `α : ℝ` non-negative and `x : ℝ≥0∞` with `x ≠ 0`, the EReal
product `(α : EReal) * ENNReal.log x` is bounded below (≠ ⊥). -/
theorem coe_mul_log_ne_bot {α : ℝ} (hα : 0 ≤ α) {x : ℝ≥0∞} (hx_ne_zero : x ≠ 0) :
    ((α : EReal) * ENNReal.log x) ≠ ⊥ := by
  rw [EReal.mul_ne_bot]
  refine ⟨Or.inl (EReal.coe_ne_bot _),
          Or.inr (fun h => hx_ne_zero (ENNReal.log_eq_bot_iff.mp h)),
          Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.mpr hα)⟩

/-- **EReal-softmax weight equals natural-power weight** at each atom,
when the underlying weight is in `ℝ≥0∞`. -/
theorem softmaxWeight_natMul_log_eq_pow {α : Type*} (n : ℕ) (w : α → ℝ≥0∞)
    (a : α) :
    softmaxWeight (fun b => (n : EReal) * ENNReal.log (w b)) a = w a ^ n := by
  -- Direct via mathlib's `EReal.exp_nmul: exp (n * x) = (exp x) ^ n`
  -- and `ENNReal.exp_log: exp (log x) = x`.
  show EReal.exp ((n : EReal) * ENNReal.log (w a)) = w a ^ n
  rw [EReal.exp_nmul, ENNReal.exp_log]

/-- **Apply formula for natural-power softmax**: `softmax (n · log w) a =
w(a)^n / Σ_b w(b)^n`. Direct rewrite of `softmax_apply` via
`softmaxWeight_natMul_log_eq_pow`. -/
theorem softmax_natMul_log_apply {α : Type*} [Fintype α] (n : ℕ) (w : α → ℝ≥0∞)
    (h_no_top : ∀ a, ((n : EReal) * ENNReal.log (w a)) ≠ ⊤)
    (h_some_finite : ∃ a, ((n : EReal) * ENNReal.log (w a)) ≠ ⊥) (a : α) :
    softmax (fun b => (n : EReal) * ENNReal.log (w b)) h_no_top h_some_finite a
      = w a ^ n / ∑ b, w b ^ n := by
  rw [softmax_apply]
  simp_rw [softmaxWeight_natMul_log_eq_pow]

end PMF
