import Linglib.Core.DecisionTheory.RationalAction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gumbel–Luce equivalence (McFadden's theorem) [mcfadden-1974]

The exact algebraic connection between Gumbel noise in a random utility model
(RUM) and the Luce choice rule (softmax) [luce-1959].

A RUM assigns each alternative `i` a random utility `Uᵢ = uᵢ + εᵢ`, with `uᵢ`
deterministic and `εᵢ` random noise, and predicts `P(i chosen) = P(Uᵢ = maxⱼ Uⱼ)`.
When the `εᵢ` are i.i.d. Gumbel(0, β), this probability is exactly softmax:

    `P(i chosen) = exp(uᵢ/β) / Σⱼ exp(uⱼ/β) = softmax((1/β) • u)ᵢ`.

The proof reduces to the Laplace integral `∫₀^∞ exp(-S·t) dt = 1/S` after the
change of variables `t = exp(-x/β)`. The Gaussian-noise counterpart (Thurstone
Case V, the normal CDF) is in `Thurstone.lean`.

## Main results

* `integral_exp_neg_mul_Ioi_zero` — the Laplace integral `∫₀^∞ exp(-S·t) dt = 1/S`.
* `mcfaddenIntegral_eq_softmax` — McFadden's theorem (algebraic core).
* `gumbelMaxProb_is_mcfaddenIntegral` — the measure-theoretic content: the Gumbel
  max-probability integral equals `mcfaddenIntegral`.
* `mcfaddenIntegral_binary` — the binary case is the logistic function.
* `gumbel_from_functional_eq` — uniqueness: the Gumbel CDF is the only max-CDF
  satisfying the defining functional equation.
-/

namespace Core

open Real MeasureTheory Set BigOperators Finset Filter

/-! ### The Gumbel distribution -/

/-- The Gumbel CDF with location 0 and scale `β`:

    `F(x; β) = exp(-exp(-x/β))`

    The Type I extreme value distribution. Used as the noise distribution
    in the Luce/McFadden random utility model. -/
noncomputable def gumbelCDF (β : ℝ) (x : ℝ) : ℝ :=
  exp (-exp (-x / β))

/-- The Gumbel PDF with location 0 and scale `β`:

    `f(x; β) = (1/β) · exp(-x/β) · exp(-exp(-x/β))` -/
noncomputable def gumbelPDF (β : ℝ) (x : ℝ) : ℝ :=
  (1 / β) * exp (-x / β) * exp (-exp (-x / β))

/-- The Gumbel CDF is strictly positive. -/
theorem gumbelCDF_pos (β : ℝ) (x : ℝ) : 0 < gumbelCDF β x :=
  exp_pos _

/-- The Gumbel CDF is at most 1. -/
theorem gumbelCDF_le_one (β : ℝ) (x : ℝ) : gumbelCDF β x ≤ 1 :=
  exp_le_one_iff.mpr (neg_nonpos.mpr (le_of_lt (exp_pos _)))

/-- The Gumbel PDF is positive when β > 0. -/
theorem gumbelPDF_pos {β : ℝ} (hβ : 0 < β) (x : ℝ) : 0 < gumbelPDF β x := by
  simp only [gumbelPDF]
  apply mul_pos (mul_pos _ (exp_pos _)) (exp_pos _)
  exact div_pos one_pos hβ

/-! ### The Laplace integral `∫₀^∞ exp(-S·t) dt = 1/S` -/

/-- The Laplace integral: `∫₀^∞ exp(-S·t) dt = 1/S` for `S > 0`.

    This is the core computation in McFadden's theorem. After the change of
    variables `t = exp(-x/β)` in the Gumbel max-probability integral, the
    problem reduces to this exponential integral.

    Follows directly from Mathlib's `integral_exp_mul_Ioi` with `a = -S`
    and `c = 0`. -/
theorem integral_exp_neg_mul_Ioi_zero {S : ℝ} (hS : 0 < S) :
    ∫ t in Ioi (0 : ℝ), exp (-S * t) = 1 / S := by
  have h := integral_exp_mul_Ioi (show -S < (0 : ℝ) by linarith) (0 : ℝ)
  simp only [mul_zero, exp_zero] at h
  rw [h, neg_div_neg_eq]

/-! ### McFadden's theorem: the algebraic core -/

section McFadden

variable {ι : Type*} [Fintype ι]

/-- The McFadden integral for alternative `i` with scale `β`:

    `Iᵢ = exp(uᵢ/β) · ∫₀^∞ exp(-S·t) dt`

    where `S = Σⱼ exp(uⱼ/β)` is the partition function.

    After the change of variables `t = exp(-x/β)` in the original
    Gumbel density integral, the max-probability `P(Uᵢ = max_j Uⱼ)` takes
    this form. See `gumbelMaxProb_is_mcfaddenIntegral`. -/
noncomputable def mcfaddenIntegral (u : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  exp (u i / β) * ∫ t in Ioi (0 : ℝ), exp (-(∑ j : ι, exp (u j / β)) * t)

section Softmax

variable [Nonempty ι] (u : ι → ℝ) {β : ℝ}

/-- **McFadden's theorem (algebraic core)** — Lemma 1 of [mcfadden-1974]:
    the McFadden integral equals softmax. For utilities `u` and scale `β`,

    `exp(uᵢ/β) · ∫₀^∞ exp(-S·t) dt = exp(uᵢ/β) / S = softmax((1/β) • u)ᵢ`,

    where `S = Σⱼ exp(uⱼ/β)`. The identity is purely algebraic and holds for
    every `β` (the RUM-relevant case is `β > 0`). [mcfadden-1974] assumes i.i.d.
    Weibull (Gnedenko extreme-value) noise with CDF `exp(-e^{-ε})` and derives the
    softmax selection probability `Pᵢ = e^{Vᵢ} / Σ e^{Vⱼ}`; the probabilistic
    interpretation is formalized in `gumbelMaxProb_is_mcfaddenIntegral`. -/
theorem mcfaddenIntegral_eq_softmax (i : ι) :
    mcfaddenIntegral u β i = softmax ((1 / β) • u) i := by
  simp only [mcfaddenIntegral, softmax, Pi.smul_apply, smul_eq_mul]
  have hS : 0 < ∑ j : ι, exp (u j / β) :=
    Finset.sum_pos (λ j _ => exp_pos _) ⟨Classical.arbitrary ι, mem_univ _⟩
  rw [integral_exp_neg_mul_Ioi_zero hS]
  simp_rw [show ∀ j : ι, u j / β = (1 / β) * u j from λ j => by ring]
  rw [mul_one_div]

/-- The McFadden integrals sum to 1 (they form a probability distribution). -/
theorem mcfaddenIntegral_sum :
    ∑ i : ι, mcfaddenIntegral u β i = 1 := by
  simp_rw [mcfaddenIntegral_eq_softmax]
  exact softmax_sum_eq_one ((1 / β) • u)

/-- Each McFadden integral is positive. -/
theorem mcfaddenIntegral_pos (i : ι) :
    0 < mcfaddenIntegral u β i := by
  rw [mcfaddenIntegral_eq_softmax]
  exact softmax_pos ((1 / β) • u) i

end Softmax

end McFadden

/-! ### Binary case: McFadden equals the logistic function -/

section Binary

variable (u : Fin 2 → ℝ) {β : ℝ}

/-- **Binary McFadden = logistic**: for two alternatives, the McFadden integral
    reduces to the logistic function.

    `mcfaddenIntegral([u₁, u₂], β)(0) = Real.sigmoid((u₁ - u₂) / β)`

    This is the exact Gumbel-Luce result for binary choice: if `ε₁, ε₂` are
    i.i.d. Gumbel(0, β), then `P(u₁+ε₁ > u₂+ε₂) = Real.sigmoid((u₁-u₂)/β)`.

    Compare with Thurstone Case V (`Thurstone.lean`):
    `P(u₁+η₁ > u₂+η₂) = Φ((u₁-u₂)/(σ√2))` for Gaussian noise η. -/
theorem mcfaddenIntegral_binary :
    mcfaddenIntegral u β 0 = Real.sigmoid ((u 0 - u 1) / β) := by
  rw [mcfaddenIntegral_eq_softmax, softmax_binary]
  congr 1; ring

/-- The binary McFadden integral for alternative 1 is the complement. -/
theorem mcfaddenIntegral_binary_one :
    mcfaddenIntegral u β 1 = 1 - Real.sigmoid ((u 0 - u 1) / β) := by
  have hsum := mcfaddenIntegral_sum (u := u) (β := β)
  rw [Fin.sum_univ_two] at hsum
  linarith [mcfaddenIntegral_binary (u := u) (β := β)]

end Binary

/-! ### The Gumbel RUM as a `RationalAction` -/

section GumbelRUM

variable {ι : Type*} [Fintype ι]

/-- Construct a `RationalAction` from a Gumbel RUM.

    The score function is `exp(uᵢ/β)`, which gives Luce's choice rule.
    This is the *exact* optimal policy under i.i.d. Gumbel noise
    (by McFadden's theorem), not an approximation. -/
noncomputable def RationalAction.fromGumbelRUM (u : ι → ℝ) (β : ℝ) :
    RationalAction Unit ι where
  score := λ _ i => exp (u i / β)
  score_nonneg := λ _ _ => le_of_lt (exp_pos _)

/-- The Gumbel RUM policy equals the McFadden integral (= softmax). -/
theorem RationalAction.fromGumbelRUM_policy [Nonempty ι] (u : ι → ℝ) {β : ℝ} (i : ι) :
    (RationalAction.fromGumbelRUM u β).policy () i =
    mcfaddenIntegral u β i := by
  rw [mcfaddenIntegral_eq_softmax]
  simp only [RationalAction.policy, RationalAction.fromGumbelRUM,
             RationalAction.totalScore, softmax, Pi.smul_apply, smul_eq_mul]
  have hne : ∑ j : ι, exp (u j / β) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (λ j _ => exp_pos _) ⟨Classical.arbitrary ι, mem_univ _⟩)
  rw [if_neg hne]
  congr 1
  · congr 1; ring
  · congr 1; ext j; congr 1; ring

end GumbelRUM

/-! ### Measure-theoretic content: the Gumbel max-probability integral -/

/-- `gumbelMaxCDF S β x = exp(-S · exp(-x/β))`: the CDF of the maximum random
    utility (a scaled Gumbel), the antiderivative core of the McFadden integral. -/
private noncomputable abbrev gumbelMaxCDF (S β x : ℝ) : ℝ := exp (-S * exp (-x / β))

/-- `gumbelMaxProbAntideriv C S β x = (C/S) · gumbelMaxCDF S β x`: the
    antiderivative used in the FTC computation of the max-probability integral. -/
private noncomputable abbrev gumbelMaxProbAntideriv (C S β x : ℝ) : ℝ :=
  C / S * gumbelMaxCDF S β x

private lemma hasDerivAt_exp_neg_div {β : ℝ} (x : ℝ) :
    HasDerivAt (fun x => exp (-x / β)) (exp (-x / β) * (-1 / β)) x := by
  have h := hasDerivAt_id x |>.neg.div_const β
  exact (Real.hasDerivAt_exp _).comp x (h.congr_deriv (by simp [neg_div]))

private lemma hasDerivAt_gumbelMaxCDF (S β x : ℝ) :
    HasDerivAt (gumbelMaxCDF S β)
      (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β)))) x :=
  ((hasDerivAt_exp_neg_div (β := β) x).const_mul (-S)).exp

private lemma hasDerivAt_gumbelMaxProbAntideriv (C S β x : ℝ) :
    HasDerivAt (gumbelMaxProbAntideriv C S β)
      (C / S * (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β))))) x :=
  (hasDerivAt_gumbelMaxCDF S β x).const_mul (C / S)

private lemma tendsto_gumbelMaxCDF_atTop {β : ℝ} (hβ : 0 < β) (S : ℝ) :
    Tendsto (gumbelMaxCDF S β) atTop (nhds 1) := by
  show Tendsto (fun x => exp (-S * exp (-x / β))) atTop (nhds 1)
  rw [show (1 : ℝ) = exp 0 from exp_zero.symm]
  exact (continuous_exp.tendsto 0).comp (by
    rw [show (0 : ℝ) = -S * 0 from by ring]
    exact (tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.atBot_div_const hβ)).const_mul (-S))

private lemma tendsto_gumbelMaxCDF_atBot {S β : ℝ} (hS : 0 < S) (hβ : 0 < β) :
    Tendsto (gumbelMaxCDF S β) atBot (nhds 0) := by
  show Tendsto (fun x => exp (-S * exp (-x / β))) atBot (nhds 0)
  exact tendsto_exp_atBot.comp
    ((tendsto_exp_atTop.comp
      (tendsto_neg_atBot_atTop.atTop_div_const hβ)).const_mul_atTop_of_neg
      (neg_lt_zero.mpr hS))

private lemma tendsto_gumbelMaxProbAntideriv_atTop (C : ℝ) {S β : ℝ} (hβ : 0 < β) :
    Tendsto (gumbelMaxProbAntideriv C S β) atTop (nhds (C / S)) := by
  show Tendsto (fun x => C / S * gumbelMaxCDF S β x) atTop (nhds (C / S))
  simpa using (tendsto_gumbelMaxCDF_atTop hβ S).const_mul (C / S)

private lemma tendsto_gumbelMaxProbAntideriv_atBot (C : ℝ) {S β : ℝ} (hS : 0 < S) (hβ : 0 < β) :
    Tendsto (gumbelMaxProbAntideriv C S β) atBot (nhds 0) := by
  show Tendsto (fun x => C / S * gumbelMaxCDF S β x) atBot (nhds 0)
  simpa using (tendsto_gumbelMaxCDF_atBot hS hβ).const_mul (C / S)

private lemma gumbelMaxProbAntideriv_deriv_nonneg {C S β : ℝ}
    (hC : 0 ≤ C) (hS : 0 < S) (hβ : 0 < β) (x : ℝ) :
    0 ≤ C / S * (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β)))) := by
  show 0 ≤ C / S * (exp (-S * exp (-x / β)) * (-S * (exp (-x / β) * (-1 / β))))
  have : C / S * (exp (-S * exp (-x / β)) * (-S * (exp (-x / β) * (-1 / β)))) =
      C / (S * β) * (exp (-S * exp (-x / β)) * (S * exp (-x / β))) := by field_simp
  rw [this]; exact mul_nonneg (div_nonneg hC (by positivity))
    (mul_nonneg (le_of_lt (exp_pos _)) (by positivity))

private lemma gumbelMaxProbAntideriv_integrableOn_Ioi {C S β : ℝ}
    (hC : 0 ≤ C) (hS : 0 < S) (hβ : 0 < β) :
    IntegrableOn
      (fun x => C / S * (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β)))))
      (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => hasDerivAt_gumbelMaxProbAntideriv C S β x)
    (fun x _ => gumbelMaxProbAntideriv_deriv_nonneg hC hS hβ x)
    (tendsto_gumbelMaxProbAntideriv_atTop C hβ)

private lemma gumbelMaxProbAntideriv_integrableOn_Iic {C S β : ℝ}
    (hC : 0 ≤ C) (hS : 0 < S) (hβ : 0 < β) :
    IntegrableOn
      (fun x => C / S * (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β)))))
      (Set.Iic 0) := by
  set f := fun x => C / S * (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β))))
  have hcont : Continuous f := by
    show Continuous fun x =>
      C / S * (exp (-S * exp (-x / β)) * (-S * (exp (-x / β) * (-1 / β))))
    fun_prop
  have hfi : ∀ c : ℝ, IntegrableOn f (Set.Ioc c 0) := fun c => hcont.integrableOn_Ioc
  have hint : ∀ c : ℝ, IntervalIntegrable f volume c 0 := fun c => hcont.intervalIntegrable c 0
  have hftc : ∀ c ≤ (0 : ℝ), ∫ x in c..0, f x =
      gumbelMaxProbAntideriv C S β 0 - gumbelMaxProbAntideriv C S β c := by
    intro c hc
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc
      (fun x _ => (hasDerivAt_gumbelMaxProbAntideriv C S β x).continuousAt.continuousWithinAt)
      (fun x _ => hasDerivAt_gumbelMaxProbAntideriv C S β x) (hint c)
  have hnorm_eq : ∀ c ≤ (0 : ℝ), ∫ x in c..0, ‖f x‖ = ∫ x in c..0, f x := by
    intro c hc; congr 1; ext x
    exact norm_of_nonneg (gumbelMaxProbAntideriv_deriv_nonneg hC hS hβ x)
  refine integrableOn_Iic_of_intervalIntegral_norm_tendsto
    (gumbelMaxProbAntideriv C S β 0) 0 hfi tendsto_id ?_
  have hlim : Tendsto (fun c => gumbelMaxProbAntideriv C S β 0 - gumbelMaxProbAntideriv C S β c)
      atBot (nhds (gumbelMaxProbAntideriv C S β 0)) := by
    have h : Tendsto (fun c => gumbelMaxProbAntideriv C S β 0 - gumbelMaxProbAntideriv C S β c)
        atBot (nhds (gumbelMaxProbAntideriv C S β 0 - 0)) :=
      tendsto_const_nhds.sub (tendsto_gumbelMaxProbAntideriv_atBot C hS hβ)
    rwa [sub_zero] at h
  exact hlim.congr' (by
    filter_upwards [Filter.Iic_mem_atBot (0 : ℝ)] with c (hc : c ≤ 0)
    rw [hnorm_eq c hc, hftc c hc])

private lemma gumbelMaxProbAntideriv_deriv_integrable {C S β : ℝ}
    (hC : 0 ≤ C) (hS : 0 < S) (hβ : 0 < β) :
    Integrable
      (fun x => C / S * (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β))))) := by
  rw [← integrableOn_univ, show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0
    from (Set.Iic_union_Ioi).symm]
  exact IntegrableOn.union
    (gumbelMaxProbAntideriv_integrableOn_Iic hC hS hβ)
    (gumbelMaxProbAntideriv_integrableOn_Ioi hC hS hβ)

private theorem gumbelMaxProbAntideriv_integral {C S β : ℝ}
    (hC : 0 ≤ C) (hS : 0 < S) (hβ : 0 < β) :
    ∫ x : ℝ, C / S * (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β)))) =
    C / S := by
  have := integral_of_hasDerivAt_of_tendsto
    (fun x => hasDerivAt_gumbelMaxProbAntideriv C S β x)
    (gumbelMaxProbAntideriv_deriv_integrable hC hS hβ)
    (tendsto_gumbelMaxProbAntideriv_atBot C hS hβ)
    (tendsto_gumbelMaxProbAntideriv_atTop C hβ)
  linarith

private lemma gumbelMaxProb_integrand_eq {n : ℕ}
    (u : Fin n → ℝ) (β : ℝ) (hβ : 0 < β) (i : Fin n) (x : ℝ) :
    gumbelPDF β (x - u i) * ∏ j ∈ univ.erase i, gumbelCDF β (x - u j) =
    exp (u i / β) / (∑ j : Fin n, exp (u j / β)) *
      (gumbelMaxCDF (∑ j : Fin n, exp (u j / β)) β x *
       (-(∑ j : Fin n, exp (u j / β)) * (exp (-x / β) * (-1 / β)))) := by
  simp only [gumbelPDF, gumbelCDF]
  set S := ∑ j : Fin n, exp (u j / β)
  have hS_ne : S ≠ 0 := ne_of_gt (Finset.sum_pos (fun j _ => exp_pos _) ⟨i, mem_univ _⟩)
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have h_prod : exp (-exp (-(x - u i) / β)) *
      ∏ j ∈ univ.erase i, exp (-exp (-(x - u j) / β)) =
      gumbelMaxCDF S β x := by
    rw [Finset.mul_prod_erase univ (fun j => exp (-exp (-(x - u j) / β))) (mem_univ i)]
    rw [← exp_sum]
    show exp (∑ j : Fin n, -exp (-(x - u j) / β)) = exp (-S * exp (-x / β))
    congr 1
    simp_rw [show ∀ j : Fin n, -(x - u j) / β = u j / β + (-x / β) from fun j => by ring,
             exp_add]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  have h_exp : exp (-(x - u i) / β) = exp (u i / β) * exp (-x / β) := by
    rw [show -(x - u i) / β = u i / β + (-x / β) from by ring, exp_add]
  rw [show (1 / β * exp (-(x - u i) / β) * exp (-exp (-(x - u i) / β))) *
      ∏ j ∈ univ.erase i, exp (-exp (-(x - u j) / β)) =
      1 / β * exp (-(x - u i) / β) *
      (exp (-exp (-(x - u i) / β)) * ∏ j ∈ univ.erase i, exp (-exp (-(x - u j) / β)))
      from by ring]
  rw [h_prod, h_exp]
  show 1 / β * (exp (u i / β) * exp (-x / β)) * gumbelMaxCDF S β x =
    exp (u i / β) / S * (gumbelMaxCDF S β x * (-S * (exp (-x / β) * (-1 / β))))
  field_simp

/-- **Gumbel RUM = McFadden integral** — the measure-theoretic content of
    Lemma 1 in [mcfadden-1974].

    If `ε₁, …, εₙ` are i.i.d. Gumbel(0, β), then the probability that alternative
    `i` attains the maximum random utility equals the McFadden integral:

    `P(uᵢ + εᵢ = maxⱼ(uⱼ + εⱼ)) = mcfaddenIntegral u β i`

    The proof uses the antiderivative `G(x) = (C/S) · exp(-S · exp(-x/β))` with
    `C = exp(uᵢ/β)` and `S = Σⱼ exp(uⱼ/β)`: by the FTC on ℝ
    (`integral_of_hasDerivAt_of_tendsto`), `∫ G' = C/S = mcfaddenIntegral`. -/
theorem gumbelMaxProb_is_mcfaddenIntegral
    {n : ℕ} (u : Fin n → ℝ) (β : ℝ) (hβ : 0 < β) (i : Fin n) :
    (∫ x : ℝ, gumbelPDF β (x - u i) *
      ∏ j ∈ univ.erase i, gumbelCDF β (x - u j))
    = mcfaddenIntegral u β i := by
  have hS : 0 < ∑ j : Fin n, exp (u j / β) :=
    Finset.sum_pos (fun j _ => exp_pos _) ⟨i, mem_univ _⟩
  simp_rw [gumbelMaxProb_integrand_eq u β hβ i]
  rw [gumbelMaxProbAntideriv_integral (le_of_lt (exp_pos _)) hS hβ]
  simp only [mcfaddenIntegral]
  rw [integral_exp_neg_mul_Ioi_zero hS]
  ring

/-! ### Uniqueness: Gumbel is the only distribution yielding softmax

McFadden's Lemma 2 shows that the Gumbel distribution is the **only** i.i.d. noise
distribution yielding the softmax (Luce) choice rule. The key step: if the max-CDF
`G` satisfies the functional equation `G(x - c) = G(x) ^ exp c` for all `x, c`, then
`G` is a Gumbel CDF `G(t) = exp(-α · exp(-t))` with `α = -log(G 0) > 0`. Setting
`x = 0`, `c = -t` gives `G t = G 0 ^ exp(-t)`, then `G 0 ^ y = exp(log(G 0) · y)` via
`rpow_def_of_pos`. -/

/-- If a function G satisfies the functional equation
    `G(x - c) = G(x) ^ exp(c)` for all `x, c ∈ ℝ`,
    and `0 < G(0) < 1`, then G is a Gumbel CDF:

    `G(t) = exp(-α · exp(-t))` where `α = -log(G(0)) > 0`.

    This is the core of McFadden's Lemma 2: the functional equation
    characterizing the max-CDF uniquely determines the Gumbel family. The
    hypothesis `G 0 < 1` is unused in this proof but pins down `α > 0`
    (see `gumbel_alpha_pos`), excluding the degenerate `α = 0` case. -/
theorem gumbel_from_functional_eq (G : ℝ → ℝ)
    (hG0_pos : 0 < G 0) (_hG0_lt : G 0 < 1)
    (hfe : ∀ x c : ℝ, G (x - c) = (G x) ^ (exp c)) :
    ∀ t : ℝ, G t = exp (-(-log (G 0)) * exp (-t)) := by
  intro t
  -- Set x = 0, c = -t in the functional equation
  have h := hfe 0 (-t)
  simp only [zero_sub, neg_neg] at h
  -- h : G t = (G 0) ^ exp (-t)
  rw [h, rpow_def_of_pos hG0_pos]
  -- Goal: exp (log (G 0) * exp (-t)) = exp (-(-log (G 0)) * exp (-t))
  congr 1; ring

/-- The scale parameter α = -log(G(0)) is positive when 0 < G(0) < 1. -/
theorem gumbel_alpha_pos (G : ℝ → ℝ)
    (hG0_pos : 0 < G 0) (hG0_lt : G 0 < 1) :
    0 < -log (G 0) := by
  rw [neg_pos]
  exact log_neg hG0_pos hG0_lt

/-- When G(0) = e⁻¹ (i.e., α = 1), the functional equation gives the
    standard Gumbel CDF: G(t) = exp(-exp(-t)). -/
theorem gumbel_standard_from_functional_eq (G : ℝ → ℝ)
    (hG0 : G 0 = exp (-1))
    (hfe : ∀ x c : ℝ, G (x - c) = (G x) ^ (exp c)) :
    ∀ t : ℝ, G t = exp (-exp (-t)) := by
  have hG0_pos : 0 < G 0 := by rw [hG0]; exact exp_pos _
  have hG0_lt : G 0 < 1 := by rw [hG0]; exact exp_lt_one_iff.mpr (by linarith)
  have h := gumbel_from_functional_eq G hG0_pos hG0_lt hfe
  intro t
  rw [h t]
  congr 1
  -- Goal: -(-log (G 0)) * exp (-t) = -exp (-t)
  rw [hG0, log_exp]; ring

end Core
