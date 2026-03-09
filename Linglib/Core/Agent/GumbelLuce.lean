import Linglib.Core.Agent.RationalAction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Gumbel-Luce Equivalence (McFadden's Theorem) @cite{mcfadden-1974}

The exact algebraic connection between Gumbel noise in a Random Utility Model
(RUM) and the Luce choice rule (softmax). @cite{luce-1959}

## Random Utility Models

A Random Utility Model (RUM) assigns each alternative `i` a random utility:

    `Uᵢ = uᵢ + εᵢ`

where `uᵢ` is a deterministic component and `εᵢ` is random noise.
The choice probability is `P(i chosen) = P(Uᵢ = max_j Uⱼ)`.

Two noise distributions yield closed-form choice probabilities:

- **Gaussian noise** → `Φ` (Thurstone Case V, §2.D of @cite{luce-1959})
- **Gumbel noise** → softmax (@cite{mcfadden-1974})

## McFadden's Theorem

If the `εᵢ` are i.i.d. Gumbel(0, β), then:

    `P(i chosen) = exp(uᵢ/β) / Σⱼ exp(uⱼ/β) = softmax(u, 1/β)ᵢ`

This is **exact** — no approximation involved. The proof reduces to the
Laplace integral `∫₀^∞ exp(-S·t) dt = 1/S` after a change of variables.

## Thurstone–Luce Bridge

Combined with the Thurstone result (`Thurstone.lean`), this gives the precise
relationship between the two models:

- Gaussian noise → normal CDF (Thurstone, exact)
- Gumbel noise → logistic/softmax (Luce, exact by McFadden)
- `Φ ≈ logistic` (numerical approximation, max error ~0.01)

The two models are both RUMs, differing only in noise distribution.
The logistic approximation to the normal CDF (`Thurstone.lean` §4) is what
connects them, not a foundational assumption.

## Main Results

- `integral_exp_neg_mul_Ioi_zero`: Laplace integral `∫₀^∞ exp(-S·t) dt = 1/S`
- `mcfaddenIntegral_eq_softmax`: McFadden's theorem (algebraic core)
- `mcfaddenIntegral_binary`: Binary case reduces to logistic function
- `gumbelCDF`, `gumbelPDF`: Gumbel distribution definitions
-/

set_option autoImplicit false

namespace Core

open Real MeasureTheory Set BigOperators Finset

-- ============================================================================
-- §1. Gumbel Distribution
-- ============================================================================

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

-- ============================================================================
-- §2. Key Integral: ∫₀^∞ exp(-S·t) dt = 1/S
-- ============================================================================

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

-- ============================================================================
-- §3. McFadden's Theorem (Algebraic Core)
-- ============================================================================

/-- The McFadden integral for alternative `i` with scale `β > 0`:

    `Iᵢ = exp(uᵢ/β) · ∫₀^∞ exp(-S·t) dt`

    where `S = Σⱼ exp(uⱼ/β)` is the partition function.

    After the change of variables `t = exp(-x/β)` in the original
    Gumbel density integral, the max-probability `P(Uᵢ = max_j Uⱼ)` takes
    this form. See `gumbelMaxProb_is_mcfaddenIntegral`. -/
noncomputable def mcfaddenIntegral {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  exp (u i / β) * ∫ t in Ioi (0 : ℝ), exp (-(∑ j : ι, exp (u j / β)) * t)

/-- **McFadden's Theorem (algebraic core)** — Lemma 1 of @cite{mcfadden-1974}:
    The McFadden integral equals softmax.

    For any utilities `u₁, ..., uₙ` and scale `β > 0`:

    `exp(uᵢ/β) · ∫₀^∞ exp(-S·t) dt = exp(uᵢ/β) / S = softmax(u, 1/β)ᵢ`

    where `S = Σⱼ exp(uⱼ/β)`.

    This is the algebraic content of McFadden's Lemma 1 (p. 111), generalized
    from unit scale (β = 1) to arbitrary β > 0. McFadden assumes i.i.d. Weibull
    (Gnedenko extreme value) noise with CDF `P(ε ≤ ε) = exp(-e^{-ε})` —
    eq. (13) — and derives the softmax selection probability `P_i = e^{V_i} / Σ e^{V_j}`
    — eq. (12). The probabilistic interpretation is formalized separately in
    `gumbelMaxProb_is_mcfaddenIntegral`. -/
theorem mcfaddenIntegral_eq_softmax {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℝ) {β : ℝ} (_hβ : 0 < β) (i : ι) :
    mcfaddenIntegral u β i = softmax u (1 / β) i := by
  simp only [mcfaddenIntegral, softmax]
  have hS : 0 < ∑ j : ι, exp (u j / β) :=
    Finset.sum_pos (λ j _ => exp_pos _) ⟨Classical.arbitrary ι, mem_univ _⟩
  rw [integral_exp_neg_mul_Ioi_zero hS]
  simp_rw [show ∀ j : ι, u j / β = (1 / β) * u j from λ j => by ring]
  rw [mul_one_div]

-- ============================================================================
-- §4. Properties
-- ============================================================================

/-- The McFadden integrals sum to 1 (they form a probability distribution). -/
theorem mcfaddenIntegral_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    ∑ i : ι, mcfaddenIntegral u β i = 1 := by
  simp_rw [mcfaddenIntegral_eq_softmax u hβ]
  exact softmax_sum_eq_one u (1 / β)

/-- Each McFadden integral is positive. -/
theorem mcfaddenIntegral_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℝ) {β : ℝ} (hβ : 0 < β) (i : ι) :
    0 < mcfaddenIntegral u β i := by
  rw [mcfaddenIntegral_eq_softmax u hβ]
  exact softmax_pos u (1 / β) i

-- ============================================================================
-- §5. Binary Case: McFadden = Logistic
-- ============================================================================

/-- **Binary McFadden = Logistic**: For two alternatives, the McFadden integral
    reduces to the logistic function.

    `mcfaddenIntegral([u₁, u₂], β)(0) = logistic((u₁ - u₂) / β)`

    This is the exact Gumbel-Luce result for binary choice: if `ε₁, ε₂` are
    i.i.d. Gumbel(0, β), then `P(u₁+ε₁ > u₂+ε₂) = logistic((u₁-u₂)/β)`.

    Compare with Thurstone Case V (`Thurstone.lean`):
    `P(u₁+η₁ > u₂+η₂) = Φ((u₁-u₂)/(σ√2))` for Gaussian noise η. -/
theorem mcfaddenIntegral_binary (u : Fin 2 → ℝ) {β : ℝ} (hβ : 0 < β) :
    mcfaddenIntegral u β 0 = logistic ((u 0 - u 1) / β) := by
  rw [mcfaddenIntegral_eq_softmax u hβ, softmax_binary]
  congr 1; ring

/-- The binary McFadden integral for alternative 1 is the complement. -/
theorem mcfaddenIntegral_binary_one (u : Fin 2 → ℝ) {β : ℝ} (hβ : 0 < β) :
    mcfaddenIntegral u β 1 = 1 - logistic ((u 0 - u 1) / β) := by
  have hsum := mcfaddenIntegral_sum u hβ (ι := Fin 2)
  rw [Fin.sum_univ_two] at hsum
  linarith [mcfaddenIntegral_binary u hβ]

-- ============================================================================
-- §6. McFadden as RationalAction
-- ============================================================================

/-- Construct a `RationalAction` from a Gumbel RUM.

    The score function is `exp(uᵢ/β)`, which gives Luce's choice rule.
    This is the *exact* optimal policy under i.i.d. Gumbel noise
    (by McFadden's theorem), not an approximation. -/
noncomputable def RationalAction.fromGumbelRUM {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (β : ℝ) : RationalAction Unit ι where
  score := λ _ i => exp (u i / β)
  score_nonneg := λ _ _ => le_of_lt (exp_pos _)

/-- The Gumbel RUM policy equals the McFadden integral (= softmax). -/
theorem RationalAction.fromGumbelRUM_policy {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℝ) {β : ℝ} (hβ : 0 < β) (i : ι) :
    (RationalAction.fromGumbelRUM u β).policy () i =
    mcfaddenIntegral u β i := by
  rw [mcfaddenIntegral_eq_softmax u hβ]
  simp only [RationalAction.policy, RationalAction.fromGumbelRUM,
             RationalAction.totalScore, softmax]
  have hne : ∑ j : ι, exp (u j / β) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (λ j _ => exp_pos _) ⟨Classical.arbitrary ι, mem_univ _⟩)
  rw [if_neg hne]
  congr 1
  · congr 1; ring
  · congr 1; ext j; congr 1; ring

-- ============================================================================
-- §7. Measure-Theoretic Connection
-- ============================================================================

/-- **Gumbel RUM = McFadden Integral** — the measure-theoretic content
    of Lemma 1 in @cite{mcfadden-1974} (p. 111).

    If `ε₁, ..., εₙ` are i.i.d. Gumbel(0, β), then the probability that
    alternative `i` has the maximum random utility equals the McFadden integral:

    `P(uᵢ + εᵢ = max_j(uⱼ + εⱼ)) = mcfaddenIntegral u β i`

    McFadden's proof (p. 111) with `Vᵢ = v(s, xᵢ)`:
    1. From eq. (13), `F_i(ε + V_i - V_1, ..., ε + V_i - V_J)`
       `= exp(-ε) · ∏ⱼ exp(-exp(-ε - V_i + V_j))`
       `= exp(-ε) · exp(-exp(-ε) · Σⱼ exp(V_j - V_i))`
    2. Substituting in eq. (3) and integrating yields eq. (12):
       `P_i = e^{V_i} / Σⱼ e^{V_j}`

    TODO: Full proof requires the change-of-variables `t = exp(-x/β)` via
    `MeasureTheory.integral_comp_mul_deriv_Ioi`. -/
theorem gumbelMaxProb_is_mcfaddenIntegral
    {n : ℕ} (u : Fin n → ℝ) (β : ℝ) (_hβ : 0 < β) (i : Fin n) :
    (∫ x : ℝ, gumbelPDF β (x - u i) *
      ∏ j ∈ univ.erase i, gumbelCDF β (x - u j))
    = mcfaddenIntegral u β i := by
  sorry -- TODO: change of variables t = exp(-x/β)

-- ============================================================================
-- §8. Uniqueness: Gumbel is the Only Distribution Giving Softmax
-- ============================================================================

/-!
## McFadden's Lemma 2 (Uniqueness) @cite{mcfadden-1974}

McFadden's Lemma 2 shows that the Gumbel distribution is the **only**
i.i.d. noise distribution yielding the softmax (Luce) choice rule. The key
step is: if the max-CDF `G` satisfies the functional equation

    `G(x - c) = G(x) ^ exp(c)` for all `x, c ∈ ℝ`

then `G` must be a Gumbel CDF: `G(t) = exp(-α · exp(-t))` where
`α = -log(G(0)) > 0`.

The proof sets `x = 0` and `c = -t` in the functional equation, giving
`G(t) = G(0)^{exp(-t)}`, then rewrites `G(0)^y = exp(log(G(0)) · y)`
using `rpow_def_of_pos`.
-/

/-- If a function G satisfies the functional equation
    `G(x - c) = G(x) ^ exp(c)` for all `x, c ∈ ℝ`,
    and `0 < G(0) < 1`, then G is a Gumbel CDF:

    `G(t) = exp(-α · exp(-t))` where `α = -log(G(0)) > 0`.

    This is the core of McFadden's Lemma 2: the functional equation
    characterizing the max-CDF uniquely determines the Gumbel family. -/
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
