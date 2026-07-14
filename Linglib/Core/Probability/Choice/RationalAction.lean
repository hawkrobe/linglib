import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.MeanInequalities
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Linglib.Core.Probability.LogitChoice

/-!
# Rational action

[luce-1959] [cover-thomas-2006] [zaslavsky-hu-levy-2020] [adams-messick-1958]

The mathematical foundation for all soft-rational agents: RSA speakers and
listeners, BToM agents, and decision-theoretic actors. A `RationalAction` agent
selects actions with probability proportional to a non-negative score — the
**Luce choice rule**, the unique rule satisfying independence of irrelevant
alternatives (IIA): the relative probability of two actions depends only on their
scores.

The exponential parameterization (`softmax`) lives in `Core.Probability.LogitChoice`,
and its variational / information-theoretic / limiting theory in
`Core.Probability.SoftmaxTheory` (re-exported here); this file is the agent-framing
layer on top of those pure-math cores.

## Main definitions

* `RationalAction`, `RationalAction.policy` — the Luce choice rule.
* `RationalAction.fromSoftmax` — build an agent from a utility via `exp(α · u)`,
  bridging the agent framing to the `softmax` core.
* `ChoiceFn` and `ChoiceFn.hasRatioScale` / `hasProductRule` / `hasPairwiseIIA` —
  the choice-axiom forms.

## Main results

* `RationalAction.policy_eq_of_proportional`, `RationalAction.policy_eq_iff_proportional`
  — the policy depends only on the ratio scale of the scores.
* `RationalAction.iia`, `RationalAction.product_rule` — Luce's choice axiom for `pChoice`.
* `axiom1_ratio_iff_pairwiseIIA` — equivalence of the choice-axiom forms.
-/

namespace Core

open Real Finset

/-! ### Score-based agents (Luce choice rule) -/

/-- A rational action agent: selects actions with probability ∝ score(state, action).

This is the Luce choice rule. The `score` function is unnormalized;
normalization to a proper distribution is derived (see `policy`).

Key instances:
- RSA L0: `score(u, w) = prior(w) · meaning(u, w)`
- RSA S1: `score(w, u) = rpow(informativity(w, u), α) · exp(-α · cost(u))`
- BToM agent: `score(state, action) = exp(β · Q(state, action))`
-/
structure RationalAction (State Action : Type*) [Fintype Action] where
  /-- Unnormalized score: policy(a|s) ∝ score(s, a). -/
  score : State → Action → ℝ
  /-- Scores are non-negative. -/
  score_nonneg : ∀ s a, 0 ≤ score s a

variable {S A : Type*} [Fintype A]

/-- Total score across all actions in a state (normalization constant). -/
noncomputable def RationalAction.totalScore (ra : RationalAction S A) (s : S) : ℝ :=
  ∑ a : A, ra.score s a

theorem RationalAction.totalScore_nonneg (ra : RationalAction S A) (s : S) :
    0 ≤ ra.totalScore s :=
  Finset.sum_nonneg fun a _ => ra.score_nonneg s a

/-- Normalized policy: P(a|s) = score(s,a) / Σ_a' score(s,a').
    Returns 0 for all actions if totalScore = 0. -/
noncomputable def RationalAction.policy (ra : RationalAction S A) (s : S) (a : A) : ℝ :=
  if ra.totalScore s = 0 then 0 else ra.score s a / ra.totalScore s

theorem RationalAction.policy_nonneg (ra : RationalAction S A) (s : S) (a : A) :
    0 ≤ ra.policy s a := by
  simp only [policy]
  split
  · exact le_refl 0
  · exact div_nonneg (ra.score_nonneg s a) (ra.totalScore_nonneg s)

/-- Policy sums to 1 when totalScore is nonzero. -/
theorem RationalAction.policy_sum_eq_one (ra : RationalAction S A) (s : S)
    (h : ra.totalScore s ≠ 0) :
    ∑ a : A, ra.policy s a = 1 := by
  simp only [policy, h, ↓reduceIte, ← Finset.sum_div]
  exact div_self h

/-- Policy monotonicity: higher score → higher probability. -/
theorem RationalAction.policy_monotone (ra : RationalAction S A) (s : S)
    (a₁ a₂ : A) (h : ra.score s a₁ ≤ ra.score s a₂) :
    ra.policy s a₁ ≤ ra.policy s a₂ := by
  simp only [policy]
  split
  · exact le_refl 0
  · next hne =>
    have hpos : 0 < ra.totalScore s :=
      lt_of_le_of_ne (ra.totalScore_nonneg s) (Ne.symm hne)
    exact div_le_div_of_nonneg_right h (le_of_lt hpos)

/-- Zero score implies zero policy, regardless of whether totalScore is zero. -/
theorem RationalAction.policy_eq_zero_of_score_eq_zero (ra : RationalAction S A) (s : S)
    (a : A) (h : ra.score s a = 0) :
    ra.policy s a = 0 := by
  simp only [policy]
  split
  · rfl
  · simp [h]

/-- Policy respects score equality: equal scores → equal probabilities.
    Follows directly from the Luce rule: both sides are `score / totalScore`
    with the same denominator. -/
theorem RationalAction.policy_eq_of_score_eq (ra : RationalAction S A) (s : S)
    (a₁ a₂ : A) (h : ra.score s a₁ = ra.score s a₂) :
    ra.policy s a₁ = ra.policy s a₂ := by
  simp only [policy, h]

/-- When `totalScore` equals the score of action `a`, the policy for `a` is 1. -/
theorem RationalAction.policy_eq_one_of_totalScore_eq (ra : RationalAction S A) (s : S)
    (a : A) (h_sum : ra.totalScore s = ra.score s a) (h_pos : 0 < ra.score s a) :
    ra.policy s a = 1 := by
  simp only [policy, h_sum, ne_of_gt h_pos, ↓reduceIte, div_self (ne_of_gt h_pos)]

/-- Score ordering implies the negation of the strict policy ordering. -/
theorem RationalAction.policy_not_lt_of_score_le (ra : RationalAction S A) (s : S)
    (a₁ a₂ : A) (h : ra.score s a₂ ≤ ra.score s a₁) :
    ¬(ra.policy s a₁ < ra.policy s a₂) :=
  not_lt_of_ge (ra.policy_monotone s a₂ a₁ h)

/-- Strict policy monotonicity: strictly higher score gives strictly higher
    probability. -/
@[gcongr only]
theorem RationalAction.policy_lt_of_score_lt (ra : RationalAction S A) (s : S)
    (a₁ a₂ : A) (hlt : ra.score s a₁ < ra.score s a₂) :
    ra.policy s a₁ < ra.policy s a₂ := by
  have ha₂_pos : 0 < ra.score s a₂ :=
    lt_of_le_of_lt (ra.score_nonneg s a₁) hlt
  have htot_pos : 0 < ra.totalScore s :=
    lt_of_lt_of_le ha₂_pos
      (Finset.single_le_sum (fun a _ => ra.score_nonneg s a) (Finset.mem_univ a₂))
  simp only [policy, ne_of_gt htot_pos, ↓reduceIte]
  exact div_lt_div_of_pos_right hlt htot_pos

/-- Iff combining `policy_lt_of_score_lt` with the contrapositive of
    `policy_monotone`: at the same state, policy strict ordering coincides
    with score strict ordering. -/
theorem RationalAction.policy_lt_iff_score_lt (ra : RationalAction S A) (s : S)
    (a₁ a₂ : A) :
    ra.policy s a₁ < ra.policy s a₂ ↔ ra.score s a₁ < ra.score s a₂ :=
  ⟨fun h => by
    by_contra hle; push Not at hle
    exact absurd h (not_lt.mpr (ra.policy_monotone s a₂ a₁ hle)),
   ra.policy_lt_of_score_lt s a₁ a₂⟩

/-- Cross-state policy comparison (states with different normalization
    constants): the cross-product `score(s₁,a) · total(s₂) < score(s₂,a) · total(s₁)`
    is equivalent to `policy s₁ a < policy s₂ a` when both totals are positive. -/
theorem RationalAction.policy_lt_cross (ra : RationalAction S A) (s₁ s₂ : S) (a : A)
    (h_pos₁ : 0 < ra.totalScore s₁) (h_pos₂ : 0 < ra.totalScore s₂)
    (h_cross : ra.score s₁ a * ra.totalScore s₂ < ra.score s₂ a * ra.totalScore s₁) :
    ra.policy s₁ a < ra.policy s₂ a := by
  simp only [policy, ne_of_gt h_pos₁, ne_of_gt h_pos₂, ↓reduceIte]
  exact (div_lt_div_iff₀ h_pos₁ h_pos₂).mpr h_cross

/-- Cross-state policy comparison, with the `totalScore > 0` hypotheses derived
    from the cross-product inequality itself (so no positivity hypothesis is
    needed). -/
@[gcongr only]
theorem RationalAction.policy_lt_cross_of_cross_lt (ra : RationalAction S A)
    (s₁ s₂ : S) (a : A)
    (h_cross : ra.score s₁ a * ra.totalScore s₂ < ra.score s₂ a * ra.totalScore s₁) :
    ra.policy s₁ a < ra.policy s₂ a := by
  have h_lhs_nonneg : 0 ≤ ra.score s₁ a * ra.totalScore s₂ :=
    mul_nonneg (ra.score_nonneg s₁ a)
      (Finset.sum_nonneg fun b _ => ra.score_nonneg s₂ b)
  have h_rhs_pos : 0 < ra.score s₂ a * ra.totalScore s₁ :=
    lt_of_le_of_lt h_lhs_nonneg h_cross
  have h_tot1_nonneg : (0 : ℝ) ≤ ra.totalScore s₁ :=
    Finset.sum_nonneg fun b _ => ra.score_nonneg s₁ b
  have h_score2_pos : 0 < ra.score s₂ a :=
    (mul_pos_iff.mp h_rhs_pos).elim (fun ⟨h, _⟩ => h)
      (fun ⟨h, _⟩ => absurd h (not_lt.mpr (ra.score_nonneg s₂ a)))
  have h_tot1_pos : 0 < ra.totalScore s₁ :=
    (mul_pos_iff.mp h_rhs_pos).elim (fun ⟨_, h⟩ => h)
      (fun ⟨_, h⟩ => absurd h (not_lt.mpr h_tot1_nonneg))
  have h_tot2_pos : 0 < ra.totalScore s₂ :=
    lt_of_lt_of_le h_score2_pos
      (Finset.single_le_sum (fun b _ => ra.score_nonneg s₂ b) (Finset.mem_univ a))
  exact ra.policy_lt_cross s₁ s₂ a h_tot1_pos h_tot2_pos h_cross

/-- Score-sum ordering implies policy-sum ordering when both sides share the same
    state (same denominator). -/
theorem RationalAction.policy_list_sum_lt (ra : RationalAction S A) (s : S)
    (as₁ as₂ : List A)
    (h : (as₁.map (ra.score s)).sum < (as₂.map (ra.score s)).sum)
    (htot : 0 < ra.totalScore s) :
    (as₁.map (ra.policy s)).sum < (as₂.map (ra.policy s)).sum := by
  have htot_ne : ra.totalScore s ≠ 0 := ne_of_gt htot
  have hpol : ∀ a, ra.policy s a = ra.score s a / ra.totalScore s := by
    intro a; simp only [policy, htot_ne, ↓reduceIte]
  have hconv : ∀ (as : List A),
      (as.map (ra.policy s)).sum = (as.map (ra.score s)).sum / ra.totalScore s := by
    intro as; induction as with
    | nil => simp
    | cons a tl ih => simp [hpol, ih, add_div]
  rw [hconv, hconv]
  exact div_lt_div_of_pos_right h htot

/-- Finset-sum ordering implies policy-sum ordering when both sides share the
    same state (same denominator); the `Finset.sum` analogue of
    `policy_list_sum_lt`, with positivity derived from the score ordering. -/
theorem RationalAction.finset_sum_policy_lt_of_sum_score_lt
    (ra : RationalAction S A) (s : S) (F₁ F₂ : Finset A)
    (h : F₁.sum (ra.score s) < F₂.sum (ra.score s)) :
    F₁.sum (ra.policy s) < F₂.sum (ra.policy s) := by
  have hF₁_nonneg : 0 ≤ F₁.sum (ra.score s) :=
    Finset.sum_nonneg fun a _ => ra.score_nonneg s a
  have hF₂_pos : 0 < F₂.sum (ra.score s) := lt_of_le_of_lt hF₁_nonneg h
  have htot_pos : 0 < ra.totalScore s :=
    lt_of_lt_of_le hF₂_pos (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ F₂) (fun a _ _ => ra.score_nonneg s a))
  have htot_ne : ra.totalScore s ≠ 0 := ne_of_gt htot_pos
  have hpol : ∀ a, ra.policy s a = ra.score s a / ra.totalScore s := by
    intro a; simp only [policy, htot_ne, ↓reduceIte]
  have hconv : ∀ (F : Finset A),
      F.sum (ra.policy s) = F.sum (ra.score s) / ra.totalScore s := by
    intro F; rw [show F.sum (ra.policy s) = F.sum (fun a => ra.score s a / ra.totalScore s) from
      Finset.sum_congr rfl (fun a _ => hpol a), Finset.sum_div]
  rw [hconv, hconv]
  exact div_lt_div_of_pos_right h htot_pos

/-! ### Luce's choice axiom (IIA)

[luce-1959] showed that the ratio rule `P(a|s) = v(a)/Σv(b)` is
characterized by the **independence of irrelevant alternatives** (IIA): the
relative probability of two actions depends only on their scores, not on what
other actions are available.

We formalize:
- The **constant ratio rule**: `policy(a₁) · score(a₂) = policy(a₂) · score(a₁)`
- **Choice from subsets** (`pChoice`): restriction of the choice rule to a `Finset`
- **IIA**: ratios in any subset equal score ratios
- The **product rule**: `P(a,T) = P(a,S) · P(S,T)` for `S ⊆ T`
- **Scale invariance**: multiplying all scores by `k > 0` preserves policy
- **Uniqueness** (forward direction): proportional scores yield the same policy
-/

section LuceChoiceAxiom

variable {S A : Type*} [Fintype A]

/-- Constant ratio rule:
    `policy(a₁) · score(a₂) = policy(a₂) · score(a₁)`.
    The odds ratio policy(a₁)/policy(a₂) = score(a₁)/score(a₂). -/
theorem RationalAction.policy_ratio (ra : RationalAction S A) (s : S) (a₁ a₂ : A) :
    ra.policy s a₁ * ra.score s a₂ = ra.policy s a₂ * ra.score s a₁ := by
  simp only [policy]
  split
  · simp
  · next hne =>
    field_simp

/-- Choice probability from a subset: `pChoice(a, T) = score(a) / Σ_{b∈T} score(b)`.
    Returns 0 if `a ∉ T` or the subset total is 0. -/
noncomputable def RationalAction.pChoice [DecidableEq A] (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) : ℝ :=
  if a ∈ T then
    let subTotal := ∑ b ∈ T, ra.score s b
    if subTotal = 0 then 0 else ra.score s a / subTotal
  else 0

/-- `pChoice` on the full set equals `policy`. -/
theorem RationalAction.pChoice_univ [DecidableEq A] (ra : RationalAction S A) (s : S) (a : A) :
    ra.pChoice s Finset.univ a = ra.policy s a := by
  simp only [pChoice, Finset.mem_univ, ↓reduceIte, policy, totalScore]

/-- `pChoice` is non-negative. -/
theorem RationalAction.pChoice_nonneg [DecidableEq A] (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) :
    0 ≤ ra.pChoice s T a := by
  simp only [pChoice]
  split
  · split
    · exact le_refl 0
    · next hne =>
      exact div_nonneg (ra.score_nonneg s a)
        (Finset.sum_nonneg fun b _ => ra.score_nonneg s b)
  · exact le_refl 0

/-- `pChoice` sums to 1 over the subset when the subset total is nonzero. -/
theorem RationalAction.pChoice_sum_eq_one [DecidableEq A] (ra : RationalAction S A) (s : S)
    (T : Finset A) (hT : ∑ b ∈ T, ra.score s b ≠ 0) :
    ∑ a ∈ T, ra.pChoice s T a = 1 := by
  simp only [pChoice]
  have : ∑ a ∈ T, (if a ∈ T then if ∑ b ∈ T, ra.score s b = 0 then 0
      else ra.score s a / ∑ b ∈ T, ra.score s b else 0) =
      ∑ a ∈ T, (if ∑ b ∈ T, ra.score s b = 0 then 0
      else ra.score s a / ∑ b ∈ T, ra.score s b) := by
    apply Finset.sum_congr rfl
    intro a ha; simp [ha]
  rw [this]; simp only [hT, ↓reduceIte, ← Finset.sum_div]; exact div_self hT

/-- IIA core: the ratio of `pChoice` values in any subset equals the score ratio.
    For `a₁, a₂ ∈ T` with `score(a₂) > 0`:
    `pChoice(a₁, T) · score(a₂) = pChoice(a₂, T) · score(a₁)`. -/
theorem RationalAction.pChoice_ratio [DecidableEq A] (ra : RationalAction S A) (s : S)
    (T : Finset A) (a₁ a₂ : A) (h₁ : a₁ ∈ T) (h₂ : a₂ ∈ T) :
    ra.pChoice s T a₁ * ra.score s a₂ = ra.pChoice s T a₂ * ra.score s a₁ := by
  simp only [pChoice, h₁, h₂, ↓reduceIte]
  split
  · simp
  · next hne => field_simp

/-- Helper: `pChoice` value for `a ∈ T` with nonzero total. -/
private theorem RationalAction.pChoice_mem [DecidableEq A] (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T) (hT : ∑ b ∈ T, ra.score s b ≠ 0) :
    ra.pChoice s T a = ra.score s a / ∑ b ∈ T, ra.score s b := by
  simp only [pChoice, ha, hT, ↓reduceIte]

/-- IIA: `P(a, S) = P(a, T) / Σ_{b∈S} P(b, T)` for `S ⊆ T`.
    Choice probability from a subset is the conditional probability. -/
theorem RationalAction.iia [DecidableEq A] (ra : RationalAction S A) (s : S)
    (S' T : Finset A) (hST : S' ⊆ T)
    (a : A) (ha : a ∈ S')
    (hS_pos : ∑ b ∈ S', ra.score s b ≠ 0)
    (hT_pos : ∑ b ∈ T, ra.score s b ≠ 0) :
    ra.pChoice s S' a = ra.pChoice s T a / ∑ b ∈ S', ra.pChoice s T b := by
  rw [ra.pChoice_mem s S' a ha hS_pos, ra.pChoice_mem s T a (hST ha) hT_pos]
  have hsum : ∑ b ∈ S', ra.pChoice s T b =
      (∑ b ∈ S', ra.score s b) / ∑ c ∈ T, ra.score s c := by
    have : ∀ b ∈ S', ra.pChoice s T b = ra.score s b / ∑ c ∈ T, ra.score s c :=
      fun b hb => ra.pChoice_mem s T b (hST hb) hT_pos
    rw [Finset.sum_congr rfl this, Finset.sum_div]
  rw [hsum]
  field_simp

/-- Product rule:
    `P(a, T) = P(a, S) · P(S, T)` for `a ∈ S ⊆ T`,
    where `P(S, T) = Σ_{b∈S} score(b) / Σ_{b∈T} score(b)`. -/
theorem RationalAction.product_rule [DecidableEq A] (ra : RationalAction S A) (s : S)
    (S' T : Finset A) (hST : S' ⊆ T)
    (a : A) (ha : a ∈ S')
    (hS_pos : ∑ b ∈ S', ra.score s b ≠ 0)
    (hT_pos : ∑ b ∈ T, ra.score s b ≠ 0) :
    ra.pChoice s T a =
    ra.pChoice s S' a * ((∑ b ∈ S', ra.score s b) / ∑ b ∈ T, ra.score s b) := by
  rw [ra.pChoice_mem s T a (hST ha) hT_pos, ra.pChoice_mem s S' a ha hS_pos]
  have hS_ne : (∑ b ∈ S', ra.score s b) ≠ 0 := hS_pos
  rw [div_mul_div_comm, show ra.score s a * ∑ b ∈ S', ra.score s b =
      (∑ b ∈ S', ra.score s b) * ra.score s a from mul_comm _ _,
      mul_div_mul_left _ _ hS_ne]

/-- Scale all scores by a positive constant `k`. -/
noncomputable def RationalAction.scaleBy (ra : RationalAction S A) (k : ℝ) (hk : 0 < k) :
    RationalAction S A where
  score s a := k * ra.score s a
  score_nonneg s a := mul_nonneg (le_of_lt hk) (ra.score_nonneg s a)

/-- Scale invariance: scaling scores by `k > 0` preserves policy. -/
theorem RationalAction.scaleBy_policy (ra : RationalAction S A) (s : S) (a : A)
    (k : ℝ) (hk : 0 < k) :
    (ra.scaleBy k hk).policy s a = ra.policy s a := by
  simp only [policy, scaleBy, totalScore, ← Finset.mul_sum]
  have hk_ne : k ≠ 0 := ne_of_gt hk
  by_cases hs0 : ∑ a' : A, ra.score s a' = 0
  · simp [hs0]
  · have hne : k * ∑ a' : A, ra.score s a' ≠ 0 := mul_ne_zero hk_ne hs0
    simp [hs0, hne]
    field_simp

/-- Uniqueness (forward direction):
    If scores are proportional (`score'(s,a) = k · score(s,a)` for some `k > 0`),
    then both agents have the same policy. -/
theorem RationalAction.policy_eq_of_proportional (ra ra' : RationalAction S A) (s : S)
    (k : ℝ) (hk : 0 < k) (h : ∀ a, ra'.score s a = k * ra.score s a) (a : A) :
    ra'.policy s a = ra.policy s a := by
  simp only [policy, totalScore]
  have hk_ne : k ≠ 0 := ne_of_gt hk
  simp_rw [h, ← Finset.mul_sum]
  by_cases hs0 : ∑ a' : A, ra.score s a' = 0
  · simp [hs0]
  · have hne : k * ∑ a' : A, ra.score s a' ≠ 0 := mul_ne_zero hk_ne hs0
    simp [hs0, hne]
    field_simp

end LuceChoiceAxiom


/-- Construct a `RationalAction` from a utility function via softmax: the score
is `exp(α · utility(s, a))`, so `policy = softmax(utility, α)`. -/
noncomputable def RationalAction.fromSoftmax
    (utility : S → A → ℝ) (α : ℝ) : RationalAction S A where
  score s a := exp (α * utility s a)
  score_nonneg _ _ := le_of_lt (exp_pos _)

/-- The policy of a softmax agent equals the softmax function. -/
theorem RationalAction.fromSoftmax_policy_eq [Nonempty A]
    (utility : S → A → ℝ) (α : ℝ) (s : S) (a : A) :
    (RationalAction.fromSoftmax utility α).policy s a = softmax (α • utility s) a := by
  simp only [policy, fromSoftmax, totalScore, softmax, Pi.smul_apply, smul_eq_mul]
  have hne : ∑ j : A, exp (α * utility s j) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty)
  simp only [hne, ↓reduceIte]


/-! ### Uniqueness of the ratio scale

`policy_eq_of_proportional` (proved earlier) shows that proportional scores
yield the same policy. The converse — that identical policies force proportional
scores — completes the uniqueness characterization: **same policy ↔ proportional
scores**, with proportionality constant `k = totalScore₂/totalScore₁`.

This is distinct from the independence-of-unit condition, which concerns
state-dependent transformations `f` satisfying `f(kv) = kf(v)` — how scale values
transform across experimental conditions, not the uniqueness of the scale within
a condition.
-/

section UniquenessCharacterization

variable {S A : Type*} [Fintype A]

/-- Converse direction (uniqueness of ratio scale):
    If two agents with positive total scores have the same policy,
    then their scores are proportional with constant `k = total₂/total₁`. -/
theorem RationalAction.proportional_of_policy_eq
    (ra₁ ra₂ : RationalAction S A) (s : S)
    (h₁ : 0 < ra₁.totalScore s)
    (h₂ : 0 < ra₂.totalScore s)
    (hpol : ∀ a, ra₁.policy s a = ra₂.policy s a) :
    ∀ a, ra₂.score s a =
      (ra₂.totalScore s / ra₁.totalScore s) * ra₁.score s a := by
  intro a
  have h₁_ne : ra₁.totalScore s ≠ 0 := ne_of_gt h₁
  have h₂_ne : ra₂.totalScore s ≠ 0 := ne_of_gt h₂
  have h := hpol a
  simp only [policy, h₁_ne, h₂_ne, ↓reduceIte] at h
  rw [div_eq_div_iff h₁_ne h₂_ne] at h
  field_simp [h₁_ne]
  linarith

/-- Full uniqueness characterization:
    Two agents with positive total scores have the same policy if and only if
    their scores are proportional. -/
theorem RationalAction.policy_eq_iff_proportional
    (ra₁ ra₂ : RationalAction S A) (s : S)
    (h₁ : 0 < ra₁.totalScore s)
    (h₂ : 0 < ra₂.totalScore s) :
    (∀ a, ra₁.policy s a = ra₂.policy s a) ↔
    ∃ k : ℝ, 0 < k ∧ ∀ a, ra₂.score s a = k * ra₁.score s a := by
  constructor
  · intro hpol
    exact ⟨ra₂.totalScore s / ra₁.totalScore s,
           div_pos h₂ h₁,
           proportional_of_policy_eq ra₁ ra₂ s h₁ h₂ hpol⟩
  · intro ⟨k, hk, hprop⟩ a
    exact (policy_eq_of_proportional ra₁ ra₂ s k hk hprop a).symm

end UniquenessCharacterization

/-! ### The pairwise choice kernel

`pairwiseProb v x y = v x / (v x + v y)` is the binary Luce rule — the
Bradley–Terry kernel. Hypotheses are pointwise (`0 < v x`) so the suite
applies to locally positive scales such as `cf.prob T` produced by
`ChoiceFn.HasChoiceAxiom.ratioScaleOn` below. On an exponential scale the
kernel is the logistic of the utility difference (`pairwiseProb_exp`) —
[luce-1959]'s Fechnerian coordinates `u = log v` (Ch. 2, §2.A.2). -/

section PairwiseProb

variable {A : Type*} {v : A → ℝ} {x y z : A}

/-- The pairwise choice probability `P(x, {x,y})` under a ratio scale `v`:
    `P(x, y) = v(x) / (v(x) + v(y))` — the Luce model prediction for binary
    forced choice. -/
noncomputable def pairwiseProb (v : A → ℝ) (x y : A) : ℝ :=
  v x / (v x + v y)

/-- Pairwise probabilities are non-negative for non-negative scales. -/
theorem pairwiseProb_nonneg (hx : 0 ≤ v x) (hy : 0 ≤ v y) :
    0 ≤ pairwiseProb v x y :=
  div_nonneg hx (add_nonneg hx hy)

/-- Pairwise probabilities are at most 1 for positive scales. -/
theorem pairwiseProb_le_one (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y ≤ 1 := by
  simp only [pairwiseProb]
  rw [div_le_one (add_pos hx hy)]
  linarith

/-- Complementarity: `P(x, y) + P(y, x) = 1` for positive scales. -/
theorem pairwiseProb_complement (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y + pairwiseProb v y x = 1 := by
  simp only [pairwiseProb]
  rw [show v y + v x = v x + v y from by ring, ← add_div,
      div_self (ne_of_gt (add_pos hx hy))]

/-- `P(x, x) = 1/2` for positive scales (indifference with self). -/
theorem pairwiseProb_self (hx : 0 < v x) : pairwiseProb v x x = 1 / 2 := by
  simp only [pairwiseProb]
  rw [div_eq_iff (by linarith : v x + v x ≠ 0)]
  ring

/-- `P(x, y) > 1/2` iff `v(x) > v(y)`: the higher-scale alternative is
    chosen more than half the time. -/
theorem pairwiseProb_gt_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    1 / 2 < pairwiseProb v x y ↔ v y < v x := by
  simp only [pairwiseProb]
  rw [lt_div_iff₀ (add_pos hx hy)]
  constructor <;> intro h <;> nlinarith

/-- `P(x, y) ≥ 1/2` iff `v(x) ≥ v(y)`. -/
theorem pairwiseProb_ge_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    1 / 2 ≤ pairwiseProb v x y ↔ v y ≤ v x := by
  simp only [pairwiseProb]
  rw [le_div_iff₀ (add_pos hx hy)]
  constructor <;> intro h <;> nlinarith

/-- `P(x, y) < 1/2` iff `v(x) < v(y)`. -/
theorem pairwiseProb_lt_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y < 1 / 2 ↔ v x < v y := by
  simp only [pairwiseProb]
  rw [div_lt_iff₀ (add_pos hx hy)]
  constructor <;> intro h <;> nlinarith

/-- `P(x, y) = 1/2` iff `v(x) = v(y)`. -/
theorem pairwiseProb_eq_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y = 1 / 2 ↔ v x = v y := by
  simp only [pairwiseProb]
  rw [div_eq_iff (ne_of_gt (add_pos hx hy))]
  constructor <;> intro h <;> linarith

/-- Monotonicity: `P(x, z) ≥ P(y, z)` iff `v(x) ≥ v(y)`.

    The function `t ↦ t/(t+c)` is monotone increasing for `c > 0`,
    so the ordering of pairwise probabilities against any fixed `z`
    mirrors the ordering of scale values. -/
theorem pairwiseProb_mono_iff (hx : 0 < v x) (hy : 0 < v y) (hz : 0 < v z) :
    pairwiseProb v y z ≤ pairwiseProb v x z ↔ v y ≤ v x := by
  simp only [pairwiseProb]
  rw [div_le_div_iff₀ (add_pos hy hz) (add_pos hx hz)]
  constructor <;> intro h <;> nlinarith

/-- Constant-ratio law: two pairwise probabilities on the same scale agree
    iff the cross products of their scale values do. -/
theorem pairwiseProb_eq_pairwiseProb_iff {x' y' : A} (hx : 0 < v x)
    (hy : 0 < v y) (hx' : 0 < v x') (hy' : 0 < v y') :
    pairwiseProb v x y = pairwiseProb v x' y' ↔ v x * v y' = v x' * v y := by
  simp only [pairwiseProb]
  rw [div_eq_div_iff (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- Fechnerian coordinates ([luce-1959] Ch. 2, §2.A.2, `u = log v`): on an
    exponential scale the pairwise rule is the logistic of the utility
    difference — the bridge from the Luce choice rule to logit choice. -/
theorem pairwiseProb_exp (u : A → ℝ) (x y : A) :
    pairwiseProb (λ a => Real.exp (u a)) x y = Real.sigmoid (u x - u y) := by
  have hx := Real.exp_pos (u x)
  have hy := Real.exp_pos (u y)
  simp only [pairwiseProb, Real.sigmoid, neg_sub, Real.exp_sub]
  rw [inv_eq_one_div, div_eq_div_iff (by positivity) (by positivity)]
  field_simp

end PairwiseProb

/-! ### Alternative forms of the choice axiom

[luce-1959] proves three equivalent formulations of the choice axiom:

**(a) Ratio form**: There exists a positive function `v` such that
`P(x, T) = v(x) / Σ_{y∈T} v(y)` for all `x ∈ T`.

**(b) Product rule**: `P(x, T) = P(x, S) · P(S, T)` for `x ∈ S ⊆ T`,
where `P(S, T) = Σ_{y∈S} P(y, T)`.

**(c) Pairwise independence**: The odds ratio `P(x,{x,y}) · P(y,T) =
P(y,{x,y}) · P(x,T)` — pairwise ratios are preserved in any superset.

The ratio form (a) is the definition of `RationalAction`; (a)→(b) is
`product_rule` and (a)→(c) is `pChoice_ratio`.

All three describe the globally imperfect regime. Luce's Axiom 1 itself is
two-clause and weaker: `ChoiceFn.HasChoiceAxiom` below states it in full,
and `ChoiceFn.HasChoiceAxiom.ratioScaleOn` is the existence half of his
Theorem 3 (local ratio scales on imperfectly discriminated menus).
-/

section Appendix1

variable {A : Type*} [DecidableEq A]

/-- A choice function on finite subsets — the canonical [luce-1959] form.
    For each non-empty subset `T ⊆ A`, `prob T : A → ℝ` is a probability
    distribution: non-negative, vanishing outside `T`, summing to 1 inside. The
    Luce-axiom forms (`hasRatioScale`, `hasProductRule`, `hasPairwiseIIA`) are
    stated as predicates below. -/
structure ChoiceFn (A : Type*) [DecidableEq A] where
  /-- P(a, T): probability of choosing `a` from set `T` -/
  prob : Finset A → A → ℝ
  /-- Probabilities are non-negative -/
  prob_nonneg : ∀ (T : Finset A) (a : A), 0 ≤ prob T a
  /-- Zero probability outside the choice set -/
  prob_zero_outside : ∀ (T : Finset A) (a : A), a ∉ T → prob T a = 0
  /-- Probabilities sum to 1 within the choice set ([luce-1959]) -/
  prob_sum_eq_one : ∀ (T : Finset A), T.Nonempty → ∑ a ∈ T, prob T a = 1

namespace ChoiceFn

variable {A : Type*} [DecidableEq A]

/-- **Binary choice view**: `binary cf x y` is the probability of choosing `x`
    over `y` in the binary forced choice between them, defined via
    `cf.prob {x, y} x`. -/
def binary (cf : ChoiceFn A) (x y : A) : ℝ := cf.prob {x, y} x

/-- Binary choice probabilities are non-negative. -/
theorem binary_nonneg (cf : ChoiceFn A) (x y : A) : 0 ≤ cf.binary x y :=
  cf.prob_nonneg _ _

/-- Binary choice probabilities are at most 1. -/
theorem binary_le_one (cf : ChoiceFn A) (x y : A) : cf.binary x y ≤ 1 := by
  -- prob {x,y} x ≤ ∑ a ∈ {x,y}, prob {x,y} a = 1 (by sum_eq_one)
  have hxy : x ∈ ({x, y} : Finset A) := Finset.mem_insert_self x _
  have hpos : ∀ a ∈ ({x, y} : Finset A), 0 ≤ cf.prob {x, y} a :=
    fun a _ => cf.prob_nonneg _ _
  have hsum := cf.prob_sum_eq_one {x, y} ⟨x, hxy⟩
  calc cf.binary x y = cf.prob {x, y} x := rfl
    _ ≤ ∑ a ∈ ({x, y} : Finset A), cf.prob {x, y} a :=
        Finset.single_le_sum hpos hxy
    _ = 1 := hsum

/-- **Binary complementarity**: `cf.binary x y + cf.binary y x = 1`
    when `x ≠ y`. Derived from `prob_sum_eq_one` over `{x, y}`. -/
theorem binary_complement (cf : ChoiceFn A) {x y : A} (hxy : x ≠ y) :
    cf.binary x y + cf.binary y x = 1 := by
  -- {y, x} = {x, y} by pair commutativity
  have hcomm : ({y, x} : Finset A) = ({x, y} : Finset A) := Finset.pair_comm y x
  show cf.prob {x, y} x + cf.prob {y, x} y = 1
  rw [hcomm]
  -- Now sums-to-1 over {x, y}
  have hxset : x ∈ ({x, y} : Finset A) := Finset.mem_insert_self x _
  have hsum := cf.prob_sum_eq_one {x, y} ⟨x, hxset⟩
  rw [show ({x, y} : Finset A) = insert x {y} from rfl,
      Finset.sum_insert (by simp; exact hxy),
      Finset.sum_singleton] at hsum
  exact hsum

/-- Self-choice is certain: `cf.binary x x = 1`, since `{x, x} = {x}` and
    probabilities sum to 1 on the singleton. -/
theorem binary_self (cf : ChoiceFn A) (x : A) : cf.binary x x = 1 := by
  have h := cf.prob_sum_eq_one {x} ⟨x, Finset.mem_singleton_self x⟩
  simpa [binary] using h

end ChoiceFn

/-- **Axiom 1, Form (a)**: ratio scale representation.
    There exists `v > 0` such that `P(x, T) = v(x) / Σ v(y)`. -/
def ChoiceFn.hasRatioScale (cf : ChoiceFn A) : Prop :=
  ∃ v : A → ℝ, (∀ a, 0 < v a) ∧
    ∀ (T : Finset A) (a : A), a ∈ T →
      cf.prob T a = v a / ∑ b ∈ T, v b

/-- **Axiom 1, Form (b)**: product rule.
    `P(x, T) = P(x, S) · Σ_{y∈S} P(y, T)` for `x ∈ S ⊆ T`. -/
def ChoiceFn.hasProductRule (cf : ChoiceFn A) : Prop :=
  ∀ (S T : Finset A), S ⊆ T → S.Nonempty →
    (∑ b ∈ T, cf.prob T b = 1) →
    ∀ a ∈ S,
      cf.prob T a = cf.prob S a * ∑ b ∈ S, cf.prob T b

/-- **Axiom 1, Form (c)**: pairwise independence (IIA).
    The odds ratio is preserved in any superset:
    `P(x,T) · P(y,{x,y}) = P(y,T) · P(x,{x,y})`. -/
def ChoiceFn.hasPairwiseIIA (cf : ChoiceFn A) : Prop :=
  ∀ (T : Finset A) (a b : A), a ∈ T → b ∈ T →
    cf.prob T a * cf.prob {a, b} b = cf.prob T b * cf.prob {a, b} a

/-- (a) → (b): the ratio form implies the product rule. -/
theorem ratio_implies_product (cf : ChoiceFn A)
    (h : cf.hasRatioScale) : cf.hasProductRule := by
  intro S T hST hS _hT a ha
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  rw [hv_rule T a (hST ha), hv_rule S a ha]
  have hS_ne : (∑ b ∈ S, v b) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (λ b _ => hv_pos b) hS)
  have hT_ne : (∑ b ∈ T, v b) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (λ b _ => hv_pos b) (Finset.Nonempty.mono hST hS))
  have hsum : ∑ b ∈ S, cf.prob T b = (∑ b ∈ S, v b) / ∑ c ∈ T, v c := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (λ b hb => hv_rule T b (hST hb))
  rw [hsum]; field_simp

/-- (a) → (c): the ratio form implies pairwise IIA. -/
theorem ratio_implies_pairwiseIIA (cf : ChoiceFn A)
    (h : cf.hasRatioScale) : cf.hasPairwiseIIA := by
  intro T a b ha hb
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  have hab_a : a ∈ ({a, b} : Finset A) := Finset.mem_insert.mpr (Or.inl rfl)
  have hab_b : b ∈ ({a, b} : Finset A) := by simp
  rw [hv_rule T a ha, hv_rule T b hb,
      hv_rule {a, b} b hab_b, hv_rule {a, b} a hab_a]
  ring

/-- (c) → (a): pairwise IIA implies the ratio form. The ratio scale is
    constructed by fixing a reference element `x₀` and setting
    `v(x) = P(x, {x, x₀}) / P(x₀, {x, x₀})` (requires strict positivity on the
    choice set). -/
theorem pairwiseIIA_implies_ratio [Inhabited A] (cf : ChoiceFn A)
    (hIIA : cf.hasPairwiseIIA)
    (hpos : ∀ (T : Finset A) (a : A), a ∈ T → 0 < cf.prob T a) :
    cf.hasRatioScale := by
  have hsum := cf.prob_sum_eq_one
  set x₀ := (default : A)
  set v := fun a => cf.prob {a, x₀} a / cf.prob {a, x₀} x₀ with hv_def
  have hv_pos : ∀ a, 0 < v a := fun a =>
    div_pos (hpos _ a (mem_insert.mpr (Or.inl rfl))) (hpos _ x₀ (by simp))
  have ratio_mul : ∀ (T : Finset A) (a b : A), a ∈ T → b ∈ T →
      cf.prob T a * cf.prob {b, x₀} b * cf.prob {a, x₀} x₀ =
      cf.prob T b * cf.prob {a, x₀} a * cf.prob {b, x₀} x₀ := by
    intro T a b ha hb
    set T' := insert x₀ T
    have ha' : a ∈ T' := mem_insert_of_mem ha
    have hb' : b ∈ T' := mem_insert_of_mem hb
    have hx₀' : x₀ ∈ T' := mem_insert_self x₀ T
    have hT := hIIA T a b ha hb
    have hT'ab := hIIA T' a b ha' hb'
    have hT'ax₀ := hIIA T' a x₀ ha' hx₀'
    have hT'bx₀ := hIIA T' b x₀ hb' hx₀'
    have hB : cf.prob T' a * cf.prob {a, x₀} x₀ * cf.prob {b, x₀} b =
              cf.prob T' b * cf.prob {b, x₀} x₀ * cf.prob {a, x₀} a := by
      linear_combination cf.prob {b, x₀} b * hT'ax₀ - cf.prob {a, x₀} a * hT'bx₀
    have hA_mul : (cf.prob T a * cf.prob T' b - cf.prob T b * cf.prob T' a) *
                  cf.prob {a, b} b = 0 := by
      linear_combination cf.prob T' b * hT - cf.prob T b * hT'ab
    have hA : cf.prob T a * cf.prob T' b = cf.prob T b * cf.prob T' a := by
      rcases mul_eq_zero.mp hA_mul with h | h
      · linarith
      · exact absurd h (ne_of_gt (hpos _ b (by simp)))
    have hT'b_ne : cf.prob T' b ≠ 0 := ne_of_gt (hpos T' b hb')
    have h1 : cf.prob T' b * (cf.prob T a * cf.prob {b, x₀} b * cf.prob {a, x₀} x₀) =
              cf.prob T' b * (cf.prob T b * cf.prob {a, x₀} a * cf.prob {b, x₀} x₀) := by
      linear_combination cf.prob {b, x₀} b * cf.prob {a, x₀} x₀ * hA + cf.prob T b * hB
    exact mul_left_cancel₀ hT'b_ne h1
  refine ⟨v, hv_pos, fun T a ha => ?_⟩
  have hT_ne : T.Nonempty := ⟨a, ha⟩
  have hsum_v_pos : 0 < ∑ b ∈ T, v b :=
    Finset.sum_pos (fun b _ => hv_pos b) hT_ne
  rw [eq_div_iff (ne_of_gt hsum_v_pos)]
  have swap : ∀ b ∈ T, cf.prob T a * v b = v a * cf.prob T b := by
    intro b hb
    simp only [hv_def]
    have hrm := ratio_mul T a b ha hb
    have hne_a : cf.prob {a, x₀} x₀ ≠ 0 := ne_of_gt (hpos _ x₀ (by simp))
    have hne_b : cf.prob {b, x₀} x₀ ≠ 0 := ne_of_gt (hpos _ x₀ (by simp))
    field_simp
    linarith
  calc cf.prob T a * ∑ b ∈ T, v b
      = ∑ b ∈ T, cf.prob T a * v b := mul_sum T v (cf.prob T a)
    _ = ∑ b ∈ T, v a * cf.prob T b := sum_congr rfl swap
    _ = v a * ∑ b ∈ T, cf.prob T b := (mul_sum T (cf.prob T) (v a)).symm
    _ = v a * 1 := by rw [hsum T hT_ne]
    _ = v a := mul_one _

/-- **Axiom 1 equivalence**: the ratio form ↔ pairwise IIA, under strict
    positivity on each choice set. -/
theorem axiom1_ratio_iff_pairwiseIIA [Inhabited A] (cf : ChoiceFn A)
    (hpos : ∀ (T : Finset A) (a : A), a ∈ T → 0 < cf.prob T a) :
    cf.hasRatioScale ↔ cf.hasPairwiseIIA :=
  ⟨ratio_implies_pairwiseIIA cf, fun h => pairwiseIIA_implies_ratio cf h hpos⟩

/-- A positive binary ratio scale on a set `S`: binary choice between distinct
    elements of `S` follows the Luce rule `P(x, y) = v x / (v x + v y)`.

    This is the binary trace of `hasRatioScale` restricted to `S`
    (`ChoiceFn.hasRatioScale.binaryRatioScaleOn`). Keeping `S` local matters for
    [luce-1959]'s Chapter 3, which mixes imperfect discrimination (a ratio scale
    on a small set of gambles, via Theorem 4) with perfect discrimination
    (`P ∈ {0, 1}`) elsewhere — a global positive scale forces every binary
    probability into `(0, 1)`. Restricting to distinct pairs matters because
    `binary x x = 1 ≠ 1/2` (`ChoiceFn.binary_self`). -/
def ChoiceFn.BinaryRatioScaleOn (cf : ChoiceFn A) (S : Set A) (v : A → ℝ) : Prop :=
  (∀ x ∈ S, 0 < v x) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → cf.binary x y = pairwiseProb v x y

/-- A global ratio scale restricts to a binary ratio scale on every set. -/
theorem ChoiceFn.hasRatioScale.binaryRatioScaleOn {cf : ChoiceFn A}
    (h : cf.hasRatioScale) : ∃ v : A → ℝ, ∀ S : Set A, cf.BinaryRatioScaleOn S v := by
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  refine ⟨v, fun S => ⟨fun x _ => hv_pos x, fun x _ y _ hxy => ?_⟩⟩
  rw [ChoiceFn.binary, hv_rule {x, y} x (Finset.mem_insert_self x _),
      Finset.sum_pair hxy, pairwiseProb]

/-! ### The choice axiom in full -/

/-- Discrimination is imperfect throughout `T`: `0 < P(x, y) < 1` for distinct
    `x, y ∈ T` ([luce-1959]'s "`P(x, y) ≠ 0, 1` for all `x, y ∈ T`"). The
    diagonal is excluded because [luce-1959] (p. 5) sets `P(x, x) = ½` by pure
    notational convention, whereas a total `ChoiceFn` has `binary x x = 1`
    (`ChoiceFn.binary_self`). -/
def ChoiceFn.ImperfectOn (cf : ChoiceFn A) (T : Finset A) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 0 < cf.binary x y ∧ cf.binary x y < 1

/-- **Luce's choice axiom**, both clauses (Axiom 1, p. 6 of [luce-1959], with
    `P_T(S) = ∑_{a ∈ S} P_T(a)`):

    (i) `product_rule`: under imperfect discrimination throughout `T`,
    nested-menu probabilities compose multiplicatively —
    `P_T(R) = P_S(R) · P_T(S)` for `R ⊆ S ⊆ T`;

    (ii) `deletion`: an alternative `x` never chosen over some `y` may be
    deleted — `P_T(S) = P_{T∖{x}}(S∖{x})` for every `S ⊆ T`.

    Unlike the globally positive `hasRatioScale`, clause (ii) lets the axiom
    govern menus mixing perfect and imperfect discrimination — the regime of
    [luce-1959] Chapter 3, where the three-class theorems force `Q ∈ {0, 1}`
    between extreme event classes. -/
structure ChoiceFn.HasChoiceAxiom (cf : ChoiceFn A) : Prop where
  product_rule : ∀ T : Finset A, cf.ImperfectOn T → ∀ R S : Finset A,
    R ⊆ S → S ⊆ T →
    ∑ a ∈ R, cf.prob T a = (∑ a ∈ R, cf.prob S a) * ∑ a ∈ S, cf.prob T a
  deletion : ∀ T : Finset A, ∀ x ∈ T, ∀ y ∈ T, x ≠ y → cf.binary x y = 0 →
    ∀ S ⊆ T, ∑ a ∈ S, cf.prob T a = ∑ a ∈ S.erase x, cf.prob (T.erase x) a

/-- A global ratio scale satisfies the full choice axiom: clause (i) by ratio
    arithmetic, clause (ii) vacuously (no discrimination is perfect). -/
theorem ChoiceFn.hasRatioScale.hasChoiceAxiom {cf : ChoiceFn A}
    (h : cf.hasRatioScale) : cf.HasChoiceAxiom := by
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  constructor
  · intro T _ R S hRS hST
    rcases R.eq_empty_or_nonempty with rfl | hR
    · simp
    have hS : S.Nonempty := hR.mono hRS
    have hSne : (∑ b ∈ S, v b) ≠ 0 :=
      ne_of_gt (Finset.sum_pos (fun b _ => hv_pos b) hS)
    have hTne : (∑ b ∈ T, v b) ≠ 0 :=
      ne_of_gt (Finset.sum_pos (fun b _ => hv_pos b) (hS.mono hST))
    have eT : ∀ W : Finset A, W ⊆ T →
        ∑ a ∈ W, cf.prob T a = (∑ a ∈ W, v a) / ∑ b ∈ T, v b := by
      intro W hW
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a ha => hv_rule T a (hW ha)
    have eS : ∑ a ∈ R, cf.prob S a = (∑ a ∈ R, v a) / ∑ b ∈ S, v b := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a ha => hv_rule S a (hRS ha)
    rw [eT R (hRS.trans hST), eT S hST, eS]
    field_simp
  · intro T x hx y hy hxy h0 S hS
    have hb : cf.binary x y = v x / (v x + v y) := by
      rw [ChoiceFn.binary, hv_rule {x, y} x (Finset.mem_insert_self x _),
          Finset.sum_pair hxy]
    rw [hb] at h0
    exact absurd h0
      (ne_of_gt (div_pos (hv_pos x) (add_pos (hv_pos x) (hv_pos y))))

/-- Existence half of **Theorem 3** of [luce-1959] (p. 23): under the choice
    axiom, on any finite `T` with imperfect discrimination throughout, the
    restricted choice probabilities are a ratio scale — with `v = P_T` itself
    as the scale, Luce's own construction. (The uniqueness half — `v` unique
    up to a positive multiple — is not formalized.) -/
theorem ChoiceFn.HasChoiceAxiom.ratioScaleOn {cf : ChoiceFn A}
    (h : cf.HasChoiceAxiom) {T : Finset A} (hT : T.Nonempty)
    (himp : cf.ImperfectOn T) :
    ∃ v : A → ℝ, (∀ x ∈ T, 0 < v x) ∧
      ∀ S ⊆ T, ∀ a ∈ S, cf.prob S a = v a / ∑ b ∈ S, v b := by
  have hpos : ∀ x ∈ T, 0 < cf.prob T x := by
    intro x hx
    rcases lt_or_eq_of_le (cf.prob_nonneg T x) with hlt | heq
    · exact hlt
    -- a zero propagates to every element of T, contradicting the unit sum
    have hall : ∀ y ∈ T, cf.prob T y = 0 := by
      intro y hy
      rcases eq_or_ne y x with rfl | hyx
      · exact heq.symm
      have hsub : ({x, y} : Finset A) ⊆ T :=
        Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
      have hprod := h.product_rule T himp {x} {x, y} (by simp) hsub
      rw [Finset.sum_singleton, Finset.sum_singleton,
          Finset.sum_pair (Ne.symm hyx)] at hprod
      have hbin : 0 < cf.prob {x, y} x := (himp x hx y hy (Ne.symm hyx)).1
      have h0 : cf.prob {x, y} x * cf.prob T y = 0 := by
        rw [← heq] at hprod
        linarith [hprod]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (ne_of_gt hbin)
      · exact h'
    have hsum := cf.prob_sum_eq_one T hT
    rw [Finset.sum_eq_zero hall] at hsum
    exact absurd hsum (by norm_num)
  refine ⟨cf.prob T, hpos, fun S hS a ha => ?_⟩
  have hSpos : (0 : ℝ) < ∑ b ∈ S, cf.prob T b :=
    Finset.sum_pos (fun b hb => hpos b (hS hb)) ⟨a, ha⟩
  have hprod := h.product_rule T himp {a} S (Finset.singleton_subset_iff.mpr ha) hS
  rw [Finset.sum_singleton, Finset.sum_singleton] at hprod
  rw [eq_div_iff (ne_of_gt hSpos)]
  linarith [hprod]

/-- Binary form of Theorem 3: the choice axiom plus imperfect discrimination
    on `T` yield a binary ratio scale on `T`. -/
theorem ChoiceFn.HasChoiceAxiom.binaryRatioScaleOn {cf : ChoiceFn A}
    (h : cf.HasChoiceAxiom) {T : Finset A} (hT : T.Nonempty)
    (himp : cf.ImperfectOn T) :
    ∃ v : A → ℝ, cf.BinaryRatioScaleOn ↑T v := by
  obtain ⟨v, hvpos, hrule⟩ := h.ratioScaleOn hT himp
  refine ⟨v, fun x hx => hvpos x (Finset.mem_coe.mp hx),
    fun x hx y hy hxy => ?_⟩
  have hsub : ({x, y} : Finset A) ⊆ T :=
    Finset.insert_subset (Finset.mem_coe.mp hx)
      (Finset.singleton_subset_iff.mpr (Finset.mem_coe.mp hy))
  rw [ChoiceFn.binary, hrule {x, y} hsub x (Finset.mem_insert_self x _),
      Finset.sum_pair hxy, pairwiseProb]

end Appendix1


end Core
