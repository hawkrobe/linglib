import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Mul

/-!
# Rational Action @cite{luce-1959}
@cite{cover-thomas-2006} @cite{zaslavsky-hu-levy-2020} @cite{adams-messick-1958}The mathematical foundation for all soft-rational agents: RSA speakers/listeners,
BToM agents, and decision-theoretic actors.

## Architecture

A `RationalAction` agent selects actions with probability proportional to a
non-negative score function — the **Luce choice rule**. This is the
unique choice rule satisfying IIA (independence of irrelevant alternatives):
the relative probability of two actions depends only on their scores.

The key mathematical results characterizing this choice rule are:

1. **Softmax** (§2): The exponential parameterization `score = exp(α · utility)`
   gives `policy = softmax(utility, α)`. This is the standard form in RSA.

2. **Gibbs Variational Principle** (§3): Softmax uniquely maximizes
   `H(p) + α · ⟨p, s⟩` on the probability simplex. This is the mathematical
   foundation for RSA convergence.

3. **Maximum Entropy** (§4): Softmax is the max-entropy distribution subject
   to an expected-utility constraint. Equivalently, it minimizes free energy
   (the Boltzmann distribution from statistical mechanics).

4. **Bayesian Optimality** (§5): The Bayesian posterior maximizes expected
   log-likelihood. This is the listener half of RSA convergence.

-/

namespace Core

open Real BigOperators Finset

-- ============================================================================
-- §1. RationalAction: Score-Based Agents
-- ============================================================================

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

/-- When totalScore equals the score of action `a`, the policy for `a` is 1.
    Used by the compositional proof builder when all other scores are zero,
    so `totalScore = score a + 0 +... + 0 = score a`, making `policy = 1`. -/
theorem RationalAction.policy_eq_one_of_totalScore_eq (ra : RationalAction S A) (s : S)
    (a : A) (h_sum : ra.totalScore s = ra.score s a) (h_pos : 0 < ra.score s a) :
    ra.policy s a = 1 := by
  simp only [policy, h_sum, ne_of_gt h_pos, ↓reduceIte, div_self (ne_of_gt h_pos)]

/-- Score ordering implies ¬(policy strict ordering). Used by compositional proof
    builder for ¬(L1 w₁ < L1 w₂) goals. -/
theorem RationalAction.policy_not_lt_of_score_le (ra : RationalAction S A) (s : S)
    (a₁ a₂ : A) (h : ra.score s a₂ ≤ ra.score s a₁) :
    ¬(ra.policy s a₁ < ra.policy s a₂) :=
  not_lt_of_ge (ra.policy_monotone s a₂ a₁ h)

/-- Strict policy monotonicity: strictly higher score → strictly higher probability.

    Used by `rsa_decide` to eliminate shared denominator computations: when
    comparing `policy s a₁ < policy s a₂` (same state), it suffices to show
    `score s a₁ < score s a₂`, skipping the expensive `totalScore` computation
    in the proof term. -/
@[gcongr]
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
    by_contra hle; push_neg at hle
    exact absurd h (not_lt.mpr (ra.policy_monotone s a₂ a₁ hle)),
   ra.policy_lt_of_score_lt s a₁ a₂⟩

/-- Cross-state policy comparison: compares policy values at different states
    (different denominators). Used for S2 cross-world comparisons where
    S2(u|w₁) vs S2(u|w₂) have different normalization constants.

    The cross-product condition `score(s₁,a) * total(s₂) < score(s₂,a) * total(s₁)`
    is equivalent to `score(s₁,a)/total(s₁) < score(s₂,a)/total(s₂)` when both
    totals are positive. -/
theorem RationalAction.policy_lt_cross (ra : RationalAction S A) (s₁ s₂ : S) (a : A)
    (h_pos₁ : 0 < ra.totalScore s₁) (h_pos₂ : 0 < ra.totalScore s₂)
    (h_cross : ra.score s₁ a * ra.totalScore s₂ < ra.score s₂ a * ra.totalScore s₁) :
    ra.policy s₁ a < ra.policy s₂ a := by
  simp only [policy, ne_of_gt h_pos₁, ne_of_gt h_pos₂, ↓reduceIte]
  exact (div_lt_div_iff₀ h_pos₁ h_pos₂).mpr h_cross

/-- Cross-state policy comparison with positivity derived from the cross-product.

    Like `policy_lt_cross` but derives the `totalScore > 0` conditions from the
    cross-product inequality itself: if `0 ≤ score(s₁,a) * total(s₂) < score(s₂,a) * total(s₁)`,
    then `score(s₂,a) * total(s₁) > 0`, so both `score(s₂,a) > 0` and `total(s₁) > 0`.
    And `score(s₂,a) ≤ total(s₂)`, so `total(s₂) > 0`.

    Used by `rsa_predict` for cross-utterance L1 comparisons where the two sides
    have different normalization constants. -/
@[gcongr]
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
    state (same denominator). Used by `rsa_predict` for marginal L1 comparisons
    where the worlds being summed differ but the utterance and config are shared. -/
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
    same state (same denominator). Like `policy_list_sum_lt` but for Finset.sum.

    Derives totalScore positivity from the score ordering itself, so no extra
    hypothesis is needed: if 0 ≤ Σ_{F₁} score < Σ_{F₂} score, then some score
    is positive, so totalScore > 0.

    Used by `rsa_predict` for denominator cancellation in marginal comparisons. -/
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

-- ============================================================================
-- §1a. Luce's Choice Axiom (IIA)
-- ============================================================================

/-!
## Luce's Choice Axiom

showed that the ratio rule `P(a|s) = v(a)/Σv(b)` is
characterized by the **independence of irrelevant alternatives** (IIA): the
relative probability of two actions depends only on their scores, not on what
other actions are available.

We formalize:
- The **constant ratio rule** (Theorem 2): `policy(a₁) · score(a₂) = policy(a₂) · score(a₁)`
- **Choice from subsets** (`pChoice`): restriction of the choice rule to a `Finset`
- **IIA** (Axiom 1): ratios in any subset equal score ratios
- The **product rule** (Theorem 1): `P(a,T) = P(a,S) · P(S,T)` for `S ⊆ T`
- **Scale invariance** (Theorem 5): multiplying all scores by `k > 0` preserves policy
- **Uniqueness** (Theorem 4, forward): proportional scores yield the same policy
-/

section LuceChoiceAxiom

variable {S A : Type*} [Fintype A]

/-- Constant Ratio Rule (Theorem 2):
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
    `pChoice(a₁, T) · score(a₂) = pChoice(a₂, T) · score(a₁)` (Axiom 1). -/
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

/-- IIA (Axiom 1): `P(a, S) = P(a, T) / Σ_{b∈S} P(b, T)` for `S ⊆ T`.
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

/-- Product rule (Theorem 1):
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

/-- Scale invariance (Theorem 5): scaling scores by `k > 0` preserves policy. -/
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

/-- Uniqueness (forward direction, Theorem 4):
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

-- ============================================================================
-- §2. Softmax Function
-- ============================================================================

/-!
## Softmax Function

The softmax function `σ(s, α)ᵢ = exp(α · sᵢ) / Σⱼ exp(α · sⱼ)` is the
exponential parameterization of the Luce choice rule. Following Franke & Degen
(submitted), we establish Facts 1–8.
-/

/-- The softmax function: softmax(s, α)ᵢ = exp(α · sᵢ) / Σⱼ exp(α · sⱼ). -/
noncomputable def softmax {ι : Type*} [Fintype ι] (s : ι → ℝ) (α : ℝ) : ι → ℝ :=
  λ i => exp (α * s i) / ∑ j : ι, exp (α * s j)

/-- The partition function (normalizing constant) Z = Σⱼ exp(α · sⱼ). -/
noncomputable def partitionFn {ι : Type*} [Fintype ι] (s : ι → ℝ) (α : ℝ) : ℝ :=
  ∑ j : ι, exp (α * s j)

/-- Log-sum-exp: log of partition function. -/
noncomputable def logSumExp {ι : Type*} [Fintype ι] (s : ι → ℝ) (α : ℝ) : ℝ :=
  log (∑ j : ι, exp (α * s j))

section SoftmaxBasic

variable {ι : Type*} [Fintype ι]

/-- The partition function is always positive. -/
theorem partitionFn_pos [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    0 < partitionFn s α := by
  apply Finset.sum_pos
  · intro i _; exact exp_pos _
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

/-- The logistic (sigmoid) function: `S(x) = 1 / (1 + exp(−x))`. -/
noncomputable def logistic (x : ℝ) : ℝ := 1 / (1 + exp (-x))

/-- The logit function: `L(p) = log(p / (1 − p))`.
    Inverse of `logistic` on (0, 1). -/
noncomputable def logit (p : ℝ) : ℝ := log (p / (1 - p))

/-- `logit` inverts `logistic`: `logit(logistic(x)) = x`. -/
theorem logit_logistic (x : ℝ) : logit (logistic x) = x := by
  simp only [logit, logistic]
  have hdenom_ne : (1 + exp (-x)) ≠ 0 := ne_of_gt (by linarith [exp_pos (-x)])
  have hexp_ne : exp (-x) ≠ 0 := ne_of_gt (exp_pos _)
  have key : 1 / (1 + exp (-x)) / (1 - 1 / (1 + exp (-x))) = exp x := by
    field_simp
    ring_nf
    rw [← Real.exp_add]; simp
  rw [key, Real.log_exp]

/-- `logistic` inverts `logit` for `0 < p < 1`: `logistic(logit(p)) = p`. -/
theorem logistic_logit {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    logistic (logit p) = p := by
  simp only [logistic, logit]
  have h1mp : 0 < 1 - p := by linarith
  have hfrac : 0 < p / (1 - p) := div_pos hp0 h1mp
  have hinv : 0 < (p / (1 - p))⁻¹ := inv_pos.mpr hfrac
  rw [show -Real.log (p / (1 - p)) = Real.log (p / (1 - p))⁻¹
    from (Real.log_inv _).symm]
  rw [Real.exp_log hinv]
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  field_simp
  linarith

/-- Fact 3: For n = 2, softmax reduces to logistic. -/
theorem softmax_binary (s : Fin 2 → ℝ) (α : ℝ) :
    softmax s α 0 = logistic (α * (s 0 - s 1)) := by
  simp only [softmax, logistic, Fin.sum_univ_two]
  have key : α * s 0 + (-(α * (s 0 - s 1))) = α * s 1 := by ring
  have h : exp (α * s 0) + exp (α * s 1) =
           exp (α * s 0) * (1 + exp (-(α * (s 0 - s 1)))) := by
    rw [mul_add, mul_one, ← exp_add, key]
  rw [h, ← div_div, div_self (ne_of_gt (exp_pos _))]

/-- Softmax log-odds equals `logit` of the binary softmax probability
    (when there are exactly two alternatives). -/
theorem logit_softmax_binary (s : Fin 2 → ℝ) (α : ℝ) :
    logit (softmax s α 0) = α * (s 0 - s 1) := by
  rw [softmax_binary, logit_logistic]

/-- Fact 6: Softmax is translation invariant. -/
theorem softmax_add_const (s : ι → ℝ) (α c : ℝ) :
    softmax (λ i => s i + c) α = softmax s α := by
  funext i
  simp only [softmax]
  have hexp : ∀ j, exp (α * (s j + c)) = exp (α * s j) * exp (α * c) := by
    intro j; rw [← exp_add]; ring_nf
  simp_rw [hexp, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (ne_of_gt (exp_pos _))]

/-- Fact 8: Multiplicative scaling can be absorbed into α. -/
theorem softmax_scale (s : ι → ℝ) (α a : ℝ) (ha : a ≠ 0) :
    softmax (λ i => a * s i) (α / a) = softmax s α := by
  funext i
  simp only [softmax]
  congr 1
  · congr 1; field_simp
  · apply Finset.sum_congr rfl; intro j _; congr 1; field_simp

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

/-- Log of softmax = score minus log partition function. -/
theorem log_softmax [Nonempty ι] (s : ι → ℝ) (α : ℝ) (i : ι) :
    Real.log (softmax s α i) = α * s i - Real.log (partitionFn s α) := by
  simp only [softmax, partitionFn]
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Finset.sum_pos
    (fun j _ => Real.exp_pos _) Finset.univ_nonempty))]
  rw [Real.log_exp]

/-- Softmax with default α = 1. -/
noncomputable def softmax1 (s : ι → ℝ) : ι → ℝ := softmax s 1

/-- Temperature form: τ = 1/α. -/
noncomputable def softmaxTemp (s : ι → ℝ) (τ : ℝ) : ι → ℝ :=
  softmax s (1 / τ)

/-- Softmax is an exponential family distribution. -/
theorem softmax_exponential_family (s : ι → ℝ) (α : ℝ) (i : ι) [Nonempty ι] :
    softmax s α i = exp (α * s i - logSumExp s α) := by
  simp only [softmax, logSumExp]
  rw [exp_sub]
  have h : exp (log (∑ j : ι, exp (α * s j))) = ∑ j : ι, exp (α * s j) :=
    exp_log (partitionFn_pos s α)
  rw [h]

/-- Luce choice with rpow scores equals softmax over log scores.

    f(i)^α / Σⱼ f(j)^α = softmax(log ∘ f, α)(i)  when all f(i) > 0.

    This is the general identity connecting belief-based RSA (which uses
    rpow) to the softmax framework (which uses exp). Every S1 model with
    `s1Score = rpow(l0, α)` inherits all softmax limit theorems via this
    identity: as α → ∞, rpow-based Luce choice concentrates on the
    argmax of f, i.e., the most informative utterance. -/
theorem rpow_luce_eq_softmax [Nonempty ι] (f : ι → ℝ) (α : ℝ)
    (hf : ∀ i, 0 < f i) (i : ι) :
    f i ^ α / ∑ j : ι, f j ^ α =
    softmax (fun j => log (f j)) α i := by
  simp only [softmax]
  congr 1
  · rw [rpow_def_of_pos (hf i), mul_comm]
  · apply Finset.sum_congr rfl
    intro j _
    rw [rpow_def_of_pos (hf j), mul_comm]

end SoftmaxBasic

-- ============================================================================
-- §2a. Fechnerian Characterization & Softmax Bridge
-- ============================================================================

/-!
## Why Softmax? The Fechnerian Characterization

The exponential parameterization `score = exp(α · utility)` is not a design
choice — it is the **unique** transformation connecting Luce's ratio scale to
a utility (interval) scale (§2.A; @cite{adams-messick-1958}).

**Ratio vs interval scales.** Luce's Axiom 1 (IIA) yields a **ratio scale**
`v`: only ratios `v(a)/v(b)` are meaningful (Theorem 4). Fechner's
psychophysics requires an **interval scale** `u`: only differences
`u(a) - u(b)` are meaningful. The question: how are `v` and `u` related?

**Derivation.** From `P(a,b) = v(a)/(v(a)+v(b))`, the odds ratio is
`v(a)/v(b) = g(u(a) - u(b))` for some function `g`. Transitivity of ratios
(`v(a)/v(c) = [v(a)/v(b)] · [v(b)/v(c)]`) forces Cauchy's multiplicative
functional equation: `g(s + t) = g(s) · g(t)`. The unique monotone increasing
solution is `g(s) = exp(k · s)` (`cauchy_mul_exp`), giving:

- `v(a) = C · exp(k · u(a))` — the ratio scale IS the exponential of utility
- `P(a,b) = 1/(1 + exp(-k · (u(a) - u(b))))` — the logistic function
- For n alternatives: `P(a|S) = exp(k · u(a)) / Σ exp(k · u(b))` — softmax

The parameter `k > 0` is the rationality parameter `α` in RSA.

-/

private theorem cauchy_g0_eq_one (g : ℝ → ℝ)
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) : g 0 = 1 := by
  have h0 : g 0 = g 0 * g 0 := by
    have := hg_mul 0 0; simp at this; exact this
  have : g 0 * (g 0 - 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · exfalso
    have h1 : g (-1) < g 0 := hg_mono (by linarith : (-1 : ℝ) < 0)
    have h2 : g 0 < g 1 := hg_mono (by linarith : (0 : ℝ) < 1)
    have h3 : g (-1) * g 1 = g 0 := by
      have := hg_mul (-1) 1; simp at this; exact this.symm
    rw [h] at h1 h2 h3
    linarith [mul_neg_of_neg_of_pos h1 h2]
  · linarith

private theorem cauchy_g_pos (g : ℝ → ℝ)
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) (x : ℝ) : 0 < g x := by
  have hg0 := cauchy_g0_eq_one g hg_mul hg_mono
  have hsq : g x = g (x / 2) * g (x / 2) := by
    have := hg_mul (x / 2) (x / 2); rw [add_halves] at this; exact this
  by_contra h; push_neg at h
  have hgx_zero : g x = 0 := le_antisymm h (by rw [hsq]; exact mul_self_nonneg _)
  have hx2_zero : g (x / 2) = 0 := by rwa [hsq, mul_self_eq_zero] at hgx_zero
  have hg0' : g 0 = g x * g (-x) := by
    have := hg_mul x (-x); simp at this; exact this
  rw [hgx_zero, zero_mul] at hg0'; linarith

private theorem cauchy_additive_zero (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) : h 0 = 0 := by
  have := hadd 0 0; simp at this; linarith

private theorem cauchy_additive_neg (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (x : ℝ) : h (-x) = -h x := by
  have : h (x + (-x)) = h x + h (-x) := hadd x (-x)
  simp [cauchy_additive_zero h hadd] at this; linarith

private theorem cauchy_additive_nat (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (n : ℕ) : h n = n * h 1 := by
  induction n with
  | zero => simp [cauchy_additive_zero h hadd]
  | succ k ih => rw [Nat.cast_succ, hadd, ih]; ring

private theorem cauchy_additive_int (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (n : ℤ) : h n = n * h 1 := by
  cases n with
  | ofNat k => simp [cauchy_additive_nat h hadd k]
  | negSucc k =>
    simp only [Int.cast_negSucc]
    rw [cauchy_additive_neg h hadd, cauchy_additive_nat h hadd (k + 1)]
    push_cast; ring

private theorem cauchy_additive_rat (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (q : ℚ) : h q = q * h 1 := by
  have hden_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hden_ne : (q.den : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hmul_nat : ∀ (n : ℕ) (x : ℝ), h (n * x) = n * h x := by
    intro n x; induction n with
    | zero => simp [cauchy_additive_zero h hadd]
    | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih]; ring
  have step1 : (q.den : ℝ) * h q = h (q.num : ℤ) := by
    rw [← hmul_nat q.den q]; congr 1; rw [Rat.cast_def]; field_simp
  rw [cauchy_additive_int h hadd] at step1
  have : h q = (q.num : ℝ) * h 1 / q.den := by field_simp at step1 ⊢; linarith
  rw [this, Rat.cast_def]; field_simp

private theorem cauchy_monotone_additive_linear (h : ℝ → ℝ)
    (hadd : ∀ s t, h (s + t) = h s + h t) (hmono : StrictMono h) :
    ∀ x, h x = x * h 1 := by
  have h0 : h 0 = 0 := cauchy_additive_zero h hadd
  have h1_pos : 0 < h 1 := by linarith [hmono (show (0 : ℝ) < 1 by norm_num), h0]
  intro x
  by_contra hne
  rcases ne_iff_lt_or_gt.mp hne with hlt | hgt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show h x / h 1 < x by
      rw [div_lt_iff₀ h1_pos]; linarith)
    have : h x < h q := by
      rw [cauchy_additive_rat h hadd q]
      have := (div_lt_iff₀ h1_pos).mp hq1; linarith
    linarith [hmono hq2]
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < h x / h 1 by
      rw [lt_div_iff₀ h1_pos]; linarith)
    have : h q < h x := by
      rw [cauchy_additive_rat h hadd q]
      have := (lt_div_iff₀ h1_pos).mp hq2; linarith
    linarith [hmono hq1]

/-- **Cauchy's multiplicative functional equation** (classical):
    If `g : ℝ → ℝ` satisfies `g(s + t) = g(s) · g(t)` and is strictly
    monotone increasing, then `g(s) = exp(k · s)` for some `k > 0`.

    The proof reduces to the additive Cauchy equation via `log`: setting
    `h = log ∘ g`, the multiplicative equation becomes `h(s+t) = h(s) + h(t)`.
    The key lemma (`cauchy_monotone_additive_linear`) shows that a strictly
    monotone additive function must be linear, by density of ℚ in ℝ:
    `h` agrees with `x ↦ k·x` on rationals (by induction), and any
    deviation on an irrational `x` would violate monotonicity via a
    rational witness between `x` and `h(x)/k`. -/
theorem cauchy_mul_exp (g : ℝ → ℝ)
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) :
    ∃ k : ℝ, 0 < k ∧ g 0 = 1 ∧ ∀ s, g s = Real.exp (k * s) := by
  have hg0 := cauchy_g0_eq_one g hg_mul hg_mono
  have hg_pos := cauchy_g_pos g hg_mul hg_mono
  set h := fun x => log (g x) with hh_def
  have hadd : ∀ s t, h (s + t) = h s + h t := fun s t => by
    simp only [h]; rw [hg_mul s t, log_mul (ne_of_gt (hg_pos s)) (ne_of_gt (hg_pos t))]
  have hmono : StrictMono h := fun a b hab => by
    simp only [h]; exact log_lt_log (hg_pos a) (hg_mono hab)
  have hlinear := cauchy_monotone_additive_linear h hadd hmono
  have hk_pos : 0 < h 1 := by
    have := hmono (show (0 : ℝ) < 1 by norm_num)
    simp only [h] at this; rw [hg0, log_one] at this; exact this
  refine ⟨h 1, hk_pos, hg0, fun s => ?_⟩
  have := hlinear s
  simp only [h] at this
  rw [← exp_log (hg_pos s), this, mul_comm]

/-- **Fechnerian uniqueness** (§2.A; @cite{adams-messick-1958}):
    If a ratio scale `v` and interval scale `u` represent the same
    ordering via `v(x)/v(y) = g(u(x) - u(y))` for a strictly monotone
    multiplicative `g`, then `v` is the exponential of `u`.

    This is WHY `fromSoftmax` uses `exp(α · utility)`: the exponential
    is **forced** by the requirement that log-odds be linear in utility
    differences. It is the unique bridge between Luce's ratio scale
    (Chapter 1) and Fechner's interval scale (Chapter 2). -/
theorem luce_fechnerian_exp {X : Type*} (v u : X → ℝ) (g : ℝ → ℝ)
    (hv_pos : ∀ x, 0 < v x)
    (h_ratio : ∀ x y, v x / v y = g (u x - u y))
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) :
    ∃ k : ℝ, 0 < k ∧ ∀ x₀ x, v x = v x₀ * Real.exp (k * (u x - u x₀)) := by
  obtain ⟨k, hk, _, hg_exp⟩ := cauchy_mul_exp g hg_mul hg_mono
  exact ⟨k, hk, fun x₀ x => by
    have h := h_ratio x x₀
    rw [hg_exp (u x - u x₀)] at h
    rwa [div_eq_iff (ne_of_gt (hv_pos x₀)), mul_comm] at h⟩

/-- Construct a RationalAction from a utility function via softmax.

The score is `exp(α · utility(s, a))`, so `policy = softmax(utility, α)`.
The exponential parameterization is forced by the Fechnerian characterization
(`luce_fechnerian_exp`): it is the unique bridge from Luce's ratio scale
to an additive utility scale. -/
noncomputable def RationalAction.fromSoftmax
    (utility : S → A → ℝ) (α : ℝ) : RationalAction S A where
  score s a := exp (α * utility s a)
  score_nonneg _ _ := le_of_lt (exp_pos _)

/-- The policy of a softmax agent equals the softmax function. -/
theorem RationalAction.fromSoftmax_policy_eq [Nonempty A]
    (utility : S → A → ℝ) (α : ℝ) (s : S) (a : A) :
    (RationalAction.fromSoftmax utility α).policy s a = softmax (utility s) α a := by
  simp only [policy, fromSoftmax, totalScore, softmax]
  have hpos : 0 < ∑ j : A, exp (α * utility s j) := partitionFn_pos (utility s) α
  have hne : ∑ j : A, exp (α * utility s j) ≠ 0 := ne_of_gt hpos
  simp only [hne, ↓reduceIte]

-- ============================================================================
-- §3. KL Divergence and Gibbs Variational Principle
-- ============================================================================

/-!
## KL Divergence and the Gibbs Variational Principle

The softmax distribution uniquely maximizes entropy + expected score
on the probability simplex. This is the mathematical foundation for
RSA convergence (@cite{zaslavsky-hu-levy-2020}, Proposition 1).

### Proof strategy

The Gibbs VP reduces to KL non-negativity via three identities:

1. H(p) + KL(p‖q) = -∑ pᵢ log qᵢ (negMulLog + KL term telescope)
2. -∑ pᵢ log qᵢ = -α⟨p,s⟩ + log Z (substitute log qᵢ = α sᵢ - log Z)
3. H(q) + α⟨q,s⟩ = log Z (softmax self-information)

Combining: H(p) + α⟨p,s⟩ + KL = log Z = H(q) + α⟨q,s⟩, so KL ≥ 0 ⟹ LHS ≤ RHS.

-/

section KLDivergence

variable {ι : Type*} [Fintype ι]

/-- Finite KL divergence: KL(p ‖ q) = Σ pᵢ · log(pᵢ / qᵢ).
    Convention: 0 · log(0/q) = 0. -/
noncomputable def klFinite (p q : ι → ℝ) : ℝ :=
  ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i)

/-- When q > 0, each KL term can be written via klFun:
    p · log(p/q) = q · klFun(p/q) + (p - q). -/
private theorem kl_term_eq_klFun {p_i q_i : ℝ} (hq : 0 < q_i) (_hp : 0 ≤ p_i) :
    (if p_i = 0 then (0 : ℝ) else p_i * log (p_i / q_i)) =
    q_i * InformationTheory.klFun (p_i / q_i) + (p_i - q_i) := by
  by_cases hp0 : p_i = 0
  · simp only [hp0, ↓reduceIte, zero_div, InformationTheory.klFun_zero, mul_one, zero_sub,
               add_neg_cancel]
  · simp only [hp0, ↓reduceIte]
    unfold InformationTheory.klFun
    have hq_ne : q_i ≠ 0 := ne_of_gt hq
    field_simp
    ring

/-- Finite KL divergence equals Σ qᵢ · klFun(pᵢ/qᵢ) when Σpᵢ = Σqᵢ. -/
theorem kl_eq_sum_klFun (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    klFinite p q = ∑ i, q i * InformationTheory.klFun (p i / q i) := by
  unfold klFinite
  have hterm : ∀ i, (if p i = 0 then (0 : ℝ) else p i * log (p i / q i)) =
      q i * InformationTheory.klFun (p i / q i) + (p i - q i) :=
    λ i => kl_term_eq_klFun (hq i) (hp i)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hcancel : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  linarith

/-- **Gibbs' inequality (finite form)**: KL(p ‖ q) ≥ 0.

    For distributions p, q with qᵢ > 0, pᵢ ≥ 0, and Σpᵢ = Σqᵢ:
      Σᵢ pᵢ · log(pᵢ/qᵢ) ≥ 0

    Proof via Mathlib's `klFun_nonneg`: klFun(x) ≥ 0 for x ≥ 0. -/
theorem kl_nonneg (p q : ι → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = ∑ i, q i) :
    0 ≤ klFinite p q := by
  rw [kl_eq_sum_klFun p q hq hp hsum]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (le_of_lt (hq i))
  exact InformationTheory.klFun_nonneg (div_nonneg (hp i) (le_of_lt (hq i)))

/-- Alternative KL non-negativity with distribution hypotheses. -/
theorem kl_nonneg' [Nonempty ι] {p q : ι → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    0 ≤ klFinite p q :=
  kl_nonneg p q hq_pos hp_nonneg (by rw [hp_sum, hq_sum])

end KLDivergence

-- ============================================================================
-- §3a. Gibbs Variational Principle
-- ============================================================================

section GibbsVariational

variable {ι : Type*} [Fintype ι]

/-- The per-meaning speaker objective: f(s) = Σᵤ [negMulLog(sᵤ) + α · sᵤ · vᵤ].

This is the function that the speaker maximizes for each meaning m,
where vᵤ = log L(m|u) is the listener utility of utterance u. -/
noncomputable def speakerObj (v : ι → ℝ) (α : ℝ) (s : ι → ℝ) : ℝ :=
  ∑ u, (Real.negMulLog (s u) + α * s u * v u)

/-- The softmax achieves f(s*) = log Z, where Z is the partition function. -/
theorem speakerObj_at_softmax [Nonempty ι] (v : ι → ℝ) (α : ℝ) :
    speakerObj v α (softmax v α) = logSumExp v α := by
  unfold speakerObj logSumExp
  have hZ_pos : 0 < partitionFn v α := partitionFn_pos v α
  have hlog_softmax : ∀ u, log (softmax v α u) = α * v u - log (partitionFn v α) := by
    intro u
    simp only [softmax, partitionFn]
    rw [log_div (ne_of_gt (exp_pos _)) (ne_of_gt (Finset.sum_pos
      (fun j _ => exp_pos _) Finset.univ_nonempty)), log_exp]
  have hterm : ∀ u, Real.negMulLog (softmax v α u) + α * softmax v α u * v u =
      softmax v α u * log (partitionFn v α) := by
    intro u; unfold Real.negMulLog; rw [hlog_softmax]; ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, softmax_sum_eq_one, one_mul]
  rfl

/-- Key identity: speakerObj(s) + KL(s ‖ s*) = logSumExp (= speakerObj(s*)). -/
private theorem speakerObj_plus_kl [Nonempty ι] (v : ι → ℝ) (α : ℝ)
    (s : ι → ℝ) (_hs_nonneg : ∀ i, 0 ≤ s i) (hs_sum : ∑ i, s i = 1) :
    speakerObj v α s + klFinite s (softmax v α) = logSumExp v α := by
  unfold speakerObj klFinite logSumExp
  rw [← Finset.sum_add_distrib]
  have hZ_pos : 0 < ∑ j : ι, exp (α * v j) := partitionFn_pos v α
  have hZ_ne : (∑ j : ι, exp (α * v j)) ≠ 0 := ne_of_gt hZ_pos
  have hterm : ∀ u, (Real.negMulLog (s u) + α * s u * v u) +
      (if s u = 0 then (0 : ℝ) else s u * log (s u / softmax v α u)) =
      s u * log (∑ j : ι, exp (α * v j)) := by
    intro u
    by_cases hs0 : s u = 0
    · simp [hs0, Real.negMulLog]
    · simp only [hs0, ↓reduceIte]
      have hs_pos : 0 < softmax v α u := softmax_pos v α u
      rw [log_div hs0 (ne_of_gt hs_pos)]
      have hlog_sm : log (softmax v α u) = α * v u - log (∑ j : ι, exp (α * v j)) := by
        simp only [softmax]
        rw [log_div (ne_of_gt (exp_pos _)) (ne_of_gt (Finset.sum_pos
          (fun j _ => exp_pos _) Finset.univ_nonempty)), log_exp]
      rw [hlog_sm]; unfold Real.negMulLog; ring
  simp_rw [hterm, ← Finset.sum_mul, hs_sum, one_mul]

/-- **Gibbs Variational Principle**: softmax maximizes entropy + expected score.

For any distribution p on ι and scores s : ι → ℝ:
  H(p) + α·⟨p, s⟩ ≤ H(q) + α·⟨q, s⟩
where q = softmax(s, α) and H(p) = Σ negMulLog(pᵢ). -/
theorem gibbs_variational [Nonempty ι] (s : ι → ℝ) (α : ℝ) (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) + α * ∑ i, p i * s i ≤
    (∑ i, Real.negMulLog (softmax s α i)) + α * ∑ i, softmax s α i * s i := by
  set q := softmax s α
  have hq_pos : ∀ i, 0 < q i := fun i => softmax_pos s α i
  have hq_sum : ∑ i, q i = 1 := softmax_sum_eq_one s α
  have hkl := kl_nonneg' hp_nonneg hq_pos hp_sum hq_sum
  have h_logq : ∀ i, Real.log (q i) = α * s i - logSumExp s α := fun i => log_softmax s α i
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
  have h1 : (∑ i, Real.negMulLog (p i)) + klFinite p q =
      -(∑ i, p i * Real.log (q i)) := by
    unfold klFinite
    rw [← Finset.sum_add_distrib]
    simp_rw [h_combine, Finset.sum_neg_distrib]
  have h2 : -(∑ i, p i * Real.log (q i)) = -(α * ∑ i, p i * s i) + logSumExp s α := by
    have : ∑ i, p i * Real.log (q i) = α * ∑ i, p i * s i - logSumExp s α := by
      simp_rw [h_logq]
      rw [show ∑ i : ι, p i * (α * s i - logSumExp s α) =
          ∑ i, (α * (p i * s i) - logSumExp s α * p i) from
        Finset.sum_congr rfl fun i _ => by ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp_sum, mul_one]
    linarith
  have h3 : (∑ i, Real.negMulLog (q i)) + α * ∑ i, q i * s i = logSumExp s α := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show ∑ i : ι, (Real.negMulLog (q i) + α * (q i * s i)) = ∑ i, logSumExp s α * q i from
      Finset.sum_congr rfl fun i _ => by simp only [Real.negMulLog, h_logq i]; ring]
    rw [← Finset.mul_sum, hq_sum, mul_one]
  linarith

end GibbsVariational

-- ============================================================================
-- §3b. Softmax → Argmax Limit (OT ↔ MaxEnt Connection)
-- ============================================================================

/-!
## Softmax Concentration at High Rationality

As the rationality parameter α → ∞, softmax concentrates all probability mass
on the action with highest utility — i.e., softmax converges to argmax. This
connects:

- **MaxEnt phonology ↔ OT**: a MaxEnt grammar with weights `w` becomes
  categorical (OT-like) as temperature → 0 (equivalently α → ∞).
- **RSA ↔ neo-Gricean pragmatics**: a soft-rational RSA speaker becomes a
  hard-rational Gricean reasoner in the α → ∞ limit.

### Proof sketch

From `softmax_odds`, we have `σᵢ / σⱼ = exp(α(sᵢ − sⱼ))`. When `sᵢ > sⱼ`,
this ratio → ∞ as α → ∞, so `σⱼ / σᵢ → 0`. Since `Σ σₖ = 1`, the maximizer's
probability → 1 by squeezing: `1 - σ_max = Σ_{k≠max} σₖ`, and each non-maximal
term → 0 (bounded by `exp(-α · gap)` where gap = sᵢ - sⱼ > 0).
-/

section SoftmaxLimit

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Nonempty ι] [DecidableEq ι] in
/-- Each softmax component is bounded by `exp(α(sⱼ - s_{i_max}))`, obtained
    by dropping all but the `i_max` term from the partition function. -/
private theorem softmax_le_exp_diff (s : ι → ℝ) (α : ℝ) (j i_max : ι) :
    softmax s α j ≤ exp (α * (s j - s i_max)) := by
  simp only [softmax]
  rw [show α * (s j - s i_max) = α * s j - α * s i_max from by ring, exp_sub]
  exact div_le_div_of_nonneg_left (exp_pos _).le (exp_pos _)
    (single_le_sum (f := fun k => exp (α * s k)) (fun k _ => (exp_pos _).le) (mem_univ i_max))

omit [Nonempty ι] [DecidableEq ι] in
/-- When `x < 0`, `exp(α · x) < ε` for all sufficiently large `α`. -/
private theorem exp_mul_neg_lt (x : ℝ) (hx : x < 0) (ε : ℝ) (hε : 0 < ε)
    (α : ℝ) (hα : α > log ε / x) : exp (α * x) < ε := by
  calc exp (α * x) < exp (log ε) := by
        apply exp_lt_exp.mpr
        have := mul_lt_mul_of_neg_right hα hx
        rwa [div_mul_cancel₀ (log ε) (ne_of_lt hx)] at this
    _ = ε := exp_log hε

/-- **Softmax → argmax limit**: as α → ∞, softmax concentrates on the unique
    maximizer. For any `i_max` with `s i_max` strictly greater than all other
    scores, `softmax(s, α)_{i_max} → 1`.

    This is the formal connection between MaxEnt (soft optimization) and OT
    (hard optimization): OT is the α → ∞ limit of MaxEnt. -/
theorem softmax_argmax_limit (s : ι → ℝ) (i_max : ι)
    (h_max : ∀ j, j ≠ i_max → s j < s i_max) :
    ∀ ε > 0, ∃ α₀ : ℝ, ∀ α, α > α₀ → |softmax s α i_max - 1| < ε := by
  intro ε hε
  set n := Fintype.card ι
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  set εn := ε / n
  have hεn : 0 < εn := div_pos hε hn_pos
  let threshFn : ι → ℝ := fun j =>
    if j = i_max then (0 : ℝ) else log εn / (s j - s i_max)
  refine ⟨univ.sup' ⟨i_max, mem_univ _⟩ threshFn, fun α hα => ?_⟩
  have hbound : ∀ j ≠ i_max, softmax s α j < εn := by
    intro j hj
    apply lt_of_le_of_lt (softmax_le_exp_diff s α j i_max)
    apply exp_mul_neg_lt _ (sub_neg.mpr (h_max j hj)) εn hεn
    have h1 : threshFn j ≤ univ.sup' ⟨i_max, mem_univ _⟩ threshFn :=
      le_sup' _ (mem_univ j)
    simp only [threshFn, hj, ↓reduceIte] at h1
    linarith
  have htail : 1 - softmax s α i_max = ∑ j ∈ univ.erase i_max, softmax s α j := by
    rw [← softmax_sum_eq_one (ι := ι) s α, ← add_sum_erase _ _ (mem_univ i_max)]; ring
  have htail_nonneg : 0 ≤ 1 - softmax s α i_max := by
    rw [htail]; exact sum_nonneg fun j _ => le_of_lt (softmax_pos s α j)
  have htail_strict : 1 - softmax s α i_max < ε := by
    rw [htail]
    rcases (univ.erase i_max : Finset ι).eq_empty_or_nonempty with hempty | ⟨j, hj⟩
    · simp [hempty]; exact hε
    · calc ∑ k ∈ univ.erase i_max, softmax s α k
          < ∑ _ ∈ univ.erase i_max, εn :=
            sum_lt_sum (fun k hk => le_of_lt (hbound k (mem_erase.mp hk).1))
              ⟨j, hj, hbound j (mem_erase.mp hj).1⟩
        _ ≤ ∑ (_ : ι), εn :=
            sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => hεn.le)
        _ = ↑n * εn := by rw [sum_const, card_univ, nsmul_eq_mul]
        _ = ε := mul_div_cancel₀ _ (ne_of_gt hn_pos)
  rw [abs_sub_lt_iff]; constructor <;> linarith

omit [Nonempty ι] [DecidableEq ι] in
/-- Complement of the limit: non-maximal actions get probability → 0. -/
theorem softmax_nonmax_limit (s : ι → ℝ) (i_max : ι)
    (h_max : ∀ j, j ≠ i_max → s j < s i_max) (j : ι) (hj : j ≠ i_max) :
    ∀ ε > 0, ∃ α₀ : ℝ, ∀ α, α > α₀ → softmax s α j < ε := by
  intro ε hε
  exact ⟨log ε / (s j - s i_max), fun α hα =>
    lt_of_le_of_lt (softmax_le_exp_diff s α j i_max)
      (exp_mul_neg_lt _ (sub_neg.mpr (h_max j hj)) ε hε α hα)⟩

end SoftmaxLimit

-- ============================================================================
-- §4. Shannon Entropy and Maximum Entropy
-- ============================================================================

section Entropy

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Shannon entropy: H(p) = -Σᵢ pᵢ log pᵢ.

For a ℚ-valued counterpart suitable for decidable computation, see
`Core.InformationTheory.entropy` in `Linglib/Core/InformationTheory.lean`. -/
noncomputable def shannonEntropy (p : ι → ℝ) : ℝ :=
  -∑ i : ι, if p i = 0 then 0 else p i * log (p i)

omit [Nonempty ι] in
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

/-- Maximum entropy is achieved by uniform distribution.

Proof: KL(p ‖ uniform) ≥ 0, and KL(p ‖ uniform) = log n - H(p). -/
theorem shannonEntropy_le_log_card (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    shannonEntropy p ≤ log (Fintype.card ι) := by
  -- Use KL(p ‖ uniform) ≥ 0
  set n := (Fintype.card ι : ℝ) with hn_def
  have hn_pos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  set q : ι → ℝ := λ _ => 1 / n with hq_def
  have hq_pos : ∀ i, 0 < q i := fun _ => by simp [hq_def]; positivity
  have hq_sum : ∑ i, q i = 1 := by
    simp only [hq_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn_def]
    field_simp
  have hkl := kl_nonneg' hp_nonneg hq_pos hp_sum hq_sum
  -- KL(p ‖ q) = -H(p) - Σ pᵢ log(1/n) = -H(p) + log n
  suffices h : klFinite p q = -shannonEntropy p + log n by linarith
  simp only [klFinite, shannonEntropy]
  -- Each term: if p=0 then 0 else p*log(p/q) = (if p=0 then 0 else p*log p) + p*log n
  have hterm : ∀ i, (if p i = 0 then (0 : ℝ) else p i * log (p i / q i)) =
      (if p i = 0 then (0 : ℝ) else p i * log (p i)) + p i * log n := by
    intro i
    by_cases hp0 : p i = 0
    · simp [hp0]
    · simp only [hp0, ↓reduceIte]
      have hq_ne : q i ≠ 0 := ne_of_gt (hq_pos i)
      rw [log_div hp0 hq_ne]
      have : log (q i) = -log n := by
        simp only [hq_def, log_div one_ne_zero hn_ne, log_one, zero_sub]
      rw [this]; ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp_sum, one_mul, neg_neg]

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
  have hsm_pos : ∀ i, exp (α * s i) / ∑ j : ι, exp (α * s j) ≠ 0 := by
    intro i; exact ne_of_gt (div_pos (exp_pos _) hZ)
  simp only [hsm_pos, ↓reduceIte]
  have hlog : ∀ i, log (exp (α * s i) / ∑ j : ι, exp (α * s j)) =
                   α * s i - log (∑ j : ι, exp (α * s j)) := by
    intro i; rw [log_div (ne_of_gt (exp_pos _)) hne, log_exp]
  simp_rw [hlog]
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

/-- Entropy-regularized objective: G_α(p, s) = ⟨s, p⟩ + (1/α) H(p). -/
noncomputable def entropyRegObjective (s : ι → ℝ) (α : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i : ι, p i * s i + (1 / α) * shannonEntropy p

/-- The maximum value of the entropy-regularized objective. -/
theorem entropyRegObjective_softmax (s : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    entropyRegObjective s α (softmax s α) = (1 / α) * log (partitionFn s α) := by
  simp only [entropyRegObjective, shannonEntropy_softmax]
  have hne : α ≠ 0 := ne_of_gt hα
  field_simp
  ring

omit [Nonempty ι] in
/-- Shannon entropy equals sum of negMulLog for distributions. -/
private theorem shannonEntropy_eq_negMulLog (p : ι → ℝ)
    (_hp_nonneg : ∀ i, 0 ≤ p i) :
    shannonEntropy p = ∑ i, Real.negMulLog (p i) := by
  simp only [shannonEntropy, Real.negMulLog]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp0 : p i = 0
  · simp [hp0]
  · simp only [hp0, ↓reduceIte, neg_mul]

/-- Fact 5: Softmax maximizes the entropy-regularized objective.

Proof: `gibbs_variational` gives `H(p) + α⟨p,s⟩ ≤ H(q) + α⟨q,s⟩`;
dividing by `α > 0` yields the result. -/
theorem softmax_maximizes_entropyReg (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    entropyRegObjective s α p ≤ entropyRegObjective s α (softmax s α) := by
  simp only [entropyRegObjective]
  have hgibbs := gibbs_variational s α p hp_nonneg hp_sum
  -- Rewrite Shannon entropy as sum of negMulLog
  rw [shannonEntropy_eq_negMulLog p hp_nonneg,
      shannonEntropy_eq_negMulLog (softmax s α) (fun i => softmax_nonneg s α i)]
  -- gibbs_variational: Σ negMulLog(pᵢ) + α Σ pᵢsᵢ ≤ Σ negMulLog(qᵢ) + α Σ qᵢsᵢ
  -- We need: Σ pᵢsᵢ + (1/α)(Σ negMulLog(pᵢ)) ≤ Σ qᵢsᵢ + (1/α)(Σ negMulLog(qᵢ))
  -- This follows from dividing by α > 0
  have hα_ne : α ≠ 0 := ne_of_gt hα
  -- gibbs_variational: H(p)+α⟨p,s⟩ ≤ H(q)+α⟨q,s⟩, divide by α > 0
  have h := div_le_div_of_nonneg_right hgibbs (le_of_lt hα)
  simp only [add_div, mul_div_cancel_left₀ _ hα_ne] at h
  -- h : Σ negMulLog(pᵢ) / α + Σ pᵢsᵢ ≤ Σ negMulLog(qᵢ) / α + Σ qᵢsᵢ
  -- Convert div to 1/α * to match entropyRegObjective
  simp only [div_eq_inv_mul] at h
  rw [show (α⁻¹ : ℝ) = 1 / α from by ring] at h
  linarith

omit [Nonempty ι] in
/-- KL divergence zero implies distributions are equal (when q > 0 and sums match). -/
private theorem kl_eq_zero_imp_eq (p q : ι → ℝ) (hq_pos : ∀ i, 0 < q i)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = ∑ i, q i)
    (hkl : klFinite p q = 0) :
    p = q := by
  rw [kl_eq_sum_klFun p q hq_pos hp_nonneg hsum] at hkl
  funext i
  have hpi_div_qi_nonneg : 0 ≤ p i / q i := div_nonneg (hp_nonneg i) (le_of_lt (hq_pos i))
  have hqi_pos : 0 < q i := hq_pos i
  have hqi_nonneg : 0 ≤ q i := le_of_lt hqi_pos
  -- Each term q_i * klFun(p_i/q_i) ≥ 0 and their sum = 0
  have hterm_nonneg : ∀ j, 0 ≤ q j * InformationTheory.klFun (p j / q j) := by
    intro j; exact mul_nonneg (le_of_lt (hq_pos j))
      (InformationTheory.klFun_nonneg (div_nonneg (hp_nonneg j) (le_of_lt (hq_pos j))))
  have hterm_zero : q i * InformationTheory.klFun (p i / q i) = 0 := by
    have hsz := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm_nonneg j) |>.mp hkl
    exact hsz i (Finset.mem_univ i)
  -- q_i > 0 so klFun(p_i/q_i) = 0, hence p_i/q_i = 1
  rcases mul_eq_zero.mp hterm_zero with hq0 | hkl0
  · exact absurd hq0 (ne_of_gt hqi_pos)
  · rw [InformationTheory.klFun_eq_zero_iff hpi_div_qi_nonneg] at hkl0
    exact div_eq_one_iff_eq (ne_of_gt hqi_pos) |>.mp hkl0

/-- Softmax is the unique maximizer.

Proof: equality in the objective ⟹ KL(p ‖ softmax) = 0 (via `speakerObj_plus_kl`),
hence p = softmax (via `kl_eq_zero_imp_eq`). -/
theorem softmax_unique_maximizer (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1)
    (h_max : entropyRegObjective s α p = entropyRegObjective s α (softmax s α)) :
    p = softmax s α := by
  set q := softmax s α with hq_def
  have hq_pos : ∀ i, 0 < q i := fun i => softmax_pos s α i
  have hq_sum : ∑ i, q i = 1 := softmax_sum_eq_one s α
  -- From speakerObj_plus_kl: speakerObj(p) + KL(p ‖ q) = logSumExp = speakerObj(q) + 0
  have h_p := speakerObj_plus_kl s α p hp_nonneg hp_sum
  have h_q := speakerObj_plus_kl s α q (fun i => le_of_lt (hq_pos i)) hq_sum
  -- KL(q ‖ q) = 0
  have hkl_self : klFinite q q = 0 := by
    simp only [klFinite]
    apply Finset.sum_eq_zero
    intro i _
    have hne : q i ≠ 0 := ne_of_gt (hq_pos i)
    simp [hne]
  rw [hkl_self, add_zero] at h_q
  -- So KL(p ‖ q) = logSumExp - speakerObj(p) = speakerObj(q) - speakerObj(p)
  have hkl_val : klFinite p q = speakerObj s α q - speakerObj s α p := by linarith
  -- entropyRegObjective equality means speakerObj equality (up to rescaling)
  -- entropyRegObjective = Σ p*s + (1/α) * H(p)
  -- speakerObj = Σ negMulLog(p) + α * Σ p*s  (i.e. H(p) + α⟨p,s⟩ but per-element)
  -- We showed: entropyRegObj(p) = (1/α) * speakerObj(p)
  have hobj_eq : speakerObj s α p = speakerObj s α q := by
    -- entropyRegObjective = Σ p*s + (1/α)*H(p) = (1/α)(H(p) + α Σ p*s) = (1/α)*speakerObj
    have hα_ne' : α ≠ 0 := ne_of_gt hα
    have hconv : ∀ r : ι → ℝ, (∀ i, 0 ≤ r i) →
        entropyRegObjective s α r = (1 / α) * speakerObj s α r := by
      intro r hr_nn
      simp only [entropyRegObjective, speakerObj]
      rw [shannonEntropy_eq_negMulLog r hr_nn, Finset.mul_sum, ← Finset.sum_add_distrib,
          Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
      ring
    have h1 := hconv p hp_nonneg
    have h2 := hconv q (fun i => le_of_lt (hq_pos i))
    have hα_ne : (1 : ℝ) / α ≠ 0 := by positivity
    rw [h1, h2] at h_max
    exact mul_left_cancel₀ hα_ne h_max
  -- Therefore KL(p ‖ q) = 0
  have hkl_zero : klFinite p q = 0 := by linarith
  exact kl_eq_zero_imp_eq p q hq_pos hp_nonneg (by rw [hp_sum, hq_sum]) hkl_zero

/-- Free energy (from statistical mechanics). -/
noncomputable def freeEnergy (s : ι → ℝ) (α : ℝ) (p : ι → ℝ) : ℝ :=
  -∑ i : ι, p i * s i - (1 / α) * shannonEntropy p

/-- Softmax is the Boltzmann distribution: minimizes free energy. -/
theorem softmax_minimizes_freeEnergy (s : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : ι, p i = 1) :
    freeEnergy s α (softmax s α) ≤ freeEnergy s α p := by
  simp only [freeEnergy]
  have h := softmax_maximizes_entropyReg s α hα p hp_nonneg hp_sum
  simp only [entropyRegObjective] at h
  linarith

/-- The log-partition function is convex in α.

Proof: By Hölder's inequality. For `0 < a, b` with `a + b = 1`:
  `∑ exp(x·sᵢ)^a · exp(y·sᵢ)^b ≤ (∑ exp(x·sᵢ))^a · (∑ exp(y·sᵢ))^b`
Since `exp(x·sᵢ)^a · exp(y·sᵢ)^b = exp((ax+by)·sᵢ)`, taking logs gives
  `logSumExp(s, ax+by) ≤ a·logSumExp(s, x) + b·logSumExp(s, y)`. -/
theorem logSumExp_convex (s : ι → ℝ) :
    ConvexOn ℝ Set.univ (λ α => logSumExp s α) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    unfold logSumExp
    -- Edge cases: a = 0 or b = 0
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp [show b = 1 from by linarith]
    rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp [show a = 1 from by linarith]
    -- Main case: 0 < a, 0 < b, a + b = 1
    -- Key step: exp((ax+by)·sᵢ) = exp(x·sᵢ)^a · exp(y·sᵢ)^b
    have hexp_split : ∀ i, exp ((a * x + b * y) * s i) =
        (exp (x * s i)) ^ a * (exp (y * s i)) ^ b := by
      intro i
      rw [← exp_mul, ← exp_mul]
      rw [show (a * x + b * y) * s i = x * s i * a + y * s i * b from by ring]
      rw [exp_add]
    -- Apply Hölder with p = 1/a, q = 1/b
    have hpq : a⁻¹.HolderConjugate b⁻¹ := HolderConjugate.inv_inv ha_pos hb_pos hab
    have holder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ (α := ι)) hpq
      (f := fun i => (exp (x * s i)) ^ a)
      (g := fun i => (exp (y * s i)) ^ b)
      (fun i _ => rpow_nonneg (le_of_lt (exp_pos _)) a)
      (fun i _ => rpow_nonneg (le_of_lt (exp_pos _)) b)
    -- Simplify Hölder LHS: ∑ exp(x·sᵢ)^a · exp(y·sᵢ)^b = ∑ exp((ax+by)·sᵢ)
    conv at holder => lhs; arg 2; ext i; rw [← hexp_split]
    -- Simplify Hölder RHS powers: (exp(x·sᵢ)^a)^(1/a) = exp(x·sᵢ), etc.
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have hsimp_f : ∀ i, ((exp (x * s i)) ^ a) ^ a⁻¹ = exp (x * s i) := by
      intro i
      rw [← rpow_mul (le_of_lt (exp_pos _)), mul_inv_cancel₀ ha_ne, rpow_one]
    have hsimp_g : ∀ i, ((exp (y * s i)) ^ b) ^ b⁻¹ = exp (y * s i) := by
      intro i
      rw [← rpow_mul (le_of_lt (exp_pos _)), mul_inv_cancel₀ hb_ne, rpow_one]
    simp_rw [hsimp_f, hsimp_g] at holder
    -- The RHS of holder uses (1 / a⁻¹) and (1 / b⁻¹); simplify to a and b
    simp only [one_div, inv_inv] at holder
    -- Take log of both sides (both are positive)
    have hZ_x : (0 : ℝ) < ∑ i : ι, exp (x * s i) := partitionFn_pos s x
    have hZ_y : (0 : ℝ) < ∑ i : ι, exp (y * s i) := partitionFn_pos s y
    have hZ_mid : 0 < ∑ j : ι, exp ((a * x + b * y) * s j) := partitionFn_pos s (a * x + b * y)
    have hlog_le := log_le_log hZ_mid holder
    rw [log_mul (ne_of_gt (rpow_pos_of_pos hZ_x a)) (ne_of_gt (rpow_pos_of_pos hZ_y b)),
        log_rpow hZ_x, log_rpow hZ_y] at hlog_le
    linarith

/-- Derivative of log-partition gives expected value:
    `d/dα log(Σ exp(α sᵢ)) = Σ softmax(s,α)ᵢ · sᵢ`.

    Proof via chain rule on `log ∘ Σ exp(α · sᵢ)`, then `hasDerivAt_finset_sum`. -/
theorem deriv_logSumExp (s : ι → ℝ) (α : ℝ) :
    deriv (λ α => logSumExp s α) α = ∑ i : ι, softmax s α i * s i := by
  simp only [logSumExp, softmax]
  have hZ_pos : 0 < ∑ j : ι, exp (α * s j) := partitionFn_pos s α
  have hZ_ne : (∑ j : ι, exp (α * s j)) ≠ 0 := ne_of_gt hZ_pos
  -- Derivative of each exp(α * s j) w.r.t. α
  have hexp : ∀ j : ι, HasDerivAt (fun a => exp (a * s j))
      (exp (α * s j) * s j) α := by
    intro j
    have h1 : HasDerivAt (fun a => a * s j) (1 * s j) α :=
      (hasDerivAt_id α).mul_const (s j)
    have h2 := (Real.hasDerivAt_exp (α * s j)).comp α h1
    simp only [one_mul] at h2
    exact h2
  -- Derivative of the sum
  have hsum : HasDerivAt (fun a => ∑ j : ι, exp (a * s j))
      (∑ j : ι, exp (α * s j) * s j) α :=
    HasDerivAt.fun_sum fun j _ => hexp j
  -- Derivative of log(sum) via chain rule, then extract
  rw [(hsum.log hZ_ne).deriv, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

-- ── Offset generalizations ──────────────────────────────────────────────
-- These generalize logSumExp/softmax to include per-element offsets rᵢ:
--   logSumExpOffset s r α = log Σ exp(α·sᵢ + rᵢ)
-- This form appears when differentiating the log-partition w.r.t. a single
-- weight wⱼ in a multi-constraint grammar, where
--   sᵢ = contribution of constraint j to candidate i
--   rᵢ = contribution of all other constraints (constant w.r.t. wⱼ)
-- ────────────────────────────────────────────────────────────────────────

/-- Partition function with per-element offsets: `Z(α) = Σⱼ exp(α · sⱼ + rⱼ)`. -/
noncomputable def partitionFnOffset (s r : ι → ℝ) (α : ℝ) : ℝ :=
  ∑ j : ι, exp (α * s j + r j)

theorem partitionFnOffset_pos (s r : ι → ℝ) (α : ℝ) :
    0 < partitionFnOffset s r α :=
  Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty

/-- Log-sum-exp with offsets: `log Σ exp(α · sᵢ + rᵢ)`. -/
noncomputable def logSumExpOffset (s r : ι → ℝ) (α : ℝ) : ℝ :=
  log (partitionFnOffset s r α)

/-- Softmax with offsets: `exp(α · sᵢ + rᵢ) / Z(α)`. -/
noncomputable def softmaxOffset (s r : ι → ℝ) (α : ℝ) (i : ι) : ℝ :=
  exp (α * s i + r i) / partitionFnOffset s r α

/-- Derivative of offset log-partition gives weighted expected value:
    `d/dα log(Σ exp(α·sᵢ + rᵢ)) = Σ softmaxOffset(s,r,α)ᵢ · sᵢ`. -/
theorem hasDerivAt_logSumExpOffset (s r : ι → ℝ) (α : ℝ) :
    HasDerivAt (logSumExpOffset s r)
      (∑ i : ι, softmaxOffset s r α i * s i) α := by
  unfold logSumExpOffset partitionFnOffset softmaxOffset
  have hZ_ne : (∑ j : ι, exp (α * s j + r j)) ≠ 0 :=
    ne_of_gt (partitionFnOffset_pos s r α)
  have hexp : ∀ j : ι, HasDerivAt (fun a => exp (a * s j + r j))
      (exp (α * s j + r j) * s j) α := by
    intro j
    have h1 : HasDerivAt (fun a => a * s j + r j) (s j) α := by
      have := ((hasDerivAt_id α).mul_const (s j)).add_const (r j)
      simpa using this
    exact (Real.hasDerivAt_exp (α * s j + r j)).comp α h1
  have hsum : HasDerivAt (fun a => ∑ j : ι, exp (a * s j + r j))
      (∑ j : ι, exp (α * s j + r j) * s j) α :=
    HasDerivAt.fun_sum fun j _ => hexp j
  convert hsum.log hZ_ne using 1
  simp only [partitionFnOffset]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The offset log-partition function is convex in α.

Same Hölder argument as `logSumExp_convex`: the key factoring
`exp((ax+by)·sᵢ + rᵢ) = exp(x·sᵢ + rᵢ)^a · exp(y·sᵢ + rᵢ)^b`
holds because `a + b = 1`, absorbing the offset. -/
theorem logSumExpOffset_convex (s r : ι → ℝ) :
    ConvexOn ℝ Set.univ (logSumExpOffset s r) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    unfold logSumExpOffset partitionFnOffset
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp [show b = 1 from by linarith]
    rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp [show a = 1 from by linarith]
    have hexp_split : ∀ i, exp ((a * x + b * y) * s i + r i) =
        (exp (x * s i + r i)) ^ a * (exp (y * s i + r i)) ^ b := by
      intro i
      rw [← exp_mul, ← exp_mul, ← exp_add]
      congr 1
      linear_combination -(r i) * hab
    have hpq : a⁻¹.HolderConjugate b⁻¹ := HolderConjugate.inv_inv ha_pos hb_pos hab
    have holder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ (α := ι)) hpq
      (f := fun i => (exp (x * s i + r i)) ^ a)
      (g := fun i => (exp (y * s i + r i)) ^ b)
      (fun i _ => rpow_nonneg (le_of_lt (exp_pos _)) a)
      (fun i _ => rpow_nonneg (le_of_lt (exp_pos _)) b)
    conv at holder => lhs; arg 2; ext i; rw [← hexp_split]
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have hsimp_f : ∀ i, ((exp (x * s i + r i)) ^ a) ^ a⁻¹ = exp (x * s i + r i) := by
      intro i
      rw [← rpow_mul (le_of_lt (exp_pos _)), mul_inv_cancel₀ ha_ne, rpow_one]
    have hsimp_g : ∀ i, ((exp (y * s i + r i)) ^ b) ^ b⁻¹ = exp (y * s i + r i) := by
      intro i
      rw [← rpow_mul (le_of_lt (exp_pos _)), mul_inv_cancel₀ hb_ne, rpow_one]
    simp_rw [hsimp_f, hsimp_g] at holder
    simp only [one_div, inv_inv] at holder
    have hZ_x : (0 : ℝ) < ∑ i : ι, exp (x * s i + r i) := partitionFnOffset_pos s r x
    have hZ_y : (0 : ℝ) < ∑ i : ι, exp (y * s i + r i) := partitionFnOffset_pos s r y
    have hZ_mid : 0 < ∑ j : ι, exp ((a * x + b * y) * s j + r j) :=
      partitionFnOffset_pos s r (a * x + b * y)
    have hlog_le := log_le_log hZ_mid holder
    rw [log_mul (ne_of_gt (rpow_pos_of_pos hZ_x a)) (ne_of_gt (rpow_pos_of_pos hZ_y b)),
        log_rpow hZ_x, log_rpow hZ_y] at hlog_le
    linarith

/-- The log conditional likelihood `α ↦ (α · sᵧ + rᵧ) − logSumExpOffset(s,r,α)`
    is concave (affine minus convex). -/
theorem logConditional_concaveOn (s r : ι → ℝ) (y : ι) :
    ConcaveOn ℝ Set.univ
      (fun α => (α * s y + r y) - logSumExpOffset s r α) := by
  apply ConcaveOn.sub
  · constructor
    · exact convex_univ
    · intro x _ z _ a b ha hb hab
      simp only [smul_eq_mul]
      nlinarith [show a * r y + b * r y = r y from by linear_combination (r y) * hab]
  · exact logSumExpOffset_convex s r

/-- The derivative of log conditional likelihood `α ↦ (α·sᵧ + rᵧ) − logSumExpOffset`
    is the observed feature value minus the expected value:
    `d/dα = sᵧ − Σᵢ softmaxOffset(s,r,α)ᵢ · sᵢ`. -/
theorem hasDerivAt_logConditional (s r : ι → ℝ) (y : ι) (α : ℝ) :
    HasDerivAt (fun w => (w * s y + r y) - logSumExpOffset s r w)
      (s y - ∑ i : ι, softmaxOffset s r α i * s i) α := by
  have h_affine : HasDerivAt (fun a => a * s y + r y) (s y) α := by
    have := ((hasDerivAt_id α).mul_const (s y)).add_const (r y)
    simpa using this
  exact h_affine.sub (hasDerivAt_logSumExpOffset s r α)

/-- Strong duality: max entropy = min free energy. -/
theorem max_entropy_duality (s : ι → ℝ) (c : ℝ)
    (α : ℝ) (_hα : 0 < α) (h_constraint : ∑ i : ι, softmax s α i * s i = c) :
    shannonEntropy (softmax s α) = log (partitionFn s α) - α * c := by
  rw [shannonEntropy_softmax, h_constraint]

end Entropy

-- ============================================================================
-- §5. Bayesian Optimality
-- ============================================================================

section BayesianOptimality

variable {ι : Type*} [Fintype ι]

/-- **Bayesian optimality**: The normalized posterior maximizes weighted log-likelihood
on the probability simplex.

For weights wᵢ ≥ 0 with C = Σwᵢ > 0, and any distribution L on the simplex
(Lᵢ > 0, Σ Lᵢ = 1), the normalized posterior p*ᵢ = wᵢ/C satisfies:

  Σᵢ wᵢ · log(Lᵢ) ≤ Σᵢ wᵢ · log(p*ᵢ)

This is used for listener optimality: with wᵢ = P(m)·S(u|m), the
Bayesian listener L*(m|u) = wᵢ/C maximizes Σ_m P(m)·S(u|m)·log L(m|u). -/
theorem bayesian_maximizes (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hC_pos : 0 < ∑ i, w i)
    (L : ι → ℝ) (hL_pos : ∀ i, 0 < L i) (hL_sum : ∑ i, L i = 1) :
    ∑ i, w i * log (L i) ≤ ∑ i, w i * log (w i / ∑ j, w j) := by
  set C := ∑ i, w i with hC_def
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hp_nonneg : ∀ i, 0 ≤ w i / C := λ i => div_nonneg (hw_nonneg i) (le_of_lt hC_pos)
  have hp_sum : ∑ i, w i / C = 1 := by rw [← Finset.sum_div, div_self hC_ne]
  have hkl : 0 ≤ klFinite (λ i => w i / C) L :=
    kl_nonneg _ L hL_pos hp_nonneg (by rw [hp_sum, hL_sum])
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

end BayesianOptimality

-- ============================================================================
-- §6. Uniqueness Characterization (converse of Theorem 4)
-- ============================================================================

/-!
## Uniqueness of the Ratio Scale

Theorem 4 (proved earlier as `policy_eq_of_proportional`) shows that
proportional scores yield the same policy. The converse — that identical
policies force proportional scores — completes the uniqueness characterization:
**same policy ↔ proportional scores**, with proportionality constant
`k = totalScore₂/totalScore₁`.

Note: This is distinct from the "Independence-of-Unit Condition" in §1.F
(pp. 28–33), which concerns state-dependent transformations f satisfying
f(kv) = kf(v). That condition addresses how scale values transform across
experimental conditions, not the uniqueness of the scale within a condition.
-/

section UniquenessCharacterization

variable {S A : Type*} [Fintype A]

/-- Converse of Theorem 4 (uniqueness of ratio scale):
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

/-- Full uniqueness characterization (Theorem 4 and its converse):
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

-- ============================================================================
-- §7. Appendix 1: Alternative Forms of Axiom 1 (pp. 129–132)
-- ============================================================================

/-!
## Alternative Forms of Axiom 1

proves three equivalent formulations of the choice
axiom:

**(a) Ratio form**: There exists a positive function `v` such that
`P(x, T) = v(x) / Σ_{y∈T} v(y)` for all `x ∈ T`.

**(b) Product rule**: `P(x, T) = P(x, S) · P(S, T)` for `x ∈ S ⊆ T`,
where `P(S, T) = Σ_{y∈S} P(y, T)`.

**(c) Pairwise independence**: The odds ratio `P(x,{x,y}) · P(y,T) =
P(y,{x,y}) · P(x,T)` — pairwise ratios are preserved in any superset.

The ratio form (a) is the definition of `RationalAction`; (a)→(b) is
`product_rule` and (a)→(c) is `pChoice_ratio`.
-/

section Appendix1

variable {A : Type*} [DecidableEq A]

/-- A general choice function on finite subsets: the minimal structure for
    stating Axiom 1 equivalences without assuming a ratio scale a priori. -/
structure ChoiceFn (A : Type*) [DecidableEq A] where
  /-- P(a, T): probability of choosing `a` from set `T` -/
  prob : Finset A → A → ℝ
  /-- Probabilities are non-negative -/
  prob_nonneg : ∀ (T : Finset A) (a : A), 0 ≤ prob T a
  /-- Zero probability outside the choice set -/
  prob_zero_outside : ∀ (T : Finset A) (a : A), a ∉ T → prob T a = 0

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

/-- (a) → (b): Ratio form implies product rule (Appendix 1). -/
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

/-- (a) → (c): Ratio form implies pairwise IIA (Appendix 1). -/
theorem ratio_implies_pairwiseIIA (cf : ChoiceFn A)
    (h : cf.hasRatioScale) : cf.hasPairwiseIIA := by
  intro T a b ha hb
  obtain ⟨v, hv_pos, hv_rule⟩ := h
  have hab_a : a ∈ ({a, b} : Finset A) := Finset.mem_insert.mpr (Or.inl rfl)
  have hab_b : b ∈ ({a, b} : Finset A) := by simp
  rw [hv_rule T a ha, hv_rule T b hb,
      hv_rule {a, b} b hab_b, hv_rule {a, b} a hab_a]
  ring

/-- (c) → (a): Pairwise IIA implies ratio form (Appendix 1).
    The ratio scale is constructed by fixing a reference element x₀ and
    setting v(x) = P(x, {x, x₀}) / P(x₀, {x, x₀}). Requires normalization
    (probabilities sum to 1) and strict positivity for elements in the choice set. -/
theorem pairwiseIIA_implies_ratio [Inhabited A] (cf : ChoiceFn A)
    (hIIA : cf.hasPairwiseIIA)
    (hsum : ∀ (T : Finset A), T.Nonempty → ∑ a ∈ T, cf.prob T a = 1)
    (hpos : ∀ (T : Finset A) (a : A), a ∈ T → 0 < cf.prob T a) :
    cf.hasRatioScale := by
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

/-- **Axiom 1 equivalence** (Appendix 1):
    Ratio form ↔ pairwise IIA (under normalization and positivity). -/
theorem axiom1_ratio_iff_pairwiseIIA [Inhabited A] (cf : ChoiceFn A)
    (hsum : ∀ (T : Finset A), T.Nonempty → ∑ a ∈ T, cf.prob T a = 1)
    (hpos : ∀ (T : Finset A) (a : A), a ∈ T → 0 < cf.prob T a) :
    cf.hasRatioScale ↔ cf.hasPairwiseIIA :=
  ⟨ratio_implies_pairwiseIIA cf, fun h => pairwiseIIA_implies_ratio cf h hsum hpos⟩

end Appendix1

end Core
