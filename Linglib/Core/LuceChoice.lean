import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-!
# Luce Choice Rule (Generic)

The core structure for all soft-rational agents, parameterized over any
ordered field `F` (i.e., `[Field F] [LinearOrder F] [IsStrictOrderedRing F]`).
At `F = ℚ`, all definitions are computable and predictions can be verified via
`native_decide`. At `F = ℝ`, the same definitions serve mathematical
meta-theory (softmax, entropy, KL divergence).

## Architecture

A `RationalAction` agent selects actions with probability proportional to a
non-negative score function — the **Luce choice rule** (Luce 1959). This is the
unique choice rule satisfying IIA (independence of irrelevant alternatives):
the relative probability of two actions depends only on their scores.

We formalize:

1. **Core structure** (§1): `RationalAction`, `policy`, normalization properties
2. **Luce's Choice Axiom** (§1a): IIA, product rule, scale invariance, uniqueness

The ℝ-specific analysis (softmax, Gibbs variational principle, entropy, KL
divergence, Bayesian optimality) lives in `Core.RationalAction`, which imports
this file at `F = ℝ`.

## References

- Luce, R. D. (1959). Individual Choice Behavior.
- Franke, M. & Degen, J. (submitted). The softmax function.
-/

namespace Core

open BigOperators Finset

-- ============================================================================
-- §1. RationalAction: Score-Based Agents
-- ============================================================================

/-- A rational action agent: selects actions with probability ∝ score(state, action).

This is the Luce choice rule (Luce 1959). The `score` function is unnormalized;
normalization to a proper distribution is derived (see `policy`).

Generic over any ordered field `F`:
- At `F = ℚ`: fully computable, supports `native_decide`
- At `F = ℝ`: noncomputable, supports mathematical analysis (softmax, entropy, etc.)

Key instances:
- RSA L0: `score(u, w) = meaning(u, w)`
- RSA S1: `score(w, u) = s1ScoreFn(L0, α, w, u)`
- BToM agent: `score(state, action) = exp(β · Q(state, action))` -/
structure RationalAction (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (State Action : Type*) [Fintype Action] where
  /-- Unnormalized score: policy(a|s) ∝ score(s, a). -/
  score : State → Action → F
  /-- Scores are non-negative. -/
  score_nonneg : ∀ s a, 0 ≤ score s a

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {S A : Type*} [Fintype A]

/-- Total score across all actions in a state (normalization constant). -/
def RationalAction.totalScore (ra : RationalAction F S A) (s : S) : F :=
  ∑ a : A, ra.score s a

theorem RationalAction.totalScore_nonneg (ra : RationalAction F S A) (s : S) :
    0 ≤ ra.totalScore s :=
  Finset.sum_nonneg fun a _ => ra.score_nonneg s a

/-- Normalized policy: P(a|s) = score(s,a) / Σ_a' score(s,a').

Uses Lean's `x / 0 = 0` convention to handle the degenerate case where all
scores are zero, avoiding a `DecidableEq F` dependency. When `totalScore = 0`,
all scores are 0 (by non-negativity), so `0 / 0 = 0`. -/
def RationalAction.policy (ra : RationalAction F S A) (s : S) (a : A) : F :=
  ra.score s a / ra.totalScore s

theorem RationalAction.policy_nonneg (ra : RationalAction F S A) (s : S) (a : A) :
    0 ≤ ra.policy s a :=
  div_nonneg (ra.score_nonneg s a) (ra.totalScore_nonneg s)

/-- Policy sums to 1 when totalScore is nonzero. -/
theorem RationalAction.policy_sum_eq_one (ra : RationalAction F S A) (s : S)
    (h : ra.totalScore s ≠ 0) :
    ∑ a : A, ra.policy s a = 1 := by
  simp only [policy, ← Finset.sum_div]
  exact div_self h

/-- Policy monotonicity: higher score → higher probability. -/
theorem RationalAction.policy_monotone (ra : RationalAction F S A) (s : S)
    (a₁ a₂ : A) (h : ra.score s a₁ ≤ ra.score s a₂) :
    ra.policy s a₁ ≤ ra.policy s a₂ := by
  simp only [policy]
  rcases eq_or_lt_of_le (ra.totalScore_nonneg s) with h0 | hpos
  · simp [show ra.totalScore s = 0 from h0.symm]
  · exact div_le_div_of_nonneg_right h (le_of_lt hpos)

-- ============================================================================
-- §1a. Luce's Choice Axiom (IIA)
-- ============================================================================

/-!
## Luce's Choice Axiom

Luce (1959, Chapter 1) showed that the ratio rule `P(a|s) = v(a)/Σv(b)` is
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

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {S A : Type*} [Fintype A]

/-- Constant Ratio Rule (Luce 1959, Theorem 2):
    `policy(a₁) · score(a₂) = policy(a₂) · score(a₁)`.
    The odds ratio policy(a₁)/policy(a₂) = score(a₁)/score(a₂). -/
theorem RationalAction.policy_ratio (ra : RationalAction F S A) (s : S) (a₁ a₂ : A) :
    ra.policy s a₁ * ra.score s a₂ = ra.policy s a₂ * ra.score s a₁ := by
  simp only [policy, div_mul_eq_mul_div, mul_comm (ra.score s a₁) (ra.score s a₂)]

/-- Choice probability from a subset: `pChoice(a, T) = score(a) / Σ_{b∈T} score(b)`.
    Returns 0 if `a ∉ T`. Uses `x / 0 = 0` for the zero-total case. -/
def RationalAction.pChoice [DecidableEq A] (ra : RationalAction F S A) (s : S)
    (T : Finset A) (a : A) : F :=
  if a ∈ T then ra.score s a / ∑ b ∈ T, ra.score s b
  else 0

/-- `pChoice` on the full set equals `policy`. -/
theorem RationalAction.pChoice_univ [DecidableEq A] (ra : RationalAction F S A)
    (s : S) (a : A) :
    ra.pChoice s Finset.univ a = ra.policy s a := by
  simp only [pChoice, Finset.mem_univ, ↓reduceIte, policy, totalScore]

/-- `pChoice` is non-negative. -/
theorem RationalAction.pChoice_nonneg [DecidableEq A] (ra : RationalAction F S A)
    (s : S) (T : Finset A) (a : A) :
    0 ≤ ra.pChoice s T a := by
  simp only [pChoice]
  split
  · exact div_nonneg (ra.score_nonneg s a)
      (Finset.sum_nonneg fun b _ => ra.score_nonneg s b)
  · exact le_refl 0

/-- `pChoice` sums to 1 over the subset when the subset total is nonzero. -/
theorem RationalAction.pChoice_sum_eq_one [DecidableEq A] (ra : RationalAction F S A)
    (s : S) (T : Finset A) (hT : ∑ b ∈ T, ra.score s b ≠ 0) :
    ∑ a ∈ T, ra.pChoice s T a = 1 := by
  simp only [pChoice]
  have : ∀ a ∈ T, (if a ∈ T then ra.score s a / ∑ b ∈ T, ra.score s b else (0 : F)) =
      ra.score s a / ∑ b ∈ T, ra.score s b :=
    fun a ha => by simp [ha]
  rw [Finset.sum_congr rfl this, ← Finset.sum_div]
  exact div_self hT

/-- IIA core: the ratio of `pChoice` values in any subset equals the score ratio. -/
theorem RationalAction.pChoice_ratio [DecidableEq A] (ra : RationalAction F S A)
    (s : S) (T : Finset A) (a₁ a₂ : A) (h₁ : a₁ ∈ T) (h₂ : a₂ ∈ T) :
    ra.pChoice s T a₁ * ra.score s a₂ = ra.pChoice s T a₂ * ra.score s a₁ := by
  simp only [pChoice, h₁, h₂, ↓reduceIte, div_mul_eq_mul_div,
    mul_comm (ra.score s a₁) (ra.score s a₂)]

/-- Helper: `pChoice` value for `a ∈ T`. -/
private theorem RationalAction.pChoice_mem [DecidableEq A] (ra : RationalAction F S A)
    (s : S) (T : Finset A) (a : A) (ha : a ∈ T) :
    ra.pChoice s T a = ra.score s a / ∑ b ∈ T, ra.score s b := by
  simp only [pChoice, ha, ↓reduceIte]

/-- IIA (Luce 1959, Axiom 1): `P(a, S) = P(a, T) / Σ_{b∈S} P(b, T)` for `S ⊆ T`.
    Choice probability from a subset is the conditional probability. -/
theorem RationalAction.iia [DecidableEq A] (ra : RationalAction F S A) (s : S)
    (S' T : Finset A) (hST : S' ⊆ T)
    (a : A) (ha : a ∈ S')
    (hS_pos : ∑ b ∈ S', ra.score s b ≠ 0)
    (hT_pos : ∑ b ∈ T, ra.score s b ≠ 0) :
    ra.pChoice s S' a = ra.pChoice s T a / ∑ b ∈ S', ra.pChoice s T b := by
  rw [ra.pChoice_mem s S' a ha, ra.pChoice_mem s T a (hST ha)]
  have hsum : ∑ b ∈ S', ra.pChoice s T b =
      (∑ b ∈ S', ra.score s b) / ∑ c ∈ T, ra.score s c := by
    have : ∀ b ∈ S', ra.pChoice s T b = ra.score s b / ∑ c ∈ T, ra.score s c :=
      fun b hb => ra.pChoice_mem s T b (hST hb)
    rw [Finset.sum_congr rfl this, Finset.sum_div]
  rw [hsum]
  field_simp

/-- Product rule (Luce 1959, Theorem 1):
    `P(a, T) = P(a, S) · P(S, T)` for `a ∈ S ⊆ T`,
    where `P(S, T) = Σ_{b∈S} score(b) / Σ_{b∈T} score(b)`. -/
theorem RationalAction.product_rule [DecidableEq A] (ra : RationalAction F S A) (s : S)
    (S' T : Finset A) (hST : S' ⊆ T)
    (a : A) (ha : a ∈ S')
    (hS_pos : ∑ b ∈ S', ra.score s b ≠ 0)
    (_hT_pos : ∑ b ∈ T, ra.score s b ≠ 0) :
    ra.pChoice s T a =
    ra.pChoice s S' a * ((∑ b ∈ S', ra.score s b) / ∑ b ∈ T, ra.score s b) := by
  rw [ra.pChoice_mem s T a (hST ha), ra.pChoice_mem s S' a ha]
  rw [div_mul_div_comm, mul_comm (ra.score s a) _, mul_div_mul_left _ _ hS_pos]

/-- Scale all scores by a positive constant `k`. -/
def RationalAction.scaleBy (ra : RationalAction F S A) (k : F) (hk : 0 < k) :
    RationalAction F S A where
  score s a := k * ra.score s a
  score_nonneg s a := mul_nonneg (le_of_lt hk) (ra.score_nonneg s a)

/-- Scale invariance (Luce 1959, Theorem 5): scaling scores by `k > 0` preserves policy. -/
theorem RationalAction.scaleBy_policy (ra : RationalAction F S A) (s : S) (a : A)
    (k : F) (hk : 0 < k) :
    (ra.scaleBy k hk).policy s a = ra.policy s a := by
  simp only [policy, scaleBy, totalScore, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt hk)

/-- Uniqueness (forward direction, Luce 1959, Theorem 4):
    If scores are proportional (`score'(s,a) = k · score(s,a)` for some `k > 0`),
    then both agents have the same policy. -/
theorem RationalAction.policy_eq_of_proportional (ra ra' : RationalAction F S A) (s : S)
    (k : F) (hk : 0 < k) (h : ∀ a, ra'.score s a = k * ra.score s a) (a : A) :
    ra'.policy s a = ra.policy s a := by
  simp only [policy, totalScore]
  simp_rw [h, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt hk)

end LuceChoiceAxiom

end Core
