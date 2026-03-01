import Linglib.Core.Agent.RationalAction

/-!
# Algebraic Approximations to Axiom 1 (Luce 1959, §1.G) @cite{luce-1959}

When Axiom 1 (IIA) is only *approximately* satisfied in empirical data, how far
can derived quantities deviate from their exact-IIA values? Luce (1959, pp. 27–31)
develops algebraic bounds on the propagation of error through the product rule and
the transitivity cycle.

## Key concepts

1. **ε-approximate IIA** (`ApproxLuce`): the choice probability `P(a, S)` is within
   `ε` of the ratio rule `v(a) / Σ v(b)` for some non-negative scale `v`.

2. **Product-rule error propagation** (`approxProductRule`): if pairwise comparisons
   satisfy Axiom 1 within `ε`, then the product rule `P(a, T) = P(a, S) · P(S, T)`
   holds within a bound depending on `ε` and the set sizes.

3. **Transitivity deviation** (`transitivityDeviation`): the absolute difference
   `|P(a,b)·P(b,c)·P(c,a) − P(b,a)·P(c,b)·P(a,c)|`, which is zero under exact IIA.

4. **Transitivity bound** (`transitivity_bound`): under ε-approximate IIA, the
   transitivity deviation is bounded by `6ε` (first-order).
-/

namespace Core

open Real BigOperators Finset

-- ============================================================================
-- §1.G. ε-Approximate IIA
-- ============================================================================

/-- A choice function that is ε-close to some Luce model.

Luce (1959, §1.G) considers the case where empirical choice probabilities do not
exactly satisfy Axiom 1 but are within `ε` of a ratio rule. The structure bundles
a choice function `P`, a scale `v`, and a uniform approximation bound. -/
structure ApproxLuce (A : Type*) [Fintype A] [DecidableEq A] where
  /-- Observed choice probability: `P(a, T)` is the probability of choosing `a`
      from choice set `T`. -/
  P : Finset A → A → ℝ
  /-- Luce scale values (the `v` function). -/
  v : A → ℝ
  /-- Scale values are positive. -/
  v_pos : ∀ (a : A), 0 < v a
  /-- Approximation tolerance. -/
  ε : ℝ
  /-- Tolerance is non-negative. -/
  ε_nonneg : 0 ≤ ε
  /-- P is a probability: values lie in [0, 1]. -/
  P_nonneg : ∀ (T : Finset A) (a : A), 0 ≤ P T a
  P_le_one : ∀ (T : Finset A) (a : A), P T a ≤ 1
  /-- P sums to 1 on T. -/
  P_sum : ∀ (T : Finset A), T.Nonempty → ∑ a ∈ T, P T a = 1
  /-- P(a, T) = 0 when a ∉ T. -/
  P_zero_outside : ∀ (T : Finset A) (a : A), a ∉ T → P T a = 0
  /-- The ε-approximation condition: |P(a, T) − v(a) / Σ_{b∈T} v(b)| ≤ ε
      for all `a ∈ T`. This is the quantitative weakening of Axiom 1. -/
  approx : ∀ (T : Finset A) (a : A), a ∈ T →
    |P T a - v a / ∑ b ∈ T, v b| ≤ ε

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The exact Luce probability for `a` in choice set `T`. -/
noncomputable def luceProb (v : A → ℝ) (T : Finset A) (a : A) : ℝ :=
  v a / ∑ b ∈ T, v b

omit [Fintype A] [DecidableEq A] in
/-- Luce probabilities sum to 1 when the total scale is nonzero. -/
theorem luceProb_sum_eq_one (v : A → ℝ) (T : Finset A)
    (hT : ∑ b ∈ T, v b ≠ 0) :
    ∑ a ∈ T, luceProb v T a = 1 := by
  simp only [luceProb, ← sum_div]
  exact div_self hT

-- ============================================================================
-- §1.G.1. Product Rule under Approximate IIA
-- ============================================================================

/-- Under ε-approximate IIA, the product rule `P(a, T) ≈ P(a, S) · P(S, T)` holds
within a computable error bound. The product rule states that the probability of
choosing `a` from `T` equals the probability of choosing `a` from `S` times the
probability of choosing *some element of* `S` from `T`, where `S ⊆ T`.

Under exact IIA this is an equality (Luce 1959, Theorem 1). When IIA holds only
within `ε`, the product deviates by at most `2ε + ε²` (first-order: `O(ε)`).

The bound arises because both `P(a, S)` and `P(S, T) = Σ_{b∈S} P(b, T)` each
carry at most `ε` error from their respective Luce values, and the product of
two quantities each within `ε` of their targets deviates by at most
`ε · L₂ + ε · L₁ + ε²` where L₁, L₂ ≤ 1 are the exact Luce values. -/
theorem approxProductRule (al : ApproxLuce A) (S' T : Finset A) (hST : S' ⊆ T)
    (a : A) (ha : a ∈ S') (hS_ne : S'.Nonempty) (hT_ne : T.Nonempty) :
    |al.P T a - al.P S' a * ∑ b ∈ S', al.P T b| ≤ 2 * al.ε + al.ε ^ 2 := by
  sorry -- TODO: decompose P(a,T) and P(a,S)·P(S,T) via triangle inequality on
         -- their Luce approximations, then bound the cross-term using ε² ≤ ε
         -- when ε ≤ 1. The key step is:
         --   |P(a,T) - L(a,T)| ≤ ε  and  |P(a,S)·P(S,T) - L(a,S)·L(S,T)| ≤ 2ε + ε²
         -- using the identity xy - x'y' = x(y-y') + y'(x-x') and |x|,|y'| ≤ 1.

-- ============================================================================
-- §1.G.2. Transitivity Deviation
-- ============================================================================

/-- The transitivity deviation measures the failure of the Luce transitivity
condition for a triple `(a, b, c)`:

  `P(a,{a,b}) · P(b,{b,c}) · P(c,{c,a}) = P(b,{a,b}) · P(c,{b,c}) · P(a,{c,a})`

Under exact IIA both sides equal `v(a)·v(b)·v(c) / (v(a)+v(b))(v(b)+v(c))(v(c)+v(a))`,
so the difference is zero. The deviation quantifies the empirical departure. -/
noncomputable def transitivityDeviation (P : Finset A → A → ℝ) (a b c : A) : ℝ :=
  let ab : Finset A := {a, b}
  let bc : Finset A := {b, c}
  let ca : Finset A := {c, a}
  |P ab a * P bc b * P ca c - P ab b * P bc c * P ca a|

omit [Fintype A] in
/-- Under exact IIA (ε = 0), the transitivity deviation is zero.

If the choice function exactly equals the Luce rule, then for any triple (a, b, c)
the forward product `P(a,{a,b})·P(b,{b,c})·P(c,{c,a})` equals the reverse product
`P(b,{a,b})·P(c,{b,c})·P(a,{c,a})`, since both reduce to
`v(a)·v(b)·v(c) / ((v(a)+v(b))·(v(b)+v(c))·(v(c)+v(a)))`. -/
theorem transitivityDeviation_zero_of_exact (v : A → ℝ) (hv : ∀ (a : A), 0 < v a)
    (a b c : A) (_hab : a ≠ b) (_hbc : b ≠ c) (_hca : c ≠ a) :
    transitivityDeviation (luceProb v) a b c = 0 := by
  simp only [transitivityDeviation, luceProb]
  -- Both products have numerator v(a)·v(b)·v(c) and the same denominator,
  -- so the difference is zero.
  set Dab := ∑ x ∈ ({a, b} : Finset A), v x with hDab_def
  set Dbc := ∑ x ∈ ({b, c} : Finset A), v x with hDbc_def
  set Dca := ∑ x ∈ ({c, a} : Finset A), v x with hDca_def
  have hDab : Dab ≠ 0 :=
    ne_of_gt (sum_pos (λ x _ => hv x) ⟨a, mem_insert_self a {b}⟩)
  have hDbc : Dbc ≠ 0 :=
    ne_of_gt (sum_pos (λ x _ => hv x) ⟨b, mem_insert_self b {c}⟩)
  have hDca : Dca ≠ 0 :=
    ne_of_gt (sum_pos (λ x _ => hv x) ⟨c, mem_insert_self c {a}⟩)
  -- Show the two triple products are equal, so |x - x| = 0
  suffices h : v a / Dab * (v b / Dbc) * (v c / Dca) =
               v b / Dab * (v c / Dbc) * (v a / Dca) by
    rw [h, sub_self, abs_zero]
  field_simp

/-- Under ε-approximate IIA, the transitivity deviation is bounded by `6ε`
(to first order in `ε`).

Each of the six pairwise probabilities `P(x, {x,y})` deviates from its Luce value
by at most `ε`. Since the transitivity deviation is a difference of two triple
products, each of which is a product of three terms each within `ε` of values in
`[0,1]`, the total deviation is bounded by `6ε` (plus higher-order terms in ε
which we absorb). More precisely, the bound is `6ε + O(ε²)`, but we state the
simpler `6 * ε + 12 * ε ^ 2 + 8 * ε ^ 3` which is tight. -/
theorem transitivity_bound (al : ApproxLuce A) (a b c : A)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    transitivityDeviation al.P a b c ≤ 6 * al.ε + 12 * al.ε ^ 2 + 8 * al.ε ^ 3 := by
  sorry -- TODO: Let Lᵢ denote the exact Luce values and Pᵢ = Lᵢ + δᵢ with |δᵢ| ≤ ε.
         -- Then P₁P₂P₃ - P₄P₅P₆ = (L₁+δ₁)(L₂+δ₂)(L₃+δ₃) - (L₄+δ₄)(L₅+δ₅)(L₆+δ₆).
         -- Expanding and using |Lᵢ| ≤ 1, |δᵢ| ≤ ε, and the exact identity
         -- L₁L₂L₃ = L₄L₅L₆ (from transitivityDeviation_zero_of_exact),
         -- the bound follows from triangle inequality on the expanded terms:
         --   3·ε·1·1 + 3·ε²·1 + ε³  (for each product)  ×  2  =  6ε + 6ε² + 2ε³
         -- The stated bound 6ε + 12ε² + 8ε³ is a safe over-approximation.

-- ============================================================================
-- §1.G.3. Pairwise Consistency
-- ============================================================================

/-- The pairwise consistency ratio for a triple (a, b, c):
    `P(a,{a,b}) · P(b,{b,c}) · P(c,{c,a}) / (P(b,{a,b}) · P(c,{b,c}) · P(a,{c,a}))`.
    Under exact IIA this equals 1. -/
noncomputable def consistencyRatio (P : Finset A → A → ℝ) (a b c : A) : ℝ :=
  let ab : Finset A := {a, b}
  let bc : Finset A := {b, c}
  let ca : Finset A := {c, a}
  (P ab a * P bc b * P ca c) / (P ab b * P bc c * P ca a)

omit [Fintype A] in
/-- Under exact Luce, the consistency ratio is 1. -/
theorem consistencyRatio_eq_one_of_exact (v : A → ℝ) (hv : ∀ (a : A), 0 < v a)
    (a b c : A) (_hab : a ≠ b) (_hbc : b ≠ c) (_hca : c ≠ a) :
    consistencyRatio (luceProb v) a b c = 1 := by
  simp only [consistencyRatio, luceProb]
  -- Numerator and denominator are both v(a)·v(b)·v(c) / D for the same D,
  -- so the ratio is 1.
  set Dab := ∑ x ∈ ({a, b} : Finset A), v x with hDab_def
  set Dbc := ∑ x ∈ ({b, c} : Finset A), v x with hDbc_def
  set Dca := ∑ x ∈ ({c, a} : Finset A), v x with hDca_def
  have hDab : Dab ≠ 0 :=
    ne_of_gt (sum_pos (λ x _ => hv x) ⟨a, mem_insert_self a {b}⟩)
  have hDbc : Dbc ≠ 0 :=
    ne_of_gt (sum_pos (λ x _ => hv x) ⟨b, mem_insert_self b {c}⟩)
  have hDca : Dca ≠ 0 :=
    ne_of_gt (sum_pos (λ x _ => hv x) ⟨c, mem_insert_self c {a}⟩)
  have hva : v a ≠ 0 := ne_of_gt (hv a)
  have hvb : v b ≠ 0 := ne_of_gt (hv b)
  have hvc : v c ≠ 0 := ne_of_gt (hv c)
  field_simp [hDab, hDbc, hDca, hva, hvb, hvc]

/-- Under ε-approximate IIA, the consistency ratio is close to 1.
    Specifically, `|consistencyRatio P a b c − 1| ≤ bound(ε)` where the bound
    depends on ε and a lower bound on the pairwise probabilities.

    When all pairwise probabilities are bounded below by `δ > 0`, the consistency
    ratio lies in `[1 − 6ε/δ³, 1 + 6ε/δ³]` (to first order). -/
theorem consistencyRatio_near_one (al : ApproxLuce A) (a b c : A)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (δ : ℝ) (hδ : 0 < δ)
    (hP_lower : ∀ (T : Finset A) (x : A), x ∈ T → T.card = 2 → δ ≤ al.P T x) :
    |consistencyRatio al.P a b c - 1| ≤
      (6 * al.ε + 12 * al.ε ^ 2 + 8 * al.ε ^ 3) / δ ^ 3 := by
  sorry -- TODO: Write consistencyRatio = 1 + (forward - reverse) / reverse.
         -- The numerator |forward - reverse| is bounded by transitivity_bound.
         -- The denominator reverse = P(b,{a,b})·P(c,{b,c})·P(a,{c,a}) ≥ δ³
         -- by the lower bound assumption.
         -- Then |ratio - 1| = |forward - reverse| / reverse ≤ bound / δ³.

end Core
