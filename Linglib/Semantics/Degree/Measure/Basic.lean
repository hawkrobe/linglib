module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Admissible measures and dimensional restriction

A measure function is admissible for a background ordering if it is strictly monotone, and a
domain is dimensionally restricted if any two admissible measures order its elements alike.
Linear orders are dimensionally restricted, and multi-dimensional orders such as weight × volume
are not.

## Main definitions

* `admissibleMeasure`: strict monotonicity of a measure function.
* `DimensionallyRestricted`: any two admissible measures agree on the comparative ordering.

## Main results

* `admissibleMeasure.reflect_le`: on a total preorder an admissible measure reflects the order.
* `linearOrder_dimensionallyRestricted`, `prod_not_dimensionallyRestricted`: linear orders are
  dimensionally restricted, and a product order is not.

## References

* [schwarzschild-2002], [schwarzschild-2006], [krifka-1989], [wellwood-2015],
  [cariani-santorio-wellwood-2024], [pasternak-2019]
-/

@[expose] public section

namespace Degree

/-- A measure function `μ` is admissible for a background ordering if `s₁ < s₂` entails
`μ s₁ < μ s₂`, that is, if it is strictly monotone. The condition recurs under several names, as
the Monotonicity Constraint of [schwarzschild-2002] and [schwarzschild-2006] on measures in
pseudopartitives, admissibility of the measure of *much* in [wellwood-2015], the confidence
orderings of [cariani-santorio-wellwood-2024] (eq. 21), and the monotonicity of `μ_int` on mental
states in [pasternak-2019] (def 4). The extensive measures of [krifka-1989] have it over parts
with remainders (`Mereology.IsExtensiveMeasure.strictMono`). -/
abbrev admissibleMeasure {S D : Type*} [Preorder S] [Preorder D]
    (μ : S → D) : Prop :=
  StrictMono μ

/-- On a total preorder an admissible measure reflects the ordering, so a state measuring at
most another lies below it. The converse fails for tied states, which admissibility leaves free to
be measured apart. -/
theorem admissibleMeasure.reflect_le {S D : Type*} [Preorder S] [@Std.Total S (· ≤ ·)]
    [Preorder D] {μ : S → D} (hμ : admissibleMeasure μ) {a b : S} (h : μ a ≤ μ b) : a ≤ b :=
  (total_of (· ≤ ·) a b).elim id fun hba ↦
    by_contra fun hab ↦ (hμ (lt_of_le_not_ge hba hab)).not_ge h

/-! ### Dimensional restriction -/

/-- A domain is dimensionally restricted if any two admissible measure functions into the scale
`D` agree on the comparative ordering of all its elements, so that the background ordering alone
determines the comparative. Linear orders are dimensionally restricted
(`linearOrder_dimensionallyRestricted`), and the componentwise order on `D × D` is not
(`prod_not_dimensionallyRestricted`). -/
def DimensionallyRestricted (α : Type*) [Preorder α] (D : Type := ℝ) [Preorder D] : Prop :=
  ∀ (μ₁ μ₂ : α → D), StrictMono μ₁ → StrictMono μ₂ →
    ∀ (a b : α), μ₁ a < μ₁ b ↔ μ₂ a < μ₂ b

/-- Linear orders are dimensionally restricted, since the ambient order determines the
comparative ordering whichever admissible measure function is chosen. -/
theorem linearOrder_dimensionallyRestricted {α : Type*} [LinearOrder α] {D : Type} [Preorder D] :
    DimensionallyRestricted α D :=
  fun _ _ hμ₁ hμ₂ _ _ => hμ₁.lt_iff_lt.trans hμ₂.lt_iff_lt.symm

/-- If two admissible measures disagree on some pair, the domain is NOT
    dimensionally restricted. -/
theorem not_restricted_of_disagreement {α : Type*} [Preorder α] {D : Type} [Preorder D]
    {μ₁ μ₂ : α → D} (hμ₁ : StrictMono μ₁) (hμ₂ : StrictMono μ₂)
    {a b : α} (h₁ : μ₁ a < μ₁ b) (h₂ : ¬ μ₂ a < μ₂ b) :
    ¬ DimensionallyRestricted α D :=
  fun hDR => h₂ ((hDR μ₁ μ₂ hμ₁ hμ₂ a b).mp h₁)

/-- The componentwise-ordered `D × D` (weight × volume) is not dimensionally restricted, since
the admissible measures `2·w + v` and `w + v` order the incomparable elements `(0, 1)` and
`(1, 0)` differently; this is the multi-dimensional signature of entity and event domains. -/
theorem prod_not_dimensionallyRestricted {D : Type} [Field D] [LinearOrder D]
    [IsStrictOrderedRing D] : ¬ DimensionallyRestricted (D × D) D := by
  have hmono : ∀ c : D, 0 < c → StrictMono (fun p : D × D => c * p.1 + p.2) := by
    intro c hc p q hpq
    rcases Prod.lt_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := mul_lt_mul_of_pos_left h1 hc
      dsimp only
      nlinarith
    · have := mul_le_mul_of_nonneg_left h1 hc.le
      dsimp only
      nlinarith
  exact not_restricted_of_disagreement (μ₁ := fun p => 2 * p.1 + p.2)
    (μ₂ := fun p => 1 * p.1 + p.2) (hmono 2 (by norm_num)) (hmono 1 (by norm_num))
    (a := (0, 1)) (b := (1, 0)) (by norm_num) (by norm_num)

end Degree
