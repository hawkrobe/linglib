import Linglib.Semantics.Mereology

/-!
# Admissible measures and dimensional restriction

The monotonicity requirement on measure functions, and the
order-theoretic content of dimension availability.

## Main declarations

* `admissibleMeasure` — the multi-tradition monotonicity condition on a
  measure function: mathlib's `StrictMono`, named once.
* `DimensionallyRestricted` — any two admissible measures agree on the
  comparative ordering; holds exactly on linear orders
  (`linearOrder_dimensionallyRestricted` /
  `prod_not_dimensionallyRestricted`).
-/

namespace Degree

/-- The monotonicity-preservation requirement on measure functions used in
    monotonicity-requiring constructions: `μ` is admissible for a background
    ordering iff `s₁ ≺ s₂` entails `μ(s₁) < μ(s₂)`. This is Mathlib's
    `StrictMono`.

    **Single-name canonical Prop for a multi-tradition convergence.** This
    one Prop names the same condition that appears under different labels
    across the literature; linglib hosts it once here and lets every
    consumer credit its own source:

    - [schwarzschild-2002] [schwarzschild-2006] — *Monotonicity Constraint*
      on the measure function in nominal pseudopartitives.
    - [krifka-1989] — extensive measure functions on quantized objects.
    - [wellwood-2015] — `μ` admissibility for `much`-comparatives;
      `admissibleMeasure_of_mereoDim` bridges to the bundled `MereoDim`
      typeclass.
    - [cariani-santorio-wellwood-2024] (eq. 21) — CSW use this exact
      formulation for confidence orderings.
    - [pasternak-2019] (def 4) — `μ_int` monotonicity on the
      part-whole structure of mental states.
    - [ying-zhi-xuan-wong-mansinghka-tenenbaum-2025] —
      `EpistemicThreshold.isProbabilistic` is a strengthening of this
      (Monotone, not StrictMono).

    The bundled-typeclass form is `MereoDim` in `Semantics/Mereology.lean`
    (with `[PartialOrder]` carriers); the unbundled-Prop form is here
    (with `[Preorder]`, more permissive). Use `MereoDim` when typeclass
    inference is desired; use `admissibleMeasure` when the witness is
    passed explicitly. -/
abbrev admissibleMeasure {S D : Type*} [Preorder S] [Preorder D]
    (μ : S → D) : Prop :=
  StrictMono μ

/-- Every `MereoDim` witness yields the unbundled `admissibleMeasure` Prop
    (`MereoDim` bundles `StrictMono` with `[PartialOrder]` carriers). -/
theorem admissibleMeasure_of_mereoDim
    {A D : Type*} [PartialOrder A] [PartialOrder D]
    {μ : A → D} (h : Mereology.MereoDim μ) :
    admissibleMeasure μ :=
  h.toStrictMono

/-! ### Dimensional restriction -/

/-- A domain is dimensionally restricted when any two admissible measure
    functions (`StrictMono` maps to ℚ) agree on the comparative ordering
    of all elements: the comparative is determined by the background
    ordering alone, not by the choice of measure.

    Dimensional restriction holds iff the ambient preorder is total: the
    forward direction is `linearOrder_dimensionallyRestricted`; the
    converse is witnessed by incomparable elements with disagreeing
    measures (`prod_not_dimensionallyRestricted`). -/
def DimensionallyRestricted (α : Type*) [Preorder α] : Prop :=
  ∀ (μ₁ μ₂ : α → ℚ), StrictMono μ₁ → StrictMono μ₂ →
    ∀ (a b : α), μ₁ a < μ₁ b ↔ μ₂ a < μ₂ b

/-- Linear orders are dimensionally restricted: the comparative ordering
    is uniquely determined by the ambient order, regardless of which
    admissible measure function is chosen. -/
theorem linearOrder_dimensionallyRestricted {α : Type*} [LinearOrder α] :
    DimensionallyRestricted α :=
  fun _ _ hμ₁ hμ₂ _ _ => hμ₁.lt_iff_lt.trans hμ₂.lt_iff_lt.symm

/-- If two admissible measures disagree on some pair, the domain is NOT
    dimensionally restricted. -/
theorem not_restricted_of_disagreement {α : Type*} [Preorder α]
    {μ₁ μ₂ : α → ℚ} (hμ₁ : StrictMono μ₁) (hμ₂ : StrictMono μ₂)
    {a b : α} (h₁ : μ₁ a < μ₁ b) (h₂ : ¬ μ₂ a < μ₂ b) :
    ¬ DimensionallyRestricted α :=
  fun hDR => h₂ ((hDR μ₁ μ₂ hμ₁ hμ₂ a b).mp h₁)

/-- The converse witness: on the componentwise-ordered `ℚ × ℚ` (weight ×
    volume), the admissible measures `2·w + v` and `w + v` order the
    incomparable elements `(0, 1)` and `(1, 0)` differently — the
    multi-dimensional signature of entity/event domains. -/
theorem prod_not_dimensionallyRestricted :
    ¬ DimensionallyRestricted (ℚ × ℚ) := by
  have hmono : ∀ c : ℚ, 0 < c → StrictMono (fun p : ℚ × ℚ => c * p.1 + p.2) := by
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
