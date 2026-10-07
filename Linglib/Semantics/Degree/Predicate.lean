module

public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Max
public import Mathlib.Logic.Function.Const
public import Mathlib.Tactic.NormNum
public import Linglib.Semantics.Degree.Boundedness
public import Linglib.Semantics.Degree.Comparison

/-!
# Degree predicates

A measure `μ : W → α` and a degree `d` determine five degree predicates, the meanings of
*exactly*, *at least*, *more than*, *at most* and *less than*: the sets
`Degree.Comparison.{eq,ge,gt,le,lt}.over μ d`. Kennedy gives modified and bare numerals one
denotation that differs only in this comparison relation, and Geurts and Nouwen's split between
Class A and Class B modifiers is whether the relation keeps its boundary.

A family of propositions indexed by degrees is upward monotone when it is `Monotone` under the
pointwise order on `W → Prop`, and downward monotone when it is `Antitone`. Exact readings are
neither, which is why bare numerals do not form a Horn scale.

## Main statements

* `bimonotone_constant`: a family that is both upward and downward monotone is constant.
* `eqOver_not_upward_monotone`, `eqOver_not_downward_monotone`: exact readings are not monotone
  in the degree.

## References

* [kennedy-2015]
* [geurts-nouwen-2007]
* [nouwen-2010]
-/

@[expose] public section

namespace Degree

variable {α : Type*} [LinearOrder α]

/-- A family of propositions that is both upward and downward monotone in the degree is
constant. -/
theorem bimonotone_constant {W : Type*} (P : α → W → Prop)
    (hUp : Monotone P) (hDown : Antitone P) : Function.IsConst P := fun x y ↦
  (le_total x y).elim (fun h ↦ le_antisymm (hUp h) (hDown h))
    (fun h ↦ le_antisymm (hDown h) (hUp h))

/-! ### Exact readings against the other degree predicates -/

/-- *More than `d`* and *exactly `d`* are disjoint. -/
theorem gtOver_disjoint_eqOver {W : Type*} (μ : W → α) (d : α) (w : W) :
    ¬ (w ∈ Comparison.eq.over μ d ∧ w ∈ Comparison.gt.over μ d) := by
  simp only [Comparison.mem_over, Comparison.rel, gt_iff_lt]
  rintro ⟨h₁, h₂⟩
  exact lt_irrefl d (h₁ ▸ h₂)

/-- *Less than `d`* and *exactly `d`* are disjoint. -/
theorem ltOver_disjoint_eqOver {W : Type*} (μ : W → α) (d : α) (w : W) :
    ¬ (w ∈ Comparison.eq.over μ d ∧ w ∈ Comparison.lt.over μ d) := by
  simp only [Comparison.mem_over, Comparison.rel]
  rintro ⟨h₁, h₂⟩
  exact lt_irrefl d (h₁ ▸ h₂)

/-- *Exactly `d`* entails *at least `d`*. -/
theorem eqOver_imp_geOver {W : Type*} (μ : W → α) (d : α) (w : W) :
    w ∈ Comparison.eq.over μ d → w ∈ Comparison.ge.over μ d := by
  simp only [Comparison.mem_over, Comparison.rel, ge_iff_le]
  exact fun h => h ▸ le_refl _

/-- *Exactly `d`* entails *at most `d`*. -/
theorem eqOver_imp_leOver {W : Type*} (μ : W → α) (d : α) (w : W) :
    w ∈ Comparison.eq.over μ d → w ∈ Comparison.le.over μ d := by
  simp only [Comparison.mem_over, Comparison.rel]
  exact fun h => h ▸ le_refl _

/-- A world that measures above `d` satisfies *at least `d`* but not *exactly `d`*. -/
theorem geOver_strictly_weaker_than_eqOver {W : Type*} (μ : W → α)
    {d d' : α} (hlt : d < d') {w : W} (hμ : μ w = d') :
    w ∈ Comparison.ge.over μ d ∧ w ∉ Comparison.eq.over μ d := by
  simp only [Comparison.mem_over, Comparison.rel, ge_iff_le]
  refine ⟨?_, ?_⟩
  · rw [hμ]; exact le_of_lt hlt
  · rw [hμ]; exact ne_of_gt hlt

/-- *Exactly* is not upward monotone in the degree as soon as the scale has two degrees. -/
theorem eqOver_not_upward_monotone {W : Type*} (μ : W → α)
    {d d' : α} (hne : d ≠ d') (hle : d ≤ d') {w : W} (hμ : μ w = d) :
    ¬ ∀ x y, x ≤ y → w ∈ Comparison.eq.over μ x → w ∈ Comparison.eq.over μ y := by
  simp only [Comparison.mem_over, Comparison.rel]
  intro h
  exact hne ((h d d' hle hμ).symm.trans hμ).symm

/-- *Exactly* is not downward monotone in the degree as soon as the scale has two degrees. -/
theorem eqOver_not_downward_monotone {W : Type*} (μ : W → α)
    {d d' : α} (hne : d ≠ d') (hle : d' ≤ d) {w : W} (hμ : μ w = d) :
    ¬ ∀ x y, y ≤ x → w ∈ Comparison.eq.over μ x → w ∈ Comparison.eq.over μ y := by
  simp only [Comparison.mem_over, Comparison.rel]
  intro h
  exact hne ((h d d' hle hμ).symm.trans hμ).symm

end Degree
