import Mathlib.Order.Interval.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Abel

/-!
# Interval contents on ordered types
[krifka-1989] [krifka-1998] [rouillard-2026]

A finitely additive, strictly positive content on the nonempty closed
intervals of a preorder, valued in an ordered additive monoid. The
order-theoretic sibling of `ExtMeasure` (`Core/Order/Mereology.lean`,
[krifka-1998]'s extensive measure functions over a `SemilatticeSup`):
disjoint intervals have no interval join, so the two substrates coexist
rather than one subsuming the other.

Mathlib's `NonemptyInterval.length` is the canonical group-valued example
(`ofStrictMono` at `F = id`); its `length_add` is additivity over
*Minkowski* interval addition, orthogonal to the *concatenation*
additivity axiomatized here, which mathlib does not state.

## Main declarations

- `IsIntervalContent`: additivity over interval concatenation plus strict
  positivity on nondegenerate intervals.
- `IsIntervalContent.ofStrictMono`: Stieltjes-style constructor — a
  strictly monotone potential `F` into an ordered group induces the
  content `fun i => F i.snd - F i.fst`.
- `IsIntervalContent.measure_lt_of_left_lt`: moving the left endpoint
  strictly right strictly decreases measure.
- `IsIntervalContent.not_isLeast_rightAnchored`: over a dense order, the
  measures of right-anchored covers `[l, s]` with `l` strictly below a
  point have no least element — the domain-general form of
  [rouillard-2026]'s G-TIA information collapse.
-/

namespace Core.Order

variable {α M : Type*}

/-- A finitely additive, strictly positive content on the nonempty closed
    intervals of a preorder: the order-interval counterpart of
    [krifka-1998]'s extensive measure functions (`ExtMeasure`). -/
class IsIntervalContent [Preorder α] [AddCommMonoid M] [PartialOrder M]
    (μ : NonemptyInterval α → M) : Prop where
  /-- Additivity over interval concatenation. -/
  additive : ∀ (a b c : α) (hab : a ≤ b) (hbc : b ≤ c),
    μ ⟨⟨a, c⟩, hab.trans hbc⟩ = μ ⟨⟨a, b⟩, hab⟩ + μ ⟨⟨b, c⟩, hbc⟩
  /-- Strict positivity on nondegenerate intervals. -/
  positive : ∀ (a b : α) (h : a < b), 0 < μ ⟨⟨a, b⟩, h.le⟩

namespace IsIntervalContent

section Preorder

variable [Preorder α] [AddCommMonoid M] [PartialOrder M]
  (μ : NonemptyInterval α → M) [IsIntervalContent μ]

/-- Degenerate intervals have measure zero, given cancellation. -/
theorem degenerate_eq_zero [IsCancelAdd M] (a : α) :
    μ ⟨⟨a, a⟩, le_refl a⟩ = 0 := by
  have h := additive (μ := μ) a a a (le_refl a) (le_refl a)
  exact add_left_cancel (a := μ ⟨⟨a, a⟩, le_refl a⟩) (by rw [add_zero, ← h])

/-- Moving the left endpoint strictly right strictly decreases measure. -/
theorem measure_lt_of_left_lt [AddRightStrictMono M]
    {a b s : α} (hab : a < b) (hbs : b ≤ s) :
    μ ⟨⟨b, s⟩, hbs⟩ < μ ⟨⟨a, s⟩, hab.le.trans hbs⟩ := by
  rw [additive (μ := μ) a b s hab.le hbs]
  exact lt_add_of_pos_left _ (positive (μ := μ) a b hab)

/-- Moving the right endpoint strictly right strictly increases measure. -/
theorem measure_lt_of_lt_right [AddLeftStrictMono M]
    {a b s : α} (hab : a ≤ b) (hbs : b < s) :
    μ ⟨⟨a, b⟩, hab⟩ < μ ⟨⟨a, s⟩, hab.trans hbs.le⟩ := by
  rw [additive (μ := μ) a b s hab hbs.le]
  exact lt_add_of_pos_right _ (positive (μ := μ) b s hbs)

end Preorder

section Dense

variable [LinearOrder α] [DenselyOrdered α] [AddCommMonoid M]
  [PartialOrder M] [AddRightStrictMono M]
  (μ : NonemptyInterval α → M) [IsIntervalContent μ]

/-- **No minimal right-anchored cover**: over a dense order, the measures
    of intervals `[l, s]` with left endpoint strictly below `a` have no
    least element — the domain-general form of [rouillard-2026]'s G-TIA
    information collapse ("there cannot be a smallest open interval to
    include a closed time"). Decomposes through `StrictAnti.map_isLeast`:
    a least measure would be a greatest left endpoint, which density
    forbids. -/
theorem not_isLeast_rightAnchored {a s : α} (has : a ≤ s) (x : M) :
    ¬ IsLeast (Set.range fun l : Set.Iio a =>
      μ ⟨⟨l.1, s⟩, (l.2.trans_le has).le⟩) x := by
  intro h
  obtain ⟨l, rfl⟩ := h.1
  have hanti : StrictAnti fun l : Set.Iio a =>
      μ ⟨⟨l.1, s⟩, (l.2.trans_le has).le⟩ :=
    fun p q hpq => measure_lt_of_left_lt μ hpq (q.2.trans_le has).le
  rw [← Set.image_univ] at h
  have hg : IsGreatest Set.univ l := hanti.map_isLeast.mp h
  obtain ⟨m, hm₁, hm₂⟩ := exists_between l.2
  exact absurd (hg.2 (Set.mem_univ (⟨m, hm₂⟩ : Set.Iio a))) (not_le.mpr hm₁)

end Dense

section OfStrictMono

variable [Preorder α] {G : Type*} [AddCommGroup G] [PartialOrder G]
  [IsOrderedAddMonoid G]

/-- Stieltjes-style constructor: a strictly monotone potential into an
    ordered group induces an interval content. Additivity is telescoping;
    positivity is the strict monotonicity. At `F = id` this recovers
    `NonemptyInterval.length`. -/
theorem ofStrictMono (F : α → G) (hF : StrictMono F) :
    IsIntervalContent (fun i : NonemptyInterval α => F i.snd - F i.fst) where
  additive a b c _ _ := by dsimp only; abel
  positive a b h := sub_pos.mpr (hF h)

/-- `NonemptyInterval.length` on `ℚ` is a content (non-vacuity witness). -/
example : IsIntervalContent (NonemptyInterval.length (α := ℚ)) :=
  ofStrictMono _ strictMono_id

end OfStrictMono

end IsIntervalContent

end Core.Order
