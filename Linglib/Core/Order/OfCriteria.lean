module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Defs.PartialOrder

/-!
# The criteria-derived preorder

This file defines the preorder that a family of criteria induces on a type. Given a relation
`sat : α → C → Prop` and a set of criteria, `Preorder.ofCriteria sat criteria` ranks `a` below
`b` when `a` satisfies every criterion of the set that `b` satisfies. It is the pullback of `⊇`
along the map sending an element to the set of criteria it satisfies
(`ofCriteria_le_iff_subset`).

## Main declarations

* `Preorder.ofCriteria`: the criteria-derived preorder.
* `Preorder.ofCriteria_le_of_subset`: fewer criteria give a coarser order.
* `Preorder.satisfied`, `Preorder.maximalFor_satisfied_iff`: the criteria that an element
  satisfies, and the minimal elements of the order as the elements satisfying a maximal set.
-/

@[expose] public section

namespace Preorder

variable {α C : Type*}

/-- The criteria-derived preorder ranks `a` below `b` when `a` satisfies every criterion in
`criteria` that `b` satisfies. -/
@[reducible] def ofCriteria (sat : α → C → Prop) (criteria : Set C) :
    Preorder α where
  le a b := ∀ c ∈ criteria, sat b c → sat a c
  le_refl _ _ _ h := h
  le_trans _ _ _ hab hbc c hc h := hab c hc (hbc c hc h)

/-- The criteria-derived order unfolds to its definition. The lemma is not tagged `simp`, so
unfolding is opt-in. -/
theorem ofCriteria_le_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    (ofCriteria sat criteria).le a b ↔ ∀ c ∈ criteria, sat b c → sat a c :=
  Iff.rfl

/-- The criteria-derived order is the pullback of `⊇` along the map sending `a` to the set of
criteria it satisfies, with target `(Set C)ᵒᵈ`. -/
theorem ofCriteria_le_iff_subset (sat : α → C → Prop) (criteria : Set C)
    (a b : α) :
    (ofCriteria sat criteria).le a b ↔
      {c ∈ criteria | sat b c} ⊆ {c ∈ criteria | sat a c} := by
  constructor
  · intro h c hc
    obtain ⟨hcrit, hsat⟩ := Set.mem_sep_iff.mp hc
    exact Set.mem_sep_iff.mpr ⟨hcrit, h c hcrit hsat⟩
  · intro h c hc hsat
    exact (Set.mem_sep_iff.mp (h (Set.mem_sep_iff.mpr ⟨hc, hsat⟩))).2

/-- Fewer criteria give a coarser order, so dominance over a set of criteria transfers to any
subset. -/
theorem ofCriteria_le_of_subset {sat : α → C → Prop}
    {criteria criteria' : Set C} (hsub : criteria ⊆ criteria') {a b : α}
    (h : (ofCriteria sat criteria').le a b) :
    (ofCriteria sat criteria).le a b :=
  fun c hc ↦ h c (hsub hc)

/-! ### The satisfied criteria as a valuation -/

/-- The criteria that `a` satisfies. The criteria-derived order is the pullback of `⊇` along this
map (`satisfied_subset_iff`), so the minimal elements of the order are the `MaximalFor` elements of
the map (`maximalFor_satisfied_iff`). The best elements are thus those satisfying a maximal set of
criteria, with no order instance on the type. -/
def satisfied (sat : α → C → Prop) (criteria : Set C) (a : α) : Set C :=
  {c ∈ criteria | sat a c}

theorem satisfied_subset_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    satisfied sat criteria a ⊆ satisfied sat criteria b ↔ (ofCriteria sat criteria).le b a :=
  (ofCriteria_le_iff_subset sat criteria b a).symm

theorem maximalFor_satisfied_iff (sat : α → C → Prop) (criteria : Set C) (P : α → Prop)
    (a : α) :
    MaximalFor P (satisfied sat criteria) a ↔ @Minimal α (ofCriteria sat criteria).toLE P a := by
  simp only [MaximalFor, Minimal, satisfied_subset_iff]

instance (sat : α → C → Prop) (l : List C) [DecidableEq C] [∀ a c, Decidable (sat a c)]
    (a b : α) : Decidable (satisfied sat {c | c ∈ l} a ≤ satisfied sat {c | c ∈ l} b) :=
  decidable_of_iff (∀ c ∈ l, sat a c → sat b c) (by
    simp only [satisfied_subset_iff, ofCriteria_le_iff, Set.mem_ofPred_eq])

end Preorder
