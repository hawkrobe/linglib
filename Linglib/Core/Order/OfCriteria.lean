module

public import Linglib.Core.Order.PreorderLattice
public import Mathlib.Order.Concept

/-!
# The criteria-derived preorder

This file defines the preorder that a family of criteria induces on a type. Given a relation
`sat : α → C → Prop` and a set of criteria, `Preorder.ofCriteria sat criteria` ranks `a` below
`b` when `a` satisfies every criterion of the set that `b` satisfies. It is the pullback of `⊇`
along the map sending an element to the set of criteria it satisfies
(`ofCriteria_le_iff_subset`).

## Main declarations

* `Preorder.ofCriteria`: the criteria-derived preorder.
* `Preorder.ofCriteria_antitone`, `Preorder.ofCriteria_empty`: fewer criteria give a coarser
  order, and no criteria give the total one.
* `Preorder.satisfied`, `Preorder.maximalFor_satisfied_iff`: the criteria that an element
  satisfies, and the minimal elements of the order as the elements satisfying a maximal set.
* `Preorder.satisfied_eq_inter_upperPolar`: the criteria an element satisfies are its intent in
  the formal context `sat`, restricted to the criteria.
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

/-- The strict criteria-derived order unfolds to the order and the failure of its converse. -/
theorem ofCriteria_lt_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    (ofCriteria sat criteria).lt a b ↔
      (ofCriteria sat criteria).le a b ∧ ¬ (ofCriteria sat criteria).le b a :=
  Iff.rfl

/-- The criteria-derived order is the pullback of `⊇` along the map sending `a` to the set of
criteria it satisfies, with target `(Set C)ᵒᵈ`. -/
theorem ofCriteria_le_iff_subset (sat : α → C → Prop) (criteria : Set C)
    (a b : α) :
    (ofCriteria sat criteria).le a b ↔
      {c ∈ criteria | sat b c} ⊆ {c ∈ criteria | sat a c} :=
  ⟨fun h _ hc ↦ ⟨hc.1, h _ hc.1 hc.2⟩, fun h _ hc hb ↦ (h ⟨hc, hb⟩).2⟩

/-- Fewer criteria give a coarser order. -/
theorem ofCriteria_antitone (sat : α → C → Prop) : Antitone (ofCriteria sat) :=
  fun _ _ hsub _ _ h c hc ↦ h c (hsub hc)

/-- No criteria give the order relating every two elements. -/
@[simp] theorem ofCriteria_empty (sat : α → C → Prop) : ofCriteria sat ∅ = ⊤ :=
  top_unique fun _ _ _ _ h ↦ h.elim

/-! ### The satisfied criteria as a valuation -/

/-- The criteria that `a` satisfies. The criteria-derived order is the pullback of `⊇` along this
map (`satisfied_subset_iff`), so the minimal elements of the order are the `MaximalFor` elements of
the map (`maximalFor_satisfied_iff`). The best elements are thus those satisfying a maximal set of
criteria, with no order instance on the type. -/
def satisfied (sat : α → C → Prop) (criteria : Set C) (a : α) : Set C :=
  {c ∈ criteria | sat a c}

@[simp] theorem mem_satisfied {sat : α → C → Prop} {criteria : Set C} {a : α} {c : C} :
    c ∈ satisfied sat criteria a ↔ c ∈ criteria ∧ sat a c :=
  Iff.rfl

@[simp] theorem mem_satisfied_univ {sat : α → C → Prop} {a : α} {c : C} :
    c ∈ satisfied sat Set.univ a ↔ sat a c :=
  ⟨And.right, fun h ↦ ⟨trivial, h⟩⟩

/-- The criteria an element satisfies are its intent, `upperPolar sat {a}`, within the criteria. -/
theorem satisfied_eq_inter_upperPolar (sat : α → C → Prop) (criteria : Set C) (a : α) :
    satisfied sat criteria a = criteria ∩ upperPolar sat {a} := by
  ext c
  simp [mem_upperPolar_singleton]

/-- Over every criterion, the criteria an element satisfies are its intent. -/
theorem satisfied_univ (sat : α → C → Prop) (a : α) :
    satisfied sat Set.univ a = upperPolar sat {a} := by
  simp [satisfied_eq_inter_upperPolar]

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
