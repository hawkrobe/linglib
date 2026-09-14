import Linglib.Semantics.Modality.ModalTypes

/-!
# Semantic universals for modal meanings

This file defines the two proposed universals on modal meanings, sets of force-flavor pairs, as
predicates on `Modality.Meaning`, and the weaker property proposed as a fallback. A meaning has
independent force and flavor when it is the product of its forces and its flavors
([steinert-threlkeld-imel-guo-2023]), it varies on a single axis when its pairs all share a
force or all share a flavor ([nauze-2008]), and it is path-connected when any two of its pairs
recombine in at least one order. A single-axis meaning is a product, and a product is
path-connected.

On a Kratzer semantics ([kratzer-1981]) a modal's force and its flavor are set by separate
parameters, so its meaning is a product and satisfies the universal; a fixed-force modal ranging
over flavors, or a variable-force modal of one flavor, varies on a single axis besides.

## Main definitions

* `Modality.Meaning.ForceFlavorIndependent`: the meaning is the product of its projections.
* `Modality.Meaning.SingleAxis`: at most one force or at most one flavor.
* `Modality.Meaning.PathConnected`: closure under recombining two pairs in at least one order.

## Main results

* `Modality.Meaning.forceFlavorIndependent_iff`: the universal as stated, closure under
  recombining the force of one pair with the flavor of another.
* `Modality.Meaning.forceFlavorIndependent_iff_pair_product_subset`: independence is convexity
  for the grid betweenness of [chemla-buccola-dautriche-2019].
* `Modality.Meaning.SingleAxis.forceFlavorIndependent`,
  `Modality.Meaning.ForceFlavorIndependent.pathConnected`: the three properties in order of
  strength.
* `Modality.Meaning.forceFlavorIndependent_product`: a product meaning satisfies the universal.

## References

* [steinert-threlkeld-imel-guo-2023]
* [nauze-2008]
* [kratzer-1981]
* [chemla-buccola-dautriche-2019]
-/

namespace Modality.Meaning

variable (m : Meaning)

/-- Independence of force and flavor: a meaning is the product of its forces and its flavors, so
with `(fo₁, fl₁)` and `(fo₂, fl₂)` it expresses `(fo₁, fl₂)`. -/
def ForceFlavorIndependent : Prop := m = m.image Prod.fst ×ˢ m.image Prod.snd

/-- Single axis of variability: the pairs all share a force or all share a flavor. -/
def SingleAxis : Prop := (m.image Prod.fst).card ≤ 1 ∨ (m.image Prod.snd).card ≤ 1

/-- Path-connectedness: with `(fo₁, fl₁)` and `(fo₂, fl₂)` a meaning expresses `(fo₁, fl₂)` or
`(fo₂, fl₁)`, the Ferrers property of a relation. -/
def PathConnected : Prop := ∀ x ∈ m, ∀ y ∈ m, (x.1, y.2) ∈ m ∨ (y.1, x.2) ∈ m

instance : Decidable m.ForceFlavorIndependent := inferInstanceAs (Decidable (_ = _))

instance : Decidable m.SingleAxis := inferInstanceAs (Decidable (_ ∨ _))

instance : Decidable m.PathConnected :=
  inferInstanceAs (Decidable (∀ x ∈ m, ∀ y ∈ m, (x.1, y.2) ∈ m ∨ (y.1, x.2) ∈ m))

variable {m}

/-- The universal as stated: two pairs recombine into a third. -/
theorem forceFlavorIndependent_iff :
    m.ForceFlavorIndependent ↔ ∀ x ∈ m, ∀ y ∈ m, (x.1, y.2) ∈ m := by
  refine ⟨λ h x hx y hy => ?_, λ h => Finset.subset_product.antisymm λ ⟨a, b⟩ hz => ?_⟩
  · rw [ForceFlavorIndependent] at h
    rw [h]
    exact Finset.mk_mem_product (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy)
  · simp only [Finset.mem_product, Finset.mem_image] at hz
    obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩ := hz
    exact h x hx y hy

alias ⟨ForceFlavorIndependent.mk_mem, ForceFlavorIndependent.of_mk_mem⟩ :=
  forceFlavorIndependent_iff

/-- Independence is convexity for the grid betweenness on the force-flavor space: a meaning
contains every pair between two of its pairs, the rectangle they span. -/
theorem forceFlavorIndependent_iff_pair_product_subset :
    m.ForceFlavorIndependent ↔ ∀ x ∈ m, ∀ y ∈ m,
      ({x.1, y.1} : Finset ModalForce) ×ˢ ({x.2, y.2} : Finset ModalFlavor) ⊆ m := by
  rw [forceFlavorIndependent_iff]
  refine ⟨λ h x hx y hy ⟨a, b⟩ hz => ?_,
    λ h x hx y hy => h x hx y hy (Finset.mk_mem_product (by simp) (by simp))⟩
  simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hz
  obtain ⟨rfl | rfl, rfl | rfl⟩ := hz
  exacts [hx, h x hx y hy, h y hy x hx, hy]

theorem SingleAxis.forceFlavorIndependent (h : m.SingleAxis) : m.ForceFlavorIndependent := by
  refine .of_mk_mem λ x hx y hy => ?_
  rcases h with h | h
  · rw [Finset.card_le_one.1 h _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)]
    exact hy
  · rw [← Finset.card_le_one.1 h _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)]
    exact hx

theorem ForceFlavorIndependent.pathConnected (h : m.ForceFlavorIndependent) : m.PathConnected :=
  λ x hx y hy => Or.inl (h.mk_mem x hx y hy)

theorem ForceFlavorIndependent.singleton (x : ForceFlavor) : ForceFlavorIndependent {x} := by
  simp [ForceFlavorIndependent]

/-! ### Kratzer modals

A modal whose force and flavor are set by separate parameters expresses a product. -/

variable (F : Finset ModalForce) (Φ : Finset ModalFlavor)

theorem forceFlavorIndependent_product : ForceFlavorIndependent (F ×ˢ Φ) :=
  .of_mk_mem λ _ hx _ hy =>
    Finset.mk_mem_product (Finset.mem_product.1 hx).1 (Finset.mem_product.1 hy).2

/-- A fixed-force modal ranging over flavors varies on a single axis. -/
theorem singleAxis_singleton_product (fo : ModalForce) : SingleAxis ({fo} ×ˢ Φ) :=
  Or.inl ((Finset.card_le_card Finset.subset_product_image_fst).trans_eq (Finset.card_singleton fo))

/-- A variable-force modal of one flavor varies on a single axis. -/
theorem singleAxis_product_singleton (fl : ModalFlavor) : SingleAxis (F ×ˢ {fl}) :=
  Or.inr ((Finset.card_le_card Finset.subset_product_image_snd).trans_eq (Finset.card_singleton fl))

end Modality.Meaning
