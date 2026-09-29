module

public import Mathlib.Order.Concept
public import Linglib.Core.Order.Ortholattice

/-!
# The ortholattice of a symmetric, irreflexive relation

[UPSTREAM] candidate for `Mathlib/Order/Concept.lean`.

This file shows that the formal concepts of a symmetric, irreflexive relation `r`, an
*orthogonality* relation, form an ortholattice. The lattice structure is mathlib's concept lattice;
the new content is the orthocomplement `Aᶜ = upperPolar r A = {x | ∀ y ∈ A, r x y}`, which for a
symmetric relation is an order-reversing involution on extents.

## Main definitions

* `Concept.instCompl`: the orthocomplement of a concept, whose extent is the concept's intent.
* `Concept.instSetLike`: a concept of a single-sorted relation is determined by its extent.

## Main results

* `Concept.instInvolutiveCompl`: for a symmetric relation the orthocomplement is an involution.
* `Concept.instOrthocomplementedLattice`: for a symmetric, irreflexive relation the concepts form
  an ortholattice.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

open Order Set

namespace Order

variable {S : Type*} (r : S → S → Prop)

/-- For a symmetric relation the upper and lower polars coincide. -/
theorem upperPolar_eq_lowerPolar [Std.Symm r] (s : Set S) :
    upperPolar r s = lowerPolar r s :=
  Set.ext fun _ ↦ ⟨fun h _ ha ↦ Std.Symm.symm _ _ (h ha), fun h _ ha ↦ Std.Symm.symm _ _ (h ha)⟩

/-- For a symmetric relation the upper polar of any set is an extent. -/
theorem isExtent_upperPolar [Std.Symm r] (s : Set S) : IsExtent r (upperPolar r s) := by
  rw [upperPolar_eq_lowerPolar r]; exact isExtent_lowerPolar

end Order

namespace Concept

variable {S : Type*} (r : S → S → Prop)

/-- The orthocomplement of a concept is the concept whose extent is its intent, well defined
    because `r` is symmetric. -/
instance instCompl [Std.Symm r] : Compl (Concept S S r) where
  compl c := .ofIsExtent r c.intent <| c.upperPolar_extent ▸ Order.isExtent_upperPolar r c.extent

@[simp] theorem extent_compl [Std.Symm r] (c : Concept S S r) : cᶜ.extent = c.intent := rfl

@[simp] theorem intent_compl [Std.Symm r] (c : Concept S S r) :
    cᶜ.intent = upperPolar r c.intent := rfl

/-- A concept of a single-sorted relation is determined by its extent, so concepts
    form a `SetLike` family with `↑c = c.extent`. (No `PartialOrder` diamond: `SetLike`
    supplies only `Membership`/coercions, and `Concept`'s order is already `extent`-lifted.) -/
instance instSetLike {r : S → S → Prop} : SetLike (Concept S S r) S where
  coe c := c.extent
  coe_injective _ _ h := extent_injective h

/-- For an irreflexive relation the bottom concept has empty extent (no point is
    orthogonal to everything, including itself). -/
theorem extent_bot_eq_empty [Std.Irrefl r] : (⊥ : Concept S S r).extent = ∅ := by
  rw [Concept.extent_bot]
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun hx ↦ Std.Irrefl.irrefl x (hx (Set.mem_univ x))

/-- For a symmetric relation the orthocomplement is an involution of the concept lattice
    ([holliday-mandelkern-2024] Proposition 4.8). -/
instance instInvolutiveCompl [Std.Symm r] : InvolutiveCompl (Concept S S r) where
  compl_compl c := Concept.ext <| by simp [Order.upperPolar_eq_lowerPolar]
  compl_le_compl {c d} h := by
    show d.intent ⊆ c.intent
    rw [← c.upperPolar_extent, ← d.upperPolar_extent]; exact upperPolar_anti r h

/-- The concepts of a symmetric, irreflexive relation form an orthocomplemented
    lattice ([holliday-mandelkern-2024] Proposition 4.8). The lattice structure
    is mathlib's concept lattice; only the orthocomplement and its four axioms
    are new. -/
instance instOrthocomplementedLattice [Std.Symm r] [Std.Irrefl r] :
    OrthocomplementedLattice (Concept S S r) where
  inf_compl_le_bot _ := fun x hx ↦ absurd (rel_extent_intent hx.1 hx.2) (Std.Irrefl.irrefl x)
  top_le_sup_compl _ := fun _ _ a ha ↦ absurd (ha.2 ha.1) (Std.Irrefl.irrefl a)

end Concept
