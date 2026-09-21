module

public import Mathlib.Order.Hom.Order

/-!
# Distributive lattice structure on order homomorphisms

[UPSTREAM] Mathlib gives `α →o β` the pointwise lattice structure when `β` is a lattice. This
file records that the structure is distributive when `β` is.

## References

* [birkhoff-1967]
-/

@[expose] public section

namespace OrderHom

variable {α β : Type*} [Preorder α]

instance instDistribLattice [DistribLattice β] : DistribLattice (α →o β) :=
  { OrderHom.lattice with le_sup_inf := λ _ _ _ _ => le_sup_inf }

end OrderHom
