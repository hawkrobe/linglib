/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Hom.Basic
import Linglib.Core.Order.DeMorganAlgebra.Defs

/-!
# De Morgan and Kleene algebras: instances

`OrderDual`, `Prod`, and `Pi` instances for `LatticeWithInvolution`, `DeMorganAlgebra`,
and `Order.KleeneAlgebra`, plus the involution bundled as an order isomorphism
`α ≃o αᵒᵈ` — the `Defs`/`Basic` split mathlib uses for `BooleanAlgebra`
(cf. `OrderIso.compl` there, which this generalizes past complementation).
-/

open LatticeWithInvolution OrderDual

variable {α β : Type*}

/-! ### OrderDual -/

instance [LatticeWithInvolution α] : LatticeWithInvolution αᵒᵈ where
  compl a := toDual (ofDual a)ᶜ
  compl_compl a := congrArg toDual (compl_compl (ofDual a))
  compl_le_compl h := compl_le_compl (α := α) h

instance [DeMorganAlgebra α] : DeMorganAlgebra αᵒᵈ where
  __ := (inferInstance : DistribLattice αᵒᵈ)
  __ := (inferInstance : LatticeWithInvolution αᵒᵈ)

instance [Order.KleeneAlgebra α] : Order.KleeneAlgebra αᵒᵈ where
  inf_compl_le_sup_compl a b :=
    Order.KleeneAlgebra.inf_compl_le_sup_compl (ofDual b) (ofDual a)

/-! ### Prod -/

instance [LatticeWithInvolution α] [LatticeWithInvolution β] :
    LatticeWithInvolution (α × β) where
  compl p := (p.1ᶜ, p.2ᶜ)
  compl_compl p := Prod.ext (compl_compl p.1) (compl_compl p.2)
  compl_le_compl h := ⟨compl_le_compl h.1, compl_le_compl h.2⟩

instance [DeMorganAlgebra α] [DeMorganAlgebra β] : DeMorganAlgebra (α × β) where
  __ := (inferInstance : DistribLattice (α × β))
  __ := (inferInstance : LatticeWithInvolution (α × β))

instance [Order.KleeneAlgebra α] [Order.KleeneAlgebra β] :
    Order.KleeneAlgebra (α × β) where
  inf_compl_le_sup_compl a b :=
    ⟨Order.KleeneAlgebra.inf_compl_le_sup_compl a.1 b.1,
     Order.KleeneAlgebra.inf_compl_le_sup_compl a.2 b.2⟩

/-! ### Pi -/

instance {ι : Type*} {π : ι → Type*} [∀ i, LatticeWithInvolution (π i)] :
    LatticeWithInvolution (∀ i, π i) where
  compl f i := (f i)ᶜ
  compl_compl f := funext λ i => compl_compl (f i)
  compl_le_compl h i := compl_le_compl (h i)

instance {ι : Type*} {π : ι → Type*} [∀ i, DeMorganAlgebra (π i)] :
    DeMorganAlgebra (∀ i, π i) where
  __ := (inferInstance : DistribLattice (∀ i, π i))
  __ := (inferInstance : LatticeWithInvolution (∀ i, π i))

instance {ι : Type*} {π : ι → Type*} [∀ i, Order.KleeneAlgebra (π i)] :
    Order.KleeneAlgebra (∀ i, π i) where
  inf_compl_le_sup_compl f g i :=
    Order.KleeneAlgebra.inf_compl_le_sup_compl (f i) (g i)

/-! ### The involution as an order isomorphism -/

/-- The involution bundled as an order isomorphism onto the order dual — the
generalization of mathlib's `OrderIso.compl` from `BooleanAlgebra` to any
`LatticeWithInvolution`. -/
def LatticeWithInvolution.complOrderIso (α : Type*) [LatticeWithInvolution α] :
    α ≃o αᵒᵈ where
  toFun a := toDual aᶜ
  invFun a := (ofDual a)ᶜ
  left_inv := compl_compl
  right_inv a := congrArg toDual (compl_compl (ofDual a))
  map_rel_iff' := compl_le_compl_iff_le
