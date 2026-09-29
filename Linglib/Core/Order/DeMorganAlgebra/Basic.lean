/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Hom.Basic
public import Linglib.Core.Order.DeMorganAlgebra.Defs

/-!
# Involutive complements: instances

`Prod` and `Pi` instances for `InvolutiveCompl` and `IsKleene`, over mathlib's pointwise
`Prod.instCompl` and `Pi.instCompl`, and the involution bundled as an
order isomorphism `α ≃o αᵒᵈ`, the `Defs`/`Basic` split mathlib uses for `BooleanAlgebra`. There
is no `OrderDual` instance yet: its complement would have to agree with the one mathlib's
`OrderDual.instBiheytingAlgebra` gives the dual of a Boolean algebra, the one place a genuine
`Compl` diamond can arise.
-/

@[expose] public section

open OrderDual

variable {α β : Type*}

/-! ### Prod -/

instance [LE α] [LE β] [InvolutiveCompl α] [InvolutiveCompl β] : InvolutiveCompl (α × β) where
  compl_compl p := Prod.ext (InvolutiveCompl.compl_compl p.1) (InvolutiveCompl.compl_compl p.2)
  compl_le_compl h := ⟨InvolutiveCompl.compl_le_compl h.1, InvolutiveCompl.compl_le_compl h.2⟩

instance [Lattice α] [Lattice β] [InvolutiveCompl α] [InvolutiveCompl β] [IsKleene α]
    [IsKleene β] : IsKleene (α × β) :=
  ⟨fun a b ↦ ⟨IsKleene.inf_compl_le_sup_compl a.1 b.1, IsKleene.inf_compl_le_sup_compl a.2 b.2⟩⟩

/-! ### Pi -/

instance {ι : Type*} {π : ι → Type*} [∀ i, LE (π i)] [∀ i, InvolutiveCompl (π i)] :
    InvolutiveCompl (∀ i, π i) where
  compl_compl f := funext fun i ↦ InvolutiveCompl.compl_compl (f i)
  compl_le_compl h i := InvolutiveCompl.compl_le_compl (h i)

instance {ι : Type*} {π : ι → Type*} [∀ i, Lattice (π i)] [∀ i, InvolutiveCompl (π i)]
    [∀ i, IsKleene (π i)] : IsKleene (∀ i, π i) :=
  ⟨fun f g i ↦ IsKleene.inf_compl_le_sup_compl (f i) (g i)⟩

/-! ### The involution as an order isomorphism -/

/-- The involution bundled as an order isomorphism onto the order dual. Upstream this is mathlib's
`OrderIso.compl`, generalized from `BooleanAlgebra` to `InvolutiveCompl`. -/
def InvolutiveCompl.complOrderIso (α : Type*) [LE α] [InvolutiveCompl α] : α ≃o αᵒᵈ where
  toFun a := toDual aᶜ
  invFun a := (ofDual a)ᶜ
  left_inv := InvolutiveCompl.compl_compl
  right_inv a := congrArg toDual (InvolutiveCompl.compl_compl (ofDual a))
  map_rel_iff' {a b} := InvolutiveCompl.compl_le_compl_iff_le (α := α) (a := b) (b := a)
