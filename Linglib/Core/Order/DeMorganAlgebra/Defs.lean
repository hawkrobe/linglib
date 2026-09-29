/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Involutive complements, De Morgan algebras and Kleene algebras

An involutive complement on an ordered type is a complement `ᶜ` that is involutive and reverses
the order, Birkhoff's "involution"; a lattice with one is [kalman-1958]'s "lattice with
involution". It is the data class `InvolutiveCompl`, parameterized by the order and extending the
notation class `Compl`, as mathlib's `InvolutiveNeg` extends `Neg` and `OrderTop` takes `[LE α]`.
The De Morgan laws follow from its two fields alone. The Kleene law `a ⊓ aᶜ ≤ b ⊔ bᶜ` is the Prop
mixin `IsKleene`; Kalman's "normal" i-lattices are the distributive lattices satisfying it.

A De Morgan algebra is then `[DistribLattice α] [BoundedOrder α] [InvolutiveCompl α]`, and a
Kleene algebra adds `[IsKleene α]`; the bounds are optional, as in Kalman's i-lattices. Every
Boolean algebra is a Kleene algebra, the law degenerating through `⊥`, and the three-element chain
`Trivalent` is the canonical non-Boolean example. These are the involution branch between
mathlib's `DistribLattice` and `BooleanAlgebra`, beside the pseudocomplement branch
(`HeytingAlgebra`); the ortholattices of `Core/Order/Ortholattice.lean` drop distributivity
instead.

"Kleene algebra" is the lattice notion, not the regular-expression star-semiring of mathlib's root
`KleeneAlgebra`. The lemmas are protected in the `InvolutiveCompl` namespace because the root
names (`compl_compl`, `compl_sup`, ...) belong to mathlib's Boolean and Heyting API; upstream, the
Boolean ones would be generalized to `InvolutiveCompl`. `[UPSTREAM]` candidate; the `Prod` and
`Pi` instances and the `OrderIso α αᵒᵈ` bundling live in `DeMorganAlgebra/Basic.lean`, Kalman's
construction in `DeMorganAlgebra/Kalman.lean`.

## Main definitions

* `InvolutiveCompl`: an involutive, order-reversing complement; De Morgan
  (`InvolutiveCompl.compl_sup`, `InvolutiveCompl.compl_inf`), the exchange of the bounds, and the
  injectivity and order lemmas are derived here.
* `IsKleene`: the Kleene law (`IsKleene.inf_compl_le_sup_compl`).
* `BooleanAlgebra.toInvolutiveCompl`, `BooleanAlgebra.toIsKleene`: every Boolean algebra is a
  Kleene algebra.

## References

* [kalman-1958]
-/

@[expose] public section

variable {α : Type*}

/-- An **involutive complement** on an ordered type: `aᶜᶜ = a` and `a ≤ b → bᶜ ≤ aᶜ`
([kalman-1958]'s involution, Birkhoff's dual automorphism of period two). `Compl` is notation, so
no complementation law is implied: `a ⊓ aᶜ = ⊥` may fail. -/
class InvolutiveCompl (α : Type*) [LE α] extends Compl α where
  /-- The complement is involutive: `aᶜᶜ = a`. -/
  protected compl_compl (a : α) : aᶜᶜ = a
  /-- The complement reverses the order. -/
  protected compl_le_compl {a b : α} : a ≤ b → bᶜ ≤ aᶜ

namespace InvolutiveCompl

section LE

variable [LE α] [InvolutiveCompl α] {a b : α}

@[simp] protected theorem compl_le_compl_iff_le : aᶜ ≤ bᶜ ↔ b ≤ a :=
  ⟨fun h ↦ InvolutiveCompl.compl_compl b ▸ InvolutiveCompl.compl_compl a ▸
    InvolutiveCompl.compl_le_compl h, InvolutiveCompl.compl_le_compl⟩

protected theorem compl_injective : Function.Injective (compl : α → α) := fun a b h ↦ by
  rw [← InvolutiveCompl.compl_compl a, h, InvolutiveCompl.compl_compl]

@[simp] protected theorem compl_inj_iff : aᶜ = bᶜ ↔ a = b :=
  InvolutiveCompl.compl_injective.eq_iff

protected theorem compl_surjective : Function.Surjective (compl : α → α) :=
  fun a ↦ ⟨aᶜ, InvolutiveCompl.compl_compl a⟩

protected theorem compl_eq_iff_eq_compl : aᶜ = b ↔ a = bᶜ :=
  ⟨fun h ↦ by rw [← h, InvolutiveCompl.compl_compl],
    fun h ↦ by rw [h, InvolutiveCompl.compl_compl]⟩

/-- Orthogonality is symmetric: `a ≤ bᶜ ↔ b ≤ aᶜ`. -/
protected theorem le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ :=
  ⟨fun h ↦ InvolutiveCompl.compl_compl b ▸ InvolutiveCompl.compl_le_compl h,
    fun h ↦ InvolutiveCompl.compl_compl a ▸ InvolutiveCompl.compl_le_compl h⟩

end LE

/-- The complement is antitone (bundled form of the `compl_le_compl` field). -/
protected theorem compl_anti [Preorder α] [InvolutiveCompl α] : Antitone (compl : α → α) :=
  fun _ _ h ↦ InvolutiveCompl.compl_le_compl h

section Lattice

variable [Lattice α] [InvolutiveCompl α]

/-- De Morgan: the complement of a join is the meet of the complements, from involution and
antitonicity alone. -/
@[simp] protected theorem compl_sup (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ :=
  le_antisymm
    (le_inf (InvolutiveCompl.compl_le_compl le_sup_left)
      (InvolutiveCompl.compl_le_compl le_sup_right))
    (InvolutiveCompl.le_compl_comm.1 (sup_le (InvolutiveCompl.le_compl_comm.1 inf_le_left)
      (InvolutiveCompl.le_compl_comm.1 inf_le_right)))

/-- De Morgan: the complement of a meet is the join of the complements. -/
@[simp] protected theorem compl_inf (a b : α) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by
  rw [← InvolutiveCompl.compl_compl (aᶜ ⊔ bᶜ), InvolutiveCompl.compl_sup,
    InvolutiveCompl.compl_compl, InvolutiveCompl.compl_compl]

end Lattice

section BoundedOrder

variable [PartialOrder α] [BoundedOrder α] [InvolutiveCompl α]

@[simp] protected theorem compl_bot : (⊥ : α)ᶜ = ⊤ :=
  le_antisymm le_top (InvolutiveCompl.le_compl_comm.1 bot_le)

@[simp] protected theorem compl_top : (⊤ : α)ᶜ = ⊥ := by
  rw [← InvolutiveCompl.compl_bot, InvolutiveCompl.compl_compl]

end BoundedOrder

end InvolutiveCompl

/-- **Kleene's law**: contradictions lie below excluded middles. [kalman-1958]'s "normal"
i-lattices are the distributive lattices with an involution satisfying it; with bounds they are
the Kleene algebras, the lattice notion. -/
class IsKleene (α : Type*) [Lattice α] [InvolutiveCompl α] : Prop where
  /-- The Kleene law. -/
  inf_compl_le_sup_compl (a b : α) : a ⊓ aᶜ ≤ b ⊔ bᶜ

/-- A Boolean algebra's complement is involutive and antitone. -/
instance (priority := 100) BooleanAlgebra.toInvolutiveCompl [BooleanAlgebra α] :
    InvolutiveCompl α where
  compl_compl := compl_compl
  compl_le_compl h := compl_le_compl h

/-- Every Boolean algebra satisfies the Kleene law, which degenerates through `⊥`. -/
instance (priority := 100) BooleanAlgebra.toIsKleene [BooleanAlgebra α] : IsKleene α :=
  ⟨fun a _ ↦ (BooleanAlgebra.inf_compl_le_bot a).trans _root_.bot_le⟩
