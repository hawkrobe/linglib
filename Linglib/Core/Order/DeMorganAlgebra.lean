/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# De Morgan algebras and Kleene lattices

`LatticeWithInvolution` is a bounded lattice with an involutive antitone complement `ᶜ` —
the common reduct of `OrthocomplementedLattice` (which adds the complementation laws) and
`DeMorganAlgebra` (which adds distributivity instead). The De Morgan laws are proved once
here, from involution and antitonicity alone. A `KleeneLattice` is a De Morgan algebra
satisfying the Kleene law `a ⊓ aᶜ ≤ b ⊔ bᶜ`: every `BooleanAlgebra` qualifies (the law
degenerates through `⊥`), and the three-element chain `Trivalent.Truth3` is the canonical
non-Boolean example.

Mathlib has no De Morgan/Kleene *lattice* class (its `KleeneAlgebra` is the
star-semiring); `[UPSTREAM]` candidate for `Mathlib/Order/DeMorganAlgebra.lean`. The
`Lattice`/`Algebra` suffix split tracks the literature (Kalman's Kleene lattices) and
avoids the star-semiring collision, on the `Order.Ideal` vs ring `Ideal` precedent.

## Main definitions

* `LatticeWithInvolution` — bounded lattice + involutive antitone `ᶜ`; De Morgan
  (`compl_sup`/`compl_inf`), `compl_bot`/`compl_top`, and the injectivity/order lemmas
  are derived here.
* `DeMorganAlgebra` — a distributive `LatticeWithInvolution`.
* `KleeneLattice` — a `DeMorganAlgebra` with the Kleene law
  (`inf_compl_le_sup_compl`); every `BooleanAlgebra` is an instance.
-/

/-- A bounded lattice with an involutive, order-reversing complement — the common reduct
of `OrthocomplementedLattice` and `DeMorganAlgebra`. `Compl` is pure notation, so `ᶜ`
carries no complementation laws here: `a ⊓ aᶜ = ⊥` may fail. -/
class LatticeWithInvolution (α : Type*) extends Lattice α, BoundedOrder α, Compl α where
  /-- Complement is involutive: `aᶜᶜ = a`. -/
  compl_compl (a : α) : aᶜᶜ = a
  /-- Complement is order-reversing. -/
  compl_antitone {a b : α} : a ≤ b → bᶜ ≤ aᶜ

namespace LatticeWithInvolution

variable {α : Type*} [LatticeWithInvolution α] {a b : α}

theorem compl_le_compl_iff_le : aᶜ ≤ bᶜ ↔ b ≤ a :=
  ⟨fun h => compl_compl b ▸ compl_compl a ▸ compl_antitone h, fun h => compl_antitone h⟩

theorem compl_injective : Function.Injective (compl : α → α) := fun _ _ h => by
  have := congrArg compl h
  rwa [compl_compl, compl_compl] at this

theorem compl_surjective : Function.Surjective (compl : α → α) :=
  fun a => ⟨aᶜ, compl_compl a⟩

theorem compl_eq_iff_eq_compl : aᶜ = b ↔ a = bᶜ :=
  ⟨fun h => by rw [← h, compl_compl], fun h => by rw [h, compl_compl]⟩

/-- Orthogonality is symmetric: `a ≤ bᶜ ↔ b ≤ aᶜ`. -/
theorem le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ :=
  ⟨fun h => compl_compl b ▸ compl_antitone h, fun h => compl_compl a ▸ compl_antitone h⟩

/-- De Morgan: complement of a join is the meet of complements — from involution and
antitonicity alone; no distributivity or complementation is used. -/
theorem compl_sup (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  apply le_antisymm
  · exact le_inf (compl_antitone le_sup_left) (compl_antitone le_sup_right)
  · have ha : a ≤ (aᶜ ⊓ bᶜ)ᶜ := by
      have h : aᶜᶜ ≤ (aᶜ ⊓ bᶜ)ᶜ := compl_antitone inf_le_left
      rwa [compl_compl] at h
    have hb : b ≤ (aᶜ ⊓ bᶜ)ᶜ := by
      have h : bᶜᶜ ≤ (aᶜ ⊓ bᶜ)ᶜ := compl_antitone inf_le_right
      rwa [compl_compl] at h
    have h := compl_antitone (sup_le ha hb)
    rwa [compl_compl] at h

/-- De Morgan: complement of a meet is the join of complements. -/
theorem compl_inf (a b : α) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by
  have h := compl_sup aᶜ bᶜ
  rw [compl_compl, compl_compl] at h
  rw [← h, compl_compl]

@[simp] theorem compl_bot : (⊥ : α)ᶜ = ⊤ :=
  le_antisymm le_top (compl_compl (⊤ : α) ▸ compl_antitone bot_le)

@[simp] theorem compl_top : (⊤ : α)ᶜ = ⊥ := by
  have h : (⊤ : α)ᶜ ≤ ⊥ᶜᶜ := compl_antitone le_top
  rw [compl_compl] at h
  exact le_antisymm h bot_le

end LatticeWithInvolution

/-- A De Morgan algebra: a distributive bounded lattice with an involutive antitone
complement. Unlike `BooleanAlgebra`, complementation may fail (`a ⊓ aᶜ ≠ ⊥`). -/
class DeMorganAlgebra (α : Type*) extends DistribLattice α, LatticeWithInvolution α

/-- A Kleene lattice: a De Morgan algebra satisfying the Kleene law. Named against
mathlib's star-semiring `KleeneAlgebra`; this is Kalman's lattice notion, the variety of
strong Kleene logic. -/
class KleeneLattice (α : Type*) extends DeMorganAlgebra α where
  /-- The Kleene law: contradictions lie below excluded middles. -/
  inf_compl_le_sup_compl (a b : α) : a ⊓ aᶜ ≤ b ⊔ bᶜ

/-- Every Boolean algebra is a Kleene lattice: the Kleene law degenerates through `⊥`.
Low priority so Boolean API is preferred where applicable. -/
instance (priority := 100) BooleanAlgebra.toKleeneLattice {α : Type*} [BooleanAlgebra α] :
    KleeneLattice α where
  compl_compl := compl_compl
  compl_antitone := fun h => compl_le_compl h
  inf_compl_le_sup_compl a _ := (BooleanAlgebra.inf_compl_le_bot a).trans _root_.bot_le
