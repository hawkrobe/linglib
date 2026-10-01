/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.ModularLattice
public import Linglib.Core.Order.DeMorganAlgebra.Defs

/-!
# Orthocomplemented and orthomodular lattices

This file defines orthocomplemented lattices, or ortholattices, and orthomodular lattices. An
*ortholattice* is a bounded lattice with an involutive, order-reversing complement `ᶜ` satisfying
non-contradiction, `a ⊓ aᶜ = ⊥`, and so, by De Morgan, excluded middle, `a ⊔ aᶜ = ⊤`.

Heyting algebras and ortholattices weaken Boolean algebras in opposite directions. A Heyting
algebra keeps distributivity and the pseudocomplement law `a ⊓ b = ⊥ → b ≤ aᶜ` but gives up the
involution; an ortholattice keeps the involution and the complement laws but gives up
distributivity. Holliday and Mandelkern show that in an ortholattice distributivity and the
pseudocomplement law are equivalent, and that either makes it a Boolean algebra.

An ortholattice is *orthomodular* when `a ≤ b` implies `b = a ⊔ (aᶜ ⊓ b)`. Every modular
ortholattice, and so every Boolean algebra, is orthomodular. The motivating example is the lattice
of closed subspaces of a Hilbert space, Birkhoff and von Neumann's propositions of quantum
mechanics. The regular propositions of Holliday and Mandelkern's epistemic compatibility frames
form an ortholattice that is not orthomodular.

## Main definitions

* `IsOrtholattice α`: the Prop mixin over `[Lattice α] [BoundedOrder α] [InvolutiveCompl α]`
  (the involutive antitone `ᶜ` of `Core/Order/DeMorganAlgebra/Defs.lean`) adding
  non-contradiction.
* `IsOrthomodularLattice α`: an ortholattice satisfying the orthomodular law.
* `DistribLattice.booleanAlgebraOfOrthocomplemented`: a distributive ortholattice is a Boolean
  algebra with `ᶜ` as its complement.

## Main results

* `IsOrtholattice.inf_sup_le_iff_le_compl_of_disjoint`: an ortholattice is distributive iff its
  orthocomplement is a pseudocomplement.
* `IsModularLattice.toIsOrthomodularLattice`: a modular ortholattice is orthomodular.
* `isOrthomodularLattice_iff_sup_compl_inf_sup`: the equational form of the orthomodular law.

## TODO

Upstream candidate for `Mathlib/Order/Ortholattice.lean`. The mathlib instance is the lattice of
closed subspaces of a Hilbert space, in `Mathlib/Analysis/InnerProductSpace/Projection/`:
`ClosedSubmodule.orthogonal` is an `InvolutiveCompl` by `ClosedSubmodule.orthogonal_orthogonal_eq`
and `ClosedSubmodule.orthogonal_le`, non-contradiction is `ClosedSubmodule.inf_orthogonal_eq_bot`,
and orthomodularity is `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`.

## References

* [birkhoff-von-neumann-1936]
* [holliday-mandelkern-2024]
-/

@[expose] public section

variable {α : Type*}

/-- An **ortholattice** is a bounded lattice whose involutive complement satisfies
non-contradiction, `a ⊓ aᶜ ≤ ⊥` ([holliday-mandelkern-2024] Definition 3.3). It is the sibling of
mathlib's `ComplementedLattice` with the complement chosen by `ᶜ`. Excluded middle follows by De
Morgan, `IsOrtholattice.top_le_sup_compl`. -/
class IsOrtholattice (α : Type*) [Lattice α] [BoundedOrder α] [InvolutiveCompl α] : Prop where
  /-- Every element is disjoint from its complement, `a ⊓ aᶜ ≤ ⊥`. -/
  protected inf_compl_le_bot (a : α) : a ⊓ aᶜ ≤ ⊥

namespace IsOrtholattice

/- The involutive-antitone consequences (De Morgan, injectivity, `le_compl_comm`, ...) are
inherited from the shared base: use the `InvolutiveCompl.*` names. -/

variable [Lattice α] [BoundedOrder α] [InvolutiveCompl α] [IsOrtholattice α] {a b : α}

@[simp]
protected theorem inf_compl_eq_bot (a : α) : a ⊓ aᶜ = ⊥ :=
  le_bot_iff.1 (IsOrtholattice.inf_compl_le_bot a)

/-- Excluded middle, the De Morgan dual of non-contradiction. -/
protected theorem top_le_sup_compl (a : α) : ⊤ ≤ a ⊔ aᶜ := by
  rw [← InvolutiveCompl.compl_le_compl_iff_le, InvolutiveCompl.compl_sup,
    InvolutiveCompl.compl_compl, InvolutiveCompl.compl_top, inf_comm]
  exact IsOrtholattice.inf_compl_le_bot a

@[simp]
protected theorem sup_compl_eq_top (a : α) : a ⊔ aᶜ = ⊤ :=
  top_le_iff.1 (IsOrtholattice.top_le_sup_compl a)

protected theorem isCompl_compl (a : α) : IsCompl a aᶜ :=
  .of_eq (IsOrtholattice.inf_compl_eq_bot a) (IsOrtholattice.sup_compl_eq_top a)

protected theorem disjoint_compl_right (a : α) : Disjoint a aᶜ :=
  (IsOrtholattice.isCompl_compl a).disjoint

/-- Orthogonal elements are disjoint. The converse is the pseudocomplement law, which holds only
in Boolean algebras (`IsOrtholattice.inf_sup_le_iff_le_compl_of_disjoint`). -/
protected theorem disjoint_of_le_compl (h : a ≤ bᶜ) : Disjoint a b :=
  (IsOrtholattice.disjoint_compl_right b).symm.mono_left h

/-! ### Distributivity and pseudocomplementation -/

/-- Under the pseudocomplement law disjunctive syllogism holds, the first step of the proof of
[holliday-mandelkern-2024] Proposition 3.7. -/
private theorem sup_inf_compl_le (h : ∀ a b : α, Disjoint a b → b ≤ aᶜ) (a b : α) :
    (a ⊔ b) ⊓ aᶜ ≤ b := by
  have : Disjoint bᶜ ((a ⊔ b) ⊓ aᶜ) := by
    rw [disjoint_iff, inf_comm bᶜ, inf_assoc, ← InvolutiveCompl.compl_sup,
      IsOrtholattice.inf_compl_eq_bot]
  simpa only [InvolutiveCompl.compl_compl] using h _ _ this

/-- An ortholattice is distributive iff its orthocomplement is a pseudocomplement, that is, iff
`a ⊓ b = ⊥` implies `b ≤ aᶜ` ([holliday-mandelkern-2024] Proposition 3.7). -/
theorem inf_sup_le_iff_le_compl_of_disjoint :
    (∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) ↔ ∀ a b : α, Disjoint a b → b ≤ aᶜ := by
  refine ⟨fun hd a b h ↦ ?_, fun h a b c ↦ ?_⟩
  · calc b = b ⊓ (a ⊔ aᶜ) := by rw [IsOrtholattice.sup_compl_eq_top, inf_top_eq]
      _ ≤ b ⊓ a ⊔ b ⊓ aᶜ := hd b a aᶜ
      _ ≤ aᶜ := sup_le (h.symm.eq_bot.le.trans bot_le) inf_le_right
  · have hb : a ⊓ (b ⊔ c) ⊓ (a ⊓ b)ᶜ ≤ bᶜ := by
      have := sup_inf_compl_le h aᶜ bᶜ
      rw [InvolutiveCompl.compl_compl] at this
      rw [InvolutiveCompl.compl_inf]
      exact (le_inf inf_le_right (inf_le_left.trans inf_le_left)).trans this
    have hc : a ⊓ (b ⊔ c) ⊓ (a ⊓ b)ᶜ ≤ a ⊓ c := le_inf (inf_le_left.trans inf_le_left)
      ((le_inf (inf_le_left.trans inf_le_right) hb).trans (sup_inf_compl_le h b c))
    have := h ((a ⊓ b)ᶜ ⊓ (a ⊓ c)ᶜ) (a ⊓ (b ⊔ c)) <| disjoint_iff.2 <| le_bot_iff.1 <| by
      rw [inf_comm ((a ⊓ b)ᶜ ⊓ (a ⊓ c)ᶜ), ← inf_assoc]
      exact (inf_le_inf_right _ hc).trans (IsOrtholattice.inf_compl_eq_bot _).le
    rwa [InvolutiveCompl.compl_inf, InvolutiveCompl.compl_compl, InvolutiveCompl.compl_compl]
      at this

end IsOrtholattice

/-- Every ortholattice is complemented, with `ᶜ` as the chosen complement. -/
instance (priority := 100) IsOrtholattice.toComplementedLattice [Lattice α] [BoundedOrder α]
    [InvolutiveCompl α] [IsOrtholattice α] : ComplementedLattice α :=
  ⟨fun a ↦ ⟨aᶜ, IsOrtholattice.isCompl_compl a⟩⟩

/-- Every Boolean algebra is orthocomplemented. -/
instance (priority := 100) BooleanAlgebra.toIsOrtholattice [BooleanAlgebra α] : IsOrtholattice α :=
  ⟨BooleanAlgebra.inf_compl_le_bot⟩

/-- A distributive ortholattice is a Boolean algebra with `ᶜ` as its complement
([holliday-mandelkern-2024] Proposition 3.7). Unlike `DistribLattice.booleanAlgebraOfComplemented`
it uses no choice; it is not an instance, since a Boolean algebra would get a second structure. -/
@[instance_reducible]
def DistribLattice.booleanAlgebraOfOrthocomplemented [DistribLattice α] [BoundedOrder α]
    [InvolutiveCompl α] [IsOrtholattice α] : BooleanAlgebra α where
  __ := ‹DistribLattice α›
  __ := ‹BoundedOrder α›
  compl := compl
  inf_compl_le_bot := IsOrtholattice.inf_compl_le_bot
  top_le_sup_compl := IsOrtholattice.top_le_sup_compl

/-! ### Orthomodular lattices -/

/-- An **orthomodular lattice** is an ortholattice in which `a ≤ b` implies
`b = a ⊔ (aᶜ ⊓ b)` ([holliday-mandelkern-2024] Definition 3.5). We only require `≤`, since the
other inequality holds in every lattice. -/
class IsOrthomodularLattice (α : Type*) [Lattice α] [BoundedOrder α] [InvolutiveCompl α] : Prop
    extends IsOrtholattice α where
  /-- If `a ≤ b`, then `b ≤ a ⊔ (aᶜ ⊓ b)`. -/
  protected le_sup_compl_inf_of_le {a b : α} : a ≤ b → b ≤ a ⊔ aᶜ ⊓ b

section IsOrthomodularLattice

variable [Lattice α] [BoundedOrder α] [InvolutiveCompl α]

/-- A modular ortholattice is orthomodular ([holliday-mandelkern-2024] footnote 4), and so,
through `DistribLattice`, is every Boolean algebra. -/
instance (priority := 100) IsModularLattice.toIsOrthomodularLattice [IsOrtholattice α]
    [IsModularLattice α] : IsOrthomodularLattice α where
  le_sup_compl_inf_of_le {a _} h := by
    simpa only [IsOrtholattice.sup_compl_eq_top, top_inf_eq] using
      IsModularLattice.sup_inf_le_assoc_of_le aᶜ h

/-- The orthomodular law in the equational form of [holliday-mandelkern-2024] Definition 3.5. -/
theorem isOrthomodularLattice_iff_sup_compl_inf_sup [IsOrtholattice α] :
    IsOrthomodularLattice α ↔ ∀ a b : α, a ⊔ aᶜ ⊓ (a ⊔ b) = a ⊔ b := by
  refine ⟨fun _ a b ↦ ?_, fun h ↦ { le_sup_compl_inf_of_le := fun {a b} hab ↦ ?_ }⟩
  · exact le_antisymm (sup_le le_sup_left inf_le_right)
      (IsOrthomodularLattice.le_sup_compl_inf_of_le le_sup_left)
  · simpa only [sup_of_le_right hab] using (h a b).ge

variable [IsOrthomodularLattice α] {a b : α}

theorem sup_compl_inf_of_le (h : a ≤ b) : a ⊔ aᶜ ⊓ b = b :=
  le_antisymm (sup_le h inf_le_right) (IsOrthomodularLattice.le_sup_compl_inf_of_le h)

theorem sup_compl_inf_sup (a b : α) : a ⊔ aᶜ ⊓ (a ⊔ b) = a ⊔ b :=
  sup_compl_inf_of_le le_sup_left

/-- In an orthomodular lattice `a ≤ b` is an equality as soon as `b` is disjoint from `aᶜ`. -/
theorem eq_of_le_of_disjoint_compl (h : a ≤ b) (hd : Disjoint aᶜ b) : a = b := by
  rw [← sup_compl_inf_of_le h, hd.eq_bot, sup_bot_eq]

end IsOrthomodularLattice
