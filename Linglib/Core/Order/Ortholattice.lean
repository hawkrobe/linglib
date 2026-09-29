/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Disjoint
public import Linglib.Core.Order.DeMorganAlgebra.Defs

/-!
# Orthocomplemented Lattices

An *orthocomplemented lattice* (or *ortholattice*) is a bounded lattice
equipped with an involutive, order-reversing complement satisfying
non-contradiction and excluded middle. It is the structural dual of a
`HeytingAlgebra`: where Heyting drops the law of excluded middle but
retains distributivity, ortholattices keep excluded middle but drop
distributivity: a distributive ortholattice is a Boolean algebra.

The canonical examples are:
- closed subspaces of an inner-product space (orthocomplement = orthogonal
  complement), the propositions of quantum mechanics in [birkhoff-von-neumann-1936];
- the `◇`-regular subsets of a compatibility frame ([holliday-mandelkern-2024]).

## Main definitions

* `OrthocomplementedLattice α`: the Prop mixin over `[Lattice α] [BoundedOrder α]
  [InvolutiveCompl α]` (the shared involutive antitone `ᶜ`, `Core/Order/DeMorganAlgebra/Defs.lean`)
  adding non-contradiction and excluded middle. A complete ortholattice is
  `[CompleteLattice α] [InvolutiveCompl α] [OrthocomplementedLattice α]`.

## Main results

* De Morgan laws (`compl_sup`, `compl_inf`), `compl_injective`, `compl_surjective`,
  `compl_le_compl_iff_le`: inherited from `InvolutiveCompl` (use those names).
* `BooleanAlgebra.toOrthocomplementedLattice`: every `BooleanAlgebra` is orthocomplemented.
* `OrthocomplementedLattice.toComplementedLattice`: every ortholattice is a `ComplementedLattice`
  (the existential mathlib mixin; the complement here is a chosen function).

## What fails (relative to `BooleanAlgebra`)

Ortholattices need not satisfy:
- **distributivity**: `a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)`;
- **pseudocomplementation**: `a ⊓ b = ⊥ → b ≤ aᶜ`;
- **orthomodularity**: `a ≤ b → b = a ⊔ (aᶜ ⊓ b)`.

Imposing distributivity collapses the typeclass to `BooleanAlgebra`;
imposing orthomodularity yields *orthomodular lattices* (the algebra of
quantum-mechanical propositions). Concrete counterexamples to all three
appear in `Linglib.Studies.HollidayMandelkern2024`.

## TODO

Upstream candidate for `Mathlib/Order/Ortholattice.lean`. The natural
mathlib consumer is the lattice of closed subspaces of a Hilbert space
(via `Mathlib.Analysis.InnerProductSpace.Orthogonal`), which currently
provides every ingredient (`Submodule.orthogonal`, `inf_orthogonal_eq_bot`,
`le_orthogonal_orthogonal`) but stops short of packaging an
`OrthocomplementedLattice` instance because the class is missing.

## References

* [birkhoff-von-neumann-1936]
* [holliday-mandelkern-2024]
-/

@[expose] public section

/-- An **orthocomplementation**: the involutive complement is a complement, satisfying
non-contradiction (`a ⊓ aᶜ ≤ ⊥`) and excluded middle (`⊤ ≤ a ⊔ aᶜ`). A lattice with one is an
orthocomplemented lattice, or ortholattice; this is the sibling of mathlib's `ComplementedLattice`
with the complement chosen by `ᶜ`.

Every `BooleanAlgebra` is an ortholattice. The converse fails: ortholattices need not be
distributive. -/
class OrthocomplementedLattice (α : Type*) [Lattice α] [BoundedOrder α] [InvolutiveCompl α] :
    Prop where
  /-- Non-contradiction: `a ⊓ aᶜ ≤ ⊥`. -/
  protected inf_compl_le_bot (a : α) : a ⊓ aᶜ ≤ ⊥
  /-- Excluded middle: `⊤ ≤ a ⊔ aᶜ`. -/
  protected top_le_sup_compl (a : α) : ⊤ ≤ a ⊔ aᶜ

namespace OrthocomplementedLattice

/- The involutive-antitone consequences (De Morgan, injectivity, `le_compl_comm`, ...) are
inherited from the shared base: use the `InvolutiveCompl.*` names. -/

variable {α : Type*} [Lattice α] [BoundedOrder α] [InvolutiveCompl α] [OrthocomplementedLattice α]

@[simp]
protected theorem inf_compl_eq_bot (a : α) : a ⊓ aᶜ = ⊥ :=
  le_antisymm (OrthocomplementedLattice.inf_compl_le_bot a) bot_le

@[simp]
protected theorem sup_compl_eq_top (a : α) : a ⊔ aᶜ = ⊤ :=
  le_antisymm le_top (OrthocomplementedLattice.top_le_sup_compl a)

protected theorem isCompl_compl (a : α) : IsCompl a aᶜ where
  disjoint := disjoint_iff.mpr (OrthocomplementedLattice.inf_compl_eq_bot a)
  codisjoint := codisjoint_iff.mpr (OrthocomplementedLattice.sup_compl_eq_top a)

end OrthocomplementedLattice

/-- Every ortholattice is complemented, with `ᶜ` as the chosen complement. -/
instance (priority := 100) OrthocomplementedLattice.toComplementedLattice {α : Type*} [Lattice α]
    [BoundedOrder α] [InvolutiveCompl α] [OrthocomplementedLattice α] : ComplementedLattice α :=
  ⟨fun a ↦ ⟨aᶜ, OrthocomplementedLattice.isCompl_compl a⟩⟩

/-- Every Boolean algebra is orthocomplemented. The converse fails: ortholattices need not be
distributive. -/
instance (priority := 100) BooleanAlgebra.toOrthocomplementedLattice {α : Type*}
    [BooleanAlgebra α] : OrthocomplementedLattice α :=
  ⟨BooleanAlgebra.inf_compl_le_bot, BooleanAlgebra.top_le_sup_compl⟩
