import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Disjoint
import Linglib.Core.Order.DeMorganAlgebra

/-!
# Orthocomplemented Lattices

An *orthocomplemented lattice* (or *ortholattice*) is a bounded lattice
equipped with an involutive, order-reversing complement satisfying
non-contradiction and excluded middle. It is the structural dual of a
`HeytingAlgebra`: where Heyting drops the law of excluded middle but
retains distributivity, ortholattices keep excluded middle but drop
distributivity. `BooleanAlgebra = OrthocomplementedLattice + DistribLattice`.

The canonical examples are:
- closed subspaces of an inner-product space (orthocomplement = orthogonal
  complement) — see Birkhoff & von Neumann (1936) "The Logic of Quantum
  Mechanics", *Annals of Mathematics* 37(4):823-843, originally formulating
  ortholattices for quantum-mechanical propositions;
- `Set`-of-`◇`-regular subsets of a compatibility frame (Holliday &
  Mandelkern 2024 "The Orthologic of Epistemic Modals", *Journal of
  Philosophical Logic*).

## Main definitions

* `OrthocomplementedLattice α` — typeclass extending `LatticeWithInvolution α`
  (the shared involutive-antitone-`ᶜ` base, `Core/Order/DeMorganAlgebra.lean`)
  with non-contradiction and excluded middle.

## Main results

* De Morgan laws (`compl_sup`, `compl_inf`), `compl_injective`, `compl_surjective`,
  `compl_le_compl_iff_le` — inherited from `LatticeWithInvolution` and re-exported.
* `instBooleanOrtho`: every `BooleanAlgebra` is an `OrthocomplementedLattice`
  (low priority so Boolean instances aren't obscured).
* `instComplementedLattice`: every ortholattice is `ComplementedLattice`
  (the *existential* mathlib typeclass; we strengthen it to a chosen
  complement function).

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
`OrthocomplementedLattice` instance because the typeclass is missing.
-/

/-- An *orthocomplemented lattice* (ortholattice) is a `LatticeWithInvolution`
    additionally satisfying non-contradiction (`a ⊓ aᶜ ≤ ⊥`) and excluded middle
    (`⊤ ≤ a ⊔ aᶜ`).

    Every `BooleanAlgebra` is an ortholattice. The converse fails:
    ortholattices need not be distributive. -/
class OrthocomplementedLattice (α : Type*) extends LatticeWithInvolution α where
  /-- Non-contradiction: `a ⊓ aᶜ ≤ ⊥`. -/
  inf_compl_le_bot (a : α) : a ⊓ aᶜ ≤ ⊥
  /-- Excluded middle: `⊤ ≤ a ⊔ aᶜ`. -/
  top_le_sup_compl (a : α) : ⊤ ≤ a ⊔ aᶜ

namespace OrthocomplementedLattice

/- The involutive-antitone consequences (De Morgan, injectivity, `le_compl_comm`, …) are
inherited from the shared base `LatticeWithInvolution`; re-exported here so consumers can
keep the `OrthocomplementedLattice.*` names. -/
export LatticeWithInvolution (compl_compl compl_antitone compl_le_compl_iff_le
  compl_injective compl_surjective compl_eq_iff_eq_compl le_compl_comm
  compl_sup compl_inf compl_bot compl_top)

variable {α : Type*} [OrthocomplementedLattice α] {a b : α}

/-! ### Basic Identities -/

@[simp]
theorem inf_compl_eq_bot (a : α) : a ⊓ aᶜ = ⊥ :=
  le_antisymm (OrthocomplementedLattice.inf_compl_le_bot a) bot_le

@[simp]
theorem sup_compl_eq_top (a : α) : a ⊔ aᶜ = ⊤ :=
  le_antisymm le_top (OrthocomplementedLattice.top_le_sup_compl a)

/-! ### IsCompl and ComplementedLattice -/

theorem isCompl_compl (a : α) : IsCompl a aᶜ where
  disjoint := disjoint_iff.mpr (inf_compl_eq_bot a)
  codisjoint := codisjoint_iff.mpr (sup_compl_eq_top a)

instance instComplementedLattice : ComplementedLattice α :=
  ⟨fun a => ⟨aᶜ, isCompl_compl a⟩⟩

end OrthocomplementedLattice

/-! ### BooleanAlgebra → OrthocomplementedLattice -/

/-- Every Boolean algebra is an orthocomplemented lattice. The converse fails:
    ortholattices need not be distributive. Low priority so existing
    `BooleanAlgebra` API is preferred where applicable. -/
instance (priority := 100) instBooleanOrtho {α : Type*} [BooleanAlgebra α] :
    OrthocomplementedLattice α where
  compl_compl := _root_.compl_compl
  compl_antitone := fun h => _root_.compl_le_compl h
  inf_compl_le_bot := BooleanAlgebra.inf_compl_le_bot
  top_le_sup_compl := BooleanAlgebra.top_le_sup_compl

/-! ### Complete Orthocomplemented Lattices -/

/-- A complete lattice that is also orthocomplemented; bundled like
    `CompleteBooleanAlgebra` so the single `Lattice` is shared (no diamond). -/
class CompleteOrthocomplementedLattice (α : Type*) extends
  CompleteLattice α, OrthocomplementedLattice α
