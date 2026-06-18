import Mathlib.Order.Concept
import Linglib.Core.Order.Ortholattice

/-!
# The ortholattice of a symmetric, irreflexive relation

[UPSTREAM] candidate.

For a symmetric, irreflexive relation `r : S → S → Prop` — an *orthogonality*
relation, written `x ⊥ y` — the formal `Concept`s of `r` form an
`OrthocomplementedLattice`. The lattice structure is mathlib's concept lattice
(`Mathlib.Order.Concept`); the new content is the orthocomplement
`Aᶜ = upperPolar r A = {x | ∀ y ∈ A, x ⊥ y}`, which for symmetric `r`
restricts to an order-reversing involution on extents.

This is the framework-agnostic core of possibility semantics for orthologic
([holliday-mandelkern-2024] Proposition 4.8): the `Semantics.Modality.Orthologic`
stack is the special case `r = ¬compat`, where `orthoNeg = upperPolar r`,
`regularClosure = extentClosure r`, and the load-bearing involutivity
(Proposition 4.8) is mathlib's `upperPolar_lowerPolar_upperPolar`. The bridge to
that stack lives downstream (Core cannot import the semantics layer).

## Main definitions

* `Concept.instCompl` — the orthocomplement `Aᶜ = upperPolar r A`.
* `Concept.instOrthocomplementedLattice` — the concept lattice of a symmetric,
  irreflexive relation is an ortholattice.
* `Orthoframe` — a bundled symmetric, irreflexive orthogonality relation;
  `Orthoframe.Regular F` is its ortholattice of regular propositions.

## TODO

* Goldblatt representation ([holliday-mandelkern-2024] Theorem 4.13): every
  complete ortholattice is isomorphic to `Orthoframe.Regular` of its canonical
  orthoframe on a join-dense set, with `a ⊥ b ↔ a ≤ bᶜ`.
-/

open Order Set

namespace Order

variable {S : Type*} (r : S → S → Prop)

/-- For a symmetric relation the upper and lower polars coincide. -/
theorem upperPolar_eq_lowerPolar [Std.Symm r] (s : Set S) :
    upperPolar r s = lowerPolar r s :=
  Set.ext fun _ => ⟨fun h _ ha => Std.Symm.symm _ _ (h ha), fun h _ ha => Std.Symm.symm _ _ (h ha)⟩

/-- For a symmetric relation the upper polar of any set is an extent. -/
theorem isExtent_upperPolar [Std.Symm r] (s : Set S) : IsExtent r (upperPolar r s) := by
  rw [upperPolar_eq_lowerPolar r]; exact isExtent_lowerPolar

end Order

namespace Concept

variable {S : Type*} (r : S → S → Prop)

/-- Orthocomplement of a concept: the concept whose extent is the intent
    (`= upperPolar r`) of `c`. Well-defined because `r` is symmetric. -/
instance instCompl [Std.Symm r] : Compl (Concept S S r) where
  compl c := .ofIsExtent r c.intent <| c.upperPolar_extent ▸ Order.isExtent_upperPolar r c.extent

@[simp] theorem extent_compl [Std.Symm r] (c : Concept S S r) : cᶜ.extent = c.intent := rfl

@[simp] theorem intent_compl [Std.Symm r] (c : Concept S S r) :
    cᶜ.intent = upperPolar r c.intent := rfl

/-- The concepts of a symmetric, irreflexive relation form an orthocomplemented
    lattice ([holliday-mandelkern-2024] Proposition 4.8). The lattice structure
    is mathlib's concept lattice; only the orthocomplement and its four axioms
    are new. -/
instance instOrthocomplementedLattice [Std.Symm r] [Std.Irrefl r] :
    OrthocomplementedLattice (Concept S S r) where
  compl_compl c := Concept.ext <| by simp [Order.upperPolar_eq_lowerPolar]
  compl_antitone {c d} h := by
    show d.intent ⊆ c.intent
    rw [← c.upperPolar_extent, ← d.upperPolar_extent]; exact upperPolar_anti r h
  inf_compl_le_bot c := fun x hx => absurd (rel_extent_intent hx.1 hx.2) (Std.Irrefl.irrefl x)
  top_le_sup_compl c := fun _ _ a ha => absurd (ha.2 ha.1) (Std.Irrefl.irrefl a)

end Concept

/-! ### Bundled orthoframes -/

/-- An **orthoframe**: a set with a symmetric, irreflexive orthogonality
    relation `ortho` (written `x ⊥ y`). Its regular propositions form an
    ortholattice (`Orthoframe.Regular`). The `Semantics.Modality.Orthologic`
    compatibility frames are the special case `ortho = ¬compat`. -/
structure Orthoframe (S : Type*) where
  /-- The orthogonality relation, written `x ⊥ y`. -/
  ortho : S → S → Prop
  [ortho_symm : Std.Symm ortho]
  [ortho_irrefl : Std.Irrefl ortho]

namespace Orthoframe

variable {S : Type*}

attribute [instance] ortho_symm ortho_irrefl

/-- The ortholattice of regular propositions of an orthoframe: the concepts of
    its orthogonality relation. -/
abbrev Regular (F : Orthoframe S) : Type _ := Concept S S F.ortho

instance (F : Orthoframe S) : OrthocomplementedLattice F.Regular :=
  Concept.instOrthocomplementedLattice F.ortho

end Orthoframe
