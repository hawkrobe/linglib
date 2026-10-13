/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
public import Linglib.Core.Combinatorics.RootedTree.ContractUnary
public import Linglib.Syntax.Minimalist.Coproduct.CutFilterMap
public import Linglib.Syntax.Minimalist.Coproduct.Trace

/-!
# The deletion coproduct and the erasure of traces

Marcolli, Chomsky and Berwick extract accessible terms from a syntactic object with three
coproducts, which differ in the remainder an extraction leaves. `Δ^c` contracts each extracted
term to a trace leaf, `Δ^ρ` leaves the remainder of the admissible cut, and `Δ^d` deletes the
term and contracts the vertices left with a single child. They relate the three by projections
of the right channel: `Π_{ρ,c}` deletes the trace leaves, `Π_{d,ρ}` contracts the non-branching
vertices, and `Δ^d = (id ⊗ Π_{d,ρ}) ∘ Δ^ρ = (id ⊗ Π_{d,ρ} ∘ Π_{ρ,c}) ∘ Δ^c`, displayed before
their (1.3.10). Here `Δ^d` is defined by the first expression, and the second is proved for trees
without traces.

## Main definitions

* `ConnesKreimer.eraseTraces`: the projection that deletes every trace vertex.
* `ConnesKreimer.comulDAlgHomN`: the deletion coproduct, which is the pruning coproduct with the
  unary vertices of each trunk contracted.

## Main results

* `ConnesKreimer.eraseTraces_comp_rename_inl`: erasure is a retraction of the embedding of the
  trees without traces.
* `ConnesKreimer.eraseTraces_comulCAlgHomN`: on trees without traces, erasing the traces that the
  trace coproduct leaves gives the pruning coproduct.
* `ConnesKreimer.contractUnary_eraseTraces_comulCAlgHomN`: erasing them and contracting the unary
  vertices gives the deletion coproduct.

## Implementation notes

* Trees without traces are `UnorderedTree α` and trees with traces are `UnorderedTree (α ⊕ β)`,
  so the relations hold along the embedding `rename (UnorderedTree.map Sum.inl)`. The left
  channel of `Δ^c` on an embedded tree is embedded and the right channel is not, which is why
  the projections act on the right channel alone.
* The book's `Π_{d,ρ}` takes a tree whose vertices have at most two children to the maximal
  binary tree obtained by contracting edges. Here it is `UnorderedTree.contractUnary`, on trees
  of any arity.
* `Δ^d` carries no `Bialgebra` structure: its coassociativity holds only up to the multiplicity
  of some terms (the book's Lemma 1.2.12).

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### Erasing traces -/

/-- `eraseTraces` is the projection `Π_{ρ,c}`. It sends a tree whose root is a trace to `1` and
    removes from any other tree the subtrees rooted at a trace. -/
noncomputable def eraseTraces :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₐ[R] ConnesKreimer R (UnorderedTree α) :=
  aeval fun T ↦ (T.filterMap Sum.getLeft?).elim 1 ofTree

@[simp] theorem eraseTraces_ofTree (T : UnorderedTree (α ⊕ β)) :
    eraseTraces (R := R) (ofTree T) = (T.filterMap Sum.getLeft?).elim 1 ofTree :=
  aeval_ofTree _ T

/-- Erasure is a retraction of the embedding of the trees without traces. -/
theorem eraseTraces_comp_rename_inl :
    (eraseTraces (R := R) (β := β)).comp (rename (UnorderedTree.map Sum.inl)) =
      AlgHom.id R (ConnesKreimer R (UnorderedTree α)) := by
  ext T
  simp

/-- On trees without traces, erasing the traces that `Δ^c` leaves in the right channel gives the
    pruning coproduct `Δ^ρ`. -/
theorem eraseTraces_comulCAlgHomN (τ : UnorderedTree (α ⊕ β) → β) :
    ((Algebra.TensorProduct.map (.id R _) eraseTraces).comp (comulCAlgHomN τ)).comp
        (rename (UnorderedTree.map Sum.inl)) =
      (Algebra.TensorProduct.map (rename (UnorderedTree.map Sum.inl)) (.id R _)).comp
        (comulAlgHomN (R := R) (α := α)) := by
  ext T
  have h := congrArg (fun s ↦ (s.map fun q : Multiset (UnorderedTree (α ⊕ β)) ×
      Option (UnorderedTree α) ↦ of' (R := R) q.1 ⊗ₜ[R] q.2.elim 1 (ofTree (R := R))).sum)
    (cutSummandsCN_map_inl τ T)
  simp only [Multiset.map_map, Function.comp_def, Prod.map_apply', id, Option.elim_some] at h
  simp [comulCTreeN, comulTreeN, comulTreeNG, map_multiset_sum, Multiset.map_map,
    Function.comp_def, h]

/-! ### The deletion coproduct -/

/-- The deletion coproduct `Δ^d` is the pruning coproduct `Δ^ρ` followed, on the right channel,
    by the contraction `Π_{d,ρ}` of unary vertices. -/
noncomputable def comulDAlgHomN : ConnesKreimer R (UnorderedTree α) →ₐ[R]
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  (Algebra.TensorProduct.map (.id R _) (rename UnorderedTree.contractUnary)).comp comulAlgHomN

/-- On a tree, `Δ^d` sums the pruning cuts with the unary vertices of each trunk contracted. -/
theorem comulDAlgHomN_apply_ofTree (T : UnorderedTree α) :
    comulDAlgHomN (R := R) (ofTree T) = ofTree T ⊗ₜ[R] 1 +
      ((cutSummandsN T).map fun p ↦ of' (R := R) p.1 ⊗ₜ[R] ofTree p.2.contractUnary).sum := by
  simp [comulDAlgHomN, comulTreeN, comulTreeNG, map_multiset_sum, Multiset.map_map]

/-- On trees without traces, erasing the traces that `Δ^c` leaves and contracting the unary
    vertices gives the deletion coproduct `Δ^d`. -/
theorem contractUnary_eraseTraces_comulCAlgHomN (τ : UnorderedTree (α ⊕ β) → β) :
    ((Algebra.TensorProduct.map (.id R _)
          ((rename UnorderedTree.contractUnary).comp eraseTraces)).comp (comulCAlgHomN τ)).comp
        (rename (UnorderedTree.map Sum.inl)) =
      (Algebra.TensorProduct.map (rename (UnorderedTree.map Sum.inl)) (.id R _)).comp
        (comulDAlgHomN (R := R) (α := α)) := by
  have h := congrArg
    (AlgHom.comp (Algebra.TensorProduct.map (.id R _) (rename UnorderedTree.contractUnary)))
    (eraseTraces_comulCAlgHomN (R := R) τ)
  simpa only [comulDAlgHomN, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    AlgHom.comp_id, AlgHom.id_comp] using h

end ConnesKreimer
