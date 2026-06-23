/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Graph

/-!
# Subgraph embedding for autosegmental graphs

This file introduces the autosegmental notion of one bipartite graph occurring as
a contiguous block of another. For two graphs `F` and `G`, `F` *subgraph-embeds*
into `G` when `F`'s upper and lower tiers appear as a contiguous block of `G`'s at
some offset `(δᵤ, δₗ)` and `F`'s association lines match `G`'s shifted by that
offset — equivalently, the embedding is a precedence-preserving translation.

This is the object-level containment relation that [jardine-2017]'s
forbidden-substructure analyses are stated over: an autosegmental representation
`G` is well-formed with respect to a forbidden set `{Fᵢ}` exactly when no `Fᵢ`
subgraph-embeds into `G`. It is defined on the raw `Graph` object, with no
morphism machinery, so consumers need only the object layer rather than
`GraphHom`. The mathlib analogue is `SimpleGraph.IsContained` / `SimpleGraph.Free`,
likewise kept out of the homomorphism file.

## Main definitions

* `Autosegmental.Graph.IsSubgraphAt F G δᵤ δₗ` is the proposition that `F` sits as
  a contiguous block of `G` at offset `(δᵤ, δₗ)`.
* `Autosegmental.Graph.SubgraphEmbeds F G` is the (decidable) relation that `F`
  subgraph-embeds into `G` at some offset.
-/

namespace Autosegmental

namespace Graph

variable {α β : Type*}

/-- F's upper tier appears at offset `δᵤ` in G's upper tier, F's lower tier at
    offset `δₗ` in G's lower tier, and all of F's association lines are present
    in G shifted by `(δᵤ, δₗ)`. -/
def IsSubgraphAt (F G : Graph α β) (δᵤ δₗ : Nat) : Prop :=
  (∀ i, i < F.upper.length → G.upper[i + δᵤ]? = F.upper[i]?) ∧
  (∀ j, j < F.lower.length → G.lower[j + δₗ]? = F.lower[j]?) ∧
  (∀ p ∈ F.links, (p.fst + δᵤ, p.snd + δₗ) ∈ G.links)

instance [DecidableEq α] [DecidableEq β] (F G : Graph α β) (δᵤ δₗ : Nat) :
    Decidable (IsSubgraphAt F G δᵤ δₗ) := by
  unfold IsSubgraphAt; infer_instance

/-- `F` **subgraph-embeds** into `G` iff some offset `(δᵤ, δₗ)` places F as a
    contiguous block inside G — [jardine-2017]'s connected-subgraph embedding. -/
def SubgraphEmbeds (F G : Graph α β) : Prop :=
  ∃ δᵤ ∈ Finset.range (G.upper.length + 1),
  ∃ δₗ ∈ Finset.range (G.lower.length + 1),
    IsSubgraphAt F G δᵤ δₗ

instance [DecidableEq α] [DecidableEq β] (F G : Graph α β) :
    Decidable (SubgraphEmbeds F G) := by
  unfold SubgraphEmbeds; infer_instance

/-- `SubgraphEmbeds` is reflexive: F is a subgraph of itself at offset `(0, 0)`. -/
theorem SubgraphEmbeds.refl (G : Graph α β) : SubgraphEmbeds G G := by
  refine ⟨0, ?_, 0, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro i hi; simp
  · intro j hj; simp
  · intro p hp; simpa using hp

end Graph

end Autosegmental
