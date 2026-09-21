module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset

/-!
# Maximal independent sets of a finite graph

This file characterizes the finite maximal independent sets of a simple graph and enumerates
them. A finite set of vertices is a maximal independent set exactly when it is independent and
every vertex outside it is adjacent to one inside, which is decidable, so the maximal
independent sets of a finite graph form a computable finset.

## Main definitions

* `SimpleGraph.maximalIndepSets`: the finset of maximal independent sets of a finite graph.

## Main results

* `SimpleGraph.maximal_isIndepSet_coe_iff`: a finset is a maximal independent set exactly when
  it is independent and dominating.
* `SimpleGraph.mem_maximalIndepSets`: membership in `maximalIndepSets` is `Maximal
  G.IsIndepSet`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {s : Finset V}

/-- A finset of vertices is a maximal independent set exactly when it is independent and every
vertex outside it is adjacent to one inside. -/
theorem maximal_isIndepSet_coe_iff :
    Maximal G.IsIndepSet (s : Set V) ↔ G.IsIndepSet ↑s ∧ ∀ v ∉ s, ∃ w ∈ s, G.Adj v w := by
  constructor
  · rintro ⟨hs, hmax⟩
    refine ⟨hs, λ v hv => ?_⟩
    by_contra h
    push Not at h
    have hi : G.IsIndepSet (insert v (s : Set V)) := by
      rw [isIndepSet_iff, Set.pairwise_insert]
      exact ⟨hs, λ w hw _ => ⟨h w hw, λ h' => h w hw h'.symm⟩⟩
    exact hv (hmax hi (Set.subset_insert v _) (Set.mem_insert v _))
  · rintro ⟨hs, h⟩
    refine ⟨hs, λ t ht hst u hu => ?_⟩
    by_contra hu'
    obtain ⟨w, hw, hadj⟩ := h u hu'
    exact ht hu (hst hw) hadj.ne hadj

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The maximal independent sets of a finite graph. -/
def maximalIndepSets : Finset (Finset V) :=
  Finset.univ.powerset.filter λ s => G.IsIndepSet ↑s ∧ ∀ v, v ∉ s → ∃ w ∈ s, G.Adj v w

@[simp] theorem mem_maximalIndepSets : s ∈ G.maximalIndepSets ↔ Maximal G.IsIndepSet ↑s := by
  simp [maximalIndepSets, maximal_isIndepSet_coe_iff]

end SimpleGraph
