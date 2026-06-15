import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning

/-!
# Weight conservation for the Δ^ρ / Δᵈ (deletion) cut enumeration
[marcolli-chomsky-berwick-2025]

The deletion coproduct `cutSummandsP` (MCB Δ^ρ, Def. 1.2.6) extracts a crown
forest and leaves the **remainder** `ρ_C(T)` — the cut subtrees are removed
entirely (no trace placeholder), so vertices are conserved exactly:
`Σ #V(crown) + #V(trunk) = #V(T)` (`cutSummandsP_weight`), with **no** `+#cuts`
correction (contrast the trace variant, which adds one replacement leaf per cut).

MCB's **Δᵈ** (Def. 1.2.5) rebinarizes the remainder via `contractUnary`; each
contracted unary node drops one vertex, giving the `+2`-per-cut accessible-term
extraction (eq. 1.6.7) downstream.
-/

namespace RootedTree

namespace ConnesKreimer

open Planar

variable {α : Type*}

/-- The weight contributed by an `Option`-valued deletion remainder. -/
private def optWeight (o : Option (Planar α)) : ℕ := o.elim 0 Planar.weight

@[simp] private theorem optWeight_none : optWeight (none : Option (Planar α)) = 0 := rfl
@[simp] private theorem optWeight_some (t : Planar α) : optWeight (some t) = t.weight := rfl

mutual

/-- **Vertex conservation** for the deletion cut enumeration (tree level):
    crown vertices plus trunk vertices recover the tree's vertices exactly. -/
theorem cutSummandsP_weight :
    ∀ (t : Planar α), ∀ p ∈ cutSummandsP t,
      (Multiset.map Planar.weight p.1).sum + Planar.weight p.2 = Planar.weight t
  | .node a cs => by
    intro p hp
    rw [cutSummandsP_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsP_weight cs q hq
    show (Multiset.map Planar.weight q.1).sum + (1 + weightList q.2) = 1 + weightList cs
    omega

/-- Mutual aux: vertex conservation for children-list deletion cut summands. -/
theorem cutListSummandsP_weight :
    ∀ (cs : List (Planar α)), ∀ q ∈ cutListSummandsP cs,
      (Multiset.map Planar.weight q.1).sum + weightList q.2 = weightList cs
  | [] => by
    intro q hq
    rw [cutListSummandsP_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    rfl
  | t :: ts => by
    intro q hq
    rw [cutListSummandsP_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionP_weight t pr.1 ha
    have h2 := cutListSummandsP_weight ts pr.2 hq'
    cases hm : pr.1.2 with
    | none =>
      simp only [hm, optWeight_none] at h1
      show (Multiset.map Planar.weight (pr.1.1 + pr.2.1)).sum + weightList pr.2.2
        = weight t + weightList ts
      rw [Multiset.map_add, Multiset.sum_add]
      omega
    | some r =>
      simp only [hm, optWeight_some] at h1
      show (Multiset.map Planar.weight (pr.1.1 + pr.2.1)).sum + weightList (r :: pr.2.2)
        = weight t + weightList ts
      rw [Multiset.map_add, Multiset.sum_add]
      show (Multiset.map Planar.weight pr.1.1).sum + (Multiset.map Planar.weight pr.2.1).sum
          + (weight r + weightList pr.2.2) = weight t + weightList ts
      omega

/-- Mutual aux: vertex conservation for per-child deletion actions. -/
theorem augActionP_weight :
    ∀ (t : Planar α), ∀ a ∈ augActionP t,
      (Multiset.map Planar.weight a.1).sum + optWeight a.2 = Planar.weight t
  | t => by
    intro a ha
    rw [augActionP_eq] at ha
    rcases Multiset.mem_cons.mp ha with h | h
    · obtain rfl := h
      show (Multiset.map Planar.weight {t}).sum + optWeight (none : Option (Planar α))
        = Planar.weight t
      rw [Multiset.map_singleton, Multiset.sum_singleton, optWeight_none]
      omega
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      show (Multiset.map Planar.weight p.1).sum + optWeight (some p.2) = Planar.weight t
      rw [optWeight_some]
      exact cutSummandsP_weight t p hp

end

end ConnesKreimer

end RootedTree
