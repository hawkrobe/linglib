import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar
import Linglib.Core.Combinatorics.RootedTree.Rebinarize
import Linglib.Core.Combinatorics.RootedTree.Counting

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

open _root_.RootedTree.Planar

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

/-! ### Nonplanar descent + Δᵈ extraction -/

/-- Vertex conservation for the nonplanar deletion cuts, descended from
    `cutSummandsP_weight`. -/
theorem cutSummandsN_weight (T : Nonplanar α) :
    ∀ p ∈ cutSummandsN T,
      (p.1.map Nonplanar.weight).sum + p.2.weight = T.weight := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : Planar α, T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsN_mk] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := cutSummandsP_weight T₀ q hq
  show ((q.1.map Nonplanar.mk).map Nonplanar.weight).sum + (Nonplanar.mk q.2).weight
    = (Nonplanar.mk T₀).weight
  rw [Nonplanar.weight_mk, Nonplanar.weight_mk, Multiset.map_map,
      show q.1.map (Nonplanar.weight ∘ Nonplanar.mk) = q.1.map Planar.weight from
        Multiset.map_congr rfl (fun x _ => Nonplanar.weight_mk x)]
  exact hcons

/-- **Single-cut Δᵈ accessible-term extraction** (MCB eq. 1.6.7): deleting one
    accessible subtree `mover` from `T` and rebinarizing the remainder
    (`contractUnary p.2`) removes two accessible terms — the subtree's edge and
    the contracted parent. The hypothesis `unaryCount p.2 = 1` characterizes a
    single edge cut at a binary node (exactly one unary node is created). -/
theorem cutSummandsN_accCount_single_deletion (T : Nonplanar α)
    (p : Forest (Nonplanar α) × Nonplanar α) (hp : p ∈ cutSummandsN T)
    (mover : Nonplanar α) (hcard : p.1 = {mover}) (huc : p.2.unaryCount = 1) :
    T.accCount = mover.accCount + (Nonplanar.contractUnary p.2).accCount + 2 := by
  have hw := cutSummandsN_weight T p hp
  have hcu := Nonplanar.weight_contractUnary_add p.2
  have hmT := T.weight_pos
  have hmm := mover.weight_pos
  have hmp := p.2.weight_pos
  have hmc := (Nonplanar.contractUnary p.2).weight_pos
  rw [hcard] at hw
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at hw
  rw [huc] at hcu
  rw [Nonplanar.accCount_eq_weight_sub_one T, Nonplanar.accCount_eq_weight_sub_one mover,
      Nonplanar.accCount_eq_weight_sub_one (Nonplanar.contractUnary p.2)]
  omega

end ConnesKreimer

end RootedTree
