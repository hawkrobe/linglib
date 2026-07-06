import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar
import Linglib.Core.Combinatorics.RootedTree.ContractUnary
import Linglib.Core.Data.RoseTree.Count
import Linglib.Syntax.Minimalist.Workspace.TraceMeasures

/-!
# Vertex conservation for the Δ^ρ / Δᵈ (deletion) cut enumeration
[marcolli-chomsky-berwick-2025]

The deletion coproduct `cutSummandsP` (MCB Δ^ρ, Def. 1.2.6) extracts a crown
forest and leaves the **remainder** `ρ_C(T)` — the cut subtrees are removed
entirely (no trace placeholder), so vertices are conserved exactly:
`Σ #V(crown) + #V(trunk) = #V(T)` (`cutSummandsP_numNodes`), with **no** `+#cuts`
correction (contrast the trace variant, which adds one replacement leaf per cut).

MCB's **Δᵈ** (Def. 1.2.5) rebinarizes the remainder via `contractUnary`; each
contracted unary node drops one vertex, giving the `+2`-per-cut accessible-term
extraction (eq. 1.6.7) downstream.
-/

namespace RootedTree

namespace ConnesKreimer

variable {α : Type*}

/-- The vertex count contributed by an `Option`-valued deletion remainder. -/
private def optNumNodes (o : Option (RoseTree α)) : ℕ := o.elim 0 RoseTree.numNodes

@[simp] private theorem optNumNodes_none : optNumNodes (none : Option (RoseTree α)) = 0 := rfl
@[simp] private theorem optNumNodes_some (t : RoseTree α) : optNumNodes (some t) = t.numNodes := rfl

mutual

/-- **Vertex conservation** for the deletion cut enumeration (tree level):
    crown vertices plus trunk vertices recover the tree's vertices exactly. -/
theorem cutSummandsP_numNodes :
    ∀ (t : RoseTree α), ∀ p ∈ cutSummandsP t,
      (Multiset.map RoseTree.numNodes p.1).sum + RoseTree.numNodes p.2 = RoseTree.numNodes t
  | .node a cs => by
    intro p hp
    rw [cutSummandsP_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsP_numNodes cs q hq
    simp only [RoseTree.numNodes_node]
    omega

/-- Mutual aux: vertex conservation for children-list deletion cut summands. -/
theorem cutListSummandsP_numNodes :
    ∀ (cs : List (RoseTree α)), ∀ q ∈ cutListSummandsP cs,
      (Multiset.map RoseTree.numNodes q.1).sum + (q.2.map RoseTree.numNodes).sum
        = (cs.map RoseTree.numNodes).sum
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
    have h1 := augActionP_numNodes t pr.1 ha
    have h2 := cutListSummandsP_numNodes ts pr.2 hq'
    cases hm : pr.1.2 with
    | none =>
      simp only [hm, optNumNodes_none] at h1
      show (Multiset.map RoseTree.numNodes (pr.1.1 + pr.2.1)).sum
          + (pr.2.2.map RoseTree.numNodes).sum
        = ((t :: ts).map RoseTree.numNodes).sum
      simp only [Multiset.map_add, Multiset.sum_add, List.map_cons, List.sum_cons]
      omega
    | some r =>
      simp only [hm, optNumNodes_some] at h1
      show (Multiset.map RoseTree.numNodes (pr.1.1 + pr.2.1)).sum
          + ((r :: pr.2.2).map RoseTree.numNodes).sum
        = ((t :: ts).map RoseTree.numNodes).sum
      simp only [Multiset.map_add, Multiset.sum_add, List.map_cons, List.sum_cons]
      omega

/-- Mutual aux: vertex conservation for per-child deletion actions. -/
theorem augActionP_numNodes :
    ∀ (t : RoseTree α), ∀ a ∈ augActionP t,
      (Multiset.map RoseTree.numNodes a.1).sum + optNumNodes a.2 = RoseTree.numNodes t
  | t => by
    intro a ha
    rw [augActionP_eq] at ha
    rcases Multiset.mem_cons.mp ha with h | h
    · obtain rfl := h
      show (Multiset.map RoseTree.numNodes {t}).sum + optNumNodes (none : Option (RoseTree α))
        = RoseTree.numNodes t
      rw [Multiset.map_singleton, Multiset.sum_singleton, optNumNodes_none]
      omega
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      show (Multiset.map RoseTree.numNodes p.1).sum + optNumNodes (some p.2) = RoseTree.numNodes t
      rw [optNumNodes_some]
      exact cutSummandsP_numNodes t p hp

end

/-! ### Nonplanar descent + Δᵈ extraction -/

/-- Vertex conservation for the nonplanar deletion cuts, descended from
    `cutSummandsP_numNodes`. -/
theorem cutSummandsN_numNodes (T : Nonplanar α) :
    ∀ p ∈ cutSummandsN T,
      (p.1.map Nonplanar.numNodes).sum + p.2.numNodes = T.numNodes := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsN_mk] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := cutSummandsP_numNodes T₀ q hq
  show ((q.1.map Nonplanar.mk).map Nonplanar.numNodes).sum + (Nonplanar.mk q.2).numNodes
    = (Nonplanar.mk T₀).numNodes
  rw [Nonplanar.numNodes_mk, Nonplanar.numNodes_mk, Multiset.map_map,
      show q.1.map (Nonplanar.numNodes ∘ Nonplanar.mk) = q.1.map RoseTree.numNodes from
        Multiset.map_congr rfl (fun x _ => Nonplanar.numNodes_mk x)]
  exact hcons

/-- **No proper cut extracts the whole tree as its crown.** For any cut summand
    `p ∈ cutSummandsN T`, the crown forest `p.1` is never the singleton `{T}`.
    The full-tree extraction is the separate `ofTree T ⊗ 1` term of `comulTreeN`,
    not a member of `cutSummandsN T`. Derived from vertex conservation
    (`cutSummandsN_numNodes`) plus `numNodes_pos`: a `{T}` crown would force the
    trunk to have zero vertices. Load-bearing for the Merge cross-term
    elimination (`Minimalist.Merge.mergeOp_pair`). -/
theorem cutSummandsN_crown_ne_singleton (T : Nonplanar α)
    (p : Forest (Nonplanar α) × Nonplanar α) (hp : p ∈ cutSummandsN T) :
    p.1 ≠ ({T} : Forest (Nonplanar α)) := by
  intro hcrown
  have hw := cutSummandsN_numNodes T p hp
  rw [hcrown] at hw
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at hw
  have := p.2.numNodes_pos
  omega

/-- **No cut of `T` has `T` itself in its crown.** Every crown component is a
    proper part of `T`, so it has strictly fewer vertices than `T`; the
    full-size `T` cannot be a crown member. From vertex conservation
    (`cutSummandsN_numNodes`) plus `numNodes_pos`. Mirrors legacy
    `CutShape.not_mem_cutForest_self`; load-bearing for the Sideward cross-term
    elimination (`Minimalist.Merge.mergeOp_sideward_2b/3b`). -/
theorem cutSummandsN_self_not_mem_crown (T : Nonplanar α)
    (p : Forest (Nonplanar α) × Nonplanar α) (hp : p ∈ cutSummandsN T) :
    T ∉ p.1 := by
  intro hT_mem
  have hw := cutSummandsN_numNodes T p hp
  have hp2 := p.2.numNodes_pos
  have h_le : T.numNodes ≤ (p.1.map Nonplanar.numNodes).sum :=
    Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hT_mem)
  omega

/-- **Single-cut Δᵈ accessible-term extraction** (MCB eq. 1.6.7): deleting one
    accessible subtree `mover` from `T` and rebinarizing the remainder
    (`contractUnary p.2`) removes two accessible terms — the subtree's edge and
    the contracted parent. The hypothesis `numUnary p.2 = 1` characterizes a
    single edge cut at a binary node (exactly one unary node is created). -/
theorem cutSummandsN_accCount_single_deletion (T : Nonplanar α)
    (p : Forest (Nonplanar α) × Nonplanar α) (hp : p ∈ cutSummandsN T)
    (mover : Nonplanar α) (hcard : p.1 = {mover}) (huc : p.2.numUnary = 1) :
    T.accCount = mover.accCount + (Nonplanar.contractUnary p.2).accCount + 2 := by
  have hw := cutSummandsN_numNodes T p hp
  have hcu := Nonplanar.numNodes_contractUnary_add_numUnary p.2
  have hmT := T.numNodes_pos
  have hmm := mover.numNodes_pos
  have hmp := p.2.numNodes_pos
  have hmc := (Nonplanar.contractUnary p.2).numNodes_pos
  rw [hcard] at hw
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at hw
  rw [huc] at hcu
  rw [Nonplanar.accCount_eq_numNodes_sub_one T, Nonplanar.accCount_eq_numNodes_sub_one mover,
      Nonplanar.accCount_eq_numNodes_sub_one (Nonplanar.contractUnary p.2)]
  omega

end ConnesKreimer

end RootedTree
