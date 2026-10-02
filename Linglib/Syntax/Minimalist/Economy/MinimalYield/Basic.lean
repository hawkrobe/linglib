module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Linglib.Syntax.Minimalist.Workspace.TraceMeasures
public import Mathlib.Order.OrderDual

/-!
# Minimal Yield

Minimal Yield ([marcolli-chomsky-berwick-2025] Definition 1.6.1) is a condition on a transformation
`F → F'` of workspaces: the number `b₀` of components does not grow (no divergence), the number
`α` of accessible terms does not fall (no information loss), and the size `σ = b₀ + α` grows by
exactly one (minimality of yield). `MinimalYieldWeak` is the first two bounds and `MinimalYield`
all three. Both take the count of accessible terms of a component as a parameter, since
Proposition 1.6.4 evaluates the one condition under two countings: the deletion coproduct counts
every non-root vertex (`UnorderedTree.numEdges`), the trace coproduct every non-root vertex but its
trace leaves (`UnorderedTree.accessibleCount`). The weak form is monotonicity of the signature
`(b₀ᵒᵈ, α)` (`minimalYieldWeak_iff_signature_le`).

On the carrier `UnorderedTree (α ⊕ β)`, with `Sum.inr` marking a trace, External Merge satisfies
Minimal Yield under both countings. Internal Merge through a trace cut satisfies it under trace
counting; under deletion counting it preserves all three measures and satisfies only the weak
form. The divergent Sideward cases 3(a) and 3(b), which raise the number of components, violate
both forms under any counting.

## Main definitions

* `Minimalist.MinimalYieldWeak`, `Minimalist.MinimalYield`
* `Minimalist.MinimalYield.signature`: the Pareto signature `(b₀ᵒᵈ, α)`.

## Main results

* `Minimalist.MinimalYield.em_pair`, `MinimalYield.em_pair_accessibleCount`: External Merge
  satisfies Minimal Yield under either counting.
* `Minimalist.MinimalYield.im_accessibleCount_of_cut`: Internal Merge through a trace cut
  satisfies it under trace counting.
* `Minimalist.MinimalYield.add_right`: spectators preserve it.
* `Minimalist.MinimalYield.not_sideward_3a`, `not_sideward_3b`: the divergent Sideward cases do
  not satisfy it.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree ConnesKreimer

variable {α β κ : Type*}

/-! ### The Minimal Yield principle -/

/-- The weak Minimal Yield principle, for the count `acc` of the accessible terms of a component,
    allows no increase in the number `b₀` of components and no decrease in the number `α` of
    accessible terms. -/
structure MinimalYieldWeak (acc : κ → ℕ) (F F' : Multiset κ) : Prop where
  noDivergence : Multiset.card F' ≤ Multiset.card F
  noInfoLoss : (F.map acc).sum ≤ (F'.map acc).sum

/-- The Minimal Yield principle is the weak form together with the size `σ = b₀ + α` going up by
    exactly one. -/
structure MinimalYield (acc : κ → ℕ) (F F' : Multiset κ) : Prop
    extends MinimalYieldWeak acc F F' where
  minimalYield : Multiset.card F' + (F'.map acc).sum = Multiset.card F + (F.map acc).sum + 1

/-- Spectators preserve Minimal Yield. -/
theorem MinimalYield.add_right {acc : κ → ℕ} {F F' : Multiset κ} (h : MinimalYield acc F F')
    (W : Multiset κ) : MinimalYield acc (F + W) (F' + W) where
  noDivergence := by simpa using h.noDivergence
  noInfoLoss := by simpa using h.noInfoLoss
  minimalYield := by
    simp only [Multiset.card_add, Multiset.map_add, Multiset.sum_add]
    have := h.minimalYield
    omega

/-! ### `MinimalYieldWeak` as a Pareto pullback preorder -/

/-- The Pareto signature `(b₀ᵒᵈ, α)`, `b₀` dualised so fewer components ranks higher. -/
def MinimalYield.signature (acc : κ → ℕ) (F : Multiset κ) : ℕᵒᵈ × ℕ :=
  (OrderDual.toDual (Multiset.card F), (F.map acc).sum)

theorem minimalYieldWeak_iff_signature_le {acc : κ → ℕ} {F F' : Multiset κ} :
    MinimalYieldWeak acc F F' ↔ MinimalYield.signature acc F ≤ MinimalYield.signature acc F' :=
  ⟨fun ⟨h_b, h_a⟩ ↦ ⟨h_b, h_a⟩, fun ⟨h_b, h_a⟩ ↦ ⟨h_b, h_a⟩⟩

/-! ### External Merge -/

/-- External Merge of a pair satisfies Minimal Yield under deletion counting, with Δb₀ = −1,
    Δα = +2 and Δσ = +1. -/
theorem MinimalYield.em_pair (lbl : α) (S S' : UnorderedTree (α ⊕ β)) :
    MinimalYield UnorderedTree.numEdges ({S, S'} : Forest (UnorderedTree (α ⊕ β)))
      {UnorderedTree.node (Sum.inl lbl) {S, S'}} := by
  have hnode := UnorderedTree.numEdges_node_pair (Sum.inl lbl) S S'
  refine ⟨⟨by simp, ?_⟩, ?_⟩ <;>
  · rw [Multiset.map_singleton, Multiset.sum_singleton, hnode]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_cons, Multiset.card_singleton]
    omega

/-- External Merge of two objects that are not traces satisfies Minimal Yield under trace
    counting. -/
theorem MinimalYield.em_pair_accessibleCount (lbl : α) {S S' : UnorderedTree (α ⊕ β)}
    (hS : S.traceLeafCount < S.numNodes) (hS' : S'.traceLeafCount < S'.numNodes) :
    MinimalYield UnorderedTree.accessibleCount ({S, S'} : Forest (UnorderedTree (α ⊕ β)))
      {UnorderedTree.node (Sum.inl lbl) {S, S'}} := by
  have hnode := UnorderedTree.accessibleCount_merge lbl S S' hS hS'
  refine ⟨⟨by simp, ?_⟩, ?_⟩ <;>
  · rw [Multiset.map_singleton, Multiset.sum_singleton, hnode]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_cons, Multiset.card_singleton]
    omega

/-! ### Internal Merge -/

/-- Internal Merge via composition leaves `b₀`, `α`, `σ` unchanged under Δᵈ counting, given the
    accessible-term relation `α(T) = α(mover) + α(Q) + 2` of [marcolli-chomsky-berwick-2025]
    (1.6.7). -/
theorem im_pair_size_deltas_deletion (lbl : α) {T mover Q : UnorderedTree (α ⊕ β)}
    (h : T.numEdges = mover.numEdges + Q.numEdges + 2) :
    Multiset.card ({UnorderedTree.node (Sum.inl lbl) {mover, Q}} : Forest (UnorderedTree (α ⊕ β)))
        = Multiset.card ({T} : Forest (UnorderedTree (α ⊕ β)))
      ∧ (({UnorderedTree.node (Sum.inl lbl) {mover, Q}} : Forest (UnorderedTree
        (α ⊕ β))).map UnorderedTree.numEdges).sum
        = (({T} : Forest (UnorderedTree (α ⊕ β))).map UnorderedTree.numEdges).sum
      ∧ (({UnorderedTree.node (Sum.inl lbl) {mover, Q}} : Forest (UnorderedTree
        (α ⊕ β))).map UnorderedTree.numNodes).sum
        = (({T} : Forest (UnorderedTree (α ⊕ β))).map UnorderedTree.numNodes).sum := by
  have hnode : (UnorderedTree.node (Sum.inl lbl) {mover, Q}).numEdges
      = mover.numEdges + Q.numEdges + 2 := UnorderedTree.numEdges_node_pair (Sum.inl lbl) mover Q
  refine ⟨rfl, ?_, ?_⟩
  · rw [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_singleton,
      Multiset.sum_singleton, hnode]
    omega
  · simp only [Multiset.map_singleton, Multiset.sum_singleton, ← UnorderedTree.numEdges_add_one]
    omega

/-- This is `im_pair_size_deltas_deletion` with the α relation discharged from a Δᵈ admissible cut.
Deleting `mover` from `T` and rebinarizing the remainder (`contractUnary p.2`) leaves `b₀`, `α` and
`σ` unchanged, and `numUnary p.2 = 1` characterizes a single edge cut at a binary node. -/
theorem im_pair_size_deltas_deletion_of_cut (lbl : α) (T : UnorderedTree (α ⊕ β))
    (p : Forest (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)) (hp
      : p ∈ ConnesKreimer.cutSummandsN T)
    (mover : UnorderedTree (α ⊕ β)) (hcard : p.1 = {mover}) (huc : p.2.numUnary = 1) :
    Multiset.card ({UnorderedTree.node (Sum.inl lbl) {mover, UnorderedTree.contractUnary p.2}}
        : Forest (UnorderedTree (α ⊕ β))) = Multiset.card ({T} : Forest (UnorderedTree (α ⊕ β)))
      ∧ (({UnorderedTree.node (Sum.inl lbl) {mover, UnorderedTree.contractUnary p.2}}
        : Forest (UnorderedTree (α ⊕ β))).map UnorderedTree.numEdges).sum
        = (({T} : Forest (UnorderedTree (α ⊕ β))).map UnorderedTree.numEdges).sum
      ∧ (({UnorderedTree.node (Sum.inl lbl) {mover, UnorderedTree.contractUnary p.2}}
        : Forest (UnorderedTree (α ⊕ β))).map UnorderedTree.numNodes).sum =
          (({T} : Forest (UnorderedTree (α ⊕ β))).map UnorderedTree.numNodes).sum :=
  im_pair_size_deltas_deletion lbl
    (ConnesKreimer.cutSummandsN_numEdges_single_deletion T p hp mover hcard huc)

/-- Internal Merge via composition leaves `b₀` fixed and raises `αᶜ` and `σᶜ` by one under Δᶜ
counting, given the relation `αᶜ(T) = αᶜ(β_t) + αᶜ(trunk) + 1` of
[marcolli-chomsky-berwick-2025] (1.6.8). -/
theorem im_pair_size_deltas_contraction (lbl : α) {T β_t Q : UnorderedTree (α ⊕ β)}
    (hβ : β_t.traceLeafCount < β_t.numNodes) (hQ : Q.traceLeafCount < Q.numNodes)
    (h : T.accessibleCount = β_t.accessibleCount + Q.accessibleCount + 1) :
    Multiset.card ({UnorderedTree.node (Sum.inl lbl) {β_t, Q}} : Forest (UnorderedTree (α ⊕ β)))
        = Multiset.card ({T} : Forest (UnorderedTree (α ⊕ β)))
      ∧ Forest.accessibleCount
          ({UnorderedTree.node (Sum.inl lbl) {β_t, Q}} : Forest (UnorderedTree (α ⊕ β)))
        = Forest.accessibleCount ({T} : Forest (UnorderedTree (α ⊕ β))) + 1
      ∧ Forest.accessibleSize ({UnorderedTree.node (Sum.inl lbl) {β_t, Q}} : Forest (UnorderedTree
        (α ⊕ β)))
        = Forest.accessibleSize ({T} : Forest (UnorderedTree (α ⊕ β))) + 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [Forest.accessibleCount_singleton, Forest.accessibleCount_singleton,
        UnorderedTree.accessibleCount_merge lbl β_t Q hβ hQ]
    omega
  · simp only [Forest.accessibleSize, Multiset.card_singleton, Forest.accessibleCount_singleton]
    rw [UnorderedTree.accessibleCount_merge lbl β_t Q hβ hQ]
    omega

/-- This is `im_pair_size_deltas_contraction` with the αᶜ relation discharged from a Δᶜ admissible
cut. Re-merging an accessible subtree `β_t` of `T = node (inl a₀) F₀` with the contraction quotient
`p.2` raises `αᶜ` and `σᶜ` by one. -/
theorem im_pair_size_deltas_contraction_of_cut (lbl a₀ : α)
    (τ : UnorderedTree (α ⊕ β) → β) (F₀ : Forest (UnorderedTree (α ⊕ β)))
    (p : Forest (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β))
    (hp : p ∈ cutSummandsCN τ (UnorderedTree.node (Sum.inl a₀) F₀))
    (β_t : UnorderedTree (α ⊕ β)) (hcard : p.1 = {β_t}) :
    Multiset.card ({UnorderedTree.node (Sum.inl lbl) {β_t, p.2}} : Forest (UnorderedTree (α ⊕ β)))
        = Multiset.card ({UnorderedTree.node (Sum.inl a₀) F₀} : Forest (UnorderedTree (α ⊕ β)))
      ∧ Forest.accessibleCount
          ({UnorderedTree.node (Sum.inl lbl) {β_t, p.2}} : Forest (UnorderedTree (α ⊕ β)))
        = Forest.accessibleCount
          ({UnorderedTree.node (Sum.inl a₀) F₀} : Forest (UnorderedTree (α ⊕ β))) + 1
      ∧ Forest.accessibleSize
          ({UnorderedTree.node (Sum.inl lbl) {β_t, p.2}} : Forest (UnorderedTree (α ⊕ β)))
        = Forest.accessibleSize
          ({UnorderedTree.node (Sum.inl a₀) F₀} : Forest (UnorderedTree (α ⊕ β))) + 1 :=
  im_pair_size_deltas_contraction lbl
    (cutSummandsCN_crown_traceLeafCount_lt_numNodes τ _ p hp β_t
      (by rw [hcard]; exact Multiset.mem_singleton_self β_t))
    (UnorderedTree.traceLeafCount_lt_numNodes_of_rootInl p.2 a₀
      ((cutSummandsCN_trunk_value τ _ p hp).trans (by rw [UnorderedTree.value_node])))
    (cutSummandsCN_accessibleCount_single τ _ a₀ F₀ rfl p hp β_t hcard)

/-- Internal Merge through a trace cut satisfies Minimal Yield under trace counting, with Δb₀ = 0,
    Δα = +1 and Δσ = +1. -/
theorem MinimalYield.im_accessibleCount_of_cut (lbl a₀ : α) (τ : UnorderedTree (α ⊕ β) → β)
    (F₀ : Forest (UnorderedTree (α ⊕ β)))
    (p : Forest (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β))
    (hp : p ∈ cutSummandsCN τ (UnorderedTree.node (Sum.inl a₀) F₀))
    (β_t : UnorderedTree (α ⊕ β)) (hcard : p.1 = {β_t}) :
    MinimalYield UnorderedTree.accessibleCount
      ({UnorderedTree.node (Sum.inl a₀) F₀} : Forest (UnorderedTree (α ⊕ β)))
      {UnorderedTree.node (Sum.inl lbl) {β_t, p.2}} := by
  obtain ⟨h1, h2, -⟩ := im_pair_size_deltas_contraction_of_cut lbl a₀ τ F₀ p hp β_t hcard
  simp only [Forest.accessibleCount] at h2
  exact ⟨⟨h1.le, by omega⟩, by omega⟩

/-! ### Sideward Merge -/

/-- Sideward Merge of type 2(b) leaves the component count `b₀` unchanged. -/
theorem sideward_2b_b₀_preserved (T_i T_j Tnode T_j_q : UnorderedTree (α ⊕ β)) :
    Multiset.card ({Tnode, T_j_q} : Forest (UnorderedTree (α ⊕ β)))
      = Multiset.card ({T_i, T_j} : Forest (UnorderedTree (α ⊕ β))) := by
  simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]

/-- Sideward Merge of type 3(a) increases the component count `b₀` by one. -/
theorem sideward_3a_b₀_increases (T_i Tnode T_iq : UnorderedTree (α ⊕ β)) :
    Multiset.card ({Tnode, T_iq} : Forest (UnorderedTree (α ⊕ β)))
      = Multiset.card ({T_i} : Forest (UnorderedTree (α ⊕ β))) + 1 := by
  simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]

/-- Sideward Merge of type 3(b) increases the component count `b₀` by one. -/
theorem sideward_3b_b₀_increases (T_i T_j Tnode T_iq T_jq : UnorderedTree (α ⊕ β)) :
    Multiset.card ({Tnode, T_iq, T_jq} : Forest (UnorderedTree (α ⊕ β)))
      = Multiset.card ({T_i, T_j} : Forest (UnorderedTree (α ⊕ β))) + 1 := by
  simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]

/-- Sideward Merge of type 3(a) violates the weak Minimal Yield principle (Δb₀ > 0). -/
theorem MinimalYieldWeak.not_sideward_3a (acc : UnorderedTree (α ⊕ β) → ℕ)
    (T_i Tnode T_iq : UnorderedTree (α ⊕ β)) :
    ¬ MinimalYieldWeak acc ({T_i} : Forest (UnorderedTree (α ⊕ β)))
                       ({Tnode, T_iq} : Forest (UnorderedTree (α ⊕ β))) := by
  intro h
  have hd := h.noDivergence
  rw [sideward_3a_b₀_increases T_i Tnode T_iq] at hd
  omega

/-- Sideward Merge of type 3(b) violates the weak Minimal Yield principle (Δb₀ > 0). -/
theorem MinimalYieldWeak.not_sideward_3b (acc : UnorderedTree (α ⊕ β) → ℕ)
    (T_i T_j Tnode T_iq T_jq : UnorderedTree (α ⊕ β)) :
    ¬ MinimalYieldWeak acc ({T_i, T_j} : Forest (UnorderedTree (α ⊕ β)))
                       ({Tnode, T_iq, T_jq} : Forest (UnorderedTree (α ⊕ β))) := by
  intro h
  have hd := h.noDivergence
  rw [sideward_3b_b₀_increases T_i T_j Tnode T_iq T_jq] at hd
  omega

/-- Strong-form corollary of `MinimalYieldWeak.not_sideward_3a`. -/
theorem MinimalYield.not_sideward_3a (acc : UnorderedTree (α ⊕ β) → ℕ)
    (T_i Tnode T_iq : UnorderedTree (α ⊕ β)) :
    ¬ MinimalYield acc ({T_i} : Forest (UnorderedTree (α ⊕ β)))
                   ({Tnode, T_iq} : Forest (UnorderedTree (α ⊕ β))) :=
  fun h ↦ MinimalYieldWeak.not_sideward_3a acc T_i Tnode T_iq h.toMinimalYieldWeak

/-- Strong-form corollary of `MinimalYieldWeak.not_sideward_3b`. -/
theorem MinimalYield.not_sideward_3b (acc : UnorderedTree (α ⊕ β) → ℕ)
    (T_i T_j Tnode T_iq T_jq : UnorderedTree (α ⊕ β)) :
    ¬ MinimalYield acc ({T_i, T_j} : Forest (UnorderedTree (α ⊕ β)))
                   ({Tnode, T_iq, T_jq} : Forest (UnorderedTree (α ⊕ β))) :=
  fun h ↦ MinimalYieldWeak.not_sideward_3b acc T_i T_j Tnode T_iq T_jq h.toMinimalYieldWeak

/-! ### Unit merge -/

/-- The unit-merge stage `{T} → {β, T/β}` violates weak Minimal Yield (Δb₀ > 0). -/
theorem MinimalYieldWeak.not_unitMerge (acc : UnorderedTree (α ⊕ β) → ℕ)
    (T β_t Q : UnorderedTree (α ⊕ β)) :
    ¬ MinimalYieldWeak acc ({T} : Forest (UnorderedTree (α ⊕ β)))
                       ({β_t, Q} : Forest (UnorderedTree (α ⊕ β))) :=
  MinimalYieldWeak.not_sideward_3a acc T β_t Q

/-- Strong-form corollary of `MinimalYieldWeak.not_unitMerge`. -/
theorem MinimalYield.not_unitMerge (acc : UnorderedTree (α ⊕ β) → ℕ)
    (T β_t Q : UnorderedTree (α ⊕ β)) :
    ¬ MinimalYield acc ({T} : Forest (UnorderedTree (α ⊕ β)))
                   ({β_t, Q} : Forest (UnorderedTree (α ⊕ β))) :=
  MinimalYield.not_sideward_3a acc T β_t Q

end Minimalist
