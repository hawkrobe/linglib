import Linglib.Core.Data.RoseTree.Count
import Linglib.Syntax.Minimalist.Workspace.TraceMeasures
import Linglib.Syntax.Minimalist.Workspace.Conservation
import Linglib.Syntax.Minimalist.Workspace.DeletionConservation
import Linglib.Core.Order.PullbackPreorder
import Mathlib.Order.OrderDual

/-!
# Minimal Yield

Minimal Yield is a condition on a transformation `F → F'` of workspaces, stated on the size
measures of `Workspace/TraceMeasures.lean`: the number of components does not grow (no
divergence), the number of accessible terms does not fall (no information loss), and the number
of vertices grows by exactly one (minimality of yield). `MinimalYieldWeak` is the first two
bounds and `MinimalYield` all three. The weak form is monotonicity of the signature `(b₀ᵒᵈ, α)`,
so it is a pullback preorder on workspaces (`MinimalYieldWeak.pullbackPreorder`).

The per-case theorems evaluate the condition on the shapes the cases of Merge produce, on the
carrier `Nonplanar (α ⊕ β)` with `Sum.inl` lexical and `Sum.inr` trace: External Merge satisfies
it; Internal Merge preserves `b₀`, `α`, `σ` under Δᵈ counting and raises `αᶜ`, `σᶜ` by one under
Δᶜ counting, given the accessible-term extraction identities; the divergent Sideward cases 3(a)
and 3(b), which raise `b₀`, violate both forms.

## Main definitions

* `Minimalist.MinimalYieldWeak`, `Minimalist.MinimalYield`
* `Minimalist.MinimalYield.signature`: the Pareto signature `(b₀ᵒᵈ, α)`.

## Main results

* `Minimalist.MinimalYield.em_pair`: External Merge satisfies Minimal Yield.
* `Minimalist.MinimalYield.not_sideward_3a`, `not_sideward_3b`: the divergent Sideward cases do
  not.

## References

* [marcolli-chomsky-berwick-2025], §1.6.1–1.6.2 (Definition 1.6.1, Lemma 1.6.3,
  Propositions 1.6.4 and 1.6.8)
-/

namespace Minimalist

open RoseTree RoseTree.Nonplanar ConnesKreimer

variable {α β : Type*}

/-! ### The Minimal Yield principle -/

/-- The weak Minimal Yield principle: no increase in `b₀`, no decrease in `α`. -/
structure MinimalYieldWeak (F F' : Forest (Nonplanar (α ⊕ β))) : Prop where
  noDivergence : Forest.b₀ F' ≤ Forest.b₀ F
  noInfoLoss   : Forest.alpha F ≤ Forest.alpha F'

/-- The Minimal Yield principle: the weak form plus `σ` up by exactly one. -/
structure MinimalYield (F F' : Forest (Nonplanar (α ⊕ β))) : Prop
    extends MinimalYieldWeak F F' where
  minimalYield : Forest.sigma F' = Forest.sigma F + 1

/-! ### `MinimalYieldWeak` as a Pareto pullback preorder -/

/-- The Pareto signature `(b₀ᵒᵈ, α)`, `b₀` dualised so fewer components ranks higher. -/
def MinimalYield.signature (F : Forest (Nonplanar (α ⊕ β))) : ℕᵒᵈ × ℕ :=
  (OrderDual.toDual (Forest.b₀ F), Forest.alpha F)

theorem minimalYieldWeak_iff_signature_le {F F' : Forest (Nonplanar (α ⊕ β))} :
    MinimalYieldWeak F F' ↔ MinimalYield.signature F ≤ MinimalYield.signature F' :=
  ⟨fun ⟨h_b, h_a⟩ => ⟨h_b, h_a⟩, fun ⟨h_b, h_a⟩ => ⟨h_b, h_a⟩⟩

/-- `MinimalYieldWeak` packaged as a `PullbackPreorder`. -/
def MinimalYieldWeak.pullbackPreorder :
    Core.Order.PullbackPreorder (Forest (Nonplanar (α ⊕ β))) (ℕᵒᵈ × ℕ) :=
  Core.Order.PullbackPreorder.ofProj MinimalYield.signature (fun _ _ => inferInstance)

/-! ### External Merge -/

/-- External Merge of a pair satisfies Minimal Yield: Δb₀ = −1, Δα = +2, Δσ = +1. -/
theorem MinimalYield.em_pair (lbl : α) (S S' : Nonplanar (α ⊕ β)) :
    MinimalYield ({S, S'} : Forest (Nonplanar (α ⊕ β)))
                 ({Nonplanar.node (Sum.inl lbl) {S, S'}}) := by
  have hnode : (Nonplanar.node (Sum.inl lbl) {S, S'}).accCount
      = S.accCount + S'.accCount + 2 := Nonplanar.accCount_node_pair (Sum.inl lbl) S S'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Forest.b₀_singleton, Multiset.insert_eq_cons, Forest.b₀_cons]
    omega
  · rw [Forest.alpha_singleton, hnode]
    simp only [Multiset.insert_eq_cons, Forest.alpha_cons, Forest.alpha_singleton]
    omega
  · simp only [Forest.sigma, Forest.b₀_singleton, Forest.alpha_singleton]
    rw [hnode]
    simp only [Multiset.insert_eq_cons, Forest.b₀_cons, Forest.b₀_singleton,
      Forest.alpha_cons, Forest.alpha_singleton]
    omega

/-! ### Internal Merge -/

/-- Internal Merge via composition leaves `b₀`, `α`, `σ` unchanged (Δᵈ counting):
    the accessible-term relation `α(T) = α(mover) + α(Q) + 2` is MCB eq. 1.6.7. -/
theorem im_pair_size_deltas_deletion (lbl : α) {T mover Q : Nonplanar (α ⊕ β)}
    (h : T.accCount = mover.accCount + Q.accCount + 2) :
    Forest.b₀ ({Nonplanar.node (Sum.inl lbl) {mover, Q}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.b₀ ({T} : Forest (Nonplanar (α ⊕ β)))
      ∧ Forest.alpha ({Nonplanar.node (Sum.inl lbl) {mover, Q}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.alpha ({T} : Forest (Nonplanar (α ⊕ β)))
      ∧ Forest.sigma ({Nonplanar.node (Sum.inl lbl) {mover, Q}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.sigma ({T} : Forest (Nonplanar (α ⊕ β))) := by
  have hnode : (Nonplanar.node (Sum.inl lbl) {mover, Q}).accCount
      = mover.accCount + Q.accCount + 2 := Nonplanar.accCount_node_pair (Sum.inl lbl) mover Q
  refine ⟨rfl, ?_, ?_⟩
  · rw [Forest.alpha_singleton, Forest.alpha_singleton, hnode]
    omega
  · simp only [Forest.sigma, Forest.b₀_singleton, Forest.alpha_singleton]
    rw [hnode]
    omega

/-- `im_pair_size_deltas_deletion` with the α relation discharged from a Δᵈ
    admissible cut: deleting `mover` from `T` and rebinarizing the remainder
    (`contractUnary p.2`) leaves `b₀`, `α`, `σ` unchanged. `numUnary p.2 = 1`
    characterizes a single edge cut at a binary node. -/
theorem im_pair_size_deltas_deletion_of_cut (lbl : α) (T : Nonplanar (α ⊕ β))
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ ConnesKreimer.cutSummandsN T)
    (mover : Nonplanar (α ⊕ β)) (hcard : p.1 = {mover}) (huc : p.2.numUnary = 1) :
    Forest.b₀ ({Nonplanar.node (Sum.inl lbl) {mover, Nonplanar.contractUnary p.2}}
        : Forest (Nonplanar (α ⊕ β))) = Forest.b₀ ({T} : Forest (Nonplanar (α ⊕ β)))
      ∧ Forest.alpha ({Nonplanar.node (Sum.inl lbl) {mover, Nonplanar.contractUnary p.2}}
        : Forest (Nonplanar (α ⊕ β))) = Forest.alpha ({T} : Forest (Nonplanar (α ⊕ β)))
      ∧ Forest.sigma ({Nonplanar.node (Sum.inl lbl) {mover, Nonplanar.contractUnary p.2}}
        : Forest (Nonplanar (α ⊕ β))) = Forest.sigma ({T} : Forest (Nonplanar (α ⊕ β))) :=
  im_pair_size_deltas_deletion lbl
    (ConnesKreimer.cutSummandsN_accCount_single_deletion T p hp mover hcard huc)

/-- Internal Merge via composition leaves `b₀` fixed and raises `αᶜ`, `σᶜ` by one
    (Δᶜ counting): the relation `αᶜ(T) = αᶜ(β_t) + αᶜ(trunk) + 1` is MCB eq. 1.6.8. -/
theorem im_pair_size_deltas_contraction (lbl : α) {T β_t Q : Nonplanar (α ⊕ β)}
    (hβ : β_t.traceLeafCount < β_t.numNodes) (hQ : Q.traceLeafCount < Q.numNodes)
    (h : T.accCountC = β_t.accCountC + Q.accCountC + 1) :
    Forest.b₀ ({Nonplanar.node (Sum.inl lbl) {β_t, Q}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.b₀ ({T} : Forest (Nonplanar (α ⊕ β)))
      ∧ Forest.alphaC ({Nonplanar.node (Sum.inl lbl) {β_t, Q}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.alphaC ({T} : Forest (Nonplanar (α ⊕ β))) + 1
      ∧ Forest.sigmaC ({Nonplanar.node (Sum.inl lbl) {β_t, Q}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.sigmaC ({T} : Forest (Nonplanar (α ⊕ β))) + 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [Forest.alphaC_singleton, Forest.alphaC_singleton,
        Nonplanar.accCountC_merge lbl β_t Q hβ hQ]
    omega
  · simp only [Forest.sigmaC_eq, Forest.b₀_singleton, Forest.alphaC_singleton]
    rw [Nonplanar.accCountC_merge lbl β_t Q hβ hQ]
    omega

/-- `im_pair_size_deltas_contraction` with the αᶜ relation discharged from a Δᶜ
    admissible cut: re-merging an accessible subtree `β_t` of `T = node (inl a₀) F₀`
    with the contraction quotient `p.2` raises `αᶜ`, `σᶜ` by one. -/
theorem im_pair_size_deltas_contraction_of_cut (lbl a₀ : α)
    (τ : Nonplanar (α ⊕ β) → β) (F₀ : Forest (Nonplanar (α ⊕ β)))
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β))
    (hp : p ∈ cutSummandsCN τ (Nonplanar.node (Sum.inl a₀) F₀))
    (β_t : Nonplanar (α ⊕ β)) (hcard : p.1 = {β_t}) :
    Forest.b₀ ({Nonplanar.node (Sum.inl lbl) {β_t, p.2}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.b₀ ({Nonplanar.node (Sum.inl a₀) F₀} : Forest (Nonplanar (α ⊕ β)))
      ∧ Forest.alphaC ({Nonplanar.node (Sum.inl lbl) {β_t, p.2}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.alphaC ({Nonplanar.node (Sum.inl a₀) F₀} : Forest (Nonplanar (α ⊕ β))) + 1
      ∧ Forest.sigmaC ({Nonplanar.node (Sum.inl lbl) {β_t, p.2}} : Forest (Nonplanar (α ⊕ β)))
        = Forest.sigmaC ({Nonplanar.node (Sum.inl a₀) F₀} : Forest (Nonplanar (α ⊕ β))) + 1 :=
  im_pair_size_deltas_contraction lbl
    (cutSummandsCN_crown_traceLeafCount_lt_numNodes τ _ p hp β_t
      (by rw [hcard]; exact Multiset.mem_singleton_self β_t))
    (Nonplanar.traceLeafCount_lt_numNodes_of_rootInl p.2 a₀
      ((cutSummandsCN_trunk_rootValue τ _ p hp).trans (by rw [Nonplanar.rootValue_node])))
    (cutSummandsCN_accCountC_single τ _ a₀ F₀ rfl p hp β_t hcard)

/-! ### Sideward Merge -/

/-- Sideward Merge of type 2(b) leaves the component count `b₀` unchanged. -/
theorem sideward_2b_b₀_preserved (T_i T_j Tnode T_j_q : Nonplanar (α ⊕ β)) :
    Forest.b₀ ({Tnode, T_j_q} : Forest (Nonplanar (α ⊕ β)))
      = Forest.b₀ ({T_i, T_j} : Forest (Nonplanar (α ⊕ β))) := by
  simp only [Multiset.insert_eq_cons, Forest.b₀_cons, Forest.b₀_singleton]

/-- Sideward Merge of type 3(a) increases the component count `b₀` by one. -/
theorem sideward_3a_b₀_increases (T_i Tnode T_iq : Nonplanar (α ⊕ β)) :
    Forest.b₀ ({Tnode, T_iq} : Forest (Nonplanar (α ⊕ β)))
      = Forest.b₀ ({T_i} : Forest (Nonplanar (α ⊕ β))) + 1 := by
  simp only [Multiset.insert_eq_cons, Forest.b₀_cons, Forest.b₀_singleton]

/-- Sideward Merge of type 3(b) increases the component count `b₀` by one. -/
theorem sideward_3b_b₀_increases (T_i T_j Tnode T_iq T_jq : Nonplanar (α ⊕ β)) :
    Forest.b₀ ({Tnode, T_iq, T_jq} : Forest (Nonplanar (α ⊕ β)))
      = Forest.b₀ ({T_i, T_j} : Forest (Nonplanar (α ⊕ β))) + 1 := by
  simp only [Multiset.insert_eq_cons, Forest.b₀_cons, Forest.b₀_singleton]

/-- Sideward Merge of type 3(a) violates the weak Minimal Yield principle (Δb₀ > 0). -/
theorem MinimalYieldWeak.not_sideward_3a (T_i Tnode T_iq : Nonplanar (α ⊕ β)) :
    ¬ MinimalYieldWeak ({T_i} : Forest (Nonplanar (α ⊕ β)))
                       ({Tnode, T_iq} : Forest (Nonplanar (α ⊕ β))) := by
  intro h
  have hd := h.noDivergence
  rw [sideward_3a_b₀_increases T_i Tnode T_iq] at hd
  omega

/-- Sideward Merge of type 3(b) violates the weak Minimal Yield principle (Δb₀ > 0). -/
theorem MinimalYieldWeak.not_sideward_3b
    (T_i T_j Tnode T_iq T_jq : Nonplanar (α ⊕ β)) :
    ¬ MinimalYieldWeak ({T_i, T_j} : Forest (Nonplanar (α ⊕ β)))
                       ({Tnode, T_iq, T_jq} : Forest (Nonplanar (α ⊕ β))) := by
  intro h
  have hd := h.noDivergence
  rw [sideward_3b_b₀_increases T_i T_j Tnode T_iq T_jq] at hd
  omega

/-- Strong-form corollary of `MinimalYieldWeak.not_sideward_3a`. -/
theorem MinimalYield.not_sideward_3a (T_i Tnode T_iq : Nonplanar (α ⊕ β)) :
    ¬ MinimalYield ({T_i} : Forest (Nonplanar (α ⊕ β)))
                   ({Tnode, T_iq} : Forest (Nonplanar (α ⊕ β))) :=
  fun h => MinimalYieldWeak.not_sideward_3a T_i Tnode T_iq h.toMinimalYieldWeak

/-- Strong-form corollary of `MinimalYieldWeak.not_sideward_3b`. -/
theorem MinimalYield.not_sideward_3b
    (T_i T_j Tnode T_iq T_jq : Nonplanar (α ⊕ β)) :
    ¬ MinimalYield ({T_i, T_j} : Forest (Nonplanar (α ⊕ β)))
                   ({Tnode, T_iq, T_jq} : Forest (Nonplanar (α ⊕ β))) :=
  fun h => MinimalYieldWeak.not_sideward_3b T_i T_j Tnode T_iq T_jq h.toMinimalYieldWeak

/-! ### Unit merge -/

/-- The unit-merge stage `{T} → {β, T/β}` violates weak Minimal Yield (Δb₀ > 0). -/
theorem MinimalYieldWeak.not_unitMerge (T β_t Q : Nonplanar (α ⊕ β)) :
    ¬ MinimalYieldWeak ({T} : Forest (Nonplanar (α ⊕ β)))
                       ({β_t, Q} : Forest (Nonplanar (α ⊕ β))) :=
  MinimalYieldWeak.not_sideward_3a T β_t Q

/-- Strong-form corollary of `MinimalYieldWeak.not_unitMerge`. -/
theorem MinimalYield.not_unitMerge (T β_t Q : Nonplanar (α ⊕ β)) :
    ¬ MinimalYield ({T} : Forest (Nonplanar (α ⊕ β)))
                   ({β_t, Q} : Forest (Nonplanar (α ⊕ β))) :=
  MinimalYield.not_sideward_3a T β_t Q

end Minimalist
