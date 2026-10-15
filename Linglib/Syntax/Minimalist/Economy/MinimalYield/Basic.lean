module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Linglib.Syntax.Minimalist.Workspace.TraceMeasures
public import Mathlib.Order.OrderDual

/-!
# Minimal Yield

Minimal Yield (Definition 1.6.1 of Marcolli, Chomsky and Berwick) is a condition on a
transformation `F → F'` of workspaces. The number `b₀` of components does not grow (no
divergence), the number `α` of accessible terms does not fall (no information loss), and the size
`σ = b₀ + α` grows by exactly one (minimality of yield). `MinimalYieldWeak` is the first two
bounds and `MinimalYield` all three. Both take the count of accessible terms of a component as a
parameter, since Proposition 1.6.4 evaluates the one condition under two countings: the deletion
coproduct counts every non-root vertex (`UnorderedTree.numEdges`), the trace coproduct every
non-root vertex but its trace leaves (`UnorderedTree.accessibleCount`). The weak form is
monotonicity of the signature `(b₀ᵒᵈ, α)` (`minimalYieldWeak_iff_signature_le`).

On the carrier `UnorderedTree (α ⊕ β)`, with `Sum.inr` marking a trace, External Merge satisfies
Minimal Yield under both countings. Internal Merge through a trace cut satisfies it under trace
counting; under deletion counting it preserves all three measures and satisfies only the weak
form.

A term of Merge chooses a cut for each component of the workspace. Each component it takes whole
lowers `b₀` by one, and each tree a cut extracts costs a fixed number `k` of accessible terms: one
under the trace coproduct and two under the deletion coproduct (Lemma 1.6.3). So under trace
counting a term of Merge grows `σ` by exactly one and gains an accessible term for each object it
takes whole, and it satisfies Minimal Yield exactly when it takes one whole. External Merge and
the Sideward case 2(b) pass, and the Sideward cases 3(a) and 3(b) fail (Proposition 1.6.8). When
extractions cost two, only External Merge passes, and 2(b) satisfies only the weak form.

## Main definitions

* `Minimalist.MinimalYieldWeak`, `Minimalist.MinimalYield`
* `Minimalist.MinimalYield.signature`: the Pareto signature `(b₀ᵒᵈ, α)`.

## Main results

* `Minimalist.MinimalYield.em_pair`, `MinimalYield.em_pair_accessibleCount`: External Merge
  satisfies Minimal Yield under either counting.
* `Minimalist.MinimalYield.im_accessibleCount_of_cut`: Internal Merge through a trace cut
  satisfies it under trace counting.
* `Minimalist.MinimalYield.add_right`: spectators preserve it.
* `Minimalist.card_singleton_add_trunk_add_countP`, `sum_map_merge_term_add`: the number of
  components and of accessible terms of a term of Merge.
* `Minimalist.MinimalYield.merge_term_accessibleCount_iff`: under trace counting a term of Merge
  satisfies it exactly when it takes an object whole; `accessibleSize_merge_term`: its size grows
  by one.
* `Minimalist.MinimalYield.merge_term_iff_of_extraction_two`,
  `MinimalYieldWeak.merge_term_iff_of_extraction_two`: when extractions cost two accessible terms.
* `Minimalist.MinimalYieldWeak.not_of_forall_notMem`: a term whose crown has no component of the
  workspace violates it under any counting.

## Implementation notes

The deletion coproduct's identity (1.6.7), two accessible terms per extracted tree, needs each
extraction to leave one vertex with a single child for the deletion to contract, as when every
vertex has two children or none and no two extracted trees share a parent. It is a hypothesis of
the theorems for extractions of cost two, while the trace coproduct's identity (1.6.8) is proved
(`cutSummandsCN_accessibleCount`).

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
    (by simpa [hcard] using cutSummandsCN_accessibleCount τ (UnorderedTree.value_node _ _) hp)

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

/-! ### Terms of Merge and of its unit stage

A term of Merge or of its unit stage on `F` chooses a cut for each component of `F`
(`mergeOpG_apply_of'_eq_sum`, `mergeOpUnitG_apply_of'_eq_sum`). Its workspace holds the object `X`
built from the crown and the trunk of each component that was cut rather than taken whole. -/

section Terms

variable [DecidableEq (UnorderedTree α)]
  {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
  {F : Forest (UnorderedTree α)}
  {s : Multiset (UnorderedTree α × (Forest (UnorderedTree α) × Forest (UnorderedTree α)))}

/-- A term has one component for the object built from the crown and one for each component that
    was cut, so each component taken whole lowers `b₀` by one. -/
theorem card_singleton_add_trunk_add_countP (hs : s ∈ forestCutChoicesG cuts F)
    (X : UnorderedTree α) :
    Multiset.card ({X} + (s.map Prod.snd).sum.2) + s.countP (·.2.2 = 0) =
      Multiset.card F + 1 := by
  rw [Multiset.card_add, Multiset.card_singleton, add_assoc,
    card_add_countP_of_mem_forestCutChoicesG hs, add_comm]

/-- If each tree a cut extracts takes `k` accessible terms beyond its own with it, then a choice of
    cuts conserves accessible terms up to `k` for each extracted tree, counting each tree taken
    whole as extracting itself. -/
theorem sum_map_add_countP_of_extraction {acc : UnorderedTree α → ℕ} {k : ℕ}
    (hs : s ∈ forestCutChoicesG cuts F)
    (hext : ∀ T ∈ F, ∀ p ∈ cuts T,
      acc T = (p.1.map acc).sum + acc p.2 + k * Multiset.card p.1) :
    (F.map acc).sum + k * s.countP (·.2.2 = 0) =
      ((s.map Prod.snd).sum.1.map acc).sum + ((s.map Prod.snd).sum.2.map acc).sum +
        k * Multiset.card (s.map Prod.snd).sum.1 := by
  induction F using Multiset.induction generalizing s with
  | empty => rw [forestCutChoicesG_zero, Multiset.mem_singleton] at hs; simp [hs]
  | cons T F ih =>
    rw [forestCutChoicesG_cons, Multiset.mem_bind] at hs
    obtain ⟨a, ha, hs⟩ := hs
    obtain ⟨s', hs', rfl⟩ := Multiset.mem_map.mp hs
    have := ih hs' fun U hU ↦ hext U (Multiset.mem_cons_of_mem hU)
    have e : (fun x ↦ acc x) = acc := rfl
    rcases mem_treeCutsG.mp ha with rfl | ⟨p, hp, rfl⟩
    · rw [Multiset.countP_cons_of_pos (p := fun x : UnorderedTree α ×
        (Forest (UnorderedTree α) × Forest (UnorderedTree α)) ↦ x.2.2 = 0) _ rfl]
      simp only [Multiset.map_cons, Multiset.sum_cons, Prod.fst_add, Prod.snd_add,
        Multiset.map_add, Multiset.sum_add, Multiset.card_add, Multiset.map_singleton,
        Multiset.sum_singleton, Multiset.card_singleton, Multiset.map_zero, Multiset.sum_zero, e,
        mul_add, mul_one]
      omega
    · have h := hext T (Multiset.mem_cons_self _ _) p hp
      rw [Multiset.countP_cons_of_neg (p := fun x : UnorderedTree α ×
        (Forest (UnorderedTree α) × Forest (UnorderedTree α)) ↦ x.2.2 = 0) _
        (Multiset.singleton_ne_zero _)]
      simp only [Multiset.map_cons, Multiset.sum_cons, Prod.fst_add, Prod.snd_add,
        Multiset.map_add, Multiset.sum_add, Multiset.card_add, Multiset.map_singleton,
        Multiset.sum_singleton, e, mul_add]
      omega

/-- A term of Merge has the accessible terms of the workspace, `2` more for the Merge of its two
    objects, and `k` fewer for each object it extracts rather than takes whole. -/
theorem sum_map_merge_term_add {acc : UnorderedTree α → ℕ} {k : ℕ}
    (hs : s ∈ forestCutChoicesG cuts F)
    (hext : ∀ T ∈ F, ∀ p ∈ cuts T,
      acc T = (p.1.map acc).sum + acc p.2 + k * Multiset.card p.1)
    {S S' X : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {S, S'})
    (hX : acc X = acc S + acc S' + 2) :
    (({X} + (s.map Prod.snd).sum.2).map acc).sum + 2 * k =
      (F.map acc).sum + k * s.countP (·.2.2 = 0) + 2 := by
  have h := sum_map_add_countP_of_extraction hs hext
  rw [hK] at h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, Multiset.card_cons, Multiset.card_singleton] at h
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton]
  omega

/-- With each extraction costing one accessible term, as under `Δ^c` (Lemma 1.6.3 (1.6.8)), a
    term of Merge satisfies Minimal Yield exactly when it takes at least one of its objects whole.
    Its size `σ` always grows by one, and it diverges otherwise. -/
theorem MinimalYield.merge_term_iff_of_extraction_one {acc : UnorderedTree α → ℕ}
    (hs : s ∈ forestCutChoicesG cuts F)
    (hext : ∀ T ∈ F, ∀ p ∈ cuts T, acc T = (p.1.map acc).sum + acc p.2 + Multiset.card p.1)
    {S S' X : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {S, S'})
    (hX : acc X = acc S + acc S' + 2) :
    MinimalYield acc F ({X} + (s.map Prod.snd).sum.2) ↔ s.countP (·.2.2 = 0) ≠ 0 := by
  have hα := sum_map_merge_term_add (k := 1) hs (by simpa using hext) hK hX
  have hb := card_singleton_add_trunk_add_countP hs X
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have := h.noDivergence; omega
  all_goals omega

/-- With each extraction costing two accessible terms, as under `Δ^d` (Lemma 1.6.3 (1.6.7)), a
    term of Merge satisfies Minimal Yield exactly when it takes both of its objects whole. -/
theorem MinimalYield.merge_term_iff_of_extraction_two {acc : UnorderedTree α → ℕ}
    (hs : s ∈ forestCutChoicesG cuts F)
    (hext : ∀ T ∈ F, ∀ p ∈ cuts T, acc T = (p.1.map acc).sum + acc p.2 + 2 * Multiset.card p.1)
    {S S' X : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {S, S'})
    (hX : acc X = acc S + acc S' + 2) :
    MinimalYield acc F ({X} + (s.map Prod.snd).sum.2) ↔ s.countP (·.2.2 = 0) = 2 := by
  have hα := sum_map_merge_term_add hs hext hK hX
  have hb := card_singleton_add_trunk_add_countP hs X
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have := h.minimalYield; omega
  all_goals omega

/-- With each extraction costing two accessible terms, a term of Merge satisfies the weak form of
    Minimal Yield exactly when it takes at least one of its objects whole. -/
theorem MinimalYieldWeak.merge_term_iff_of_extraction_two {acc : UnorderedTree α → ℕ}
    (hs : s ∈ forestCutChoicesG cuts F)
    (hext : ∀ T ∈ F, ∀ p ∈ cuts T, acc T = (p.1.map acc).sum + acc p.2 + 2 * Multiset.card p.1)
    {S S' X : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {S, S'})
    (hX : acc X = acc S + acc S' + 2) :
    MinimalYieldWeak acc F ({X} + (s.map Prod.snd).sum.2) ↔ s.countP (·.2.2 = 0) ≠ 0 := by
  have hα := sum_map_merge_term_add hs hext hK hX
  have hb := card_singleton_add_trunk_add_countP hs X
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · have := h.noDivergence; omega
  all_goals omega

/-- A term of the unit stage has the accessible terms of the workspace, less `k` for the object
    it extracts unless it takes it whole. -/
theorem sum_map_unit_term_add {acc : UnorderedTree α → ℕ} {k : ℕ}
    (hs : s ∈ forestCutChoicesG cuts F)
    (hext : ∀ T ∈ F, ∀ p ∈ cuts T,
      acc T = (p.1.map acc).sum + acc p.2 + k * Multiset.card p.1)
    {β : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {β}) :
    (({β} + (s.map Prod.snd).sum.2).map acc).sum + k =
      (F.map acc).sum + k * s.countP (·.2.2 = 0) := by
  have h := sum_map_add_countP_of_extraction hs hext
  rw [hK] at h
  simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton,
    mul_one] at h
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton]
  omega

/-- A term whose crown contains no component of the workspace raises `b₀` by one, so it violates
    Minimal Yield under any counting. These are the Sideward cases 3(a) and 3(b)
    ([marcolli-chomsky-berwick-2025] Proposition 1.6.8) and the unit stage on its own
    (Remark 1.6.7). -/
theorem MinimalYieldWeak.not_of_forall_notMem (acc : UnorderedTree α → ℕ)
    (hs : s ∈ forestCutChoicesG cuts F) (hK : ∀ T ∈ (s.map Prod.snd).sum.1, T ∉ F)
    (X : UnorderedTree α) : ¬ MinimalYieldWeak acc F ({X} + (s.map Prod.snd).sum.2) := by
  intro h
  have h0 : s.countP (·.2.2 = 0) = 0 := Multiset.countP_eq_zero.mpr fun x hx hx0 ↦
    hK x.1 (mem_fst_sum_map_snd_iff.mpr
      ⟨x, hx, by simp [snd_eq_of_mem_forestCutChoicesG hs hx hx0]⟩)
      (map_fst_of_mem_forestCutChoicesG hs ▸ Multiset.mem_map_of_mem Prod.fst hx)
  have := card_singleton_add_trunk_add_countP hs X
  have := h.noDivergence
  omega

/-- Strong-form corollary of `MinimalYieldWeak.not_of_forall_notMem`. -/
theorem MinimalYield.not_of_forall_notMem (acc : UnorderedTree α → ℕ)
    (hs : s ∈ forestCutChoicesG cuts F) (hK : ∀ T ∈ (s.map Prod.snd).sum.1, T ∉ F)
    (X : UnorderedTree α) : ¬ MinimalYield acc F ({X} + (s.map Prod.snd).sum.2) :=
  fun h ↦ MinimalYieldWeak.not_of_forall_notMem acc hs hK X h.toMinimalYieldWeak

end Terms

/-! ### Terms of Merge under trace counting -/

section Trace

variable {τ : UnorderedTree (α ⊕ β) → β} {F : Forest (UnorderedTree (α ⊕ β))}
  {s : Multiset (UnorderedTree (α ⊕ β) ×
    (Forest (UnorderedTree (α ⊕ β)) × Forest (UnorderedTree (α ⊕ β))))}

private theorem extraction_accessibleCount (hF : ∀ T ∈ F, ∃ a, T.value = Sum.inl a) :
    ∀ T ∈ F, ∀ p ∈ cutSummandsCN τ T, T.accessibleCount =
      (p.1.map UnorderedTree.accessibleCount).sum + p.2.accessibleCount + Multiset.card p.1 :=
  fun T hT _ hp ↦ cutSummandsCN_accessibleCount τ (hF T hT).choose_spec hp

/-- A tree in the crown of a choice of trace cuts of lexical-rooted trees is not a trace. -/
private theorem traceLeafCount_lt_of_mem_crown (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ T ∈ F, ∃ a, T.value = Sum.inl a) {S : UnorderedTree (α ⊕ β)}
    (hS : S ∈ (s.map Prod.snd).sum.1) : S.traceLeafCount < S.numNodes := by
  obtain ⟨x, hx, hSx⟩ := mem_fst_sum_map_snd_iff.mp hS
  rcases mem_treeCutsG.mp (mem_treeCutsG_of_mem_forestCutChoicesG hs hx) with h | ⟨p, hp, h⟩
  · rw [h, Multiset.mem_singleton] at hSx
    obtain ⟨a, ha⟩ := hF x.1 (map_fst_of_mem_forestCutChoicesG hs ▸
      Multiset.mem_map_of_mem Prod.fst hx)
    exact hSx ▸ UnorderedTree.traceLeafCount_lt_numNodes_of_rootInl _ a ha
  · rw [← h] at hSx
    exact cutSummandsCN_crown_traceLeafCount_lt_numNodes τ x.1 p hp S hSx

variable [DecidableEq (UnorderedTree (α ⊕ β))]

/-- Under trace counting a term of Merge gains one accessible term for each object it takes whole
    ([marcolli-chomsky-berwick-2025] Propositions 1.6.4 and 1.6.8, for `Δ^c`). -/
theorem accessibleCount_merge_term (a : α) (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ T ∈ F, ∃ a, T.value = Sum.inl a) {S S' : UnorderedTree (α ⊕ β)}
    (hK : (s.map Prod.snd).sum.1 = {S, S'}) :
    Forest.accessibleCount ({UnorderedTree.node (Sum.inl a) {S, S'}} + (s.map Prod.snd).sum.2) =
      Forest.accessibleCount F + s.countP (·.2.2 = 0) := by
  have h := sum_map_merge_term_add (k := 1) hs (by simpa using extraction_accessibleCount hF) hK
    (UnorderedTree.accessibleCount_merge a S S'
      (traceLeafCount_lt_of_mem_crown hs hF (hK ▸ Multiset.mem_cons_self _ _))
      (traceLeafCount_lt_of_mem_crown hs hF
        (hK ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))))
  simp only [Forest.accessibleCount] at h ⊢
  omega

/-- Under trace counting every term of Merge grows the size `σ` of the workspace by exactly one. -/
theorem accessibleSize_merge_term (a : α) (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ T ∈ F, ∃ a, T.value = Sum.inl a) {S S' : UnorderedTree (α ⊕ β)}
    (hK : (s.map Prod.snd).sum.1 = {S, S'}) :
    Forest.accessibleSize ({UnorderedTree.node (Sum.inl a) {S, S'}} + (s.map Prod.snd).sum.2) =
      Forest.accessibleSize F + 1 := by
  have := accessibleCount_merge_term a hs hF hK
  have := card_singleton_add_trunk_add_countP hs (UnorderedTree.node (Sum.inl a) {S, S'})
  simp only [Forest.accessibleSize] at *
  omega

/-- Under trace counting a term of Merge satisfies Minimal Yield exactly when it takes at least
    one of its objects whole. External Merge and the Sideward case 2(b) satisfy it, and the
    Sideward cases 3(a) and 3(b) do not ([marcolli-chomsky-berwick-2025] Proposition 1.6.8). -/
theorem MinimalYield.merge_term_accessibleCount_iff (a : α)
    (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F) (hF : ∀ T ∈ F, ∃ a, T.value = Sum.inl a)
    {S S' : UnorderedTree (α ⊕ β)} (hK : (s.map Prod.snd).sum.1 = {S, S'}) :
    MinimalYield UnorderedTree.accessibleCount F
        ({UnorderedTree.node (Sum.inl a) {S, S'}} + (s.map Prod.snd).sum.2) ↔
      s.countP (·.2.2 = 0) ≠ 0 :=
  MinimalYield.merge_term_iff_of_extraction_one hs (extraction_accessibleCount hF) hK
    (UnorderedTree.accessibleCount_merge a S S'
      (traceLeafCount_lt_of_mem_crown hs hF (hK ▸ Multiset.mem_cons_self _ _))
      (traceLeafCount_lt_of_mem_crown hs hF
        (hK ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))))

/-- Under trace counting a term of the unit stage loses one accessible term unless it takes `β`
    whole, and keeps the size `σ` ([marcolli-chomsky-berwick-2025] Remark 1.6.7, for `Δ^c`). -/
theorem accessibleCount_unit_term (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ T ∈ F, ∃ a, T.value = Sum.inl a) {β' : UnorderedTree (α ⊕ β)}
    (hK : (s.map Prod.snd).sum.1 = {β'}) :
    Forest.accessibleCount ({β'} + (s.map Prod.snd).sum.2) + 1 =
        Forest.accessibleCount F + s.countP (·.2.2 = 0) ∧
      Forest.accessibleSize ({β'} + (s.map Prod.snd).sum.2) = Forest.accessibleSize F := by
  have h := sum_map_unit_term_add (k := 1) hs (by simpa using extraction_accessibleCount hF) hK
  have := card_singleton_add_trunk_add_countP hs β'
  simp only [Forest.accessibleSize, Forest.accessibleCount, one_mul] at *
  omega

end Trace

end Minimalist
