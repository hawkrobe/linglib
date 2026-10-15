module

public import Linglib.Syntax.Minimalist.Merge.Internal
public import Linglib.Syntax.Minimalist.Workspace.TraceMeasures

/-!
# No Complexity Loss

No Complexity Loss is a condition on a transformation `F → F'` of workspaces (Definition 1.6.2 of
Marcolli, Chomsky and Berwick): the map sending each component of `F` to the component of `F'`
holding its root never decreases degree, so Merge builds hierarchical structure of nondecreasing
complexity. `NoComplexityLoss F F'` asks for some such map, and `NoComplexityLoss.Map deg φ`
checks a given one, as a multiset `φ` of pairs, for a degree `deg`.

A term of Merge chooses a cut for each component, so its own map, `componentMap`, sends a
component taken whole to the Merge and a cut component to its trunk. Along it, no complexity is
lost exactly when every component is taken whole or left uncut. Every Sideward term, and every
term of the unit stage on its own, cuts a component and loses complexity (Proposition 1.6.10).
External and Internal Merge satisfy the condition. These hold for any positive degree that every
cut splits between its crown and its trunk.

## Implementation notes

The book grades by leaf count. A degree that each cut conserves avoids the nullary-node
corrections leaf count incurs when a node loses all its children under a multi-edge cut. At the
pruning cuts this is the vertex count, the canonical Connes–Kreimer grading
(`cutSummandsN_numNodes`). At the trace cuts a trace leaf takes the place of each extracted tree,
so extracting a single lexical item keeps the vertex count. They conserve instead the size `σ`,
which leaves trace leaves out (`cutSummandsCN_accessibleSize`, the book's (1.6.10)), and graded by
`σ` every Sideward term loses complexity there too.

## Main definitions

* `Minimalist.NoComplexityLoss`, `Minimalist.NoComplexityLoss.Map`
* `Minimalist.componentMap`: the component map of a choice of cuts.

## Main results

* `Minimalist.NoComplexityLoss.em_case1`, `NoComplexityLoss.im_residual`, `NoComplexityLoss.im`:
  External and Internal Merge satisfy the condition.
* `Minimalist.NoComplexityLoss.map_componentMap_merge_iff`: a term of Merge loses no complexity
  exactly when it takes components whole or leaves them uncut.
* `Minimalist.NoComplexityLoss.not_map_componentMap_merge`, `not_map_componentMap_unit`: every
  Sideward term and every term of the unit stage loses complexity.
* `Minimalist.NoComplexityLoss.not_map_accessibleSize_componentMap_merge`: at the trace cuts,
  graded by `σ`.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

/-- A workspace transformation `F → F'` satisfies No Complexity Loss
    ([marcolli-chomsky-berwick-2025] Definition 1.6.2) when some component map lands in `F'` and
    never decreases the vertex count. -/
def NoComplexityLoss {α : Type*} (F F' : Forest (UnorderedTree α)) : Prop :=
  ∃ (Φ₀ : ∀ T, T ∈ F → UnorderedTree α),
    (∀ T (h : T ∈ F), Φ₀ T h ∈ F') ∧
    (∀ T (h : T ∈ F), (Φ₀ T h).numNodes ≥ T.numNodes)

/-- External Merge satisfies No Complexity Loss ([marcolli-chomsky-berwick-2025]
    Proposition 1.6.10), since the merged components map to their Merge, which is heavier than
    each, and the spectators map to themselves. -/
theorem NoComplexityLoss.em_case1 {α : Type*} [DecidableEq (UnorderedTree α)]
    (lbl : α) (S S' : UnorderedTree α) (Fhat : Forest (UnorderedTree α)) :
    NoComplexityLoss (({S, S'} : Forest (UnorderedTree α)) + Fhat)
               (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat) := by
  refine ⟨fun T _ => if T = S ∨ T = S' then UnorderedTree.node lbl {S, S'} else T, ?_, ?_⟩
  -- (a) image is in F'
  · intro T hT
    show (if T = S ∨ T = S' then UnorderedTree.node lbl {S, S'} else T)
            ∈ ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat
    by_cases hcase : T = S ∨ T = S'
    · rw [ite_eq_left hcase]
      exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
    · rw [ite_eq_right hcase]
      have hT_Fhat : T ∈ Fhat := by
        rcases Multiset.mem_add.mp hT with hT_pair | hT_Fhat
        · exfalso; apply hcase
          rw [show ({S, S'} : Forest (UnorderedTree α)) = S ::ₘ {S'} from rfl,
              Multiset.mem_cons, Multiset.mem_singleton] at hT_pair
          exact hT_pair
        · exact hT_Fhat
      exact Multiset.mem_add.mpr (Or.inr hT_Fhat)
  -- (b) weight nondecreasing
  · intro T _
    show (if T = S ∨ T = S' then UnorderedTree.node lbl {S, S'} else T).numNodes ≥ T.numNodes
    by_cases hcase : T = S ∨ T = S'
    · rw [ite_eq_left hcase, UnorderedTree.numNodes_node,
          show ({S, S'} : Forest (UnorderedTree α)) = S ::ₘ {S'} from rfl,
          Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton]
      rcases hcase with rfl | rfl <;> omega
    · rw [ite_eq_right hcase]

/-- Internal Merge satisfies No Complexity Loss beside a spectator workspace, for any cut whose
    crown `β` and trunk `Q` together weigh at least the source `T`. The source maps to the Merge of
    `Q` and `β`, and the spectators map to themselves. -/
theorem NoComplexityLoss.im_residual {α : Type*} (lbl : α) {β T Q : UnorderedTree α}
    (h : T.numNodes ≤ β.numNodes + Q.numNodes) (Fhat : Forest (UnorderedTree α)) :
    NoComplexityLoss (({T} : Forest (UnorderedTree α)) + Fhat)
      (({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α)) + Fhat) := by
  classical
  refine ⟨fun U _ ↦ if U = T then UnorderedTree.node lbl {Q, β} else U, fun U hU ↦ ?_,
    fun U _ ↦ ?_⟩ <;> beta_reduce
  · by_cases hUT : U = T
    · rw [ite_eq_left hUT]
      exact Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _))
    · rw [ite_eq_right hUT]
      rcases Multiset.mem_add.mp hU with h1 | h1
      · exact absurd (Multiset.mem_singleton.mp h1) hUT
      · exact Multiset.mem_add.mpr (.inr h1)
  · by_cases hUT : U = T
    · rw [ite_eq_left hUT, hUT, UnorderedTree.numNodes_node_pair]
      omega
    · rw [ite_eq_right hUT]

/-- Internal Merge through a pruning cut satisfies No Complexity Loss
    ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). -/
theorem NoComplexityLoss.im {α : Type*} (lbl : α) (β T Q : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α) (hp0 : p0 ∈ cutSummandsN T)
    (h_cf : p0.1 = ({β} : Forest (UnorderedTree α)))
    (h_remainder : p0.2 = Q) :
    NoComplexityLoss (({T} : Forest (UnorderedTree α)))
               (({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α))) := by
  have h_cons := cutSummandsN_numNodes T p0 hp0
  rw [h_cf, h_remainder, Multiset.map_singleton, Multiset.sum_singleton] at h_cons
  simpa using NoComplexityLoss.im_residual lbl (β := β) (T := T) (Q := Q) (by omega) 0

/-! ### No Complexity Loss along the component map of a term of Merge

[marcolli-chomsky-berwick-2025] Definition 1.6.2 states No Complexity Loss for the induced map,
which sends each component of the workspace to the component holding its root afterwards. A term
of Merge or of its unit stage is a choice of a cut for each component (`mergeOpG_apply_of'_eq_sum`,
`mergeOpUnitG_apply_of'_eq_sum`), so its induced map pairs a component taken whole with the object
built from the crown, and a cut component with its trunk. As a multiset of pairs it keeps apart
equal components that go to different places.

The results hold for any positive degree that each cut conserves, splitting a tree's degree
between its crown and its trunk: the vertex count at the pruning cuts (`cutSummandsN_numNodes`)
and the size `σ` at the trace cuts (`cutSummandsCN_accessibleSize`, the book's (1.6.10)). -/

section ComponentMap

variable {α : Type*} {deg : UnorderedTree α → ℕ}

/-- No Complexity Loss holds along a component map when no component is paired with one of lower
    degree. -/
def NoComplexityLoss.Map (deg : UnorderedTree α → ℕ)
    (φ : Multiset (UnorderedTree α × UnorderedTree α)) : Prop :=
  ∀ x ∈ φ, deg x.1 ≤ deg x.2

variable {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
  {F : Forest (UnorderedTree α)}
  {s : Multiset (UnorderedTree α × (Forest (UnorderedTree α) × Forest (UnorderedTree α)))}

/-- A tree taken whole into the crown `{S, S'}` of a term of Merge is one of the merged objects,
    and so weighs no more than any object outweighing both. -/
private theorem deg_le_of_snd_eq_zero (hs : s ∈ forestCutChoicesG cuts F)
    {S S' X : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {S, S'}) (hS : deg S ≤ deg X)
    (hS' : deg S' ≤ deg X) : ∀ x ∈ s, x.2.2 = 0 → deg x.1 ≤ deg X := by
  intro x hx h0
  have hmem : x.1 ∈ ({S, S'} : Forest (UnorderedTree α)) :=
    hK ▸ mem_fst_sum_map_snd_iff.mpr ⟨x, hx, by simp [snd_eq_of_mem_forestCutChoicesG hs hx h0]⟩
  rcases Multiset.mem_cons.mp hmem with h | h
  · exact h ▸ hS
  · exact Multiset.mem_singleton.mp h ▸ hS'

variable [DecidableEq (UnorderedTree α)]

/-- The component map of a choice of cuts sends a tree taken whole to the object `X` built from the
    crown, and a cut tree to its trunk. -/
def componentMap (X : UnorderedTree α)
    (s : Multiset (UnorderedTree α × (Forest (UnorderedTree α) × Forest (UnorderedTree α)))) :
    Multiset (UnorderedTree α × UnorderedTree α) :=
  s.bind fun x ↦ (if x.2.2 = 0 then {X} else x.2.2).map (Prod.mk x.1)

/-- Along the component map of a choice of cuts conserving a positive degree, no complexity is lost
    exactly when every tree is taken whole or left uncut, provided the object `X` outweighs the
    trees taken whole. -/
theorem NoComplexityLoss.map_componentMap_iff (hs : s ∈ forestCutChoicesG cuts F)
    (hcons : ∀ T ∈ F, ∀ p ∈ cuts T, (p.1.map deg).sum + deg p.2 = deg T)
    (hpos : ∀ T, 0 < deg T) {X : UnorderedTree α}
    (hX : ∀ x ∈ s, x.2.2 = 0 → deg x.1 ≤ deg X) :
    NoComplexityLoss.Map deg (componentMap X s) ↔ ∀ x ∈ s, x.2.1 = 0 ∨ x.2.2 = 0 := by
  have hF : ∀ x ∈ s, x.1 ∈ F := fun x hx ↦
    map_fst_of_mem_forestCutChoicesG hs ▸ Multiset.mem_map_of_mem Prod.fst hx
  simp only [NoComplexityLoss.Map, componentMap, Multiset.mem_bind, Multiset.mem_map]
  constructor
  · intro h x hx
    rcases mem_treeCutsG.mp (mem_treeCutsG_of_mem_forestCutChoicesG hs hx) with h2 | ⟨p, hp, h2⟩
    · exact .inr (by rw [h2])
    · refine .inl ?_
      have hle := h (x.1, p.2) ⟨x, hx, p.2, by simp [← h2], rfl⟩
      have hcons := hcons x.1 (hF x hx) p hp
      rw [← h2]
      show p.1 = 0
      refine Multiset.eq_zero_of_forall_notMem fun u hu ↦ ?_
      have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem deg hu)
      have := hpos u
      simp only at hle
      omega
  · rintro h y ⟨x, hx, t, ht, rfl⟩
    by_cases h0 : x.2.2 = 0
    · rw [ite_eq_left h0, Multiset.mem_singleton] at ht
      exact ht ▸ hX x hx h0
    · rw [ite_eq_right h0] at ht
      rcases mem_treeCutsG.mp (mem_treeCutsG_of_mem_forestCutChoicesG hs hx) with h2 | ⟨p, hp, h2⟩
      · exact absurd (by rw [h2]) h0
      · have hcons := hcons x.1 (hF x hx) p hp
        rw [← h2, Multiset.mem_singleton] at ht
        have h1 : p.1 = 0 := by
          have := (h x hx).resolve_right h0
          rwa [← h2] at this
        rw [h1, Multiset.map_zero, Multiset.sum_zero, zero_add] at hcons
        exact (ht ▸ hcons).ge

/-- A tree of the crown that is not a component of the workspace was cut out of a component, and
    that component goes to a trunk of lower degree. -/
theorem NoComplexityLoss.not_map_componentMap (hs : s ∈ forestCutChoicesG cuts F)
    (hcons : ∀ T ∈ F, ∀ p ∈ cuts T, (p.1.map deg).sum + deg p.2 = deg T)
    (hpos : ∀ T, 0 < deg T) {X : UnorderedTree α}
    (hX : ∀ x ∈ s, x.2.2 = 0 → deg x.1 ≤ deg X)
    {T : UnorderedTree α} (hT : T ∈ (s.map Prod.snd).sum.1) (hTF : T ∉ F) :
    ¬ NoComplexityLoss.Map deg (componentMap X s) := by
  rw [NoComplexityLoss.map_componentMap_iff hs hcons hpos hX]
  intro h
  obtain ⟨x, hx, hTx⟩ := mem_fst_sum_map_snd_iff.mp hT
  rcases h x hx with h0 | h0
  · exact Multiset.notMem_zero _ (h0 ▸ hTx)
  · rw [snd_eq_of_mem_forestCutChoicesG hs hx h0, Multiset.mem_singleton] at hTx
    exact hTF (hTx ▸ map_fst_of_mem_forestCutChoicesG hs ▸ Multiset.mem_map_of_mem Prod.fst hx)

/-- A term of Merge loses no complexity along its component map exactly when it takes trees whole
    or leaves them uncut ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). -/
theorem NoComplexityLoss.map_componentMap_merge_iff (hs : s ∈ forestCutChoicesG cuts F)
    (hcons : ∀ T ∈ F, ∀ p ∈ cuts T, (p.1.map deg).sum + deg p.2 = deg T)
    (hpos : ∀ T, 0 < deg T) {S S' X : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {S, S'})
    (hS : deg S ≤ deg X) (hS' : deg S' ≤ deg X) :
    NoComplexityLoss.Map deg (componentMap X s) ↔ ∀ x ∈ s, x.2.1 = 0 ∨ x.2.2 = 0 :=
  NoComplexityLoss.map_componentMap_iff hs hcons hpos (deg_le_of_snd_eq_zero hs hK hS hS')

/-- Every term of Sideward Merge loses complexity along its component map
    ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). If `S` or `S'` is not a component of the
    workspace, the component it is cut out of goes to a trunk of lower degree. -/
theorem NoComplexityLoss.not_map_componentMap_merge (hs : s ∈ forestCutChoicesG cuts F)
    (hcons : ∀ T ∈ F, ∀ p ∈ cuts T, (p.1.map deg).sum + deg p.2 = deg T)
    (hpos : ∀ T, 0 < deg T) {S S' X : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {S, S'})
    (hS : deg S ≤ deg X) (hS' : deg S' ≤ deg X) (h : S ∉ F ∨ S' ∉ F) :
    ¬ NoComplexityLoss.Map deg (componentMap X s) := by
  have hX := deg_le_of_snd_eq_zero hs hK hS hS'
  rcases h with h | h
  · exact NoComplexityLoss.not_map_componentMap hs hcons hpos hX
      (hK ▸ Multiset.mem_cons_self _ _) h
  · exact NoComplexityLoss.not_map_componentMap hs hcons hpos hX
      (hK ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)) h

/-- Every term of the unit stage `M_{β,1}` with `β` not a component of the workspace loses
    complexity along its component map ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). -/
theorem NoComplexityLoss.not_map_componentMap_unit (hs : s ∈ forestCutChoicesG cuts F)
    (hcons : ∀ T ∈ F, ∀ p ∈ cuts T, (p.1.map deg).sum + deg p.2 = deg T)
    (hpos : ∀ T, 0 < deg T) {β : UnorderedTree α} (hK : (s.map Prod.snd).sum.1 = {β})
    (hβ : β ∉ F) : ¬ NoComplexityLoss.Map deg (componentMap β s) :=
  NoComplexityLoss.not_map_componentMap hs hcons hpos (fun x hx h0 ↦ by
    have : x.1 ∈ ({β} : Forest (UnorderedTree α)) :=
      hK ▸ mem_fst_sum_map_snd_iff.mpr ⟨x, hx, by simp [snd_eq_of_mem_forestCutChoicesG hs hx h0]⟩
    rw [Multiset.mem_singleton.mp this]) (hK ▸ Multiset.mem_singleton_self _) hβ

end ComponentMap

/-! ### At the trace cuts

Graded by vertices, a term of Merge at the trace cuts may lose nothing, since a trace leaf takes
the place of each extracted tree. Graded by the size `σ`, which the trace cuts conserve, every
Sideward term loses complexity. -/

section TraceCuts

variable {α β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))] {τ : UnorderedTree (α ⊕ β) → β}
  {F : Forest (UnorderedTree (α ⊕ β))}
  {s : Multiset (UnorderedTree (α ⊕ β) ×
    (Forest (UnorderedTree (α ⊕ β)) × Forest (UnorderedTree (α ⊕ β))))}

/-- At the trace cuts, graded by the size `σ`, every term of Sideward Merge loses complexity along
    its component map ([marcolli-chomsky-berwick-2025] Proposition 1.6.10). -/
theorem NoComplexityLoss.not_map_accessibleSize_componentMap_merge (a : α)
    (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F) (hF : ∀ T ∈ F, ∃ a, T.value = Sum.inl a)
    {S S' : UnorderedTree (α ⊕ β)} (hK : (s.map Prod.snd).sum.1 = {S, S'})
    (h : S ∉ F ∨ S' ∉ F) :
    ¬ NoComplexityLoss.Map (fun T ↦ Forest.accessibleSize {T})
      (componentMap (UnorderedTree.node (Sum.inl a) {S, S'}) s) := by
  have hmerge := UnorderedTree.accessibleCount_merge a S S'
    (traceLeafCount_lt_numNodes_of_mem_crown hs hF (hK ▸ Multiset.mem_cons_self _ _))
    (traceLeafCount_lt_numNodes_of_mem_crown hs hF
      (hK ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)))
  refine NoComplexityLoss.not_map_componentMap_merge hs
    (fun T hT p hp ↦ cutSummandsCN_accessibleSize τ (hF T hT).choose_spec hp)
    (fun T ↦ by simp) hK ?_ ?_ h <;> simp only [Forest.accessibleSize_singleton, hmerge] <;> omega

end TraceCuts

end Minimalist
