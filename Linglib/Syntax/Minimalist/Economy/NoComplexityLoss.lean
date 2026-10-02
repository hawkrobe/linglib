module

public import Linglib.Syntax.Minimalist.Merge.Internal

/-!
# No Complexity Loss

No Complexity Loss is a condition on a transformation `F → F'` of workspaces: some map sending
each component of `F` to a component of `F'` is nondecreasing in degree, so Merge builds
hierarchical structure of nondecreasing complexity. `NoComplexityLoss F F'` is the existential
form and `NoComplexityLoss.Map F F' Φ₀` the form for a given component map, with
`NoComplexityLoss.degreeLoss` the per-component degree difference whose nonnegativity it asserts.

On the shapes the cases of Merge produce, External and Internal Merge satisfy the condition, and
each Sideward configuration fails it under its canonical component map, because a deletion
quotient is strictly lighter than its source.

## Implementation notes

The book grades by leaf count. We grade by `UnorderedTree.numNodes`, the canonical Connes–Kreimer
grading: the deletion coproduct conserves it exactly (`cutSummandsN_numNodes`) for every cut,
with none of the nullary-node corrections leaf count incurs when a node loses all its children
under a multi-edge cut. The condition is a nondecreasing one, and vertex count delivers every
conclusion leaf count would: the Merge node's weight strictly exceeds each operand's, and every
deletion quotient's weight is strictly smaller than its source.

## Main definitions

* `Minimalist.NoComplexityLoss`, `Minimalist.NoComplexityLoss.Map`
* `Minimalist.NoComplexityLoss.degreeLoss`: the per-component degree-loss function.

## Main results

* `Minimalist.NoComplexityLoss.em_case1`, `NoComplexityLoss.im_residual`, `NoComplexityLoss.im`:
  External and Internal Merge satisfy the condition.
* `Minimalist.NoComplexityLoss.not_map_sideward_2b`, `_3a`, `_3b`: the Sideward configurations
  fail it under the canonical map.

## References

* [marcolli-chomsky-berwick-2025], §1.6.1 and §1.6.3 (Definition 1.6.2, Proposition 1.6.10)
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
    Proposition 1.6.10): the merged components map to their Merge, which is heavier than each, and
    the spectators map to themselves. -/
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
    crown `β` and trunk `Q` together weigh at least the source `T`: the source maps to the Merge of
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

/-! ### No Complexity Loss for a given component map -/

/-- No Complexity Loss for a given component map `Φ_0`, the induced map of
    [marcolli-chomsky-berwick-2025] Definition 1.6.2: every component `T ∈ F` has
    `(Φ_0 T).numNodes ≥ T.numNodes`.

    Compare `NoComplexityLoss` (existential: "some map works"). The strict form
    is needed for the negative direction: a Sideward operation might satisfy
    `NoComplexityLoss` via some non-canonical map, but its canonical map (each
    root to where its image lives) fails. -/
def NoComplexityLoss.Map {α : Type*} (F F' : Forest (UnorderedTree α))
    (Φ_0 : ∀ T, T ∈ F → UnorderedTree α) : Prop :=
  (∀ T (h : T ∈ F), Φ_0 T h ∈ F') ∧
  (∀ T (h : T ∈ F), (Φ_0 T h).numNodes ≥ T.numNodes)

/-- No Complexity Loss for a given component map implies the existential form. -/
theorem NoComplexityLoss.of_map {α : Type*}
    {F F' : Forest (UnorderedTree α)} {Φ_0 : ∀ T, T ∈ F → UnorderedTree α}
    (h : NoComplexityLoss.Map F F' Φ_0) : NoComplexityLoss F F' :=
  ⟨Φ_0, h.1, h.2⟩

/-- The degree loss of a component ([marcolli-chomsky-berwick-2025] (1.6.4)) is the weight
    difference across the component map, valued in `Int` so that violations are negative. -/
def NoComplexityLoss.degreeLoss {α : Type*} {F : Forest (UnorderedTree α)}
    (Φ_0 : ∀ T, T ∈ F → UnorderedTree α) (T : UnorderedTree α) (h : T ∈ F) : Int :=
  ((Φ_0 T h).numNodes : Int) - T.numNodes

/-- No Complexity Loss for a component map ([marcolli-chomsky-berwick-2025] (1.6.3)) is the
    nonnegativity of every degree loss. -/
theorem NoComplexityLoss.map_iff_degreeLoss_nonneg {α : Type*}
    {F F' : Forest (UnorderedTree α)} (Φ_0 : ∀ T, T ∈ F → UnorderedTree α)
    (h_image : ∀ T (h : T ∈ F), Φ_0 T h ∈ F') :
    NoComplexityLoss.Map F F' Φ_0 ↔ ∀ T (h : T ∈ F), NoComplexityLoss.degreeLoss Φ_0 T h ≥ 0 := by
  unfold NoComplexityLoss.Map NoComplexityLoss.degreeLoss
  refine ⟨fun ⟨_, h2⟩ T hT => by have := h2 T hT; omega,
          fun h => ⟨h_image, fun T hT => by have := h T hT; omega⟩⟩

/-! ### Sideward Merge -/

/-- Sideward Merge of type 2(b) violates No Complexity Loss under its canonical component map
    ([marcolli-chomsky-berwick-2025] Proposition 1.6.10): in `{T_i, T_j} → {M(T_i, β), T_j/β}`
    the component `T_j` maps to the lighter quotient `T_j/β`. -/
theorem NoComplexityLoss.not_map_sideward_2b {α : Type*} [DecidableEq (UnorderedTree α)]
    (lbl : α) (T_i T_j β T_j_q : UnorderedTree α)
    (p_j : Forest (UnorderedTree α) × UnorderedTree α) (hp_j : p_j ∈ cutSummandsN T_j)
    (h_cf : p_j.1 = ({β} : Forest (UnorderedTree α)))
    (h_rd : p_j.2 = T_j_q)
    (h_distinct : T_i ≠ T_j) :
    ¬ NoComplexityLoss.Map ({T_i, T_j} : Forest (UnorderedTree α))
                    ({UnorderedTree.node lbl {T_i, β}, T_j_q} : Forest (UnorderedTree α))
        (fun T _ => if T = T_i then UnorderedTree.node lbl {T_i, β} else T_j_q) := by
  intro h_ncl
  have h_T_j_mem : T_j ∈ ({T_i, T_j} : Forest (UnorderedTree α)) :=
    Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr rfl)
  have h_neq : T_j ≠ T_i := fun h => h_distinct h.symm
  have h_ineq :
      (if T_j = T_i then UnorderedTree.node lbl {T_i, β} else T_j_q).numNodes ≥ T_j.numNodes :=
    h_ncl.2 T_j h_T_j_mem
  rw [ite_eq_right h_neq] at h_ineq
  have h_cons := cutSummandsN_numNodes T_j p_j hp_j
  rw [h_cf] at h_cons
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at h_cons
  rw [h_rd] at h_cons
  have h_β_pos := β.numNodes_pos
  omega

/-- Sideward Merge of type 3(a) violates No Complexity Loss under its canonical component map:
    in `{T_i} → {M(a, b), T_i/(a⊔b)}` the component `T_i` maps to the quotient that has lost both
    subtrees. -/
theorem NoComplexityLoss.not_map_sideward_3a {α : Type*}
    (lbl : α) (T_i a b T_iq : UnorderedTree α)
    (p_i : Forest (UnorderedTree α) × UnorderedTree α) (hp_i : p_i ∈ cutSummandsN T_i)
    (h_cf : p_i.1 = ({a, b} : Forest (UnorderedTree α)))
    (h_rd : p_i.2 = T_iq) :
    ¬ NoComplexityLoss.Map ({T_i} : Forest (UnorderedTree α))
                    ({UnorderedTree.node lbl {a, b}, T_iq} : Forest (UnorderedTree α))
        (fun _ _ => T_iq) := by
  intro h_ncl
  have h_ineq : T_iq.numNodes ≥ T_i.numNodes := h_ncl.2 T_i (Multiset.mem_singleton.mpr rfl)
  have h_cons := cutSummandsN_numNodes T_i p_i hp_i
  rw [h_cf, show ({a, b} : Forest (UnorderedTree α)) = a ::ₘ {b} from rfl,
      Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton,
      h_rd] at h_cons
  have h_a_pos := a.numNodes_pos
  have h_b_pos := b.numNodes_pos
  omega

/-- Sideward Merge of type 3(b) violates No Complexity Loss under its canonical component map:
    in `{T_i, T_j} → {M(a, b), T_i/a, T_j/b}` the component `T_i` maps to the lighter quotient
    `T_i/a`. -/
theorem NoComplexityLoss.not_map_sideward_3b {α : Type*} [DecidableEq (UnorderedTree α)]
    (lbl : α) (T_i T_j a b T_iq T_jq : UnorderedTree α)
    (p_i : Forest (UnorderedTree α) × UnorderedTree α) (hp_i : p_i ∈ cutSummandsN T_i)
    (h_cf_i : p_i.1 = ({a} : Forest (UnorderedTree α)))
    (h_rd_i : p_i.2 = T_iq) :
    ¬ NoComplexityLoss.Map ({T_i, T_j} : Forest (UnorderedTree α))
                    ({UnorderedTree.node lbl {a, b}, T_iq, T_jq} : Forest (UnorderedTree α))
        (fun T _ => if T = T_i then T_iq else T_jq) := by
  intro h_ncl
  have h_ineq : (if T_i = T_i then T_iq else T_jq).numNodes ≥ T_i.numNodes :=
    h_ncl.2 T_i (Multiset.mem_cons_self _ _)
  rw [ite_eq_left rfl] at h_ineq
  have h_cons := cutSummandsN_numNodes T_i p_i hp_i
  rw [h_cf_i] at h_cons
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at h_cons
  rw [h_rd_i] at h_cons
  have h_a_pos := a.numNodes_pos
  omega

end Minimalist
