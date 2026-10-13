/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Basic
public import Linglib.Core.Data.UnorderedTree.Count
public import Linglib.Core.Data.UnorderedTree.DecEq
public import Linglib.Core.Data.Multiset.Bind
public import Linglib.Core.Data.RoseTree.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Admissible-cut enumeration on rose trees

The combinatorics of admissible cuts, independent of the Hopf-algebra structures built on it in
`Core/Algebra/RootedTree/Coproduct/`. An admissible cut of a tree removes a set of subtrees, no
two on a common path to the root. It splits the tree into a crown, the multiset of removed
subtrees, and a trunk, what is left at the root. The enumeration is parameterized by an
extraction policy `extract : RoseTree α → Option (List (RoseTree α))`, called on each cut subtree:

- `extract t = none` forbids cuts at that subtree;
- `extract t = some []` removes it, leaving nothing in the parent's child slot;
- `extract t = some rs` removes it and leaves the replacement trees `rs` in its slot.

The cut bookkeeping is shared by every policy; only the remainder left at a cut varies. The
policy `pruning`, which always leaves nothing, gives the cuts of the Connes–Kreimer coproduct.

## Main definitions

* `ConnesKreimer.cutSummandsG extract`: the enumeration of the pairs of a crown and a trunk.
* `ConnesKreimer.ExtractInvariant`: the policies that descend along `RoseTree.Perm`.
* `ConnesKreimer.pruning`, `ConnesKreimer.cutSummandsN`: the pruning policy and its cuts on
  `UnorderedTree`.
* `ConnesKreimer.countSingleCutsRho`: the number of single cuts with given crown and trunk.

## Main results

* `ConnesKreimer.cutSummandsG_proj_perm`: the projected enumeration is `Perm`-invariant for an
  invariant policy.
* `ConnesKreimer.cutSummandsG_filter_empty`: the empty cut is the unique cut with empty crown.
* `ConnesKreimer.cutSummandsN_node`: the pruning cuts of a node are the cut convolution over its
  children.

`[UPSTREAM]` candidate.

## References

* [connes-kreimer-1998]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

variable {α : Type*}

/-! ### The enumeration -/

mutual
/-- The cuts of a tree under the policy `extract`, as pairs of a crown and a trunk. -/
def cutSummandsG (extract : RoseTree α → Option (List (RoseTree α))) :
    RoseTree α → Multiset (Multiset (RoseTree α) × RoseTree α)
  | .node a cs => (cutListSummandsG extract cs).map fun p ↦ (p.1, .node a p.2)
/-- The cuts of a list of children, as pairs of a crown and the list of what remains. A surviving
    child contributes its trunk and a cut child contributes `extract` of it. -/
def cutListSummandsG (extract : RoseTree α → Option (List (RoseTree α))) :
    List (RoseTree α) → Multiset (Multiset (RoseTree α) × List (RoseTree α))
  | [] => {((0 : Multiset (RoseTree α)), ([] : List (RoseTree α)))}
  | t :: ts =>
      ((augActionG extract t ×ˢ cutListSummandsG extract ts) : Multiset _).map
        fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2)
/-- The choices at one child `t` are to cut `t` itself, with crown `{t}` and remainder
    `extract t` when the policy allows it, or to cut inside `t`. -/
def augActionG (extract : RoseTree α → Option (List (RoseTree α))) :
    RoseTree α → Multiset (Multiset (RoseTree α) × List (RoseTree α))
  | t =>
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Multiset (RoseTree α)), r)})
      + (cutSummandsG extract t).map fun p ↦ (p.1, [p.2])
end

variable (extract : RoseTree α → Option (List (RoseTree α)))

@[simp] theorem cutSummandsG_node (a : α) (cs : List (RoseTree α)) :
    cutSummandsG extract (RoseTree.node a cs) =
      (cutListSummandsG extract cs).map fun p ↦ (p.1, .node a p.2) := by
  unfold cutSummandsG; rfl

@[simp] theorem cutListSummandsG_nil :
    cutListSummandsG extract ([] : List (RoseTree α)) =
      {((0 : Multiset (RoseTree α)), ([] : List (RoseTree α)))} := by
  unfold cutListSummandsG; rfl

@[simp] theorem cutListSummandsG_cons (t : RoseTree α) (ts : List (RoseTree α)) :
    cutListSummandsG extract (t :: ts) =
      ((augActionG extract t ×ˢ cutListSummandsG extract ts) : Multiset _).map
        fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2) := by
  conv_lhs => unfold cutListSummandsG

@[simp] theorem augActionG_eq (t : RoseTree α) :
    augActionG extract t =
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Multiset (RoseTree α)), r)})
      + (cutSummandsG extract t).map fun p ↦ (p.1, [p.2]) := by
  conv_lhs => unfold augActionG

/-- Where the policy forbids a cut, the only choices at a child are the cuts inside it. -/
theorem augActionG_eq_none (t : RoseTree α) (h : extract t = none) :
    augActionG extract t = (cutSummandsG extract t).map fun p ↦ (p.1, [p.2]) := by
  rw [augActionG_eq, h]
  simp

/-- Where the policy allows a cut, cutting the child itself is one of the choices. -/
theorem augActionG_eq_some (t : RoseTree α) (r : List (RoseTree α)) (h : extract t = some r) :
    augActionG extract t =
      (({t} : Multiset (RoseTree α)), r) ::ₘ
        (cutSummandsG extract t).map fun p ↦ (p.1, [p.2]) := by
  rw [augActionG_eq, h, Multiset.singleton_add]

example (a : α) : cutSummandsG extract (RoseTree.leaf a) = {(0, RoseTree.leaf a)} := by
  rw [RoseTree.leaf, cutSummandsG_node, cutListSummandsG_nil]
  rfl

/-! ### Vertex conservation

When every remainder the policy leaves has `k` vertices in total, a cut conserves vertices up to
`k` per crown component. Pruning has `k = 0` and a policy leaving one leaf has `k = 1`. -/

mutual

/-- The crown and the trunk of a cut have the vertices of the tree, plus `k` for each crown
    component. -/
theorem cutSummandsG_numNodes {k : ℕ}
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numNodes).sum = k) :
    ∀ (t : RoseTree α), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map RoseTree.numNodes p.1).sum + RoseTree.numNodes p.2 =
        RoseTree.numNodes t + k * Multiset.card p.1
  | .node a cs => by
    intro p hp
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsG_numNodes hext cs q hq
    simp only [RoseTree.numNodes_node]
    omega

theorem cutListSummandsG_numNodes {k : ℕ}
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numNodes).sum = k) :
    ∀ (cs : List (RoseTree α)), ∀ q ∈ cutListSummandsG extract cs,
      (Multiset.map RoseTree.numNodes q.1).sum + (q.2.map RoseTree.numNodes).sum =
        (cs.map RoseTree.numNodes).sum + k * Multiset.card q.1
  | [] => by
    intro q hq
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    simp
  | t :: ts => by
    intro q hq
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionG_numNodes hext t pr.1 ha
    have h2 := cutListSummandsG_numNodes hext ts pr.2 hq'
    rw [Multiset.map_add, Multiset.sum_add, List.map_append, List.sum_append,
        Multiset.card_add, List.map_cons, List.sum_cons, Nat.mul_add]
    omega

theorem augActionG_numNodes {k : ℕ}
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numNodes).sum = k) :
    ∀ (t : RoseTree α), ∀ a ∈ augActionG extract t,
      (Multiset.map RoseTree.numNodes a.1).sum + (a.2.map RoseTree.numNodes).sum =
        RoseTree.numNodes t + k * Multiset.card a.1
  | t => by
    intro a ha
    rw [augActionG_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hex : extract t with
      | none =>
        rw [hex] at h
        exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hex] at h
        obtain rfl := Multiset.mem_singleton.mp h
        simp [hext t r hex]
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      have h := cutSummandsG_numNodes hext t p hp
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

end

/-! ### Projection to unordered trees

A cut of a rose tree projects to `UnorderedTree` componentwise. On children the remainder list
becomes a multiset, and the combination of the cuts of two children becomes `combinerProjG`. -/

/-- Project the crown and the trunk of a cut to unordered trees. -/
def projSummand (p : Multiset (RoseTree α) × RoseTree α) :
    Multiset (UnorderedTree α) × UnorderedTree α :=
  (p.1.map UnorderedTree.mk, UnorderedTree.mk p.2)

/-- Project the crown and the remainder list of a cut of a list of children. -/
def projForest (p : Multiset (RoseTree α) × List (RoseTree α)) :
    Multiset (UnorderedTree α) × Multiset (UnorderedTree α) :=
  (p.1.map UnorderedTree.mk, Multiset.ofList (p.2.map UnorderedTree.mk))

theorem projSummand_node (a : α) (p : Multiset (RoseTree α) × List (RoseTree α)) :
    projSummand (p.1, .node a p.2) = ((projForest p).1, UnorderedTree.node a (projForest p).2) :=
  Prod.ext rfl (UnorderedTree.node_mk_tree_list a p.2).symm

/-- Combine two pairs of a crown and a remainder by adding componentwise. -/
def combinerProjG :
    (Multiset (UnorderedTree α) × Multiset (UnorderedTree α)) ×
    (Multiset (UnorderedTree α) × Multiset (UnorderedTree α)) →
    Multiset (UnorderedTree α) × Multiset (UnorderedTree α)
  | ((F1, m1), (F2, m2)) => (F1 + F2, m1 + m2)

private theorem projForest_combine
    (p q : Multiset (RoseTree α) × List (RoseTree α)) :
    projForest (p.1 + q.1, p.2 ++ q.2) = combinerProjG (projForest p, projForest q) := by
  simp [projForest, combinerProjG]

private theorem cutListSummandsG_cons_proj (t : RoseTree α) (ts : List (RoseTree α)) :
    (cutListSummandsG extract (t :: ts)).map projForest =
      ((augActionG extract t).map projForest ×ˢ
       (cutListSummandsG extract ts).map projForest).map combinerProjG := by
  rw [cutListSummandsG_cons]
  exact Multiset.map_map_product_distrib projForest_combine _ _

/-! ### Policies that descend to unordered trees -/

/-- A policy is invariant when the projection of what it leaves at a cut depends only on the
    unordered tree that is cut. -/
def ExtractInvariant (extract : RoseTree α → Option (List (RoseTree α))) : Prop :=
  ∀ t s : RoseTree α, UnorderedTree.mk t = UnorderedTree.mk s →
    (extract t).map (List.map (UnorderedTree.mk (α := α))) =
      (extract s).map (List.map (UnorderedTree.mk (α := α)))

variable {extract}

private theorem augActionG_proj_congr (hExt : ExtractInvariant extract) {t s : RoseTree α}
    (hmk : UnorderedTree.mk t = UnorderedTree.mk s)
    (h : (cutSummandsG extract t).map projSummand = (cutSummandsG extract s).map projSummand) :
    (augActionG extract t).map projForest = (augActionG extract s).map projForest := by
  rw [augActionG_eq, augActionG_eq, Multiset.map_add, Multiset.map_add]
  congr 1
  · have hE := hExt t s hmk
    cases ht : extract t <;> cases hs : extract s <;> simp_all [projForest]
  · have h' := congrArg (Multiset.map fun q : Multiset (UnorderedTree α) × UnorderedTree α ↦
      (q.1, ({q.2} : Multiset (UnorderedTree α)))) h
    simpa [Multiset.map_map, Function.comp_def, projForest, projSummand] using h'

/-- Combining three pairs is symmetric in the first two. -/
theorem combinerProjG_swap_args
    (a b c : Multiset (UnorderedTree α) × Multiset (UnorderedTree α)) :
    combinerProjG (a, combinerProjG (b, c)) = combinerProjG (b, combinerProjG (a, c)) := by
  obtain ⟨Fa, ma⟩ := a
  obtain ⟨Fb, mb⟩ := b
  obtain ⟨Fc, mc⟩ := c
  simp only [combinerProjG, add_left_comm]

/-- The combination of three multisets of pairs is symmetric in the first two. -/
theorem swap_double_combinerProjG
    (A B C : Multiset (Multiset (UnorderedTree α) × Multiset (UnorderedTree α))) :
    (A ×ˢ (B ×ˢ C).map combinerProjG).map combinerProjG =
      (B ×ˢ (A ×ˢ C).map combinerProjG).map combinerProjG := by
  have key (A B : Multiset (Multiset (UnorderedTree α) × Multiset (UnorderedTree α))) :
      (A ×ˢ (B ×ˢ C).map combinerProjG).map combinerProjG =
        A.bind fun a ↦ B.bind fun b ↦ C.map fun c ↦ combinerProjG (a, combinerProjG (b, c)) := by
    simp only [Multiset.product, Multiset.map_bind, Multiset.map_map, Function.comp_def,
      SProd.sprod]
  rw [key, key, Multiset.bind_bind]
  simp only [combinerProjG_swap_args]

private theorem cutListSummandsG_proj_perm (extract : RoseTree α → Option (List (RoseTree α)))
    {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    (cutListSummandsG extract cs).map projForest =
      (cutListSummandsG extract ds).map projForest := by
  induction h with
  | nil => rfl
  | cons c _ ih => rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj, ih]
  | swap c d cs =>
    simp only [cutListSummandsG_cons_proj]
    exact (swap_double_combinerProjG _ _ _).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

mutual
/-- For an invariant policy, the projected cuts of a tree depend only on the unordered tree. -/
theorem cutSummandsG_proj_perm (hExt : ExtractInvariant extract) :
    ∀ {t s : RoseTree α}, RoseTree.Perm t s →
      (cutSummandsG extract t).map projSummand = (cutSummandsG extract s).map projSummand
  | _, _, @RoseTree.Perm.node _ a cs ds h => by
    have hL := congrArg (Multiset.map fun pf : Multiset (UnorderedTree α) ×
      Multiset (UnorderedTree α) ↦ (pf.1, UnorderedTree.node a pf.2))
      (cutListSummandsG_proj_permList hExt h)
    simpa [Multiset.map_map, Function.comp_def, projSummand_node] using hL
  | _, _, .trans h₁ h₂ =>
    (cutSummandsG_proj_perm hExt h₁).trans (cutSummandsG_proj_perm hExt h₂)

private theorem cutListSummandsG_proj_permList (hExt : ExtractInvariant extract) :
    ∀ {cs ds : List (RoseTree α)}, RoseTree.PermList cs ds →
      (cutListSummandsG extract cs).map projForest = (cutListSummandsG extract ds).map projForest
  | _, _, .nil => rfl
  | _, _, @RoseTree.PermList.cons _ c d cs' ds' hcd hs => by
    rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj,
      augActionG_proj_congr hExt (UnorderedTree.mk_eq_mk_iff.mpr hcd)
        (cutSummandsG_proj_perm hExt hcd),
      cutListSummandsG_proj_permList hExt hs]
  | _, _, .swap c d cs => cutListSummandsG_proj_perm extract (List.Perm.swap c d cs)
  | _, _, .trans h₁ h₂ =>
    (cutListSummandsG_proj_permList hExt h₁).trans (cutListSummandsG_proj_permList hExt h₂)
end

variable (extract)

/-! ### Cut convolution

`treeCutsG cuts T` lists the cuts of the tree `T` as a forest, including the cut that takes all
of `T`, and `forestCutsG cuts F` combines them over the trees of a forest. The admissible-cut
coproduct is a sum over these (`comulForestNG_eq_sum` in `Coproduct/WithCuts.lean`). -/

/-- All the cuts of a tree with the trunk as a forest. They are the cut taking the whole tree,
    with crown `{T}` and empty trunk, and each cut in `cuts T` with a one-tree trunk. -/
def treeCutsG (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α))
    (T : UnorderedTree α) : Multiset (Multiset (UnorderedTree α) × Multiset (UnorderedTree α)) :=
  ({T}, 0) ::ₘ (cuts T).map fun p ↦ (p.1, {p.2})

instance instLeftCommConvCut : LeftCommutative
    (fun (s acc : Multiset (Multiset (UnorderedTree α) × Multiset (UnorderedTree α))) ↦
      (s ×ˢ acc).map combinerProjG) :=
  ⟨fun a b c ↦ swap_double_combinerProjG a b c⟩

/-- The cuts of a forest combine one choice from `treeCutsG cuts T` for each tree `T`. -/
def forestCutsG (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α))
    (F : Multiset (UnorderedTree α)) :
    Multiset (Multiset (UnorderedTree α) × Multiset (UnorderedTree α)) :=
  (F.map (treeCutsG cuts)).foldr (fun s acc ↦ (s ×ˢ acc).map combinerProjG) {(0, 0)}

theorem forestCutsG_zero
    (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α)) :
    forestCutsG cuts (0 : Multiset (UnorderedTree α)) = {(0, 0)} := by
  simp [forestCutsG]

theorem forestCutsG_cons
    (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α))
    (T : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    forestCutsG cuts (T ::ₘ F) =
      (treeCutsG cuts T ×ˢ forestCutsG cuts F).map combinerProjG := by
  rw [forestCutsG, Multiset.map_cons, Multiset.foldr_cons, forestCutsG]

/-! ### The empty cut -/

mutual

/-- The empty cut is the unique cut with empty crown. -/
theorem cutSummandsG_filter_empty :
    ∀ (T : RoseTree α),
      (cutSummandsG extract T).filter (fun p ↦ p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), T)} : Multiset _)
  | .node a cs => by
    rw [cutSummandsG_node, Multiset.filter_map]
    simp only [Function.comp_def]
    rw [cutListSummandsG_filter_empty cs, Multiset.map_singleton]

/-- The empty cut is the unique cut of a list of children with empty crown. -/
theorem cutListSummandsG_filter_empty :
    ∀ (cs : List (RoseTree α)),
      (cutListSummandsG extract cs).filter (fun p ↦ p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), cs)} : Multiset _)
  | [] => by simp
  | t :: ts => by
    rw [cutListSummandsG_cons, Multiset.filter_map,
      Multiset.filter_congr (q := fun x ↦ x.1.1.card = 0 ∧ x.2.1.card = 0) fun x _ ↦ by
        simp only [Function.comp_apply, Multiset.card_add, Nat.add_eq_zero_iff],
      Multiset.filter_product
        (fun x : Multiset (RoseTree α) × List (RoseTree α) ↦ x.1.card = 0)
        (fun x : Multiset (RoseTree α) × List (RoseTree α) ↦ x.1.card = 0),
      augActionG_filter_empty t, cutListSummandsG_filter_empty ts]
    rfl

/-- Keeping the child whole is the unique choice at a child with empty crown. -/
theorem augActionG_filter_empty :
    ∀ (t : RoseTree α),
      (augActionG extract t).filter (fun p ↦ p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), [t])} : Multiset _)
  | t => by
    have h : ((cutSummandsG extract t).map fun p ↦ (p.1, [p.2])).filter (fun p ↦ p.1.card = 0) =
        {((0 : Multiset (RoseTree α)), [t])} := by
      rw [Multiset.filter_map]
      simp only [Function.comp_def]
      rw [cutSummandsG_filter_empty t, Multiset.map_singleton]
    cases hx : extract t with
    | none => rw [augActionG_eq_none extract t hx, h]
    | some r =>
      rw [augActionG_eq_some extract t r hx, Multiset.filter_cons_of_neg _ (by simp), h]

end

/-! ### Pruning cuts

The policy that leaves nothing at a cut gives the admissible cuts of the Connes–Kreimer
coproduct. It is invariant, so its cuts descend to `UnorderedTree`, where the cuts of a node are
the cut convolution over its children. -/

/-- The pruning policy cuts anywhere and leaves nothing in place of the cut subtree. -/
def pruning : RoseTree α → Option (List (RoseTree α)) := fun _ ↦ some []

theorem extractInvariant_pruning : ExtractInvariant (pruning (α := α)) := fun _ _ _ ↦ rfl

/-- The pruning cuts of an unordered tree, as pairs of a crown and a trunk. -/
def cutSummandsN : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α) :=
  Quotient.lift (fun T ↦ (cutSummandsG pruning T).map projSummand)
    fun _ _ h ↦ cutSummandsG_proj_perm extractInvariant_pruning h

@[simp] theorem cutSummandsN_mk (T : RoseTree α) :
    cutSummandsN (UnorderedTree.mk T) = (cutSummandsG pruning T).map projSummand := rfl

/-- A leaf has only the empty cut. -/
theorem cutSummandsN_leaf (a : α) :
    cutSummandsN (UnorderedTree.leaf a : UnorderedTree α) =
      ({((0 : Multiset (UnorderedTree α)), UnorderedTree.leaf a)} : Multiset _) := by
  rw [UnorderedTree.leaf, RoseTree.leaf, cutSummandsN_mk, cutSummandsG_node, cutListSummandsG_nil]
  rfl

/-- The number of pruning cut summands of `T` whose crown is `{T₁}` and whose trunk is
    `T₂`. -/
def countSingleCutsRho [DecidableEq α] (T T₁ T₂ : UnorderedTree α) : ℕ :=
  (cutSummandsN T).countP fun p ↦ p.1 = ({T₁} : Multiset (UnorderedTree α)) ∧ p.2 = T₂

private theorem treeCutsG_cutSummandsN_mk (t : RoseTree α) :
    treeCutsG cutSummandsN (UnorderedTree.mk t) = (augActionG pruning t).map projForest := by
  rw [augActionG_eq_some pruning t [] rfl, Multiset.map_cons, treeCutsG, cutSummandsN_mk,
    Multiset.map_map, Multiset.map_map]
  rfl

private theorem forestCutsG_cutSummandsN_coe (ps : List (RoseTree α)) :
    forestCutsG cutSummandsN (Multiset.ofList (ps.map UnorderedTree.mk)) =
      (cutListSummandsG pruning ps).map projForest := by
  induction ps with
  | nil => rw [cutListSummandsG_nil, Multiset.map_singleton]; exact forestCutsG_zero _
  | cons p ps ih =>
    rw [List.map_cons, ← Multiset.cons_coe, forestCutsG_cons, ih, treeCutsG_cutSummandsN_mk,
      cutListSummandsG_cons_proj]

/-- The pruning cuts of a node choose, for each child, to cut it whole or to cut inside it. -/
@[simp] theorem cutSummandsN_node (a : α) (F : Multiset (UnorderedTree α)) :
    cutSummandsN (UnorderedTree.node a F) =
      (forestCutsG cutSummandsN F).map fun pf ↦ (pf.1, UnorderedTree.node a pf.2) := by
  induction F using UnorderedTree.forest_inductionOn with
  | h ps =>
    rw [forestCutsG_cutSummandsN_coe, UnorderedTree.node_mk_tree_list, cutSummandsN_mk,
      cutSummandsG_node, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun p _ ↦ projSummand_node a p

/-- The empty cut is the unique pruning cut with empty crown. -/
theorem cutSummandsN_filter_empty (T : UnorderedTree α) :
    (cutSummandsN T).filter (fun p ↦ p.1.card = 0) = {((0 : Multiset (UnorderedTree α)), T)} :=
  Quotient.inductionOn T fun t ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsN_mk, Multiset.filter_map]
    simp only [Function.comp_def, projSummand, Multiset.card_map]
    rw [cutSummandsG_filter_empty pruning t, Multiset.map_singleton]
    rfl

end ConnesKreimer
