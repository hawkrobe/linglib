import Linglib.Core.Algebra.RootedTree.Coproduct.PruningDuality
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.Convolution

set_option autoImplicit false

/-!
# `HopfAlgebra R (ConnesKreimer R (Nonplanar α))` — Foissy Connes-Kreimer Hopf algebra
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

Completes Phase A.7 by upgrading the `Bialgebra` instance from
`CoproductNonplanar.lean` to a full `HopfAlgebra` instance via the recursive
Foissy / MCB eq. (1.2.12) antipode:

  S(x) = -x - Σᵢ S(x'ᵢ) · x''ᵢ   (for x of positive weight; reduced coproduct)
  S(1) = 1

Equivalently, summing over ALL cut summands (including the empty cut `(0, T)`,
which contributes `ofTree T`):

  S(T) = -Σ_{(cf, rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} S(ofTree Tᵢ)) · ofTree rem

Foissy's coassoc closure (in `CoproductNonplanar.lean`) plus this antipode
construction realize MCB Lemma 1.2.11 (book p. 38): the n-ary Connes–Kreimer
Hopf algebra of nonplanar rooted trees. Requires `CommRing R` (the antipode
formula uses negation; the `Bialgebra` instance only needs `CommSemiring`).

## Status

`[UPSTREAM]` candidate. Sorry-free. The full `HopfAlgebra R (ConnesKreimer R
(Nonplanar α))` instance is now realized via the right-antipode +
`WithConv.left_inv_eq_right_inv` route — the Sweedler/Kassel argument that
mathlib uses internally for `IsGroupLikeElem` but does not yet expose as a
generic constructor. Mathlib has no generic graded-connected bialgebra → Hopf
algebra construction (its `HopfAlgebra/Basic.lean` lists this as TODO); this
file is a candidate factoring of Foissy's specific recursion.

## Architecture

- **Auxiliary depth lemma** (`cutSummandsN_subtree_depth_lt`): every tree
  appearing in a cut forest of `T` has strictly smaller depth than `T`.
  Lifted from a tree-level mutual structural-induction proof.
- **Auxiliary weight lemma** (`cutSummandsN_rem_numNodes_lt`): for nontrivial
  cuts, the remainder has strictly smaller weight than the source. Substrate
  for the `weight`-recursive right antipode.
- **Multiplicity-1 uniqueness** (`cutSummandsN_filter_card_zero`): the empty
  cut `(0, T)` appears with multiplicity exactly 1. Mutual tree-level structural
  induction (with auxiliary `cutListSummandsP` version) plus a
  `multiset_filter_product` helper. Substrate for the right-antipode
  cancellation.
- **Antipode on a tree** (`antipodeTreeN`): well-founded recursion on
  `Nonplanar.depth`, using the closed form
  `S(T) = -Σ over cutSummandsN T of (Π S(Tᵢ)) · ofTree rem`.
- **Right antipode** (`antipodeRightTreeN`): well-founded recursion on
  `Nonplanar.numNodes`, using the dual form `R(T) = -ofTree T - Σ_{cf ≠ 0}
  of'(cf) · R(rem)`. The lTensor cancellation falls out of `_unfold` plus
  `cutSummandsN_filter_card_zero`.
- **Antipodes as AlgHoms** (`antipodeAlgHomN`, `antipodeRightAlgHomN`):
  multiplicative extension to forests via `AddMonoidAlgebra.lift`. H is
  commutative, so both are algebra homs (not just anti-multiplicative).
- **rTensor axiom** proved by single-step `antipodeTreeN_unfold` cancellation
  on trees + Multiset induction on forests.
- **lTensor axiom** proved by deriving `R = antipodeRightAlgHomN` satisfies
  it directly (uniqueness + `_unfold`), then using
  `WithConv.left_inv_eq_right_inv` to conclude `S = R` as algebra homs.
- **`HopfAlgebra` instance** assembled via `HopfAlgebra.ofAlgHom`.

-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommRing R] {α : Type*}

/-- `ConnesKreimer R T` inherits the `CommRing` structure from
    `AddMonoidAlgebra R (Forest T)` when `R` is a commutative ring. The
    `Bialgebra` substrate only needed `CommSemiring`; the antipode formula
    needs negation, hence `CommRing`. -/
noncomputable instance : CommRing (ConnesKreimer R (Nonplanar α)) :=
  inferInstanceAs (CommRing (AddMonoidAlgebra R (Forest (Nonplanar α))))

/-! ## §1: Subtree depth bound on cut summands

Substrate for the well-founded antipode definition. The depth of any tree
appearing in a cut forest of `T` is strictly less than `T.depth`. Proved
mutually on the tree-level substrate, then descended via the tree-level
representation. -/

/-! ### RoseTree mutual induction -/

mutual

/-- For any `(cf, rem) ∈ cutSummandsP T`, every tree `T_i ∈ cf` has depth
    bounded by `T.depth`. Mutual with `cutListSummandsP_subtree_depth_le`. -/
private theorem cutSummandsP_subtree_depth_le :
    ∀ (T : RoseTree α) (cf : Forest (RoseTree α)) (rem : RoseTree α),
      (cf, rem) ∈ cutSummandsP T → ∀ T_i ∈ cf, T_i.depth ≤ T.depth
  | .node a children, cf, rem, h_mem, T_i, h_T_i => by
    rw [cutSummandsP_node, Multiset.mem_map] at h_mem
    obtain ⟨⟨cf', rem'⟩, h_mem', h_eq⟩ := h_mem
    -- h_eq : (cf', .node a rem') = (cf, rem). Extract first component via congrArg.
    have h_cf : cf' = cf := congrArg Prod.fst h_eq
    rw [← h_cf] at h_T_i
    -- (cf', rem') ∈ cutListSummandsP children, T_i ∈ cf'.
    have hbd : T_i.depth ≤ (children.map RoseTree.depth).foldr max 0 :=
      cutListSummandsP_subtree_depth_le children cf' rem' h_mem' T_i h_T_i
    rw [RoseTree.depth_node]
    omega

/-- For any `(cf, rem_list) ∈ cutListSummandsP cs`, every tree `T_i ∈ cf`
    has depth bounded by the children's max depth. Mutual with
    `cutSummandsP_subtree_depth_le`. -/
private theorem cutListSummandsP_subtree_depth_le :
    ∀ (cs : List (RoseTree α)) (cf : Forest (RoseTree α)) (rem_list : List (RoseTree α)),
      (cf, rem_list) ∈ cutListSummandsP cs → ∀ T_i ∈ cf,
        T_i.depth ≤ (cs.map RoseTree.depth).foldr max 0
  | [], cf, rem_list, h_mem, T_i, h_T_i => by
    rw [cutListSummandsP_nil, Multiset.mem_singleton] at h_mem
    -- h_mem : (cf, rem_list) = (0, [])
    have h_cf : cf = 0 := congrArg Prod.fst h_mem
    rw [h_cf] at h_T_i
    exact absurd h_T_i (Multiset.notMem_zero _)
  | c :: cs', cf, rem_list, h_mem, T_i, h_T_i => by
    rw [cutListSummandsP_cons, Multiset.mem_map] at h_mem
    obtain ⟨⟨⟨aug_F, aug_opt⟩, cf_cs', rem_cs'⟩, h_pair, h_eq⟩ := h_mem
    rw [Multiset.mem_product] at h_pair
    obtain ⟨h_aug, h_cf_cs'⟩ := h_pair
    -- Compute cf from the lambda: cf = aug_F + cf_cs' (in either branch).
    have h_cf_eq : cf = aug_F + cf_cs' := by
      cases aug_opt
      · -- none branch: lambda gives (aug_F + cf_cs', rem_cs')
        exact (congrArg Prod.fst h_eq).symm
      · -- some r branch: lambda gives (aug_F + cf_cs', r :: rem_cs')
        exact (congrArg Prod.fst h_eq).symm
    rw [h_cf_eq, Multiset.mem_add] at h_T_i
    -- T_i ∈ aug_F or T_i ∈ cf_cs'.
    show T_i.depth ≤ max c.depth ((cs'.map RoseTree.depth).foldr max 0)
    rcases h_T_i with h_in_aug | h_in_cf_cs'
    · -- T_i ∈ aug_F. Either aug_F = {c} (extract whole) or aug_F = s.1 for s ∈ cutSummandsP c.
      rw [augActionP_eq, Multiset.mem_cons] at h_aug
      rcases h_aug with h_aug | h_aug
      · -- aug = ({c}, none), so aug_F = {c}. T_i = c.
        have h_aug_F : aug_F = {c} := congrArg Prod.fst h_aug
        rw [h_aug_F, Multiset.mem_singleton] at h_in_aug
        rw [h_in_aug]
        exact le_max_left _ _
      · -- aug = (s.1, some s.2) for s ∈ cutSummandsP c. aug_F = s.1.
        rw [Multiset.mem_map] at h_aug
        obtain ⟨s, h_s_mem, h_s_eq⟩ := h_aug
        have h_aug_F : s.1 = aug_F := congrArg Prod.fst h_s_eq
        rw [← h_aug_F] at h_in_aug
        -- T_i ∈ s.1 where (s.1, s.2) ∈ cutSummandsP c. Use IH on c.
        have := cutSummandsP_subtree_depth_le c s.1 s.2 h_s_mem T_i h_in_aug
        exact this.trans (le_max_left _ _)
    · -- T_i ∈ cf_cs'. By IH on cs'.
      have := cutListSummandsP_subtree_depth_le cs' cf_cs' rem_cs' h_cf_cs' T_i h_in_cf_cs'
      exact this.trans (le_max_right _ _)

end

/-! ### Nonplanar version (descent via tree-level rep) -/

/-- For any `(cf, rem) ∈ cutSummandsN T` (any tree `T : Nonplanar α`), every
    tree `T_i ∈ cf` has strictly smaller depth than `T`. The strict bound
    comes from the fact that `cf`'s trees are subtrees of children of `T`
    (whose depth is `T.depth - 1`), and via the empty-cut term `(0, T)`'s
    `cf = 0` (no `T_i` to consider). -/
theorem cutSummandsN_subtree_depth_lt (T : Nonplanar α)
    (cf : Forest (Nonplanar α)) (rem : Nonplanar α)
    (h_mem : (cf, rem) ∈ cutSummandsN T)
    (T_i : Nonplanar α) (h_T_i : T_i ∈ cf) : T_i.depth < T.depth := by
  -- Pick a tree-level rep T = mk T₀.
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
    ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
  rw [cutSummandsN_mk, Multiset.mem_map] at h_mem
  obtain ⟨⟨cf_p, rem_p⟩, h_mem_p, h_proj⟩ := h_mem
  -- h_proj : projSummand ⟨cf_p, rem_p⟩ = (cf, rem) reduces to (cf_p.map mk, mk rem_p) = (cf, rem).
  -- Extract first component via congrArg.
  have h_cf : cf_p.map Nonplanar.mk = cf := congrArg Prod.fst h_proj
  show T_i.depth < (Nonplanar.mk T₀).depth
  rw [Nonplanar.depth_mk]
  rw [← h_cf, Multiset.mem_map] at h_T_i
  obtain ⟨T_i_p, h_T_i_p_mem, rfl⟩ := h_T_i
  show (Nonplanar.mk T_i_p).depth < T₀.depth
  rw [Nonplanar.depth_mk]
  -- Use tree-level lemma: T_i_p.depth ≤ T₀.depth - 1.
  -- Strategy: T₀ = .node a children for some a, children. cf_p ∈ cutListSummandsP children.
  -- T_i_p ∈ cf_p means T_i_p.depth ≤ (children's max depth) = T₀.depth - 1.
  match T₀, h_mem_p with
  | .node a children, h_mem_p =>
    rw [cutSummandsP_node, Multiset.mem_map] at h_mem_p
    obtain ⟨⟨cf_p', rem_p'⟩, h_mem_p', h_eq⟩ := h_mem_p
    have h_cf_eq : cf_p' = cf_p := congrArg Prod.fst h_eq
    rw [← h_cf_eq] at h_T_i_p_mem
    have hbd : T_i_p.depth ≤ (children.map RoseTree.depth).foldr max 0 :=
      cutListSummandsP_subtree_depth_le children cf_p' rem_p' h_mem_p' T_i_p h_T_i_p_mem
    show T_i_p.depth < (RoseTree.node a children).depth
    rw [RoseTree.depth_node]
    omega

/-! ### Weight conservation (vertex count) for cuts

Δ^ρ (the deletion variant) preserves total vertex count: for every cut
`(cf, rem)` of `T`, the cut forest's total weight plus the remainder's
weight equals `T`'s weight. Substrate for the lTensor sorry closure: the
"right antipode" `antipodeRight` recurses on `rem` (weight strictly
decreases for nontrivial cuts), in contrast to the standard antipode
which recurses on `cf` (depth strictly decreases). -/

mutual

/-- Vertex conservation for cuts of tree-level trees: `cf.weight_sum + rem.numNodes = T.numNodes`. -/
private theorem cutSummandsP_numNodes_eq :
    ∀ (T : RoseTree α) (cf : Forest (RoseTree α)) (rem : RoseTree α),
      (cf, rem) ∈ cutSummandsP T → (cf.map RoseTree.numNodes).sum + rem.numNodes = T.numNodes
  | .node a children, cf, rem, h_mem => by
    rw [cutSummandsP_node, Multiset.mem_map] at h_mem
    obtain ⟨⟨cf', rem'⟩, h_mem', h_eq⟩ := h_mem
    have h_cf : cf' = cf := congrArg Prod.fst h_eq
    have h_rem : (RoseTree.node a rem' : RoseTree α) = rem := congrArg Prod.snd h_eq
    rw [← h_cf, ← h_rem]
    -- (cf', rem') ∈ cutListSummandsP children, weight conservation by IH.
    have hc := cutListSummandsP_numNodes_eq children cf' rem' h_mem'
    rw [RoseTree.numNodes_node, RoseTree.numNodes_node]
    omega

/-- Vertex conservation for cuts of tree-level lists. -/
private theorem cutListSummandsP_numNodes_eq :
    ∀ (cs : List (RoseTree α)) (cf : Forest (RoseTree α)) (rem_list : List (RoseTree α)),
      (cf, rem_list) ∈ cutListSummandsP cs →
        (cf.map RoseTree.numNodes).sum + (rem_list.map RoseTree.numNodes).sum =
          (cs.map RoseTree.numNodes).sum
  | [], cf, rem_list, h_mem => by
    rw [cutListSummandsP_nil, Multiset.mem_singleton] at h_mem
    have h_cf : cf = 0 := congrArg Prod.fst h_mem
    have h_rem : rem_list = [] := congrArg Prod.snd h_mem
    rw [h_cf, h_rem]
    simp
  | c :: cs', cf, rem_list, h_mem => by
    rw [cutListSummandsP_cons, Multiset.mem_map] at h_mem
    obtain ⟨⟨⟨aug_F, aug_opt⟩, cf_cs', rem_cs'⟩, h_pair, h_eq⟩ := h_mem
    rw [Multiset.mem_product] at h_pair
    obtain ⟨h_aug, h_cf_cs'⟩ := h_pair
    -- Both cases (aug_opt = none or some r): cf = aug_F + cf_cs'.
    have h_cf_eq : cf = aug_F + cf_cs' := by
      cases aug_opt
      · exact (congrArg Prod.fst h_eq).symm
      · exact (congrArg Prod.fst h_eq).symm
    -- For the rem_list:
    -- - none case: rem_list = rem_cs'.
    -- - some r case: rem_list = r :: rem_cs', where r = "the recurse-into-cut remainder for c".
    -- We need to handle both branches.
    -- Conservation on aug_F: weight of aug_F = c.numNodes (extract whole) or = c.numNodes - r.numNodes
    --                                          (recurse, conservation on cutSummandsP c).
    rw [h_cf_eq, Multiset.map_add, Multiset.sum_add]
    -- Goal: (aug_F.map weight).sum + (cf_cs'.map weight).sum + (rem_list.map weight).sum
    --     = ((c :: cs').map weight).sum
    show (aug_F.map RoseTree.numNodes).sum + (cf_cs'.map RoseTree.numNodes).sum +
           (rem_list.map RoseTree.numNodes).sum
       = ((c :: cs').map RoseTree.numNodes).sum
    rw [List.map_cons, List.sum_cons]
    -- Goal: ... = c.numNodes + (cs'.map RoseTree.numNodes).sum
    -- IH on cs': (cf_cs'.map weight).sum + (rem_cs'.map weight).sum = (cs'.map weight).sum.
    have ih_cs' := cutListSummandsP_numNodes_eq cs' cf_cs' rem_cs' h_cf_cs'
    rw [augActionP_eq, Multiset.mem_cons] at h_aug
    rcases h_aug with h_aug | h_aug
    · -- aug = ({c}, none). aug_F = {c}, aug_opt = none, rem_list = rem_cs'.
      have h_aug_F : aug_F = {c} := congrArg Prod.fst h_aug
      have h_aug_opt : aug_opt = Option.none := congrArg Prod.snd h_aug
      -- rem_list = rem_cs' since aug_opt = none.
      have h_rem_list : rem_list = rem_cs' := by
        rw [h_aug_opt] at h_eq
        exact (congrArg Prod.snd h_eq).symm
      rw [h_aug_F, h_rem_list]
      simp
      omega
    · -- aug = (s.1, some s.2) for s ∈ cutSummandsP c. aug_F = s.1, aug_opt = some s.2,
      -- rem_list = s.2 :: rem_cs'.
      rw [Multiset.mem_map] at h_aug
      obtain ⟨s, h_s_mem, h_s_eq⟩ := h_aug
      have h_aug_F : s.1 = aug_F := congrArg Prod.fst h_s_eq
      have h_aug_opt : Option.some s.2 = aug_opt := congrArg Prod.snd h_s_eq
      have h_rem_list : rem_list = s.2 :: rem_cs' := by
        rw [← h_aug_opt] at h_eq
        exact (congrArg Prod.snd h_eq).symm
      rw [← h_aug_F, h_rem_list]
      -- IH on cutSummandsP c: (s.1.map weight).sum + s.2.numNodes = c.numNodes.
      have ih_c := cutSummandsP_numNodes_eq c s.1 s.2 h_s_mem
      simp [List.map_cons, List.sum_cons]
      omega

end

/-- For nontrivial cuts (cf nonempty), the remainder has strictly smaller
    weight than the source tree. Substrate for the right-antipode
    well-founded recursion. -/
private theorem cutSummandsN_rem_numNodes_lt (T : Nonplanar α)
    (cf : Forest (Nonplanar α)) (rem : Nonplanar α)
    (h_mem : (cf, rem) ∈ cutSummandsN T) (h_nonempty : cf ≠ 0) :
    rem.numNodes < T.numNodes := by
  -- Pick a tree-level rep T = mk T₀.
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
    ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
  rw [cutSummandsN_mk, Multiset.mem_map] at h_mem
  obtain ⟨⟨cf_p, rem_p⟩, h_mem_p, h_proj⟩ := h_mem
  -- h_proj : projSummand (cf_p, rem_p) = (cf, rem), i.e., (cf_p.map mk, mk rem_p) = (cf, rem).
  have h_cf : cf_p.map Nonplanar.mk = cf := congrArg Prod.fst h_proj
  have h_rem : Nonplanar.mk rem_p = rem := congrArg Prod.snd h_proj
  show rem.numNodes < (Nonplanar.mk T₀).numNodes
  rw [Nonplanar.numNodes_mk, ← h_rem, Nonplanar.numNodes_mk]
  -- Goal: rem_p.numNodes < T₀.numNodes.
  -- Use tree-level conservation: cf_p.numNodes + rem_p.numNodes = T₀.numNodes (where cf_p.numNodes = sum).
  have h_eq := cutSummandsP_numNodes_eq T₀ cf_p rem_p h_mem_p
  -- Need cf_p ≠ 0 (from cf ≠ 0, since cf = cf_p.map mk).
  have h_cf_p_ne : cf_p ≠ 0 := by
    intro h_zero
    apply h_nonempty
    rw [← h_cf, h_zero, Multiset.map_zero]
  -- Total weight of cf_p ≥ |cf_p| ≥ 1 (each tree has weight ≥ 1).
  have h_cf_pos : (cf_p.map RoseTree.numNodes).sum ≥ 1 := by
    obtain ⟨T_i, h_T_i⟩ := Multiset.exists_mem_of_ne_zero h_cf_p_ne
    have h_T_i_pos : T_i.numNodes ≥ 1 := RoseTree.numNodes_pos T_i
    -- (cf_p.map weight).sum ≥ T_i.numNodes (since T_i ∈ cf_p)
    have h_in_s : T_i.numNodes ∈ cf_p.map RoseTree.numNodes :=
      Multiset.mem_map_of_mem _ h_T_i
    have h_le : T_i.numNodes ≤ (cf_p.map RoseTree.numNodes).sum :=
      Multiset.single_le_sum (s := cf_p.map RoseTree.numNodes)
        (fun _ _ => Nat.zero_le _) T_i.numNodes h_in_s
    omega
  omega

/-! ## §1.6: Multiplicity-1 uniqueness for the empty cut

Substrate for the lTensor closure (§6 below). The empty cut `(0, T)`
appears with multiplicity exactly 1 in `cutSummandsN T` (and in `cutSummandsP T₀`
for any tree-level rep). This is the combinatorial fact that the right antipode
recursion needs to cancel cleanly. -/

/-- Helper: filtering a Multiset cartesian product by a conjunctive predicate
    factors into per-coordinate filtering. Mathlib has `Finset.filter_product`
    but no Multiset version (only the decidable-Finset variant in
    `Mathlib/Data/Finset/Prod.lean`). -/
private lemma multiset_filter_product
    {β γ : Type*} (q : β → Prop) (r : γ → Prop)
    [DecidablePred q] [DecidablePred r]
    (s : Multiset β) (t : Multiset γ) :
    (s ×ˢ t).filter (fun (x : β × γ) => q x.1 ∧ r x.2) = s.filter q ×ˢ t.filter r := by
  induction s using Multiset.induction with
  | empty => rfl
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.filter_add, ih, Multiset.filter_map]
    by_cases hq : q a
    · rw [Multiset.filter_cons_of_pos _ hq, Multiset.cons_product]
      congr 1
      apply congr_arg (Multiset.map (Prod.mk a))
      apply Multiset.filter_congr
      intros b _
      simp [hq]
    · rw [Multiset.filter_cons_of_neg _ hq]
      have h_filt : Multiset.filter
          ((fun (x : β × γ) => q x.1 ∧ r x.2) ∘ Prod.mk a) t = 0 := by
        apply Multiset.filter_eq_nil.mpr
        intros b _ h
        exact hq h.1
      rw [h_filt, Multiset.map_zero, Multiset.zero_add]

mutual

/-- The empty cut `(0, T)` appears with multiplicity exactly 1 in
    `cutSummandsP T`. Mutual structural induction with the list version. -/
private lemma cutSummandsP_filter_card_zero :
    ∀ (T : RoseTree α),
      (cutSummandsP T).filter (fun pf => pf.1.card = 0) = {(0, T)}
  | .node a children => by
    rw [cutSummandsP_node, Multiset.filter_map]
    -- Beta-reduce the composed predicate to (fun p => p.1.card = 0).
    simp only [Function.comp_def]
    rw [cutListSummandsP_filter_card_zero children, Multiset.map_singleton]

/-- The empty cut `(0, [])` appears with multiplicity exactly 1 in
    `cutListSummandsP cs`. Mutual with `cutSummandsP_filter_card_zero`. -/
private lemma cutListSummandsP_filter_card_zero :
    ∀ (cs : List (RoseTree α)),
      (cutListSummandsP cs).filter (fun pf => pf.1.card = 0) = {(0, cs)}
  | [] => by
    rw [cutListSummandsP_nil, Multiset.filter_singleton]
    rw [if_pos (by simp : ((0, ([] : List (RoseTree α))) :
      Forest (RoseTree α) × List (RoseTree α)).1.card = 0)]
  | c :: cs' => by
    rw [cutListSummandsP_cons, Multiset.filter_map]
    -- The filter has predicate ((·.1.card = 0) ∘ (match-on-aug-opt)). We'll convert
    -- it to the conjunctive form `p.1.1.card = 0 ∧ p.2.1.card = 0` via filter_congr,
    -- then apply filter_product. Use congrArg to lift through the Multiset.map.
    apply Eq.trans (b := Multiset.map _ ({((0, some c), (0, cs'))} :
      Multiset ((Forest (RoseTree α) × Option (RoseTree α)) ×
                Forest (RoseTree α) × List (RoseTree α))))
    · apply congrArg
      refine Eq.trans (Multiset.filter_congr (q := fun
        (p : (Forest (RoseTree α) × Option (RoseTree α)) ×
              Forest (RoseTree α) × List (RoseTree α)) =>
        p.1.1.card = 0 ∧ p.2.1.card = 0) (fun p _ => ?_)) ?_
      · -- Per-element iff: (((·.1.card = 0) ∘ match) p) ↔ (p.1.1.card = 0 ∧ p.2.1.card = 0)
        cases h : p.1.2 with
        | none => simp [Function.comp, h, Multiset.card_add]
        | some r => simp [Function.comp, h, Multiset.card_add]
      · -- Now filter the product by the conjunctive predicate; apply filter_product.
        rw [multiset_filter_product
              (fun (pf : Forest (RoseTree α) × Option (RoseTree α)) => pf.1.card = 0)
              (fun (pf : Forest (RoseTree α) × List (RoseTree α)) => pf.1.card = 0)]
        -- For augActionP filter, factor through cutSummandsP_filter_card_zero c (mutual call).
        have h_aug : (augActionP c).filter (fun pf => pf.1.card = 0) = {(0, some c)} := by
          rw [augActionP_eq, Multiset.filter_cons]
          rw [if_neg (by simp : ¬({c} : Forest (RoseTree α)).card = 0)]
          rw [Multiset.zero_add, Multiset.filter_map]
          refine Eq.trans (congrArg (Multiset.map _) (Multiset.filter_congr
            (q := fun (s : Forest (RoseTree α) × RoseTree α) => s.1.card = 0)
            (fun s _ => Iff.rfl))) ?_
          rw [cutSummandsP_filter_card_zero c, Multiset.map_singleton]
        rw [h_aug, cutListSummandsP_filter_card_zero cs', Multiset.product_singleton]
    · -- Now: Multiset.map (match-lambda) {((0, some c), (0, cs'))} = {(0, c :: cs')}
      -- Apply the lambda: (some c) branch ⟹ (0 + 0, c :: cs') = (0, c :: cs').
      rw [Multiset.map_singleton]
      rfl

end

/-- The empty cut `(0, T)` appears with multiplicity exactly 1 in
    `cutSummandsN T`. Descent from the tree-level uniqueness lemma. Public: consumed
    by `Minimalist.Merge.mergeOp_factor_out_singleton` to isolate the surviving
    empty-cut summand. -/
lemma cutSummandsN_filter_card_zero (T : Nonplanar α) :
    (cutSummandsN T).filter (fun pf => pf.1.card = 0) = {(0, T)} := by
  -- Pick a tree-level rep T = mk T₀.
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
    ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
  rw [cutSummandsN_mk, Multiset.filter_map]
  -- Beta-reduce composed predicate: (·.1.card = 0) ∘ projSummand
  -- projSummand pf = (pf.1.map mk, mk pf.2), and (pf.1.map mk).card = pf.1.card by card_map.
  simp only [Function.comp_def, projSummand, Multiset.card_map]
  rw [cutSummandsP_filter_card_zero T₀, Multiset.map_singleton]
  rfl

/-! ## §2: Antipode definition

Recursive on tree depth via Lean's well-founded recursion. The closed form

  S(T) = -Σ_{(cf, rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} S(Tᵢ)) · ofTree rem

includes the empty cut `(0, T)` (contributing `1 · ofTree T = ofTree T`) so
that the negation cleanly gives `-ofTree T - Σ_{nontrivial} ...`. The
recursive call on `Tᵢ ∈ cf` is well-founded by `cutSummandsN_subtree_depth_lt`. -/

set_option linter.unusedVariables false in
/-- The **antipode on a single nonplanar tree**, via Foissy's recursive
    formula summing over all cut summands. The membership proofs `h_mem`
    and `h_T_i` (warned-unused by the linter inside the lambda body) are
    consumed by `decreasing_by` to discharge the well-foundedness obligation. -/
noncomputable def antipodeTreeN (T : Nonplanar α) : ConnesKreimer R (Nonplanar α) :=
  - ((cutSummandsN T).attach.map (fun ⟨pf, h_mem⟩ =>
      (pf.1.attach.map (fun ⟨T_i, h_T_i⟩ =>
        antipodeTreeN T_i)).prod * ofTree pf.2)).sum
termination_by T.depth
decreasing_by
  exact cutSummandsN_subtree_depth_lt T pf.1 pf.2 h_mem T_i h_T_i

/-! ### Multiplicative extension to forests -/

/-- The **forest-level antipode**: multiplicative extension of `antipodeTreeN`
    to forests. Packaged as a `MonoidHom` to enable lifting via
    `AddMonoidAlgebra.lift`. -/
noncomputable def antipodeMonoidHomN :
    Multiplicative (Forest (Nonplanar α)) →* ConnesKreimer R (Nonplanar α) where
  toFun F := (F.toAdd.map (antipodeTreeN (R := R))).prod
  map_one' := by
    show (((1 : Multiplicative (Forest (Nonplanar α))).toAdd).map _).prod = 1
    show ((0 : Forest (Nonplanar α)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F * G).toAdd.map (antipodeTreeN (R := R))).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    show ((F.toAdd + G.toAdd).map (antipodeTreeN (R := R))).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- The **antipode as an algebra hom** `S : H →ₐ[R] H`. Since `H` is
    commutative, the antipode is a (not anti-)algebra hom. -/
noncomputable def antipodeAlgHomN :
    ConnesKreimer R (Nonplanar α) →ₐ[R] ConnesKreimer R (Nonplanar α) :=
  AddMonoidAlgebra.lift R (ConnesKreimer R (Nonplanar α)) (Forest (Nonplanar α))
    antipodeMonoidHomN

/-! ### Right antipode (lTensor recursion)

To close the lTensor antipode axiom (which our standard antipode `antipodeTreeN`
satisfies but for which the axiom isn't directly visible from the definition),
we construct an auxiliary "right antipode" `antipodeRightTreeN` that satisfies
the lTensor axiom by definition. The two coincide as elements of `H` by
the monoid `left_inv_eq_right_inv` argument in the convolution algebra
`WithConv (H →ₗ[R] H)`. See §5 below.

The right antipode recurses on `rem` (which has strictly smaller weight for
nontrivial cuts, by `cutSummandsN_rem_numNodes_lt`) instead of on `cf`. -/

set_option linter.unusedVariables false in
/-- The **right antipode on a single nonplanar tree**: defined to satisfy the
    lTensor axiom by direct cancellation. Recurses on `rem` for nontrivial
    cuts (well-founded by `cutSummandsN_rem_numNodes_lt`). -/
noncomputable def antipodeRightTreeN (T : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) :=
  -ofTree T - ((cutSummandsN T).attach.map (fun ⟨pf, h_mem⟩ =>
    if h_card : pf.1.card ≠ 0 then
      of' pf.1 * antipodeRightTreeN pf.2
    else 0)).sum
termination_by T.numNodes
decreasing_by
  apply cutSummandsN_rem_numNodes_lt T pf.1 pf.2 h_mem
  rwa [ne_eq, ← Multiset.card_eq_zero]

/-! ### Multiplicative extension to forests for R -/

/-- The **forest-level right antipode**: multiplicative extension. -/
noncomputable def antipodeRightMonoidHomN :
    Multiplicative (Forest (Nonplanar α)) →* ConnesKreimer R (Nonplanar α) where
  toFun F := (F.toAdd.map (antipodeRightTreeN (R := R))).prod
  map_one' := by
    show ((0 : Forest (Nonplanar α)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F.toAdd + G.toAdd).map (antipodeRightTreeN (R := R))).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- The **right antipode as an algebra hom** `R : H →ₐ[R] H`. -/
noncomputable def antipodeRightAlgHomN :
    ConnesKreimer R (Nonplanar α) →ₐ[R] ConnesKreimer R (Nonplanar α) :=
  AddMonoidAlgebra.lift R (ConnesKreimer R (Nonplanar α)) (Forest (Nonplanar α))
    antipodeRightMonoidHomN

@[simp] theorem antipodeRightAlgHomN_apply_of' (F : Forest (Nonplanar α)) :
    antipodeRightAlgHomN (R := R) (of' F) =
      (F.map (antipodeRightTreeN (R := R))).prod := by
  show AddMonoidAlgebra.lift R _ _ antipodeRightMonoidHomN (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem antipodeRightAlgHomN_apply_ofTree (T : Nonplanar α) :
    antipodeRightAlgHomN (R := R) (ofTree T) = antipodeRightTreeN T := by
  unfold ofTree
  rw [antipodeRightAlgHomN_apply_of', Multiset.map_singleton, Multiset.prod_singleton]

@[simp] theorem antipodeAlgHomN_apply_of' (F : Forest (Nonplanar α)) :
    antipodeAlgHomN (R := R) (of' F) = (F.map (antipodeTreeN (R := R))).prod := by
  show AddMonoidAlgebra.lift R _ _ antipodeMonoidHomN (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem antipodeAlgHomN_apply_ofTree (T : Nonplanar α) :
    antipodeAlgHomN (R := R) (ofTree T) = antipodeTreeN T := by
  unfold ofTree
  rw [antipodeAlgHomN_apply_of', Multiset.map_singleton, Multiset.prod_singleton]

/-- The recursive lTensor equation for the right antipode, in non-`attach`-decorated
    form. Mirrors `antipodeTreeN_unfold` but for the lTensor recursion. -/
theorem antipodeRightTreeN_unfold (T : Nonplanar α) :
    antipodeRightTreeN (R := R) T = -ofTree T - ((cutSummandsN T).map
      (fun pf => if pf.1.card ≠ 0 then of' pf.1 * antipodeRightTreeN pf.2
                 else (0 : ConnesKreimer R (Nonplanar α)))).sum := by
  conv_lhs => rw [antipodeRightTreeN]
  -- Body: -ofTree T - ((cutSummandsN T).attach.map (fun ⟨pf, h_mem⟩ =>
  --   if h_card : pf.1.card ≠ 0 then of' pf.1 * antipodeRightTreeN pf.2 else 0)).sum
  -- The match-pattern lambda is defeq to (fun pf : Subtype => dite ... pf.val.1 ...).
  -- The dite body doesn't use h_card, so it's defeq to an ite.
  -- Use `show` to restate LHS lambda in attach_map_val'-friendly form.
  show -ofTree T - ((cutSummandsN T).attach.map
        (fun (pf : { x // x ∈ cutSummandsN T }) =>
          if pf.val.1.card ≠ 0 then
            of' pf.val.1 * antipodeRightTreeN pf.val.2
          else (0 : ConnesKreimer R (Nonplanar α)))).sum = _
  congr 1
  exact congrArg Multiset.sum (@Multiset.attach_map_val'
    (Forest (Nonplanar α) × Nonplanar α) _ (cutSummandsN T)
    (fun pf => if pf.1.card ≠ 0 then of' pf.1 * antipodeRightTreeN pf.2
               else (0 : ConnesKreimer R (Nonplanar α))))

/-- The recursive Foissy equation, in non-`attach`-decorated form. The
    `attach`-style def above keeps the membership info for well-foundedness;
    this unfold strips it for downstream proofs. -/
theorem antipodeTreeN_unfold (T : Nonplanar α) :
    antipodeTreeN (R := R) T = - ((cutSummandsN T).map
      (fun pf => (pf.1.map (antipodeTreeN (R := R))).prod * ofTree pf.2)).sum := by
  conv_lhs => rw [antipodeTreeN]
  -- The body: `-((cutSummandsN T).attach.map ⟨pf, _⟩ ↦ (pf.1.attach.map ⟨T_i, _⟩ ↦ S T_i).prod * ofTree pf.2).sum`
  -- We need to strip both attach via attach_map_val'.
  congr 1
  -- Goal: ((cutSummandsN T).attach.map ...).sum = ((cutSummandsN T).map ...).sum
  -- Step 1: handle the inner attach via Multiset.map_congr.
  rw [show (cutSummandsN T).attach.map (fun (pf : { x // x ∈ cutSummandsN T }) =>
            (pf.val.1.attach.map (fun (T_i : { x // x ∈ pf.val.1 }) =>
              antipodeTreeN T_i.val)).prod * ofTree pf.val.2) =
          (cutSummandsN T).attach.map (fun (pf : { x // x ∈ cutSummandsN T }) =>
            (pf.val.1.map (antipodeTreeN (R := R))).prod * ofTree pf.val.2) from by
    refine Multiset.map_congr rfl (fun ⟨pf, _⟩ _ => ?_)
    show (pf.1.attach.map (fun T_i => antipodeTreeN T_i.val)).prod * _ =
         (pf.1.map antipodeTreeN).prod * _
    congr 1
    exact congrArg Multiset.prod (Multiset.attach_map_val' _ _)]
  -- Step 2: strip the outer attach. Use attach_map_val' with explicit `f` to
  -- ensure unification picks up the lambda even with `↑pf` vs `pf.val` notation.
  exact congrArg Multiset.sum (@Multiset.attach_map_val'
    (Forest (Nonplanar α) × Nonplanar α) _ (cutSummandsN T)
    (fun pf => (pf.1.map (antipodeTreeN (R := R))).prod * ofTree pf.2))

/-- Sum decomposition: pulling out the empty-cut summand from `Σ over cutSummandsN T`
    of `of'(cf) * R(rem)` gives `R(T)` (since `of'(0) = 1` and the empty cut is unique). -/
private lemma R_sum_decomp_empty_cut (T : Nonplanar α) :
    ((cutSummandsN T).map
      (fun (p : Forest (Nonplanar α) × Nonplanar α) =>
        of' (R := R) p.1 * antipodeRightTreeN p.2)).sum =
    antipodeRightTreeN T +
    (((cutSummandsN T).filter
        (fun (p : Forest (Nonplanar α) × Nonplanar α) => p.1.card ≠ 0)).map
      (fun (p : Forest (Nonplanar α) × Nonplanar α) =>
        of' (R := R) p.1 * antipodeRightTreeN p.2)).sum := by
  conv_lhs => rw [← Multiset.filter_add_not
    (fun (p : Forest (Nonplanar α) × Nonplanar α) => p.1.card = 0)
    (cutSummandsN T)]
  rw [Multiset.map_add, Multiset.sum_add]
  rw [cutSummandsN_filter_card_zero, Multiset.map_singleton, Multiset.sum_singleton]
  rw [of'_zero, one_mul]

/-- The if-form sum used by `antipodeRightTreeN_unfold` equals the cf≠0-filter sum. -/
private lemma R_if_sum_eq_filter_sum (T : Nonplanar α) :
    ((cutSummandsN T).map
      (fun (p : Forest (Nonplanar α) × Nonplanar α) =>
        if p.1.card ≠ 0 then of' (R := R) p.1 * antipodeRightTreeN p.2
        else (0 : ConnesKreimer R (Nonplanar α)))).sum =
    (((cutSummandsN T).filter
        (fun (p : Forest (Nonplanar α) × Nonplanar α) => p.1.card ≠ 0)).map
      (fun (p : Forest (Nonplanar α) × Nonplanar α) =>
        of' (R := R) p.1 * antipodeRightTreeN p.2)).sum := by
  conv_lhs => rw [← Multiset.filter_add_not
    (fun (p : Forest (Nonplanar α) × Nonplanar α) => p.1.card = 0)
    (cutSummandsN T)]
  rw [Multiset.map_add, Multiset.sum_add]
  -- (filter cf=0).map (if cf≠0 then ... else 0) — each value is 0 since cf.card=0
  have h_zero : ((((cutSummandsN T).filter
        (fun (p : Forest (Nonplanar α) × Nonplanar α) => p.1.card = 0)).map
      (fun (p : Forest (Nonplanar α) × Nonplanar α) =>
        if p.1.card ≠ 0 then of' (R := R) p.1 * antipodeRightTreeN p.2
        else (0 : ConnesKreimer R (Nonplanar α)))).sum) = 0 := by
    apply Multiset.sum_eq_zero
    intros x h_x
    rw [Multiset.mem_map] at h_x
    obtain ⟨p, h_p_mem, rfl⟩ := h_x
    rw [Multiset.mem_filter] at h_p_mem
    simp [h_p_mem.2]
  rw [h_zero, zero_add]
  -- (filter ¬cf=0).map (if cf≠0 then ... else 0) = (filter cf≠0).map (no-if)
  congr 1
  apply Multiset.map_congr rfl
  intros p h_p_mem
  rw [Multiset.mem_filter] at h_p_mem
  simp [h_p_mem.2]

/-! ## §3: Antipode axiom on trees (depth-induction-free!)

The Foissy recursion was set up so that the antipode axiom on a single tree
follows directly from `antipodeTreeN_unfold` — no further induction is
needed. The summands of the antipode definition exactly cancel the summands
produced by `(lift S id) ∘ comulTreeN T`. -/

private theorem antipodeAlgHomN_axiom_tree (T : Nonplanar α) :
    (Algebra.TensorProduct.lift (antipodeAlgHomN (R := R))
      (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (fun _ _ => Commute.all _ _)) (comulTreeN T) = 0 := by
  -- Step 1: unfold comulTreeN and distribute the lift over the addition.
  unfold comulTreeN
  rw [map_add, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, mul_one,
      antipodeAlgHomN_apply_ofTree]
  -- Goal: antipodeTreeN T + (lift _ _ _)(Σ of' cf ⊗ ofTree rem) = 0.
  -- Step 2: distribute the lift through the multiset sum + simplify each tensor.
  rw [show (Algebra.TensorProduct.lift (antipodeAlgHomN (R := R))
            (AlgHom.id R (ConnesKreimer R (Nonplanar α))) (fun _ _ => Commute.all _ _))
            (((cutSummandsN T).map
              (fun p => of' (R := R) p.1 ⊗ₜ ofTree p.2)).sum) =
          ((cutSummandsN T).map
            (fun p => (p.1.map (antipodeTreeN (R := R))).prod * ofTree p.2)).sum from by
    rw [_root_.map_multiset_sum, Multiset.map_map]
    refine congr_arg Multiset.sum (Multiset.map_congr rfl (fun p _ => ?_))
    show (Algebra.TensorProduct.lift _ _ _) (of' p.1 ⊗ₜ ofTree p.2) = _
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, antipodeAlgHomN_apply_of']]
  -- Goal: antipodeTreeN T + Σ ... = 0.
  -- Step 3: unfold antipodeTreeN T = -Σ ..., then `neg_add_cancel`.
  rw [antipodeTreeN_unfold]
  exact neg_add_cancel _

/-- The right antipode satisfies the lTensor axiom on a single tree by direct
    cancellation: pulling out the empty-cut summand exposes `R(T)`, then
    `antipodeRightTreeN_unfold` substitutes and the rest cancels. -/
private theorem antipodeRightAlgHomN_axiom_tree (T : Nonplanar α) :
    (Algebra.TensorProduct.lift (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (antipodeRightAlgHomN (R := R))
      (fun _ _ => Commute.all _ _)) (comulTreeN T) = 0 := by
  -- Step 1: unfold comulTreeN and distribute the lift over the addition.
  unfold comulTreeN
  rw [map_add, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one, mul_one]
  -- Goal: ofTree T + (lift id R)(Σ of' cf ⊗ ofTree rem) = 0.
  -- Step 2: distribute the lift through the multiset sum.
  rw [show (Algebra.TensorProduct.lift (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
            (antipodeRightAlgHomN (R := R)) (fun _ _ => Commute.all _ _))
            (((cutSummandsN T).map
              (fun p => of' (R := R) p.1 ⊗ₜ ofTree p.2)).sum) =
          ((cutSummandsN T).map
            (fun (p : Forest (Nonplanar α) × Nonplanar α) =>
              of' (R := R) p.1 * antipodeRightTreeN p.2)).sum from by
    rw [_root_.map_multiset_sum, Multiset.map_map]
    refine congr_arg Multiset.sum (Multiset.map_congr rfl (fun p _ => ?_))
    show (Algebra.TensorProduct.lift _ _ _) (of' p.1 ⊗ₜ ofTree p.2) = _
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
        antipodeRightAlgHomN_apply_ofTree]]
  -- Goal: ofTree T + Σ over (cf, rem) of of'(cf) * R(rem) = 0
  -- Step 3: split sum at empty cut. Σ = R(T) + Σ_{cf≠0} of'(cf) * R(rem).
  rw [R_sum_decomp_empty_cut T]
  -- Goal: ofTree T + (R(T) + Σ_{cf≠0} of' cf * R rem) = 0.
  -- Step 4: substitute R(T) via unfold, and rewrite the if-form sum.
  rw [antipodeRightTreeN_unfold T, R_if_sum_eq_filter_sum T]
  -- Goal: ofTree T + (-ofTree T - Σ_{cf≠0} of' cf * R rem + Σ_{cf≠0} of' cf * R rem) = 0
  ring

/-! ## §4: Antipode axiom on forests (Multiset induction)

Forest law follows from the tree law by multiplicativity. Convolution
`(lift S id _)` is an algebra hom on `H ⊗ H` (since `H` is commutative),
so it factors through `comulForestN (T ::ₘ F') = comulTreeN T * comulForestN F'`.
The tree case `(lift S id _)(comulTreeN T) = 0` (from §3) makes the cons step
produce `0 · _ = 0`, matching `counit(of' (T ::ₘ F')) = 0`. -/

private theorem antipodeAlgHomN_axiom_forest (F : Forest (Nonplanar α)) :
    (Algebra.TensorProduct.lift (antipodeAlgHomN (R := R))
      (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (fun _ _ => Commute.all _ _)) (comulForestN F) =
    (algebraMap R (ConnesKreimer R (Nonplanar α))) (counit (of' F)) := by
  induction F using Multiset.induction with
  | empty =>
    -- LHS: comulForestN 0 = 1, then lift(1) = 1.
    -- RHS: counit (of' 0) = counit 1 = 1, algebraMap 1 = 1.
    rw [comulForestN_zero, map_one, of'_zero, map_one, map_one]
  | cons T F' _ih =>
    -- comulForestN (T ::ₘ F') = comulTreeN T * comulForestN F', and lift is alg hom
    -- so distributes over multiplication. Tree case kills the first factor.
    rw [comulForestN_cons, map_mul, antipodeAlgHomN_axiom_tree, zero_mul]
    -- Goal: 0 = algebraMap R H (counit (of' (T ::ₘ F'))).
    -- counit(of' (T ::ₘ F')) = 0 since card ≥ 1.
    symm
    rw [counit_of']
    simp [Multiset.card_cons]

/-! ## §5: AlgHom-form rTensor axiom

Lift the forest-level statement (a per-element identity for `of' F`) to the
algebra-hom equality `HopfAlgebra.ofAlgHom` consumes. Reduces via
`AddMonoidAlgebra.algHom_ext`. -/

/-- Wrapper of `antipodeAlgHomN_axiom_forest` stated at `comulAlgHomN (of' F)`
    instead of `comulForestN F`. The two are equal by `comulAlgHomN_apply_of'`. -/
private theorem antipodeAlgHomN_axiom_at_of' (F : Forest (Nonplanar α)) :
    (Algebra.TensorProduct.lift (antipodeAlgHomN (R := R))
      (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (fun _ _ => Commute.all _ _)) (comulAlgHomN (of' F)) =
    (algebraMap R (ConnesKreimer R (Nonplanar α))) (counit (of' F)) := by
  rw [comulAlgHomN_apply_of']
  exact antipodeAlgHomN_axiom_forest F

private theorem antipode_rTensor_axiom [CharZero R] [NoZeroDivisors R] :
    (Algebra.TensorProduct.lift (antipodeAlgHomN (R := R))
      (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (fun _ _ => Commute.all _ _)).comp
      (Bialgebra.comulAlgHom R (ConnesKreimer R (Nonplanar α))) =
    (Algebra.ofId R (ConnesKreimer R (Nonplanar α))).comp
      (Bialgebra.counitAlgHom R (ConnesKreimer R (Nonplanar α))) := by
  apply AddMonoidAlgebra.algHom_ext
  intro F
  -- Defeq: comp.apply, Bialgebra.comulAlgHom = AlgHom.ofLinearMap comul = comulAlgHomN,
  -- Bialgebra.counitAlgHom = AlgHom.ofLinearMap counit = counit, Algebra.ofId = algebraMap.
  exact antipodeAlgHomN_axiom_at_of' F

/-- R satisfies the lTensor axiom on a forest. Mirror of `antipodeAlgHomN_axiom_forest`
    via Multiset.induction; the tree-case kills the first factor. -/
private theorem antipodeRightAlgHomN_axiom_forest (F : Forest (Nonplanar α)) :
    (Algebra.TensorProduct.lift (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (antipodeRightAlgHomN (R := R))
      (fun _ _ => Commute.all _ _)) (comulForestN F) =
    (algebraMap R (ConnesKreimer R (Nonplanar α))) (counit (of' F)) := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestN_zero, map_one, of'_zero, map_one, map_one]
  | cons T F' _ih =>
    rw [comulForestN_cons, map_mul, antipodeRightAlgHomN_axiom_tree, zero_mul]
    symm
    rw [counit_of']
    simp [Multiset.card_cons]

/-- AlgHom-form lTensor axiom for R, stated at `comulAlgHomN (of' F)`. -/
private theorem antipodeRightAlgHomN_axiom_at_of' (F : Forest (Nonplanar α)) :
    (Algebra.TensorProduct.lift (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (antipodeRightAlgHomN (R := R))
      (fun _ _ => Commute.all _ _)) (comulAlgHomN (of' F)) =
    (algebraMap R (ConnesKreimer R (Nonplanar α))) (counit (of' F)) := by
  rw [comulAlgHomN_apply_of']
  exact antipodeRightAlgHomN_axiom_forest F

/-- The right antipode satisfies the lTensor antipode axiom as an `AlgHom` equality.
    This is the lTensor analogue of `antipode_rTensor_axiom`, but for R rather than S. -/
private theorem antipodeRight_lTensor_axiom [CharZero R] [NoZeroDivisors R] :
    (Algebra.TensorProduct.lift (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (antipodeRightAlgHomN (R := R))
      (fun _ _ => Commute.all _ _)).comp
      (Bialgebra.comulAlgHom R (ConnesKreimer R (Nonplanar α))) =
    (Algebra.ofId R (ConnesKreimer R (Nonplanar α))).comp
      (Bialgebra.counitAlgHom R (ConnesKreimer R (Nonplanar α))) := by
  apply AddMonoidAlgebra.algHom_ext
  intro F
  exact antipodeRightAlgHomN_axiom_at_of' F

/-! ## §6: lTensor axiom via WithConv glue

The standard antipode `S = antipodeAlgHomN` satisfies the rTensor axiom
(`antipode_rTensor_axiom`); the right antipode `R = antipodeRightAlgHomN`
satisfies the lTensor axiom (`antipodeRight_lTensor_axiom`). In the convolution
monoid `WithConv (H →ₗ[R] H)` these read `S * id = 1` and `id * R = 1`
respectively, so `left_inv_eq_right_inv` gives `S = R` as linear maps. By
`AlgHom.toLinearMap_injective`, `S = R` as algebra homs. Substituting `S` for
`R` in `antipodeRight_lTensor_axiom` discharges the lTensor axiom for `S`. -/

/-- Bridge: `Algebra.TensorProduct.lift f g comm` agrees with the linear map
    `μ ∘ map f g` on every tensor. The linear-map form is what `WithConv`
    convolution uses; the AlgHom-form is what our axioms are stated in. -/
private lemma lift_eq_mulPrime_comp_map
    (f g : ConnesKreimer R (Nonplanar α) →ₐ[R] ConnesKreimer R (Nonplanar α))
    (comm : ∀ a b, Commute (f a) (g b)) (z :
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    Algebra.TensorProduct.lift f g comm z =
    LinearMap.mul' R (ConnesKreimer R (Nonplanar α))
      (TensorProduct.map f.toLinearMap g.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul,
        LinearMap.mul'_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Generic WithConv lemma: an AlgHom-form lTensor/rTensor axiom for `f, g : H →ₐ H`
    is equivalent to `toConv f.toLinearMap * toConv g.toLinearMap = 1` in `WithConv`.
    Used to derive both `S * id = 1` and `id * R = 1` from the tree-level axioms. -/
private lemma withConv_mul_eq_one_of_axiom [CharZero R] [NoZeroDivisors R]
    (f g : ConnesKreimer R (Nonplanar α) →ₐ[R] ConnesKreimer R (Nonplanar α))
    (h_axiom : (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom R (ConnesKreimer R (Nonplanar α))) =
      (Algebra.ofId R (ConnesKreimer R (Nonplanar α))).comp
        (Bialgebra.counitAlgHom R (ConnesKreimer R (Nonplanar α)))) :
    (WithConv.toConv f.toLinearMap : WithConv _) * WithConv.toConv g.toLinearMap = 1 := by
  apply WithConv.ext
  apply LinearMap.ext
  intro x
  show LinearMap.mul' R _
        (TensorProduct.map f.toLinearMap g.toLinearMap (Coalgebra.comul x)) = _
  rw [← lift_eq_mulPrime_comp_map f g (fun _ _ => Commute.all _ _)]
  exact AlgHom.congr_fun h_axiom x

/-- `S = R` as algebra homs. The Sweedler/Kassel `left_inv_eq_right_inv`
    argument in the convolution monoid `WithConv (H →ₗ[R] H)`. -/
private theorem antipodeAlgHomN_eq_antipodeRightAlgHomN
    [CharZero R] [NoZeroDivisors R] :
    (antipodeAlgHomN (R := R) (α := α)) = antipodeRightAlgHomN := by
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  -- S * id = 1 from rTensor axiom; id * R = 1 from R-lTensor axiom.
  -- left_inv_eq_right_inv with a = id, b = S, c = R gives S = R.
  exact left_inv_eq_right_inv
    (withConv_mul_eq_one_of_axiom antipodeAlgHomN (AlgHom.id R _) antipode_rTensor_axiom)
    (withConv_mul_eq_one_of_axiom (AlgHom.id R _) antipodeRightAlgHomN
      antipodeRight_lTensor_axiom)

private theorem antipodeAlgHomN_axiom_at_of'_lTensor
    [CharZero R] [NoZeroDivisors R] (F : Forest (Nonplanar α)) :
    (Algebra.TensorProduct.lift (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (antipodeAlgHomN (R := R))
      (fun _ _ => Commute.all _ _)) (comulAlgHomN (of' F)) =
    (algebraMap R (ConnesKreimer R (Nonplanar α))) (counit (of' F)) := by
  rw [antipodeAlgHomN_eq_antipodeRightAlgHomN]
  exact antipodeRightAlgHomN_axiom_at_of' F

private theorem antipode_lTensor_axiom [CharZero R] [NoZeroDivisors R] :
    (Algebra.TensorProduct.lift (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
      (antipodeAlgHomN (R := R))
      (fun _ _ => Commute.all _ _)).comp
      (Bialgebra.comulAlgHom R (ConnesKreimer R (Nonplanar α))) =
    (Algebra.ofId R (ConnesKreimer R (Nonplanar α))).comp
      (Bialgebra.counitAlgHom R (ConnesKreimer R (Nonplanar α))) := by
  apply AddMonoidAlgebra.algHom_ext
  intro F
  exact antipodeAlgHomN_axiom_at_of'_lTensor F

/-! ## §7: HopfAlgebra instance

Assemble the Bialgebra (from CoproductNonplanar.lean) + antipode + axioms via
mathlib's `HopfAlgebra.ofAlgHom`. -/

noncomputable instance [CharZero R] [NoZeroDivisors R] :
    HopfAlgebra R (ConnesKreimer R (Nonplanar α)) :=
  HopfAlgebra.ofAlgHom antipodeAlgHomN
    antipode_rTensor_axiom
    antipode_lTensor_axiom

end ConnesKreimer

end RootedTree
