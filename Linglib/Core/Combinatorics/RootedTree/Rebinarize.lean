import Linglib.Core.Combinatorics.RootedTree.Nonplanar

/-!
# Rebinarization: contracting unary (non-branching) nodes
[marcolli-chomsky-berwick-2025]

`contractUnary` collapses every unary node (a vertex with exactly one child)
into that child, the edge-contraction that takes a syntactic object to its
**unique maximal binary rooted tree** (MCB Def. 1.2.5). It is the second step
of MCB's deletion quotient `T/ᵈF_v`: delete the cut subtrees (leaving the
not-necessarily-binary `T/ᵖF_v`), then `contractUnary` to rebinarize.

Each contracted unary node removes exactly one vertex, so
`weight (contractUnary t) + unaryCount t = weight t`.
-/

namespace RootedTree

namespace Planar

variable {α : Type*}

/-! ### Definitions -/

mutual
/-- Contract every unary node into its child (rebinarize to maximal binary). -/
def contractUnary : Planar α → Planar α
  | .node a []              => .node a []
  | .node _ [c]             => contractUnary c
  | .node a (c₁ :: c₂ :: cs) => .node a (contractUnaryList (c₁ :: c₂ :: cs))
/-- Auxiliary: `contractUnary` across a list of children. -/
def contractUnaryList : List (Planar α) → List (Planar α)
  | []      => []
  | c :: cs => contractUnary c :: contractUnaryList cs
end

mutual
/-- The number of unary (single-child) nodes in a tree. -/
def unaryCount : Planar α → Nat
  | .node _ []              => 0
  | .node _ [c]             => 1 + unaryCount c
  | .node _ (c₁ :: c₂ :: cs) => unaryCountList (c₁ :: c₂ :: cs)
/-- Auxiliary: total unary-node count across a list of trees. -/
def unaryCountList : List (Planar α) → Nat
  | []      => 0
  | c :: cs => unaryCount c + unaryCountList cs
end

@[simp] theorem contractUnaryList_cons (c : Planar α) (cs : List (Planar α)) :
    contractUnaryList (c :: cs) = contractUnary c :: contractUnaryList cs := rfl

@[simp] theorem unaryCountList_cons (c : Planar α) (cs : List (Planar α)) :
    unaryCountList (c :: cs) = unaryCount c + unaryCountList cs := rfl

/-! ### Weight conservation: each contracted unary node drops one vertex -/

mutual
theorem weight_contractUnary_add :
    ∀ (t : Planar α), weight (contractUnary t) + unaryCount t = weight t
  | .node a []              => rfl
  | .node a [c]             => by
    have ih := weight_contractUnary_add c
    show weight (contractUnary c) + (1 + unaryCount c) = 1 + weight c
    omega
  | .node a (c₁ :: c₂ :: cs) => by
    have ihl := weightList_contractUnaryList_add (c₁ :: c₂ :: cs)
    show (1 + weightList (contractUnaryList (c₁ :: c₂ :: cs)))
        + unaryCountList (c₁ :: c₂ :: cs) = 1 + weightList (c₁ :: c₂ :: cs)
    omega
theorem weightList_contractUnaryList_add :
    ∀ (cs : List (Planar α)),
      weightList (contractUnaryList cs) + unaryCountList cs = weightList cs
  | []      => rfl
  | c :: cs => by
    have ih := weight_contractUnary_add c
    have ihl := weightList_contractUnaryList_add cs
    show (weight (contractUnary c) + weightList (contractUnaryList cs))
        + (unaryCount c + unaryCountList cs) = weight c + weightList cs
    omega
end

/-! ### Bridges to `List.map` / `List.sum` and the ≥2-child reductions -/

theorem contractUnaryList_eq_map (cs : List (Planar α)) :
    contractUnaryList cs = cs.map contractUnary := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [contractUnaryList_cons, List.map_cons, ih]

theorem unaryCountList_eq_sum_map (cs : List (Planar α)) :
    unaryCountList cs = (cs.map unaryCount).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [unaryCountList_cons, List.map_cons, List.sum_cons, ih]

theorem contractUnary_node_of_two_le (a : α) (L : List (Planar α)) (h : 2 ≤ L.length) :
    contractUnary (.node a L) = .node a (contractUnaryList L) := by
  rcases L with _ | ⟨c, _ | ⟨d, cs⟩⟩
  · simp at h
  · simp at h
  · rfl

theorem unaryCount_node_of_two_le (a : α) (L : List (Planar α)) (h : 2 ≤ L.length) :
    unaryCount (.node a L) = unaryCountList L := by
  rcases L with _ | ⟨c, _ | ⟨d, cs⟩⟩
  · simp at h
  · simp at h
  · rfl

private theorem two_le_length_append_of {pre post : List (Planar α)} {x : Planar α}
    (h : ¬ (pre = [] ∧ post = [])) : 2 ≤ (pre ++ x :: post).length := by
  rcases pre with _ | ⟨p, ps⟩ <;> rcases post with _ | ⟨q, qs⟩
  · exact absurd ⟨rfl, rfl⟩ h
  · simp only [List.length_append, List.length_nil, List.length_cons]; omega
  · simp only [List.length_append, List.length_nil, List.length_cons]; omega
  · simp only [List.length_append, List.length_cons]; omega

/-! ### `unaryCount` is `PlanarEquiv`-invariant -/

private theorem unaryCountList_perm {cs ds : List (Planar α)} (h : cs.Perm ds) :
    unaryCountList cs = unaryCountList ds := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [unaryCountList_cons]; omega
  | swap _ _ _ => simp only [unaryCountList_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem unaryCount_planarStep {t s : Planar α} (hstep : PlanarStep t s) :
    unaryCount t = unaryCount s := by
  induction hstep with
  | @swapAtRoot a l r pre post =>
    rw [unaryCount_node_of_two_le a (pre ++ l :: r :: post)
          (two_le_length_append_of (by simp)),
        unaryCount_node_of_two_le a (pre ++ r :: l :: post)
          (two_le_length_append_of (by simp))]
    exact unaryCountList_perm ((List.Perm.swap r l post).append_left pre)
  | @recurse a pre old new post _ ih =>
    by_cases h1 : pre = [] ∧ post = []
    · obtain ⟨rfl, rfl⟩ := h1
      show 1 + unaryCount old = 1 + unaryCount new
      omega
    · rw [unaryCount_node_of_two_le a (pre ++ old :: post) (two_le_length_append_of h1),
          unaryCount_node_of_two_le a (pre ++ new :: post) (two_le_length_append_of h1),
          unaryCountList_eq_sum_map, unaryCountList_eq_sum_map,
          List.map_append, List.map_append, List.map_cons, List.map_cons,
          List.sum_append, List.sum_append, List.sum_cons, List.sum_cons, ih]

theorem unaryCount_planarEquiv {t s : Planar α} (h : PlanarEquiv t s) :
    unaryCount t = unaryCount s := by
  induction h with
  | rel _ _ hstep => exact unaryCount_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### `contractUnary` is `PlanarEquiv`-invariant -/

theorem contractUnary_planarStep {t s : Planar α} (hstep : PlanarStep t s) :
    PlanarEquiv (contractUnary t) (contractUnary s) := by
  induction hstep with
  | @swapAtRoot a l r pre post =>
    rw [contractUnary_node_of_two_le a (pre ++ l :: r :: post)
          (two_le_length_append_of (by simp)),
        contractUnary_node_of_two_le a (pre ++ r :: l :: post)
          (two_le_length_append_of (by simp)),
        contractUnaryList_eq_map, contractUnaryList_eq_map]
    exact planarEquiv_root_perm
      ((List.Perm.append_left pre (List.Perm.swap r l post)).map contractUnary)
  | @recurse a pre old new post _ ih =>
    by_cases h1 : pre = [] ∧ post = []
    · obtain ⟨rfl, rfl⟩ := h1
      exact ih
    · rw [contractUnary_node_of_two_le a (pre ++ old :: post) (two_le_length_append_of h1),
          contractUnary_node_of_two_le a (pre ++ new :: post) (two_le_length_append_of h1),
          contractUnaryList_eq_map, contractUnaryList_eq_map,
          List.map_append, List.map_append, List.map_cons, List.map_cons]
      apply planarEquiv_node_componentwise
      generalize pre.map contractUnary = P
      induction P with
      | nil =>
        exact List.Forall₂.cons ih
          (List.forall₂_same.mpr (fun _ _ => PlanarEquiv.refl _))
      | cons p ps ihp => exact List.Forall₂.cons (PlanarEquiv.refl p) ihp

theorem contractUnary_planarEquiv {t s : Planar α} (h : PlanarEquiv t s) :
    PlanarEquiv (contractUnary t) (contractUnary s) := by
  induction h with
  | rel _ _ hstep => exact contractUnary_planarStep hstep
  | refl _ => exact PlanarEquiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

end Planar

/-! ### Nonplanar `contractUnary` / `unaryCount` -/

namespace Nonplanar

variable {α : Type*}

/-- The number of unary nodes of a nonplanar tree. -/
def unaryCount : Nonplanar α → Nat :=
  Nonplanar.lift Planar.unaryCount (fun _ _ h => Planar.unaryCount_planarEquiv h)

@[simp] theorem unaryCount_mk (t : Planar α) : (mk t).unaryCount = t.unaryCount := rfl

/-- Rebinarize: contract every unary node (MCB Δᵈ, Def. 1.2.5). -/
def contractUnary : Nonplanar α → Nonplanar α :=
  Quotient.map Planar.contractUnary (fun _ _ h => Planar.contractUnary_planarEquiv h)

@[simp] theorem contractUnary_mk (t : Planar α) :
    contractUnary (mk t) = mk (Planar.contractUnary t) := rfl

/-- Each contracted unary node drops one vertex. -/
theorem weight_contractUnary_add (t : Nonplanar α) :
    (contractUnary t).weight + t.unaryCount = t.weight := by
  refine Quotient.inductionOn t fun p => ?_
  show (mk (Planar.contractUnary p)).weight + (mk p).unaryCount = (mk p).weight
  rw [weight_mk, unaryCount_mk, weight_mk]
  exact Planar.weight_contractUnary_add p

end Nonplanar

end RootedTree
