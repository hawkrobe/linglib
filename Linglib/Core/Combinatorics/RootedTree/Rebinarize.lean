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
`numNodes (contractUnary t) + unaryCount t = numNodes t`.
-/

namespace Tree

variable {α : Type*}

/-! ### Contracting unary nodes

`contractUnary` is a catamorphism over `Tree.fold`: rebuild each node from its
already-contracted children, but a lone child *replaces* the parent — that is
where a unary node collapses. -/

/-- Rebuild a node from its (contracted) children: a single child replaces the
node, otherwise the node is kept. -/
def contractCombine (a : α) : List (Tree α) → Tree α
  | [c] => c
  | cs  => node a cs

@[simp] theorem contractCombine_singleton (a : α) (c : Tree α) :
    contractCombine a [c] = c := rfl

theorem contractCombine_nil (a : α) : contractCombine a ([] : List (Tree α)) = node a [] := rfl

theorem contractCombine_cons₂ (a : α) (c d : Tree α) (cs : List (Tree α)) :
    contractCombine a (c :: d :: cs) = node a (c :: d :: cs) := rfl

/-- Contract every unary node into its child (rebinarize to maximal binary),
MCB's Δᵈ (Def. 1.2.5). -/
def contractUnary : Tree α → Tree α :=
  fold contractCombine

@[simp] theorem contractUnary_node (a : α) (cs : List (Tree α)) :
    contractUnary (node a cs) = contractCombine a (cs.map contractUnary) := by
  simp only [contractUnary, fold_node]

/-- On a node with ≥ 2 children `contractUnary` keeps the root and recurses. -/
theorem contractUnary_node_of_two_le (a : α) (cs : List (Tree α)) (h : 2 ≤ cs.length) :
    contractUnary (node a cs) = node a (cs.map contractUnary) := by
  rw [contractUnary_node]
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · simp at h
  · simp at h
  · rfl

/-- The number of unary (single-child) nodes. -/
def unaryCount : Tree α → ℕ :=
  fold fun _ ns => (if ns.length = 1 then 1 else 0) + ns.sum

@[simp] theorem unaryCount_node (a : α) (cs : List (Tree α)) :
    unaryCount (node a cs) = (if cs.length = 1 then 1 else 0) + (cs.map unaryCount).sum := by
  simp only [unaryCount, fold_node, List.length_map]

/-! ### Node-count conservation: each contracted unary node drops one vertex -/

private theorem numNodes_contractCombine (a : α) (cs : List (Tree α)) :
    (contractCombine a cs).numNodes = (if cs.length = 1 then 0 else 1) + (cs.map numNodes).sum := by
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · simp [contractCombine_nil]
  · simp
  · rw [contractCombine_cons₂, numNodes_node, if_neg (by simp only [List.length_cons]; omega)]

/-- Every contracted unary node removes exactly one vertex. A single
`Tree.rec'` induction: the per-child hypotheses combine over the child list via
`List.sum_map_add`; the two `if`s (`contractCombine` drops the root of a lone
child, `unaryCount` counts it) always sum to one. -/
theorem numNodes_contractUnary_add (t : Tree α) :
    (contractUnary t).numNodes + t.unaryCount = t.numNodes := by
  induction t with
  | node a cs ih =>
    have key : ((cs.map contractUnary).map numNodes).sum + (cs.map unaryCount).sum
        = (cs.map numNodes).sum := by
      rw [List.map_map, ← List.sum_map_add]
      exact congrArg List.sum (List.map_congr_left fun c hc => ih c hc)
    rw [contractUnary_node, numNodes_contractCombine, unaryCount_node, numNodes_node,
      List.length_map]
    split_ifs <;> omega

/-! ### `unaryCount` is `PermEquiv`-invariant -/

private theorem unaryCount_permStep {t s : Tree α} (h : PermStep t s) :
    t.unaryCount = s.unaryCount := by
  induction h with
  | @swapAtRoot a l r pre post =>
    simp only [unaryCount_node, List.length_append, List.length_cons]
    congr 1
    exact (((List.Perm.swap r l post).append_left pre).map unaryCount).sum_eq
  | @recurse a pre old new post _ ih =>
    simp only [unaryCount_node, List.length_append, List.length_cons, List.map_append,
      List.map_cons, List.sum_append, List.sum_cons, ih]

theorem unaryCount_permEquiv {t s : Tree α} (h : PermEquiv t s) :
    t.unaryCount = s.unaryCount := by
  induction h with
  | rel _ _ hstep => exact unaryCount_permStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### `contractUnary` is `PermEquiv`-invariant -/

private theorem two_le_length_append_of {pre post : List (Tree α)} {x : Tree α}
    (h : ¬ (pre = [] ∧ post = [])) : 2 ≤ (pre ++ x :: post).length := by
  rcases pre with _ | ⟨p, ps⟩ <;> rcases post with _ | ⟨q, qs⟩
  · exact absurd ⟨rfl, rfl⟩ h
  all_goals simp only [List.length_append, List.length_nil, List.length_cons]; omega

theorem contractUnary_permStep {t s : Tree α} (h : PermStep t s) :
    PermEquiv (contractUnary t) (contractUnary s) := by
  induction h with
  | @swapAtRoot a l r pre post =>
    rw [contractUnary_node_of_two_le a (pre ++ l :: r :: post) (two_le_length_append_of (by simp)),
        contractUnary_node_of_two_le a (pre ++ r :: l :: post) (two_le_length_append_of (by simp))]
    exact permEquiv_root_perm (((List.Perm.swap r l post).append_left pre).map contractUnary)
  | @recurse a pre old new post _ ih =>
    by_cases h1 : pre = [] ∧ post = []
    · obtain ⟨rfl, rfl⟩ := h1
      exact ih
    · rw [contractUnary_node_of_two_le a (pre ++ old :: post) (two_le_length_append_of h1),
          contractUnary_node_of_two_le a (pre ++ new :: post) (two_le_length_append_of h1)]
      simp only [List.map_append, List.map_cons]
      exact permEquiv_recurse_lift (pre.map contractUnary) (post.map contractUnary) ih

theorem contractUnary_permEquiv {t s : Tree α} (h : PermEquiv t s) :
    PermEquiv (contractUnary t) (contractUnary s) := by
  induction h with
  | rel _ _ hstep => exact contractUnary_permStep hstep
  | refl _ => exact PermEquiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

end Tree

/-! ### Nonplanar `contractUnary` / `unaryCount` -/

namespace RootedTree.Nonplanar

variable {α : Type*}

/-- The number of unary nodes of a nonplanar tree. -/
def unaryCount : Nonplanar α → ℕ :=
  Nonplanar.lift Tree.unaryCount (fun _ _ h => Tree.unaryCount_permEquiv h)

@[simp] theorem unaryCount_mk (t : Tree α) : (mk t).unaryCount = t.unaryCount := rfl

/-- Rebinarize: contract every unary node (MCB Δᵈ, Def. 1.2.5). -/
def contractUnary : Nonplanar α → Nonplanar α :=
  Quotient.map Tree.contractUnary (fun _ _ h => Tree.contractUnary_permEquiv h)

@[simp] theorem contractUnary_mk (t : Tree α) :
    contractUnary (mk t) = mk (Tree.contractUnary t) := rfl

/-- Each contracted unary node drops one vertex. -/
theorem numNodes_contractUnary_add (t : Nonplanar α) :
    (contractUnary t).numNodes + t.unaryCount = t.numNodes := by
  refine Quotient.inductionOn t fun p => ?_
  show (mk (Tree.contractUnary p)).numNodes + (mk p).unaryCount = (mk p).numNodes
  rw [numNodes_mk, unaryCount_mk, numNodes_mk]
  exact Tree.numNodes_contractUnary_add p

end RootedTree.Nonplanar
