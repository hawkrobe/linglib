import Linglib.Core.Data.RoseTree.Nonplanar

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

namespace RoseTree

variable {α : Type*}

/-! ### Contracting unary nodes

`contractUnary` is a catamorphism over `RoseTree.fold`: rebuild each node from its
already-contracted children, but a lone child *replaces* the parent — that is
where a unary node collapses. -/

/-- Rebuild a node from its (contracted) children: a single child replaces the
node, otherwise the node is kept. -/
def contractCombine (a : α) : List (RoseTree α) → RoseTree α
  | [c] => c
  | cs  => node a cs

@[simp] theorem contractCombine_singleton (a : α) (c : RoseTree α) :
    contractCombine a [c] = c := rfl

theorem contractCombine_nil (a : α) : contractCombine a ([] : List (RoseTree α)) = node a [] := rfl

theorem contractCombine_cons₂ (a : α) (c d : RoseTree α) (cs : List (RoseTree α)) :
    contractCombine a (c :: d :: cs) = node a (c :: d :: cs) := rfl

/-- Contract every unary node into its child (rebinarize to maximal binary),
MCB's Δᵈ (Def. 1.2.5). -/
def contractUnary : RoseTree α → RoseTree α :=
  fold contractCombine

@[simp] theorem contractUnary_node (a : α) (cs : List (RoseTree α)) :
    contractUnary (node a cs) = contractCombine a (cs.map contractUnary) := by
  simp only [contractUnary, fold_node]

/-- On a node with ≥ 2 children `contractUnary` keeps the root and recurses. -/
theorem contractUnary_node_of_two_le (a : α) (cs : List (RoseTree α)) (h : 2 ≤ cs.length) :
    contractUnary (node a cs) = node a (cs.map contractUnary) := by
  rw [contractUnary_node]
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · simp at h
  · simp at h
  · rfl

/-- The number of unary (single-child) nodes. -/
def unaryCount : RoseTree α → ℕ :=
  fold fun _ ns => (if ns.length = 1 then 1 else 0) + ns.sum

@[simp] theorem unaryCount_node (a : α) (cs : List (RoseTree α)) :
    unaryCount (node a cs) = (if cs.length = 1 then 1 else 0) + (cs.map unaryCount).sum := by
  simp only [unaryCount, fold_node, List.length_map]

/-! ### Node-count conservation: each contracted unary node drops one vertex -/

private theorem numNodes_contractCombine (a : α) (cs : List (RoseTree α)) :
    (contractCombine a cs).numNodes = (if cs.length = 1 then 0 else 1) + (cs.map numNodes).sum := by
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · simp [contractCombine_nil]
  · simp
  · rw [contractCombine_cons₂, numNodes_node, if_neg (by simp only [List.length_cons]; omega)]

/-- Every contracted unary node removes exactly one vertex. A single
`RoseTree.rec'` induction: the per-child hypotheses combine over the child list via
`List.sum_map_add`; the two `if`s (`contractCombine` drops the root of a lone
child, `unaryCount` counts it) always sum to one. -/
theorem numNodes_contractUnary_add (t : RoseTree α) :
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

/-! ### `unaryCount` is `Perm`-invariant -/

/-- `unaryCount` is a `Perm`-invariant: the fold of a permutation-invariant algebra
    (length and sum). -/
theorem unaryCount_perm {t s : RoseTree α} (h : Perm t s) :
    t.unaryCount = s.unaryCount :=
  fold_perm (fun _ _ _ h' => by rw [h'.length_eq, h'.sum_eq]) h

/-! ### `contractUnary` is `Perm`-invariant -/

private theorem forall₂_map_contract : ∀ {cs cs' : List (RoseTree α)},
    (∀ c ∈ cs, ∀ s, Perm c s → Perm (contractUnary c) (contractUnary s)) →
    List.Forall₂ Perm cs cs' →
    List.Forall₂ Perm (cs.map contractUnary) (cs'.map contractUnary)
  | _, _, _, .nil => .nil
  | _, _, ih, .cons hcc hf =>
    .cons (ih _ List.mem_cons_self _ hcc)
      (forall₂_map_contract (fun x hx s h => ih x (List.mem_cons_of_mem _ hx) s h) hf)

/-- `contractUnary` maps `Perm`-related trees to `Perm`-related trees: contraction
    is well-defined on the nonplanar quotient. -/
theorem contractUnary_perm {t s : RoseTree α} (h : Perm t s) :
    Perm (contractUnary t) (contractUnary s) := by
  induction t using RoseTree.rec' generalizing s with
  | node a cs ih =>
    obtain ⟨b, ds⟩ := s
    obtain ⟨rfl, hrel⟩ := perm_node_iff.mp h
    obtain ⟨cs', hf, hperm⟩ := Multiset.rel_coe_iff_exists.mp hrel
    have hPL : PermList (cs.map contractUnary) (ds.map contractUnary) :=
      (PermList.of_forall₂ (forall₂_map_contract (fun c hc s hcs => ih c hc hcs) hf)).trans
        (PermList.of_perm (hperm.map contractUnary))
    rw [contractUnary_node, contractUnary_node]
    revert hPL
    generalize cs.map contractUnary = L₁
    generalize ds.map contractUnary = L₂
    intro hPL
    match L₁, L₂, hPL.length_eq, hPL with
    | [], [], _, _ => exact Perm.refl _
    | [x], [y], _, hPL => exact hPL.singleton_inv
    | x :: x' :: xs, y :: y' :: ys, _, hPL => exact .node hPL
    | [], _ :: _, hl, _ => simp at hl
    | [_], [], hl, _ => simp at hl
    | [_], _ :: _ :: _, hl, _ => simp at hl
    | _ :: _ :: _, [], hl, _ => simp at hl
    | _ :: _ :: _, [_], hl, _ => simp at hl

end RoseTree

/-! ### Nonplanar `contractUnary` / `unaryCount` -/

namespace RootedTree.Nonplanar

variable {α : Type*}

/-- The number of unary nodes of a nonplanar tree. -/
def unaryCount : Nonplanar α → ℕ :=
  Nonplanar.lift RoseTree.unaryCount (fun _ _ h => RoseTree.unaryCount_perm h)

@[simp] theorem unaryCount_mk (t : RoseTree α) : (mk t).unaryCount = t.unaryCount := rfl

/-- Rebinarize: contract every unary node (MCB Δᵈ, Def. 1.2.5). -/
def contractUnary : Nonplanar α → Nonplanar α :=
  Quotient.map RoseTree.contractUnary (fun _ _ h => RoseTree.contractUnary_perm h)

@[simp] theorem contractUnary_mk (t : RoseTree α) :
    contractUnary (mk t) = mk (RoseTree.contractUnary t) := rfl

/-- Each contracted unary node drops one vertex. -/
theorem numNodes_contractUnary_add (t : Nonplanar α) :
    (contractUnary t).numNodes + t.unaryCount = t.numNodes := by
  refine Quotient.inductionOn t fun p => ?_
  show (mk (RoseTree.contractUnary p)).numNodes + (mk p).unaryCount = (mk p).numNodes
  rw [numNodes_mk, unaryCount_mk, numNodes_mk]
  exact RoseTree.numNodes_contractUnary_add p

end RootedTree.Nonplanar
