import Linglib.Core.Combinatorics.RootedTree.Counting

/-!
# Trace-aware size counting on `Nonplanar (α ⊕ β)`
[marcolli-chomsky-berwick-2025]

The MCB size measures specialized to the **contraction-quotient carrier**
`Nonplanar (α ⊕ β)`, where `Sum.inl` vertices carry original lexical
decorations and `Sum.inr` vertices are trace-marker placeholders left by
the Δ^c coproduct (a trace leaf is `node (Sum.inr b) []`, the encoding of
`Coproduct.Trace.traceLeaf`). A trace leaf is a vertex but **not** an
accessible term: it is excluded from `Acc`, so the trace-aware counts
subtract it off the generic carrier measures.

The key consequence is the failure of the clean trace-free identity
`σ = #V`: for a contraction quotient `σᶜ ≠ #V` (MCB p. 66 caveat), because
a trace leaf inflates `#V` without contributing an accessible term.

## Main definitions

* `Nonplanar.traceLeafCount` — number of `Sum.inr`-labeled leaves.
* `Nonplanar.accCountC` — trace-excluding accessible-term count `α − #traceLeaves`.
* `Nonplanar.leafCountSO0` — complexity grading `#L` on lexical leaves only.
* `Forest.alphaC` / `Forest.sigmaC` — the trace-aware workspace measures.
-/

namespace RootedTree

namespace Planar

variable {α β : Type*}

/-! ### `traceLeafCount` — counting trace-marker leaves

A trace marker is a `Sum.inr`-labeled vertex (always a leaf in practice).
Defined by structural recursion mirroring `leafCount`, with the leaf base
case split on the label's `Sum`-side. -/

mutual
/-- The number of `Sum.inr`-labeled leaves (trace markers) in a tree. -/
def traceLeafCount : Planar (α ⊕ β) → Nat
  | .node (Sum.inr _) []        => 1
  | .node (Sum.inr _) (c :: cs) => traceLeafCountList (c :: cs)
  | .node (Sum.inl _) cs        => traceLeafCountList cs
/-- Auxiliary: total trace-leaf count across a list of trees. -/
def traceLeafCountList : List (Planar (α ⊕ β)) → Nat
  | []      => 0
  | t :: ts => traceLeafCount t + traceLeafCountList ts
end

@[simp] theorem traceLeafCount_inr_nil (b : β) :
    traceLeafCount (Planar.node (Sum.inr b) [] : Planar (α ⊕ β)) = 1 := rfl

@[simp] theorem traceLeafCount_inr_cons (b : β) (c : Planar (α ⊕ β))
    (cs : List (Planar (α ⊕ β))) :
    traceLeafCount (Planar.node (Sum.inr b) (c :: cs)) =
      traceLeafCountList (c :: cs) := rfl

@[simp] theorem traceLeafCount_inl (a : α) (cs : List (Planar (α ⊕ β))) :
    traceLeafCount (Planar.node (Sum.inl a) cs) = traceLeafCountList cs := rfl

@[simp] theorem traceLeafCountList_nil :
    traceLeafCountList ([] : List (Planar (α ⊕ β))) = 0 := rfl

@[simp] theorem traceLeafCountList_cons (t : Planar (α ⊕ β))
    (ts : List (Planar (α ⊕ β))) :
    traceLeafCountList (t :: ts) = traceLeafCount t + traceLeafCountList ts := rfl

/-- On a non-leaf node, `traceLeafCount` is the `traceLeafCountList` of its
    children, regardless of the root label's `Sum`-side. Clears the
    empty/nonempty split. -/
theorem traceLeafCount_node_of_ne_nil (a : α ⊕ β) (L : List (Planar (α ⊕ β)))
    (h : L ≠ []) : traceLeafCount (Planar.node a L) = traceLeafCountList L := by
  cases a with
  | inl x => rfl
  | inr y =>
    cases L with
    | nil => contradiction
    | cons c cs => rfl

/-! #### Trace-leaf-count invariance under `PlanarEquiv` -/

private theorem traceLeafCountList_perm (cs ds : List (Planar (α ⊕ β)))
    (h : List.Perm cs ds) : traceLeafCountList cs = traceLeafCountList ds := by
  induction h with
  | nil => rfl
  | cons _ _ ih =>
    show traceLeafCount _ + traceLeafCountList _
       = traceLeafCount _ + traceLeafCountList _
    rw [ih]
  | swap _ _ _ =>
    show traceLeafCount _ + (traceLeafCount _ + traceLeafCountList _)
       = traceLeafCount _ + (traceLeafCount _ + traceLeafCountList _)
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem traceLeafCount_planarStep {t s : Planar (α ⊕ β)}
    (h : PlanarStep t s) : t.traceLeafCount = s.traceLeafCount := by
  induction h with
  | swapAtRoot =>
    rename_i a l r pre post
    rw [traceLeafCount_node_of_ne_nil a (pre ++ l :: r :: post) (by simp),
        traceLeafCount_node_of_ne_nil a (pre ++ r :: l :: post) (by simp)]
    apply traceLeafCountList_perm
    apply List.Perm.append_left
    exact .swap r l post
  | recurse _ ih =>
    rename_i a pre old new post _hstep
    rw [traceLeafCount_node_of_ne_nil a (pre ++ old :: post) (by simp),
        traceLeafCount_node_of_ne_nil a (pre ++ new :: post) (by simp)]
    induction pre with
    | nil =>
      show traceLeafCount old + traceLeafCountList post
         = traceLeafCount new + traceLeafCountList post
      rw [ih]
    | cons head tail ih_pre =>
      simp only [List.cons_append]
      show traceLeafCount head + traceLeafCountList (tail ++ old :: post)
         = traceLeafCount head + traceLeafCountList (tail ++ new :: post)
      rw [ih_pre]

theorem traceLeafCount_planarEquiv {t s : Planar (α ⊕ β)}
    (h : PlanarEquiv t s) : t.traceLeafCount = s.traceLeafCount := by
  induction h with
  | rel _ _ hstep => exact traceLeafCount_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem traceLeafCountList_eq_sum_map (cs : List (Planar (α ⊕ β))) :
    Planar.traceLeafCountList cs = (cs.map Planar.traceLeafCount).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [Planar.traceLeafCountList_cons, List.map_cons, List.sum_cons, ih]

/-! ### `traceDepthSum` — depth-weighted trace-marker count (Minimal Search depth)

The **Minimal Search depth** `d_v` of MCB §1.5.2 (book p. 59): the sum over
trace-marker leaves of their distance from the root. A single recursion
suffices — descending into the children adds `1` per trace leaf below them
(`+ traceLeafCountList cs`), so a trace leaf at depth `d` is counted `d`
times, contributing `d`. A bare trace leaf at the root contributes `0`.

For a Δ^c cut, the quotient (trunk) places a trace leaf at each cut site at
exactly the cut depth (`Coproduct.Trace.traceLeaf`), so
`traceDepthSum(quotient)` reads off the total extraction depth `Σ d_{v_i}`
of MCB rule 1 directly — no enumeration tagging required. -/

mutual
/-- Sum of root-distances of the `Sum.inr`-labeled (trace-marker) leaves. -/
def traceDepthSum : Planar (α ⊕ β) → Nat
  | .node _ cs => traceDepthSumList cs + traceLeafCountList cs
/-- Auxiliary: trace-depth across a list of children, measured in the
    children's own frame (the parent adds the `+1`-per-level offset). -/
def traceDepthSumList : List (Planar (α ⊕ β)) → Nat
  | []      => 0
  | t :: ts => traceDepthSum t + traceDepthSumList ts
end

theorem traceDepthSum_node (a : α ⊕ β) (cs : List (Planar (α ⊕ β))) :
    traceDepthSum (Planar.node a cs) = traceDepthSumList cs + traceLeafCountList cs := rfl

@[simp] theorem traceDepthSumList_nil :
    traceDepthSumList ([] : List (Planar (α ⊕ β))) = 0 := rfl

@[simp] theorem traceDepthSumList_cons (t : Planar (α ⊕ β))
    (ts : List (Planar (α ⊕ β))) :
    traceDepthSumList (t :: ts) = traceDepthSum t + traceDepthSumList ts := rfl

@[simp] theorem traceDepthSum_leaf_inl (a : α) :
    traceDepthSum (Planar.node (Sum.inl a) [] : Planar (α ⊕ β)) = 0 := rfl

@[simp] theorem traceDepthSum_leaf_inr (b : β) :
    traceDepthSum (Planar.node (Sum.inr b) [] : Planar (α ⊕ β)) = 0 := rfl

theorem traceDepthSumList_eq_sum_map (cs : List (Planar (α ⊕ β))) :
    traceDepthSumList cs = (cs.map traceDepthSum).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [traceDepthSumList_cons, List.map_cons, List.sum_cons, ih]

/-- The node-level per-child contribution `traceDepthSum c + traceLeafCount c`,
    summed: combines the two list statistics into one map. -/
theorem traceDepthSumList_add_traceLeafCountList (cs : List (Planar (α ⊕ β))) :
    traceDepthSumList cs + traceLeafCountList cs
      = (cs.map (fun c => traceDepthSum c + traceLeafCount c)).sum := by
  rw [traceDepthSumList_eq_sum_map, traceLeafCountList_eq_sum_map]
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.sum_cons]; omega

/-! #### Trace-depth invariance under `PlanarEquiv` -/

private theorem traceDepthSumList_perm (cs ds : List (Planar (α ⊕ β)))
    (h : List.Perm cs ds) : traceDepthSumList cs = traceDepthSumList ds := by
  induction h with
  | nil => rfl
  | cons _ _ ih => rw [traceDepthSumList_cons, traceDepthSumList_cons, ih]
  | swap _ _ _ => simp only [traceDepthSumList_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem traceDepthSum_planarStep {t s : Planar (α ⊕ β)}
    (h : PlanarStep t s) : t.traceDepthSum = s.traceDepthSum := by
  induction h with
  | swapAtRoot =>
    rename_i a l r pre post
    have hperm : (pre ++ l :: r :: post).Perm (pre ++ r :: l :: post) :=
      List.Perm.append_left pre (.swap r l post)
    rw [traceDepthSum_node, traceDepthSum_node,
        traceDepthSumList_perm _ _ hperm, traceLeafCountList_perm _ _ hperm]
  | recurse hstep ih =>
    rename_i a pre old new post
    have hc : old.traceLeafCount = new.traceLeafCount := traceLeafCount_planarStep hstep
    rw [traceDepthSum_node, traceDepthSum_node,
        traceDepthSumList_eq_sum_map, traceDepthSumList_eq_sum_map,
        traceLeafCountList_eq_sum_map, traceLeafCountList_eq_sum_map]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, ih, hc]

theorem traceDepthSum_planarEquiv {t s : Planar (α ⊕ β)}
    (h : PlanarEquiv t s) : t.traceDepthSum = s.traceDepthSum := by
  induction h with
  | rel _ _ hstep => exact traceDepthSum_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The children's trace leaves are bounded by the node's: a `Sum.inr` root
    can only *add* a trace leaf (the empty-trace-leaf case), never remove one. -/
theorem traceLeafCountList_le_node (a : α ⊕ β) (cs : List (Planar (α ⊕ β))) :
    traceLeafCountList cs ≤ traceLeafCount (Planar.node a cs) := by
  rcases eq_or_ne cs [] with h | h
  · subst h; exact Nat.zero_le _
  · exact (traceLeafCount_node_of_ne_nil a cs h).ge

/-- **A lexical root puts every trace marker at depth ≥ 1**: for a
    `Sum.inl`-rooted tree, the depth-weighted trace count dominates the plain
    trace count (`traceDepthSum = traceDepthSumList + traceLeafCountList`, and the
    `+ traceLeafCountList` term is exactly the descent of each child trace by one
    level). Underlies the Minimal-Search positivity `Cut.depthC_pos`. -/
theorem traceLeafCount_le_traceDepthSum_of_inl (a : α) (cs : List (Planar (α ⊕ β))) :
    traceLeafCount (Planar.node (Sum.inl a) cs) ≤
      traceDepthSum (Planar.node (Sum.inl a) cs) := by
  rw [traceLeafCount_inl, traceDepthSum_node]
  exact Nat.le_add_left _ _

end Planar

namespace Nonplanar

variable {α β : Type*}

/-- The number of `Sum.inr`-labeled (trace-marker) leaves of a nonplanar
    tree, lifted from `Planar.traceLeafCount`. -/
def traceLeafCount : Nonplanar (α ⊕ β) → Nat :=
  Nonplanar.lift Planar.traceLeafCount
    (fun _ _ h => Planar.traceLeafCount_planarEquiv h)

@[simp] theorem traceLeafCount_mk (t : Planar (α ⊕ β)) :
    (mk t).traceLeafCount = t.traceLeafCount := rfl

@[simp] theorem traceLeafCount_leaf_inl (a : α) :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).traceLeafCount = 0 := rfl

@[simp] theorem traceLeafCount_leaf_inr (b : β) :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).traceLeafCount = 1 := rfl

/-- The **Minimal Search depth** `d_v` of MCB §1.5: the sum of root-distances
    of the trace-marker leaves, lifted from `Planar.traceDepthSum`. For a Δ^c
    cut, `traceDepthSum` of the quotient is the total extraction depth. -/
def traceDepthSum : Nonplanar (α ⊕ β) → Nat :=
  Nonplanar.lift Planar.traceDepthSum
    (fun _ _ h => Planar.traceDepthSum_planarEquiv h)

@[simp] theorem traceDepthSum_mk (t : Planar (α ⊕ β)) :
    (mk t).traceDepthSum = t.traceDepthSum := rfl

@[simp] theorem traceDepthSum_leaf_inl (a : α) :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).traceDepthSum = 0 := rfl

@[simp] theorem traceDepthSum_leaf_inr (b : β) :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).traceDepthSum = 0 := rfl

/-- Trace-depth of a node decomposes over children: each child `c`
    contributes its own trace-depth plus one per trace leaf it carries
    (the `+1` for the extra level between the node and `c`). -/
@[simp] theorem traceDepthSum_node_inl (a : α) (F : Multiset (Nonplanar (α ⊕ β))) :
    (Nonplanar.node (Sum.inl a) F).traceDepthSum
      = (F.map (fun c => c.traceDepthSum + c.traceLeafCount)).sum := by
  refine Quotient.inductionOn F fun lst => ?_
  show (mk (.node (Sum.inl a) (lst.map Quotient.out))).traceDepthSum = _
  rw [traceDepthSum_mk]
  show Planar.traceDepthSum (.node (Sum.inl a) (lst.map Quotient.out)) = _
  rw [Planar.traceDepthSum_node, Planar.traceDepthSumList_add_traceLeafCountList,
      List.map_map]
  simp only [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show Planar.traceDepthSum (Quotient.out t) + Planar.traceLeafCount (Quotient.out t)
      = Nonplanar.traceDepthSum t + Nonplanar.traceLeafCount t
  congr 1
  · exact congrArg Nonplanar.traceDepthSum (Quotient.out_eq t)
  · exact congrArg Nonplanar.traceLeafCount (Quotient.out_eq t)

/-- The **trace-excluding accessible-term count** `αᶜ(T) = α(T) − #traceLeaves(T)`:
    a trace leaf is a vertex but not an accessible term (MCB p. 66). Truncated
    subtraction handles the all-trace edge case (e.g. `T = traceLeaf b`, where
    `α = 0` and `#traceLeaves = 1`). -/
def accCountC (t : Nonplanar (α ⊕ β)) : ℕ := t.accCount - t.traceLeafCount

/-- Trace leaves of a lexical-rooted node: the root contributes none, so the
    count is the children's total. -/
@[simp] theorem traceLeafCount_node_inl (a : α) (F : Multiset (Nonplanar (α ⊕ β))) :
    (Nonplanar.node (Sum.inl a) F).traceLeafCount = (F.map Nonplanar.traceLeafCount).sum := by
  refine Quotient.inductionOn F fun lst => ?_
  show (mk (.node (Sum.inl a) (lst.map Quotient.out))).traceLeafCount = _
  rw [traceLeafCount_mk]
  show Planar.traceLeafCount (.node (Sum.inl a) (lst.map Quotient.out)) = _
  rw [Planar.traceLeafCount_inl, Planar.traceLeafCountList_eq_sum_map, List.map_map]
  simp only [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show (mk (Quotient.out t)).traceLeafCount = Nonplanar.traceLeafCount t
  exact congrArg Nonplanar.traceLeafCount (Quotient.out_eq t)

/-- External Merge adds two accessible terms in the trace-aware count: the two
    children's roots become accessible (MCB Lemma 1.6.3, eq. 1.6.5). Needs each
    child to have a lexical vertex (`traceLeafCount < weight`), automatic for a
    real syntactic object. -/
theorem accCountC_merge (a : α) (l r : Nonplanar (α ⊕ β))
    (hl : l.traceLeafCount < l.weight) (hr : r.traceLeafCount < r.weight) :
    (Nonplanar.node (Sum.inl a) {l, r}).accCountC = l.accCountC + r.accCountC + 2 := by
  have hw := Nonplanar.accCount_merge (Sum.inl a) l r
  have htl : (Nonplanar.node (Sum.inl a) {l, r}).traceLeafCount
      = l.traceLeafCount + r.traceLeafCount := by
    rw [traceLeafCount_node_inl]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
  have hbl : l.traceLeafCount ≤ l.accCount := by
    rw [Nonplanar.accCount_eq_weight_sub_one]; omega
  have hbr : r.traceLeafCount ≤ r.accCount := by
    rw [Nonplanar.accCount_eq_weight_sub_one]; omega
  simp only [accCountC, htl, hw]
  omega

/-- The **complexity grading** `#L` restricted to lexical leaves:
    `#L_{SO₀}(T) = #L(T) − #traceLeaves(T)`. The trace-exclusion follows the
    UNVERIFIED-default reading of MCB Remark 1.2.2 (leaves labeled by `SO₀`);
    whether a trace leaf counts in `#L` is not settled in the book. -/
def leafCountSO0 (t : Nonplanar (α ⊕ β)) : ℕ := t.leafCount - t.traceLeafCount

end Nonplanar

/-! ## Trace-aware workspace (forest) measures -/

namespace Forest

variable {α β : Type*}

/-- Trace-excluding accessible terms across a workspace, `αᶜ(F) = Σ αᶜ(Tᵢ)`. -/
def alphaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ :=
  (F.map Nonplanar.accCountC).sum

@[simp] theorem alphaC_zero : alphaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem alphaC_cons (T : Nonplanar (α ⊕ β))
    (F : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (T ::ₘ F) = T.accCountC + alphaC F := by
  simp only [alphaC, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem alphaC_singleton (T : Nonplanar (α ⊕ β)) :
    alphaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC := by
  simp only [alphaC, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem alphaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (F + G) = alphaC F + alphaC G := by
  simp only [alphaC, Multiset.map_add, Multiset.sum_add]

/-- Trace-aware workspace size `σᶜ(F) = b₀(F) + αᶜ(F)`. Unlike the generic
    `σ`, this is **not** the vertex count for contraction quotients
    (`σᶜ ≠ #V`, MCB p. 66): a trace leaf is a vertex but not an accessible
    term, so it raises `#V` without raising `σᶜ`. -/
def sigmaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ := b₀ F + alphaC F

@[simp] theorem sigmaC_zero : sigmaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem sigmaC_cons (T : Nonplanar (α ⊕ β))
    (F : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (T ::ₘ F) = T.accCountC + 1 + sigmaC F := by
  simp only [sigmaC, b₀_cons, alphaC_cons]; omega
@[simp] theorem sigmaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (F + G) = sigmaC F + sigmaC G := by
  simp only [sigmaC, b₀_add, alphaC_add]; omega

end Forest

/-! ### The `σᶜ ≠ #V` caveat, concretely

A lexical root over a single trace leaf: `#V = 2` (root + trace leaf) but the
trace leaf contributes no accessible term, so `αᶜ = 0` and `σᶜ = 1`. -/

namespace Nonplanar

variable {α β : Type*}

/-- Minimal contraction-quotient witness for the `σᶜ ≠ #V` caveat. -/
private def traceWitness (a : α) (b : β) : Nonplanar (α ⊕ β) :=
  Nonplanar.mk (.node (Sum.inl a) [.node (Sum.inr b) []])

example (a : α) (b : β) : (traceWitness a b).weight = 2 := rfl
example (a : α) (b : β) : (traceWitness a b).traceLeafCount = 1 := rfl
example (a : α) (b : β) : (traceWitness a b).accCountC = 0 := rfl
example (a : α) (b : β) : (traceWitness a b).leafCountSO0 = 0 := rfl

/-- The trace leaf of `traceWitness` sits at depth 1, so `traceDepthSum = 1`. -/
example (a : α) (b : β) : (traceWitness a b).traceDepthSum = 1 := rfl

/-- A trace leaf two levels down contributes depth 2 to `traceDepthSum`. -/
example (a a' : α) (b : β) :
    Nonplanar.traceDepthSum
      (Nonplanar.mk (.node (Sum.inl a) [.node (Sum.inl a') [.node (Sum.inr b) []]])) = 2 := rfl

/-- Two trace leaves at depths 1 and 2 sum to 3 — the multi-extraction
    additivity `d_v = Σ d_{v_i}` of MCB rule 3. -/
example (a a' : α) (b b' : β) :
    Nonplanar.traceDepthSum
      (Nonplanar.mk (.node (Sum.inl a)
        [.node (Sum.inr b) [], .node (Sum.inl a') [.node (Sum.inr b') []]])) = 3 := rfl

/-- `σᶜ` undercounts `#V` on the contraction quotient: the trace leaf is a
    vertex but not an accessible term. -/
example (a : α) (b : β) :
    Forest.sigmaC ({traceWitness a b} : Multiset (Nonplanar (α ⊕ β))) ≠
      (({traceWitness a b} : Multiset (Nonplanar (α ⊕ β))).map
        Nonplanar.weight).sum := by
  simp only [Forest.sigmaC, Forest.b₀_singleton, Forest.alphaC_singleton,
    Multiset.map_singleton, Multiset.sum_singleton,
    show (traceWitness a b).accCountC = 0 from rfl,
    show (traceWitness a b).weight = 2 from rfl]
  decide

end Nonplanar

end RootedTree
