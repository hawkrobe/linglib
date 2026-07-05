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

namespace RoseTree

variable {α β : Type*}

/-! ### `traceLeafCount` — counting trace-marker leaves

A trace marker is a `Sum.inr`-labeled vertex (always a leaf in practice).
A `fold` over `RoseTree (α ⊕ β)`: at a node, sum the children's counts, adding
`1` only for a bare `Sum.inr`-leaf. -/

/-- The number of `Sum.inr`-labeled leaves (trace markers) in a tree. -/
def traceLeafCount : RoseTree (α ⊕ β) → ℕ :=
  fold fun v ns => match v, ns with
    | Sum.inr _, [] => 1
    | _,         ns => ns.sum

@[simp] theorem traceLeafCount_leaf_inr (b : β) :
    traceLeafCount (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 1 := rfl

@[simp] theorem traceLeafCount_leaf_inl (a : α) :
    traceLeafCount (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 := rfl

/-- On a non-leaf node, `traceLeafCount` is the sum of the children's counts,
    regardless of the root label's `Sum`-side. Clears the empty/nonempty split. -/
theorem traceLeafCount_node_of_ne_nil (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β)))
    (h : cs ≠ []) : traceLeafCount (.node v cs) = (cs.map traceLeafCount).sum := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c cs => cases v <;> simp only [traceLeafCount, fold_node, List.map_cons]

/-- On a `Sum.inl` root the count is just the children's total (the lexical
    root is never itself a trace leaf), for any child list. -/
@[simp] theorem traceLeafCount_node_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) = (cs.map traceLeafCount).sum := by
  cases cs with
  | nil => rfl
  | cons c cs => exact traceLeafCount_node_of_ne_nil _ _ (by simp)

/-! #### Trace-leaf-count invariance under `Perm` -/

/-- `traceLeafCount` is a `Perm`-invariant: the fold of a permutation-invariant
    algebra (the shape split is nil-vs-nonempty, which `List.Perm` preserves). -/
theorem traceLeafCount_perm {t s : RoseTree (α ⊕ β)}
    (h : Perm t s) : t.traceLeafCount = s.traceLeafCount := by
  refine fold_perm (fun v l₁ l₂ h' => ?_) h
  cases l₁ with
  | nil => rw [← h'.nil_eq]
  | cons x xs =>
    cases l₂ with
    | nil => exact absurd h'.eq_nil (by simp)
    | cons y ys => cases v <;> exact h'.sum_eq

/-! ### `traceDepthSum` — depth-weighted trace-marker count (Minimal Search depth)

The **Minimal Search depth** `d_v` of MCB §1.5.2 (book p. 59): the sum over
trace-marker leaves of their distance from the root. Descending into the
children adds `1` per trace leaf below them (`+ (cs.map traceLeafCount).sum`),
so a trace leaf at depth `d` is counted `d` times, contributing `d`. A bare
trace leaf at the root contributes `0`.

The recurrence couples to `traceLeafCount` at each level, so a single `fold`
does not express it; it is structural recursion with a child-list companion.

For a Δ^c cut, the quotient (trunk) places a trace leaf at each cut site at
exactly the cut depth (`Coproduct.Trace.traceLeaf`), so
`traceDepthSum(quotient)` reads off the total extraction depth `Σ d_{v_i}`
of MCB rule 1 directly — no enumeration tagging required. -/

mutual
/-- Sum of root-distances of the `Sum.inr`-labeled (trace-marker) leaves. -/
def traceDepthSum : RoseTree (α ⊕ β) → ℕ
  | .node _ cs => traceDepthSumList cs + (cs.map traceLeafCount).sum
/-- Auxiliary: trace-depth across a list of children, measured in the
    children's own frame (the parent adds the `+1`-per-level offset). -/
def traceDepthSumList : List (RoseTree (α ⊕ β)) → ℕ
  | []      => 0
  | t :: ts => traceDepthSum t + traceDepthSumList ts
end

theorem traceDepthSum_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    traceDepthSum (.node v cs) = traceDepthSumList cs + (cs.map traceLeafCount).sum := rfl

@[simp] theorem traceDepthSumList_nil :
    traceDepthSumList ([] : List (RoseTree (α ⊕ β))) = 0 := rfl

@[simp] theorem traceDepthSumList_cons (t : RoseTree (α ⊕ β)) (ts : List (RoseTree (α ⊕ β))) :
    traceDepthSumList (t :: ts) = traceDepthSum t + traceDepthSumList ts := rfl

@[simp] theorem traceDepthSum_leaf_inl (a : α) :
    traceDepthSum (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 := rfl

@[simp] theorem traceDepthSum_leaf_inr (b : β) :
    traceDepthSum (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 0 := rfl

theorem traceDepthSumList_eq_sum_map (cs : List (RoseTree (α ⊕ β))) :
    traceDepthSumList cs = (cs.map traceDepthSum).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [traceDepthSumList_cons, List.map_cons, List.sum_cons, ih]

/-- The per-child contribution `traceDepthSum c + traceLeafCount c` summed:
    combines the two child statistics into one map. -/
theorem traceDepthSum_node_eq (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    traceDepthSum (.node v cs)
      = (cs.map (fun c => traceDepthSum c + traceLeafCount c)).sum := by
  rw [traceDepthSum_node, traceDepthSumList_eq_sum_map]
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.sum_cons]; omega

/-! #### Trace-depth invariance under `Perm` -/

mutual
/-- `traceDepthSum` is a `Perm`-invariant. Not a fold (the recurrence couples to
    `traceLeafCount`), so the invariance is the mutual induction with its
    child-list companion. -/
theorem traceDepthSum_perm : ∀ {t s : RoseTree (α ⊕ β)}, Perm t s →
    t.traceDepthSum = s.traceDepthSum
  | _, _, .node h => by
    rw [traceDepthSum_node_eq, traceDepthSum_node_eq]
    exact traceDepthSumMap_permList h
  | _, _, .trans h₁ h₂ => (traceDepthSum_perm h₁).trans (traceDepthSum_perm h₂)

/-- The combined per-child statistic is `PermList`-invariant. -/
theorem traceDepthSumMap_permList : ∀ {cs ds : List (RoseTree (α ⊕ β))}, PermList cs ds →
    (cs.map (fun c => traceDepthSum c + traceLeafCount c)).sum
      = (ds.map (fun c => traceDepthSum c + traceLeafCount c)).sum
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [List.map_cons, List.sum_cons, traceDepthSum_perm h, traceLeafCount_perm h,
      traceDepthSumMap_permList hs]
  | _, _, .swap c d cs => by
    simp only [List.map_cons, List.sum_cons]
    omega
  | _, _, .trans h₁ h₂ =>
    (traceDepthSumMap_permList h₁).trans (traceDepthSumMap_permList h₂)
end

/-- The children's trace leaves are bounded by the node's: a `Sum.inr` root
    can only *add* a trace leaf (the empty-trace-leaf case), never remove one. -/
theorem traceLeafCount_le_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    (cs.map traceLeafCount).sum ≤ traceLeafCount (.node v cs) := by
  rcases eq_or_ne cs [] with h | h
  · subst h; exact Nat.zero_le _
  · exact (traceLeafCount_node_of_ne_nil v cs h).ge

/-- **A lexical root puts every trace marker at depth ≥ 1**: for a
    `Sum.inl`-rooted tree, the depth-weighted trace count dominates the plain
    trace count. Underlies the Minimal-Search positivity `Cut.depthC_pos`. -/
theorem traceLeafCount_le_traceDepthSum_of_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) ≤ traceDepthSum (.node (Sum.inl a) cs) := by
  rw [traceLeafCount_node_inl, traceDepthSum_node]
  exact Nat.le_add_left _ _

end RoseTree

namespace RootedTree

namespace Nonplanar

variable {α β : Type*}

/-- The number of `Sum.inr`-labeled (trace-marker) leaves of a nonplanar
    tree, lifted from `RoseTree.traceLeafCount`. -/
def traceLeafCount : Nonplanar (α ⊕ β) → ℕ :=
  Nonplanar.lift RoseTree.traceLeafCount
    (fun _ _ h => RoseTree.traceLeafCount_perm h)

@[simp] theorem traceLeafCount_mk (t : RoseTree (α ⊕ β)) :
    (mk t).traceLeafCount = t.traceLeafCount := rfl

@[simp] theorem traceLeafCount_leaf_inl (a : α) :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).traceLeafCount = 0 := rfl

@[simp] theorem traceLeafCount_leaf_inr (b : β) :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).traceLeafCount = 1 := rfl

/-- The **Minimal Search depth** `d_v` of MCB §1.5: the sum of root-distances
    of the trace-marker leaves, lifted from `RoseTree.traceDepthSum`. For a Δ^c
    cut, `traceDepthSum` of the quotient is the total extraction depth. -/
def traceDepthSum : Nonplanar (α ⊕ β) → ℕ :=
  Nonplanar.lift RoseTree.traceDepthSum
    (fun _ _ h => RoseTree.traceDepthSum_perm h)

@[simp] theorem traceDepthSum_mk (t : RoseTree (α ⊕ β)) :
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
  rw [traceDepthSum_mk, RoseTree.traceDepthSum_node_eq, List.map_map]
  simp only [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show RoseTree.traceDepthSum (Quotient.out t) + RoseTree.traceLeafCount (Quotient.out t)
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
  rw [traceLeafCount_mk, RoseTree.traceLeafCount_node_inl, List.map_map]
  simp only [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.sum_coe]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show (mk (Quotient.out t)).traceLeafCount = Nonplanar.traceLeafCount t
  exact congrArg Nonplanar.traceLeafCount (Quotient.out_eq t)

/-- External Merge adds two accessible terms in the trace-aware count: the two
    children's roots become accessible (MCB Lemma 1.6.3, eq. 1.6.5). Needs each
    child to have a lexical vertex (`traceLeafCount < numNodes`), automatic for a
    real syntactic object. -/
theorem accCountC_merge (a : α) (l r : Nonplanar (α ⊕ β))
    (hl : l.traceLeafCount < l.numNodes) (hr : r.traceLeafCount < r.numNodes) :
    (Nonplanar.node (Sum.inl a) {l, r}).accCountC = l.accCountC + r.accCountC + 2 := by
  have hw := Nonplanar.accCount_merge (Sum.inl a) l r
  have htl : (Nonplanar.node (Sum.inl a) {l, r}).traceLeafCount
      = l.traceLeafCount + r.traceLeafCount := by
    rw [traceLeafCount_node_inl]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
  have hbl : l.traceLeafCount ≤ l.accCount := by
    rw [Nonplanar.accCount_eq_numNodes_sub_one]; omega
  have hbr : r.traceLeafCount ≤ r.accCount := by
    rw [Nonplanar.accCount_eq_numNodes_sub_one]; omega
  simp only [accCountC, htl, hw]
  omega

/-- The **complexity grading** `#L` restricted to lexical leaves:
    `#L_{SO₀}(T) = #L(T) − #traceLeaves(T)`. The trace-exclusion follows the
    UNVERIFIED-default reading of MCB Remark 1.2.2 (leaves labeled by `SO₀`);
    whether a trace leaf counts in `#L` is not settled in the book. -/
def leafCountSO0 (t : Nonplanar (α ⊕ β)) : ℕ := t.numLeaves - t.traceLeafCount

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

example (a : α) (b : β) : (traceWitness a b).numNodes = 2 := rfl
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
        Nonplanar.numNodes).sum := by
  simp only [Forest.sigmaC, Forest.b₀_singleton, Forest.alphaC_singleton,
    Multiset.map_singleton, Multiset.sum_singleton,
    show (traceWitness a b).accCountC = 0 from rfl,
    show (traceWitness a b).numNodes = 2 from rfl]
  decide

end Nonplanar

end RootedTree
