import Linglib.Core.Algebra.RootedTree.Coproduct.TraceNonplanar
import Linglib.Syntax.Minimalist.Workspace.TraceMeasures

set_option autoImplicit false

/-!
# Conservation laws for the Δ^c (contraction) cut enumeration
[marcolli-chomsky-berwick-2025]

Size bookkeeping for the trace-preserving admissible-cut coproduct
`cutSummandsCN` on `Nonplanar (α ⊕ β)`. A cut summand `p = (p.1, p.2)`
splits a syntactic object into a *crown forest* `p.1` (the extracted
subtrees) and a *trunk* `p.2` (the contraction quotient, carrying one
trace-marker leaf per cut). The two primitive conservation laws are:

* **weight** (`cutSummandsCN_numNodes`): `Σ #V(crown) + #V(trunk) = #V(T) + #cuts`
  — extracting a subtree removes its vertices but leaves one replacement
  trace leaf per cut.
* **trace leaves** (`cutSummandsCN_traceLeafCount`): `Σ #trace(crown) + #trace(trunk)
  = #trace(T) + #cuts` — each contraction adds exactly one `Sum.inr` leaf.

Combined, they give exact conservation of *lexical* (non-trace) vertices
(`cutSummandsCN_lexical_conservation`): the trace leaf added at each cut
is excluded from the lexical count, cancelling the vertex it replaces.
These are MCB's Lemma 1.6.3 conservation laws on the canonical carrier;
the legacy planar-binary forms were `AdmissibleCut.cut_size_conservation`
and `cut_leafCount_conservation`.

## Main results

* `ConnesKreimer.cutSummandsG_traceLeafCount` — trace-leaf conservation at
  the planar level (mutual with the list/per-child auxiliaries).
* `cutSummandsCN_traceLeafCount`, `cutSummandsCN_numNodes` — descended to
  `Nonplanar`.
* `cutSummandsCN_lexical_conservation` — exact non-trace-vertex conservation.
* `Cut.numContractions` — `#cuts = card` of the crown forest.

## TODO

* The accessible-term / α extraction identities in `accCount`/`accCountC`
  form (MCB eq. 1.6.8 `α(T) = α(Tv) + αᶜ(trunk) + 1` for a single cut, and
  the σ-forms 1.6.9/1.6.10) — corollaries of the two conservation laws,
  modulo truncated-ℕ positivity bookkeeping.
-/

namespace RootedTree

namespace ConnesKreimer

variable {α β : Type*}

/-! ### Tree-level trace-leaf conservation -/

/-- Under nonempty-replacement extraction, every per-child action leaves a
    nonempty remainder. -/
private theorem augActionG_remainder_ne_nil
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hne : ∀ t r, extract t = some r → r ≠ []) (t : RoseTree (α ⊕ β)) :
    ∀ a ∈ augActionG extract t, a.2 ≠ [] := by
  intro a ha
  rw [augActionG_eq] at ha
  rcases Multiset.mem_add.mp ha with h | h
  · cases hex : extract t with
    | none => rw [hex] at h; exact absurd h (Multiset.notMem_zero a)
    | some r =>
      rw [hex] at h
      obtain rfl := Multiset.mem_singleton.mp h
      exact hne t r hex
  · obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp h
    exact List.cons_ne_nil _ _

/-- Under nonempty-replacement extraction, a cut of a nonempty child list
    leaves a nonempty remainder list. -/
private theorem cutListSummandsG_remainder_ne_nil
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hne : ∀ t r, extract t = some r → r ≠ [])
    (t : RoseTree (α ⊕ β)) (ts : List (RoseTree (α ⊕ β))) :
    ∀ q ∈ cutListSummandsG extract (t :: ts), q.2 ≠ [] := by
  intro q hq
  rw [cutListSummandsG_cons] at hq
  obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
  obtain ⟨ha, _⟩ := Multiset.mem_product.mp hpr
  have h1 := augActionG_remainder_ne_nil extract hne t pr.1 ha
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil h1
  show pr.1.2 ++ pr.2.2 ≠ []
  simp [hc]

/-- A unit-trace replacement `r` is nonempty. -/
private theorem ne_nil_of_traceLeafCount_sum_one
    (r : List (RoseTree (α ⊕ β))) (h : (r.map RoseTree.traceLeafCount).sum = 1) : r ≠ [] := by
  rintro rfl
  simp at h

mutual

/-- **Trace-leaf conservation** for Δ^c cut summands (tree level): each
    contraction replaces an extracted subtree by one `Sum.inr` leaf, so
    crown trace leaves plus trunk trace leaves recover the tree's trace
    leaves plus one per cut. Requires unit-trace-count replacements. -/
theorem cutSummandsG_traceLeafCount
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.traceLeafCount).sum = 1) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map RoseTree.traceLeafCount p.1).sum + RoseTree.traceLeafCount p.2 =
        RoseTree.traceLeafCount t + Multiset.card p.1
  | .node a cs => by
    intro p hp
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsG_traceLeafCount extract hext cs q hq
    cases a with
    | inl x =>
      simp only [RoseTree.traceLeafCount_node_inl]
      omega
    | inr y =>
      have hne : ∀ t r, extract t = some r → r ≠ [] :=
        fun t r h => ne_nil_of_traceLeafCount_sum_one r (hext t r h)
      rcases eq_or_ne cs [] with hcs | hcs
      · subst hcs
        rw [cutListSummandsG_nil] at hq
        obtain rfl := Multiset.mem_singleton.mp hq
        simp
      · have hq2 : q.2 ≠ [] := by
          obtain ⟨t', ts', rfl⟩ := List.exists_cons_of_ne_nil hcs
          exact cutListSummandsG_remainder_ne_nil extract hne t' ts' q hq
        rw [RoseTree.traceLeafCount_node_of_ne_nil (Sum.inr y) q.2 hq2,
            RoseTree.traceLeafCount_node_of_ne_nil (Sum.inr y) cs hcs]
        omega

/-- Mutual aux: trace-leaf conservation for children-list cut summands. -/
theorem cutListSummandsG_traceLeafCount
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.traceLeafCount).sum = 1) :
    ∀ (cs : List (RoseTree (α ⊕ β))), ∀ q ∈ cutListSummandsG extract cs,
      (Multiset.map RoseTree.traceLeafCount q.1).sum + (q.2.map RoseTree.traceLeafCount).sum =
        (cs.map RoseTree.traceLeafCount).sum + Multiset.card q.1
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
    have h1 := augActionG_traceLeafCount extract hext t pr.1 ha
    have h2 := cutListSummandsG_traceLeafCount extract hext ts pr.2 hq'
    rw [Multiset.map_add, Multiset.sum_add, List.map_append, List.sum_append,
        Multiset.card_add, List.map_cons, List.sum_cons]
    omega

/-- Mutual aux: trace-leaf conservation for per-child actions. -/
theorem augActionG_traceLeafCount
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.traceLeafCount).sum = 1) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ a ∈ augActionG extract t,
      (Multiset.map RoseTree.traceLeafCount a.1).sum + (a.2.map RoseTree.traceLeafCount).sum =
        RoseTree.traceLeafCount t + Multiset.card a.1
  | t => by
    intro a ha
    rw [augActionG_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hex : extract t with
      | none => rw [hex] at h; exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hex] at h
        obtain rfl := Multiset.mem_singleton.mp h
        have hr := hext t r hex
        rw [Multiset.map_singleton, Multiset.sum_singleton, hr, Multiset.card_singleton]
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      have h := cutSummandsG_traceLeafCount extract hext t p hp
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

end

mutual

/-- **Crown trace leaves are bounded by the source's** (tree level): the extracted
    crown forest of any cut has no more trace leaves than the whole tree, since
    each crown component is a subtree. Independent of the replacement policy
    (no `hext` hypothesis) — only the crown side is counted. Together with
    `cutSummandsG_traceLeafCount` this forces ≥ 1 fresh trace per cut into the
    trunk (`cutSummandsCN_trunk_traceLeafCount_ge_card`). -/
theorem cutSummandsG_crown_traceLeafCount_le
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map RoseTree.traceLeafCount p.1).sum ≤ RoseTree.traceLeafCount t
  | .node a cs => by
    intro p hp
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact (cutListSummandsG_crown_traceLeafCount_le extract cs q hq).trans
      (RoseTree.traceLeafCount_le_node a cs)

/-- Mutual aux: crown trace-leaf bound for children-list cut summands. -/
theorem cutListSummandsG_crown_traceLeafCount_le
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (cs : List (RoseTree (α ⊕ β))), ∀ q ∈ cutListSummandsG extract cs,
      (Multiset.map RoseTree.traceLeafCount q.1).sum ≤ (cs.map RoseTree.traceLeafCount).sum
  | [] => by
    intro q hq
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    exact Nat.zero_le _
  | t :: ts => by
    intro q hq
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionG_crown_traceLeafCount_le extract t pr.1 ha
    have h2 := cutListSummandsG_crown_traceLeafCount_le extract ts pr.2 hq'
    rw [Multiset.map_add, Multiset.sum_add, List.map_cons, List.sum_cons]
    omega

/-- Mutual aux: crown trace-leaf bound for per-child actions. -/
theorem augActionG_crown_traceLeafCount_le
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ a ∈ augActionG extract t,
      (Multiset.map RoseTree.traceLeafCount a.1).sum ≤ RoseTree.traceLeafCount t
  | t => by
    intro a ha
    rw [augActionG_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hex : extract t with
      | none => rw [hex] at h; exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hex] at h
        obtain rfl := Multiset.mem_singleton.mp h
        simp only [Multiset.map_singleton, Multiset.sum_singleton, le_refl]
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      exact cutSummandsG_crown_traceLeafCount_le extract t p hp

end

/-- The Δ^c extraction policy leaves unit-trace-count replacements. -/
private theorem extractC_traceLeafCount_sum_one (τ : RoseTree (α ⊕ β) → β) :
    ∀ t r, extractC τ t = some r → (r.map RoseTree.traceLeafCount).sum = 1 := by
  intro t r h
  cases t with
  | node x cs =>
    cases x with
    | inl a => rw [extractC_inl] at h; obtain rfl := Option.some.inj h; simp [traceLeaf]
    | inr b => rw [extractC_inr] at h; exact absurd h (by simp)

/-- The Δ^c node-count conservation (tree level), specializing the generic
    `cutSummandsG_numNodes` to `extractC`. -/
private theorem extractC_numNodes_sum_one (τ : RoseTree (α ⊕ β) → β) :
    ∀ t r, extractC τ t = some r → (r.map RoseTree.numNodes).sum = 1 := by
  intro t r h
  cases t with
  | node x cs =>
    cases x with
    | inl a => rw [extractC_inl] at h; obtain rfl := Option.some.inj h; simp [traceLeaf]
    | inr b => rw [extractC_inr] at h; exact absurd h (by simp)

end ConnesKreimer

/-! ### Nonplanar descent -/

variable {α β : Type*}

/-- **Trace-leaf conservation** for the nonplanar Δ^c cuts: each contraction
    adds exactly one `Sum.inr` leaf to the trunk (MCB Lemma 1.6.3). -/
theorem cutSummandsCN_traceLeafCount (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map Nonplanar.traceLeafCount).sum + p.2.traceLeafCount =
        T.traceLeafCount + Multiset.card p.1 := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := ConnesKreimer.cutSummandsG_traceLeafCount _
    (ConnesKreimer.extractC_traceLeafCount_sum_one (τ ∘ Nonplanar.mk)) T₀ q hq
  show ((q.1.map Nonplanar.mk).map Nonplanar.traceLeafCount).sum +
      (Nonplanar.mk q.2).traceLeafCount =
    (Nonplanar.mk T₀).traceLeafCount + Multiset.card (q.1.map Nonplanar.mk)
  rw [Nonplanar.traceLeafCount_mk, Nonplanar.traceLeafCount_mk, Multiset.card_map,
      Multiset.map_map,
      show q.1.map (Nonplanar.traceLeafCount ∘ Nonplanar.mk) =
          q.1.map RoseTree.traceLeafCount from
        Multiset.map_congr rfl (fun x _ => Nonplanar.traceLeafCount_mk x)]
  exact hcons

/-- **Weight (vertex) conservation** for the nonplanar Δ^c cuts: crown
    vertices plus trunk vertices recover the tree vertices plus one
    replacement trace leaf per cut (MCB Lemma 1.6.3). -/
theorem cutSummandsCN_numNodes (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map Nonplanar.numNodes).sum + p.2.numNodes =
        T.numNodes + Multiset.card p.1 := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := ConnesKreimer.cutSummandsG_numNodes _
    (ConnesKreimer.extractC_numNodes_sum_one (τ ∘ Nonplanar.mk)) T₀ q hq
  show ((q.1.map Nonplanar.mk).map Nonplanar.numNodes).sum +
      (Nonplanar.mk q.2).numNodes =
    (Nonplanar.mk T₀).numNodes + Multiset.card (q.1.map Nonplanar.mk)
  rw [Nonplanar.numNodes_mk, Nonplanar.numNodes_mk, Multiset.card_map, Multiset.map_map,
      show q.1.map (Nonplanar.numNodes ∘ Nonplanar.mk) = q.1.map RoseTree.numNodes from
        Multiset.map_congr rfl (fun x _ => Nonplanar.numNodes_mk x)]
  exact hcons

/-- The **number of contractions** in a Δ^c cut summand: one per extracted
    crown component (MCB; `numContractions` in the legacy `AdmissibleCut`). -/
def Cut.numContractions (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℕ :=
  Multiset.card p.1

/-- The **Minimal-Search depth** of a Δ^c cut summand (MCB §1.5.2): the total
    extraction depth `Σ d_{v_i}`, read off the trunk's trace markers. The Δ^c
    quotient places a trace leaf at each cut site at *exactly* the cut depth, so
    the trunk's `traceDepthSum` is the signed `+d` extraction cost of MCB rule 1.
    Under Internal Merge the matching `−d` quotient term (rule 2) references this
    same value and cancels it (cost 0); Sideward Merge incurs it uncancelled
    (cost > 0, `Cut.depthC_pos`). Depends only on the trunk `p.2`, like
    `Cut.numContractions` depends only on the crown. -/
def Cut.depthC (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℕ :=
  p.2.traceDepthSum

/-- **Lexical (non-trace) vertex conservation**: combining weight and
    trace-leaf conservation, the trace leaf added at each cut is excluded
    from the lexical count exactly when the vertex it replaced is removed,
    so non-trace vertices are conserved with no correction term. Stated
    additively to avoid truncated ℕ subtraction. -/
theorem cutSummandsCN_lexical_conservation (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map Nonplanar.traceLeafCount).sum + p.2.traceLeafCount + T.numNodes =
        (p.1.map Nonplanar.numNodes).sum + p.2.numNodes + T.traceLeafCount := by
  intro p hp
  have hw := cutSummandsCN_numNodes τ T p hp
  have ht := cutSummandsCN_traceLeafCount τ T p hp
  omega

/-- **Crown trace leaves bounded by the source's**, descended to `Nonplanar`:
    the extracted crown forest of a Δ^c cut has no more trace markers than `T`.
    (Each crown component is a subtree of `T`.) -/
theorem cutSummandsCN_crown_traceLeafCount_le (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map Nonplanar.traceLeafCount).sum ≤ T.traceLeafCount := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hle := ConnesKreimer.cutSummandsG_crown_traceLeafCount_le
    (ConnesKreimer.extractC (τ ∘ Nonplanar.mk)) T₀ q hq
  show ((q.1.map Nonplanar.mk).map Nonplanar.traceLeafCount).sum ≤
    (Nonplanar.mk T₀).traceLeafCount
  rw [Nonplanar.traceLeafCount_mk, Multiset.map_map,
      show q.1.map (Nonplanar.traceLeafCount ∘ Nonplanar.mk) =
          q.1.map RoseTree.traceLeafCount from
        Multiset.map_congr rfl (fun x _ => Nonplanar.traceLeafCount_mk x)]
  exact hle

/-- **Each Δ^c contraction leaves ≥ 1 trace marker in the trunk** (MCB Lemma
    1.6.3 corollary): the trunk's trace count is at least the number of cuts.
    From trace-leaf conservation (`Σtrace(crown) + trace(trunk) = trace(T) + #cuts`)
    and the crown bound (`Σtrace(crown) ≤ trace(T)`). -/
theorem cutSummandsCN_trunk_traceLeafCount_ge_card (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, Multiset.card p.1 ≤ p.2.traceLeafCount := by
  intro p hp
  have hcons := cutSummandsCN_traceLeafCount τ T p hp
  have hle := cutSummandsCN_crown_traceLeafCount_le τ T p hp
  omega

/-! ### Non-degeneracy: lexical-rooted pieces have a non-trace vertex

The single-cut α extraction identity (eq. 1.6.8) needs that each piece (the
extracted subtree, the trunk, the whole tree) has at least one non-trace
vertex, so that `accCountC = #V − 1 − #trace` does not truncate. Crown
components are always `Sum.inl`-rooted (the Δ^c policy declines to cut trace
nodes), and the trunk keeps the tree's root. -/

end RootedTree

namespace RootedTree

namespace ConnesKreimer

variable {α β : Type*}

mutual
/-- Every crown component of a cut is one the policy chose to extract. -/
theorem cutSummandsG_crown_isSome
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t,
      ∀ Tv ∈ p.1, extract Tv ≠ none
  | .node a cs => by
    intro p hp Tv hTv
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact cutListSummandsG_crown_isSome extract cs q hq Tv hTv
theorem cutListSummandsG_crown_isSome
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (cs : List (RoseTree (α ⊕ β))), ∀ q ∈ cutListSummandsG extract cs,
      ∀ Tv ∈ q.1, extract Tv ≠ none
  | [] => by
    intro q hq Tv hTv
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    exact absurd hTv (Multiset.notMem_zero Tv)
  | t :: ts => by
    intro q hq Tv hTv
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    rcases Multiset.mem_add.mp hTv with h | h
    · exact augActionG_crown_isSome extract t pr.1 ha Tv h
    · exact cutListSummandsG_crown_isSome extract ts pr.2 hq' Tv h
theorem augActionG_crown_isSome
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ a ∈ augActionG extract t,
      ∀ Tv ∈ a.1, extract Tv ≠ none
  | t => by
    intro a ha Tv hTv
    rw [augActionG_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hex : extract t with
      | none => rw [hex] at h; exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hex] at h
        obtain rfl := Multiset.mem_singleton.mp h
        obtain rfl := Multiset.mem_singleton.mp hTv
        rw [hex]; exact Option.some_ne_none r
    · obtain ⟨pp, hpp, rfl⟩ := Multiset.mem_map.mp h
      exact cutSummandsG_crown_isSome extract t pp hpp Tv hTv
end

/-- The Δ^c policy extracts only `Sum.inl`-rooted (lexical) subtrees. -/
theorem extractC_ne_none_imp_inl (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β))
    (h : extractC τ t ≠ none) : ∃ a cs, t = RoseTree.node (Sum.inl a) cs := by
  cases t with
  | node x cs =>
    cases x with
    | inl a => exact ⟨a, cs, rfl⟩
    | inr b => rw [extractC_inr] at h; exact absurd rfl h

end ConnesKreimer

/-! ### α extraction identity (MCB eq. 1.6.8) -/

variable {α β : Type*}

/-- Crown components of a Δ^c cut are lexical-rooted, hence have strictly
    more vertices than trace leaves. -/
theorem cutSummandsCN_crown_traceLeafCount_lt_numNodes (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, ∀ Tv ∈ p.1, Tv.traceLeafCount < Tv.numNodes := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp Tv hTv
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  change Tv ∈ q.1.map Nonplanar.mk at hTv
  obtain ⟨Tv₀, hTv₀, rfl⟩ := Multiset.mem_map.mp hTv
  have hne := ConnesKreimer.cutSummandsG_crown_isSome _ T₀ q hq Tv₀ hTv₀
  obtain ⟨a, cs, rfl⟩ := ConnesKreimer.extractC_ne_none_imp_inl (τ ∘ Nonplanar.mk) Tv₀ hne
  rw [Nonplanar.traceLeafCount_mk, Nonplanar.numNodes_mk]
  exact RoseTree.traceLeafCount_lt_numNodes_of_inl a cs

/-- A Δ^c cut never touches the root: the trunk keeps the tree's root label. -/
theorem cutSummandsCN_trunk_rootValue (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, p.2.rootValue = T.rootValue := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  cases T₀ with
  | node a cs =>
    rw [ConnesKreimer.cutSummandsG_node] at hq
    obtain ⟨q', hq', rfl⟩ := Multiset.mem_map.mp hq
    show (Nonplanar.mk (RoseTree.node a q'.2)).rootValue =
      (Nonplanar.mk (RoseTree.node a cs)).rootValue
    rw [Nonplanar.rootValue_mk, Nonplanar.rootValue_mk, RoseTree.value_node,
        RoseTree.value_node]

/-- **Single-cut accessible-term extraction** (MCB eq. 1.6.8): contracting one
    accessible subtree `Tv` out of a lexical-rooted syntactic object splits its
    accessible terms as `αᶜ(T) = αᶜ(Tv) + αᶜ(T/^c Tv) + 1` — the `+1` is the
    contraction itself. Uses `accCountC` throughout (the trace placeholder left
    at the cut site is not an accessible term). -/
theorem cutSummandsCN_accCountC_single (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) (a₀ : α) (F₀ : Forest (Nonplanar (α ⊕ β)))
    (hT : T = Nonplanar.node (Sum.inl a₀) F₀)
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (Tv : Nonplanar (α ⊕ β)) (hcard : p.1 = {Tv}) :
    T.accCountC = Tv.accCountC + p.2.accCountC + 1 := by
  have hw := cutSummandsCN_numNodes τ T p hp
  have hl := cutSummandsCN_traceLeafCount τ T p hp
  have hTv_lt : Tv.traceLeafCount < Tv.numNodes :=
    cutSummandsCN_crown_traceLeafCount_lt_numNodes τ T p hp Tv
      (by rw [hcard]; exact Multiset.mem_singleton_self Tv)
  have hT_root : T.rootValue = Sum.inl a₀ := by
    rw [hT, Nonplanar.rootValue_node]
  have hT_lt : T.traceLeafCount < T.numNodes :=
    Nonplanar.traceLeafCount_lt_numNodes_of_rootInl T a₀ hT_root
  have hp2_lt : p.2.traceLeafCount < p.2.numNodes :=
    Nonplanar.traceLeafCount_lt_numNodes_of_rootInl p.2 a₀
      ((cutSummandsCN_trunk_rootValue τ T p hp).trans hT_root)
  rw [hcard] at hw hl
  simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton] at hw hl
  simp only [Nonplanar.accCountC_eq, Nonplanar.accCount_eq_numNodes_sub_one]
  omega

/-- **Two-cut accessible-term extraction** (MCB eq. 1.6.8 for a 2-edge admissible
    cut): contracting two accessible subtrees `Tv`, `Tw` adds two contractions,
    `αᶜ(T) = αᶜ(Tv) + αᶜ(Tw) + αᶜ(T/^c {Tv,Tw}) + 2`. Used for Sideward Merge 3(a). -/
theorem cutSummandsCN_accCountC_pair (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) (a₀ : α) (F₀ : Forest (Nonplanar (α ⊕ β)))
    (hT : T = Nonplanar.node (Sum.inl a₀) F₀)
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (Tv Tw : Nonplanar (α ⊕ β)) (hcard : p.1 = {Tv, Tw}) :
    T.accCountC = Tv.accCountC + Tw.accCountC + p.2.accCountC + 2 := by
  have hw := cutSummandsCN_numNodes τ T p hp
  have hl := cutSummandsCN_traceLeafCount τ T p hp
  have hTv_lt : Tv.traceLeafCount < Tv.numNodes :=
    cutSummandsCN_crown_traceLeafCount_lt_numNodes τ T p hp Tv
      (by rw [hcard]; exact Multiset.mem_cons_self Tv {Tw})
  have hTw_lt : Tw.traceLeafCount < Tw.numNodes :=
    cutSummandsCN_crown_traceLeafCount_lt_numNodes τ T p hp Tw
      (by rw [hcard]; exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self Tw))
  have hT_root : T.rootValue = Sum.inl a₀ := by
    rw [hT, Nonplanar.rootValue_node]
  have hT_lt : T.traceLeafCount < T.numNodes :=
    Nonplanar.traceLeafCount_lt_numNodes_of_rootInl T a₀ hT_root
  have hp2_lt : p.2.traceLeafCount < p.2.numNodes :=
    Nonplanar.traceLeafCount_lt_numNodes_of_rootInl p.2 a₀
      ((cutSummandsCN_trunk_rootValue τ T p hp).trans hT_root)
  rw [hcard] at hw hl
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_cons,
    Multiset.card_singleton] at hw hl
  simp only [Nonplanar.accCountC_eq, Nonplanar.accCount_eq_numNodes_sub_one]
  omega

/-! ### Minimal-Search positivity (MCB Prop 1.5.1, Sideward direction) -/

/-- **A proper Δ^c cut of a lexical-rooted object costs ≥ 1** (MCB Prop 1.5.1).
    The trunk keeps the tree's lexical root (`cutSummandsCN_trunk_rootValue`), so
    each of its `#cuts ≥ 1` fresh trace markers sits at depth ≥ 1; hence the
    Minimal-Search depth `Cut.depthC p = Σ d_{v_i} ≥ #cuts ≥ 1`. This is the
    uncancelled Sideward cost that vanishes at ε → 0, leaving only the cost-0
    External and Internal Merges. -/
theorem Cut.depthC_pos (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) (a₀ : α)
    (hT : T.rootValue = Sum.inl a₀)
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (hproper : p.1 ≠ 0) :
    1 ≤ Cut.depthC p := by
  have htrunk_root : p.2.rootValue = Sum.inl a₀ :=
    (cutSummandsCN_trunk_rootValue τ T p hp).trans hT
  have h1 : Multiset.card p.1 ≤ p.2.traceLeafCount :=
    cutSummandsCN_trunk_traceLeafCount_ge_card τ T p hp
  have h2 : p.2.traceLeafCount ≤ p.2.traceDepthSum :=
    Nonplanar.traceLeafCount_le_traceDepthSum_of_rootInl p.2 a₀ htrunk_root
  have h3 : 1 ≤ Multiset.card p.1 := by
    rw [Nat.one_le_iff_ne_zero, Ne, Multiset.card_eq_zero]; exact hproper
  show 1 ≤ p.2.traceDepthSum
  omega

/-! ### Signed Minimal-Search cost (MCB §1.5.2 rules 1–2)

The cost of a Merge `𝔐(α,β)` sums the *signed* depth-costs of its two operands.
An extracted accessible term costs `+d` (rule 1); a contraction quotient costs
`−d` (rule 2). Internal Merge re-grafts an extracted crown with its own quotient,
so the two costs of the *same* cut cancel; Sideward Merge grafts a crown with a
non-matching partner, leaving `+d` uncancelled. -/

/-- **Extraction cost** of a Δ^c cut (MCB rule 1): pulling out the crown costs
    `+d`, the cut depth `Cut.depthC`. Signed (ℤ) so it can cancel the quotient
    cost under Internal Merge. -/
def Cut.extractionCost (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℤ :=
  (Cut.depthC p : ℤ)

/-- **Quotient cost** of a Δ^c cut (MCB rule 2): the contraction quotient (trunk)
    costs `−d` — a deep quotient is close to the whole tree, hence cheap. The
    negative companion to `Cut.extractionCost`. -/
def Cut.quotientCost (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℤ :=
  -(Cut.depthC p : ℤ)

/-- **Internal Merge cancellation** (MCB Prop 1.5.1, IM bullet): re-merging an
    extracted crown `T_v` with its OWN quotient `T_i/T_v` sums the two signed
    costs of the *same* cut, `(+d) + (−d) = 0` — the cost-0 that survives ε → 0.
    Derives from the two signed rules, not stipulated. -/
theorem Cut.extractionCost_add_quotientCost
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) :
    Cut.extractionCost p + Cut.quotientCost p = 0 := by
  simp only [Cut.extractionCost, Cut.quotientCost, add_neg_cancel]

/-- **Sideward Merge cost is positive** (MCB Prop 1.5.1, Sideward bullets):
    grafting an extracted crown of a lexical-rooted object with a non-matching
    partner leaves the `+d` extraction cost uncancelled (no quotient operand to
    supply the `−d`). Vanishes at ε → 0. -/
theorem Cut.extractionCost_pos (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β))
    (a₀ : α) (hT : T.rootValue = Sum.inl a₀)
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (hproper : p.1 ≠ 0) :
    0 < Cut.extractionCost p := by
  have h := Cut.depthC_pos τ T a₀ hT p hp hproper
  simp only [Cut.extractionCost]
  exact_mod_cast h

end RootedTree
