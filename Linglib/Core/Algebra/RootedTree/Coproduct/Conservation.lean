import Linglib.Core.Algebra.RootedTree.Coproduct.TraceNonplanar
import Linglib.Core.Combinatorics.RootedTree.TraceCounting

set_option autoImplicit false

/-!
# Conservation laws for the Δ^c (contraction) cut enumeration
[marcolli-chomsky-berwick-2025]

Size bookkeeping for the trace-preserving admissible-cut coproduct
`cutSummandsCN` on `Nonplanar (α ⊕ β)`. A cut summand `p = (p.1, p.2)`
splits a syntactic object into a *crown forest* `p.1` (the extracted
subtrees) and a *trunk* `p.2` (the contraction quotient, carrying one
trace-marker leaf per cut). The two primitive conservation laws are:

* **weight** (`cutSummandsCN_weight`): `Σ #V(crown) + #V(trunk) = #V(T) + #cuts`
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
* `cutSummandsCN_traceLeafCount`, `cutSummandsCN_weight` — descended to
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

/-! ### Planar-level trace-leaf conservation -/

private theorem traceLeafCountList_append (l₁ l₂ : List (Planar (α ⊕ β))) :
    Planar.traceLeafCountList (l₁ ++ l₂) =
      Planar.traceLeafCountList l₁ + Planar.traceLeafCountList l₂ := by
  induction l₁ with
  | nil => show Planar.traceLeafCountList l₂ = 0 + Planar.traceLeafCountList l₂; omega
  | cons t ts ih =>
    show Planar.traceLeafCount t + Planar.traceLeafCountList (ts ++ l₂) =
      Planar.traceLeafCount t + Planar.traceLeafCountList ts + Planar.traceLeafCountList l₂
    rw [ih]; omega

/-- Under nonempty-replacement extraction, every per-child action leaves a
    nonempty remainder. -/
private theorem augActionG_remainder_ne_nil
    (extract : Planar (α ⊕ β) → Option (List (Planar (α ⊕ β))))
    (hne : ∀ t r, extract t = some r → r ≠ []) (t : Planar (α ⊕ β)) :
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
    (extract : Planar (α ⊕ β) → Option (List (Planar (α ⊕ β))))
    (hne : ∀ t r, extract t = some r → r ≠ [])
    (t : Planar (α ⊕ β)) (ts : List (Planar (α ⊕ β))) :
    ∀ q ∈ cutListSummandsG extract (t :: ts), q.2 ≠ [] := by
  intro q hq
  rw [cutListSummandsG_cons] at hq
  obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
  obtain ⟨ha, _⟩ := Multiset.mem_product.mp hpr
  have h1 := augActionG_remainder_ne_nil extract hne t pr.1 ha
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil h1
  show pr.1.2 ++ pr.2.2 ≠ []
  simp [hc]

/-- `traceLeafCountList r = 1` forces `r` nonempty. -/
private theorem ne_nil_of_traceLeafCountList_one
    (r : List (Planar (α ⊕ β))) (h : Planar.traceLeafCountList r = 1) : r ≠ [] := by
  rintro rfl
  rw [Planar.traceLeafCountList_nil] at h
  omega

mutual

/-- **Trace-leaf conservation** for Δ^c cut summands (tree level): each
    contraction replaces an extracted subtree by one `Sum.inr` leaf, so
    crown trace leaves plus trunk trace leaves recover the tree's trace
    leaves plus one per cut. Requires unit-trace-count replacements. -/
theorem cutSummandsG_traceLeafCount
    (extract : Planar (α ⊕ β) → Option (List (Planar (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → Planar.traceLeafCountList r = 1) :
    ∀ (t : Planar (α ⊕ β)), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map Planar.traceLeafCount p.1).sum + Planar.traceLeafCount p.2 =
        Planar.traceLeafCount t + Multiset.card p.1
  | .node a cs => by
    intro p hp
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsG_traceLeafCount extract hext cs q hq
    cases a with
    | inl x =>
      show (Multiset.map Planar.traceLeafCount q.1).sum +
          Planar.traceLeafCount (.node (Sum.inl x) q.2) =
        Planar.traceLeafCount (.node (Sum.inl x) cs) + Multiset.card q.1
      rw [Planar.traceLeafCount_inl, Planar.traceLeafCount_inl]
      omega
    | inr y =>
      have hne : ∀ t r, extract t = some r → r ≠ [] :=
        fun t r h => ne_nil_of_traceLeafCountList_one r (hext t r h)
      rcases eq_or_ne cs [] with hcs | hcs
      · subst hcs
        rw [cutListSummandsG_nil] at hq
        obtain rfl := Multiset.mem_singleton.mp hq
        rfl
      · have hq2 : q.2 ≠ [] := by
          obtain ⟨t', ts', rfl⟩ := List.exists_cons_of_ne_nil hcs
          exact cutListSummandsG_remainder_ne_nil extract hne t' ts' q hq
        show (Multiset.map Planar.traceLeafCount q.1).sum +
            Planar.traceLeafCount (.node (Sum.inr y) q.2) =
          Planar.traceLeafCount (.node (Sum.inr y) cs) + Multiset.card q.1
        rw [Planar.traceLeafCount_node_of_ne_nil (Sum.inr y) q.2 hq2,
            Planar.traceLeafCount_node_of_ne_nil (Sum.inr y) cs hcs]
        omega

/-- Mutual aux: trace-leaf conservation for children-list cut summands. -/
theorem cutListSummandsG_traceLeafCount
    (extract : Planar (α ⊕ β) → Option (List (Planar (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → Planar.traceLeafCountList r = 1) :
    ∀ (cs : List (Planar (α ⊕ β))), ∀ q ∈ cutListSummandsG extract cs,
      (Multiset.map Planar.traceLeafCount q.1).sum + Planar.traceLeafCountList q.2 =
        Planar.traceLeafCountList cs + Multiset.card q.1
  | [] => by
    intro q hq
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    rfl
  | t :: ts => by
    intro q hq
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionG_traceLeafCount extract hext t pr.1 ha
    have h2 := cutListSummandsG_traceLeafCount extract hext ts pr.2 hq'
    show (Multiset.map Planar.traceLeafCount (pr.1.1 + pr.2.1)).sum +
        Planar.traceLeafCountList (pr.1.2 ++ pr.2.2) =
      (Planar.traceLeafCount t + Planar.traceLeafCountList ts) +
        Multiset.card (pr.1.1 + pr.2.1)
    rw [Multiset.map_add, Multiset.sum_add, traceLeafCountList_append,
        Multiset.card_add]
    omega

/-- Mutual aux: trace-leaf conservation for per-child actions. -/
theorem augActionG_traceLeafCount
    (extract : Planar (α ⊕ β) → Option (List (Planar (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → Planar.traceLeafCountList r = 1) :
    ∀ (t : Planar (α ⊕ β)), ∀ a ∈ augActionG extract t,
      (Multiset.map Planar.traceLeafCount a.1).sum + Planar.traceLeafCountList a.2 =
        Planar.traceLeafCount t + Multiset.card a.1
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
        show (Multiset.map Planar.traceLeafCount {t}).sum + Planar.traceLeafCountList r =
          Planar.traceLeafCount t + Multiset.card {t}
        rw [Multiset.map_singleton, Multiset.sum_singleton, hr, Multiset.card_singleton]
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      have h := cutSummandsG_traceLeafCount extract hext t p hp
      show (Multiset.map Planar.traceLeafCount p.1).sum +
          Planar.traceLeafCountList [p.2] = Planar.traceLeafCount t + Multiset.card p.1
      simp only [Planar.traceLeafCountList_cons, Planar.traceLeafCountList_nil]
      omega

end

/-- The Δ^c extraction policy leaves unit-trace-count replacements. -/
private theorem extractC_traceLeafCountList_one (τ : Planar (α ⊕ β) → β) :
    ∀ t r, extractC τ t = some r → Planar.traceLeafCountList r = 1 := by
  intro t r h
  cases t with
  | node x cs =>
    cases x with
    | inl a => rw [extractC_inl] at h; obtain rfl := Option.some.inj h; rfl
    | inr b => rw [extractC_inr] at h; exact absurd h (by simp)

/-- The Δ^c weight conservation (planar level), specializing the generic
    `cutSummandsG_weight` to `extractC`. -/
private theorem extractC_weightList_one (τ : Planar (α ⊕ β) → β) :
    ∀ t r, extractC τ t = some r → Planar.weightList r = 1 := by
  intro t r h
  cases t with
  | node x cs =>
    cases x with
    | inl a => rw [extractC_inl] at h; obtain rfl := Option.some.inj h; rfl
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
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : Planar (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := ConnesKreimer.cutSummandsG_traceLeafCount _
    (ConnesKreimer.extractC_traceLeafCountList_one (τ ∘ Nonplanar.mk)) T₀ q hq
  show ((q.1.map Nonplanar.mk).map Nonplanar.traceLeafCount).sum +
      (Nonplanar.mk q.2).traceLeafCount =
    (Nonplanar.mk T₀).traceLeafCount + Multiset.card (q.1.map Nonplanar.mk)
  rw [Nonplanar.traceLeafCount_mk, Nonplanar.traceLeafCount_mk, Multiset.card_map,
      Multiset.map_map,
      show q.1.map (Nonplanar.traceLeafCount ∘ Nonplanar.mk) =
          q.1.map Planar.traceLeafCount from
        Multiset.map_congr rfl (fun x _ => Nonplanar.traceLeafCount_mk x)]
  exact hcons

/-- **Weight (vertex) conservation** for the nonplanar Δ^c cuts: crown
    vertices plus trunk vertices recover the tree vertices plus one
    replacement trace leaf per cut (MCB Lemma 1.6.3). -/
theorem cutSummandsCN_weight (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map Nonplanar.weight).sum + p.2.weight =
        T.weight + Multiset.card p.1 := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : Planar (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := ConnesKreimer.cutSummandsG_weight _
    (ConnesKreimer.extractC_weightList_one (τ ∘ Nonplanar.mk)) T₀ q hq
  show ((q.1.map Nonplanar.mk).map Nonplanar.weight).sum +
      (Nonplanar.mk q.2).weight =
    (Nonplanar.mk T₀).weight + Multiset.card (q.1.map Nonplanar.mk)
  rw [Nonplanar.weight_mk, Nonplanar.weight_mk, Multiset.card_map, Multiset.map_map,
      show q.1.map (Nonplanar.weight ∘ Nonplanar.mk) = q.1.map Planar.weight from
        Multiset.map_congr rfl (fun x _ => Nonplanar.weight_mk x)]
  exact hcons

/-- The **number of contractions** in a Δ^c cut summand: one per extracted
    crown component (MCB; `numContractions` in the legacy `AdmissibleCut`). -/
def Cut.numContractions (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℕ :=
  Multiset.card p.1

/-- **Lexical (non-trace) vertex conservation**: combining weight and
    trace-leaf conservation, the trace leaf added at each cut is excluded
    from the lexical count exactly when the vertex it replaced is removed,
    so non-trace vertices are conserved with no correction term. Stated
    additively to avoid truncated ℕ subtraction. -/
theorem cutSummandsCN_lexical_conservation (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map Nonplanar.traceLeafCount).sum + p.2.traceLeafCount + T.weight =
        (p.1.map Nonplanar.weight).sum + p.2.weight + T.traceLeafCount := by
  intro p hp
  have hw := cutSummandsCN_weight τ T p hp
  have ht := cutSummandsCN_traceLeafCount τ T p hp
  omega

end RootedTree
