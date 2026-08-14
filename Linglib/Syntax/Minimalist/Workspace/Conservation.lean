/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Conservation
import Linglib.Syntax.Minimalist.Workspace.TraceMeasures

open RoseTree RoseTree.Nonplanar

/-!
# Merge economy corollaries of the Δ^c conservation laws
[marcolli-chomsky-berwick-2025]

The accessible-term extraction identities and Minimal-Search costs of MCB
§1.5–1.6, in the `accCountC`/`αᶜ` letter vocabulary
(`Workspace/TraceMeasures.lean`), derived from the conservation laws of
the cut enumeration (`Core/Combinatorics/RootedTree/Conservation.lean`).

## Main results

* `ConnesKreimer.cutSummandsCN_accCountC_single` / `_pair` — the single- and
  two-cut accessible-term extraction identities (MCB eq. 1.6.8):
  `αᶜ(T) = αᶜ(Tv) + αᶜ(T/^c Tv) + 1`.
* `ConnesKreimer.Cut.depthC_pos` — a proper Δ^c cut of a lexical-rooted
  object has Minimal-Search depth ≥ 1 (MCB Prop 1.5.1).
* `ConnesKreimer.Cut.extractionCost`, `Cut.quotientCost`, and the Internal
  Merge cancellation `Cut.extractionCost_add_quotientCost` (MCB §1.5.2
  rules 1–2); Sideward Merge's uncancelled positive cost
  (`Cut.extractionCost_pos`).
-/

namespace ConnesKreimer

/-! ### α extraction identity (MCB eq. 1.6.8) -/

variable {α β : Type*}

/-- **Single-cut accessible-term extraction** (MCB eq. 1.6.8): contracting one
    accessible subtree `Tv` out of a lexical-rooted syntactic object splits its
    accessible terms as `αᶜ(T) = αᶜ(Tv) + αᶜ(T/^c Tv) + 1` — the `+1` is the
    contraction itself. Uses `accCountC` throughout (the trace placeholder left
    at the cut site is not an accessible term). -/
theorem cutSummandsCN_accCountC_single (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) (a₀ : α) (F₀ : Multiset (Nonplanar (α ⊕ β)))
    (hT : T = Nonplanar.node (Sum.inl a₀) F₀)
    (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
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
    (T : Nonplanar (α ⊕ β)) (a₀ : α) (F₀ : Multiset (Nonplanar (α ⊕ β)))
    (hT : T = Nonplanar.node (Sum.inl a₀) F₀)
    (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
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
    (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
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
def Cut.extractionCost (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℤ :=
  (Cut.depthC p : ℤ)

/-- **Quotient cost** of a Δ^c cut (MCB rule 2): the contraction quotient (trunk)
    costs `−d` — a deep quotient is close to the whole tree, hence cheap. The
    negative companion to `Cut.extractionCost`. -/
def Cut.quotientCost (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℤ :=
  -(Cut.depthC p : ℤ)

/-- **Internal Merge cancellation** (MCB Prop 1.5.1, IM bullet): re-merging an
    extracted crown `T_v` with its OWN quotient `T_i/T_v` sums the two signed
    costs of the *same* cut, `(+d) + (−d) = 0` — the cost-0 that survives ε → 0.
    Derives from the two signed rules, not stipulated. -/
theorem Cut.extractionCost_add_quotientCost
    (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) :
    Cut.extractionCost p + Cut.quotientCost p = 0 := by
  simp only [Cut.extractionCost, Cut.quotientCost, add_neg_cancel]

/-- **Sideward Merge cost is positive** (MCB Prop 1.5.1, Sideward bullets):
    grafting an extracted crown of a lexical-rooted object with a non-matching
    partner leaves the `+d` extraction cost uncancelled (no quotient operand to
    supply the `−d`). Vanishes at ε → 0. -/
theorem Cut.extractionCost_pos (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β))
    (a₀ : α) (hT : T.rootValue = Sum.inl a₀)
    (p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (hproper : p.1 ≠ 0) :
    0 < Cut.extractionCost p := by
  have h := Cut.depthC_pos τ T a₀ hT p hp hproper
  simp only [Cut.extractionCost]
  exact_mod_cast h

end ConnesKreimer
