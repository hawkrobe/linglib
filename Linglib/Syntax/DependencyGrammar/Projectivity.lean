/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Dominance
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Sort

/-!
# Projectivity and its relaxations

A dependency graph is projective when the positions each node dominates form
a contiguous stretch of the sentence. Natural language is not always
projective, so the literature weakens the constraint in several directions.
Planarity bans crossing arcs, well-nestedness bans interleaved subtrees, and
gap degree counts the discontinuities a single node may show.

In this file we define those constraints and prove the inclusions among them
that hold on trees. The witnesses separating the constraints are the source
papers' own figures, and live in their study files.

## Main declarations

* `Alternate` — the alternation `a < c < b < d` that both binary constraints
  forbid.
* `Graph.IsProjective` — every `Graph.dominated` set is an interval
  (Definition 3).
* `Graph.IsPlanar` — no two links cross (Definition 4), the Link Grammar
  notion, traced there to [melcuk-1988].
* `Graph.Interleave`, `Graph.IsWellNested` — Definition 8.
* `Graph.gapDegree` — Definitions 6–7. Gap degree + 1 is the block-degree,
  the fan-out of the LCFRS rule extracted for that node.
* `Graph.IsProjective.isPlanar`, `Graph.IsPlanar.isWellNested` — the §3.5
  chain `projective ⊆ planar ⊆ well-nested` on trees, with
  `Graph.IsProjective.isWellNested` its composite.

## References

[kuhlmann-nivre-2006] — Mildly non-projective dependency structures, source
of the Definition numbers cited above
[kuhlmann-2013] — Mildly non-projective dependency grammar
[melcuk-1988] — Dependency syntax: theory and practice
-/

namespace DependencyGrammar

variable {n : ℕ} (g : Graph n)

/-! ### The binary constraints: projectivity, planarity, well-nestedness -/

/-- A dependency graph is projective if the positions dominated by any one
    position are order-convex. -/
def Graph.IsProjective : Prop := ∀ v, (g.dominated v).OrdConnected

/-- Positions `a b c d` alternate if `a < c < b < d`, so that the pairs
    `{a, b}` and `{c, d}` strictly interleave. -/
abbrev Alternate (a b c d : Fin n) : Prop := a < c ∧ c < b ∧ b < d

/-- A dependency graph is planar if no two links alternate, so that its arcs
    can be drawn above the sentence without crossing. -/
def Graph.IsPlanar : Prop :=
  ∀ ⦃a b c d : Fin n⦄, Linked g a b → Linked g c d → ¬ Alternate a b c d

/-- The subtrees at `v` and `w` interleave if each contributes two positions
    and the two pairs alternate. -/
def Graph.Interleave (v w : Fin n) : Prop :=
  ∃ a ∈ g.dominated v, ∃ b ∈ g.dominated v, ∃ c ∈ g.dominated w, ∃ d ∈ g.dominated w,
    Alternate a b c d

/-- A dependency graph is well-nested if interleaved subtrees are never
    disjoint, one of the two roots always dominating the other. -/
def Graph.IsWellNested : Prop :=
  ∀ v w : Fin n, g.Interleave v w → Dominates g v w ∨ Dominates g w v

/-- Projectivity, unfolded: nothing between two dominated positions escapes. -/
theorem Graph.isProjective_iff :
    g.IsProjective ↔ ∀ v x, Dominates g v x → ∀ y, Dominates g v y →
      ∀ z, x ≤ z → z ≤ y → Dominates g v z := by
  simp [Graph.IsProjective, Set.ordConnected_def, Set.subset_def]

instance : Decidable g.IsProjective := decidable_of_iff _ g.isProjective_iff.symm
instance : Decidable g.IsPlanar := inferInstanceAs (Decidable (∀ _, _))
instance (v w : Fin n) : Decidable (g.Interleave v w) :=
  inferInstanceAs (Decidable (∃ _, _))
instance : Decidable g.IsWellNested := inferInstanceAs (Decidable (∀ _, _))

/-! ### Gap degree -/

/-- The projection of `v`, as position values. -/
def Graph.projectionVals (v : Fin n) : List Nat := (g.projection v).map (·.val)

theorem Graph.projectionVals_sortedLT (v : Fin n) :
    (g.projectionVals v).SortedLT := by
  refine List.Pairwise.sortedLT (List.Pairwise.map _ (λ _ _ h => h) ?_)
  exact (List.pairwise_lt_finRange n).filter _

/-- The gap degree of a position counts the discontinuities in its
    projection, the adjacent members more than one position apart. -/
def Graph.gapDegreeAt (v : Fin n) : Nat :=
  ((g.projectionVals v).zip (g.projectionVals v).tail).countP
    (λ p => decide (1 < p.2 - p.1))

/-- The gap degree of a graph is the maximum over its positions. -/
def Graph.gapDegree : Nat := Finset.univ.sup g.gapDegreeAt

/-! ### The hierarchy on trees -/

variable {g}

/-- In a projective graph the head of an arc dominates every position the arc
    spans, since the head dominates both endpoints and is order-convex. -/
theorem Graph.IsProjective.dominates_of_mem_uIcc (hP : g.IsProjective)
    {p t x : Fin n} (h : g.Adj p t) (hx : x ∈ Set.uIcc p t) : Dominates g p x :=
  (hP p).uIcc_subset .refl (.single h) hx

/-- Every projective tree is planar. -/
theorem Graph.IsProjective.isPlanar (hT : g.IsTree) (hP : g.IsProjective) :
    g.IsPlanar := by
  rintro a b c d hL1 hL2 ⟨hac, hcb, hbd⟩
  -- The head of an arc dominates the head of any arc it spans an endpoint of.
  have step : ∀ {p t q u x : Fin n}, g.Adj p t → g.Adj q u →
      x ∈ Set.uIcc p t → (x = q ∨ x = u) → p ≠ x → Dominates g p q := by
    rintro p t q u x h1 h2 hx (rfl | rfl) hne
    exacts [hP.dominates_of_mem_uIcc h1 hx,
            Dominates.to_head hT (hP.dominates_of_mem_uIcc h1 hx) hne h2]
  have hab : c ∈ Set.uIcc a b := Set.mem_uIcc.mpr (.inl ⟨hac.le, hcb.le⟩)
  have hba : c ∈ Set.uIcc b a := Set.mem_uIcc.mpr (.inr ⟨hac.le, hcb.le⟩)
  have hcd : b ∈ Set.uIcc c d := Set.mem_uIcc.mpr (.inl ⟨hcb.le, hbd.le⟩)
  have hdc : b ∈ Set.uIcc d c := Set.mem_uIcc.mpr (.inr ⟨hcb.le, hbd.le⟩)
  rcases hL1 with h1 | h1 <;> rcases hL2 with h2 | h2
  · exact hac.ne (Dominates.antisymm hT.acyclic
      (step h1 h2 hab (.inl rfl) hac.ne) (step h2 h1 hcd (.inr rfl) hcb.ne))
  · exact ((hac.trans hcb).trans hbd).ne (Dominates.antisymm hT.acyclic
      (step h1 h2 hab (.inr rfl) hac.ne) (step h2 h1 hdc (.inr rfl) hbd.ne'))
  · exact hcb.ne' (Dominates.antisymm hT.acyclic
      (step h1 h2 hba (.inl rfl) hcb.ne') (step h2 h1 hcd (.inl rfl) hcb.ne))
  · exact hbd.ne (Dominates.antisymm hT.acyclic
      (step h1 h2 hba (.inr rfl) hcb.ne') (step h2 h1 hdc (.inl rfl) hbd.ne'))

/-- In a planar graph, a link with one endpoint strictly inside the span of
    another link has its other endpoint inside that span too. -/
theorem Graph.IsPlanar.mem_uIcc_of_linked (hPl : g.IsPlanar) {lo hi p q : Fin n}
    (hL : Linked g lo hi) (hL' : Linked g p q)
    (hlp : lo < p) (hph : p < hi) : q ∈ Set.uIcc lo hi := by
  by_contra hq
  have hout : q < lo ∨ hi < q := by
    by_contra hc
    push Not at hc
    exact hq (Set.mem_uIcc.mpr (Or.inl ⟨hc.1, hc.2⟩))
  rcases hout with h | h
  · exact hPl hL'.symm hL ⟨h, hlp, hph⟩
  · exact hPl hL hL' ⟨hlp, hph, h⟩

/-- Planarity forbids a link with one endpoint strictly inside another link's
    span and the other endpoint outside it. -/
theorem Graph.IsPlanar.no_strict_straddle (hPl : g.IsPlanar) {p q p' q' : Fin n}
    (hL : Linked g p q) (hL' : Linked g p' q') (hin : p' ∈ Set.uIcc p q)
    (hne1 : p' ≠ p) (hne2 : p' ≠ q) (hout : q' ∉ Set.uIcc p q) : False := by
  rw [Set.mem_uIcc] at hin
  rcases lt_trichotomy p q with h | rfl | h
  · have hb : p ≤ p' ∧ p' ≤ q := by
      rcases hin with h1 | h2
      · exact h1
      · exact absurd (h2.1.trans h2.2) (not_le.mpr h)
    exact hout (hPl.mem_uIcc_of_linked hL hL'
      (lt_of_le_of_ne hb.1 (Ne.symm hne1)) (lt_of_le_of_ne hb.2 hne2))
  · exact hne1 (by rcases hin with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact le_antisymm h2 h1)
  · have hb : q ≤ p' ∧ p' ≤ p := by
      rcases hin with h1 | h2
      · exact absurd (h1.1.trans h1.2) (not_le.mpr h)
      · exact h2
    rw [Set.uIcc_comm] at hout
    exact hout (hPl.mem_uIcc_of_linked hL.symm hL'
      (lt_of_le_of_ne hb.1 (Ne.symm hne2)) (lt_of_le_of_ne hb.2 hne1))

/-- Every planar tree is well-nested: interleaved subtrees would force a link
    below one of them to straddle a link below the other. -/
theorem Graph.IsPlanar.isWellNested (hT : g.IsTree) (hPl : g.IsPlanar) :
    g.IsWellNested := by
  rintro v w ⟨a, hva, b, hvb, c, hwc, d, hwd, hac, hcb, hbd⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hvw, hwv⟩ := hcon
  have hdis : ∀ {x}, Dominates g v x → Dominates g w x → False :=
    λ h1 h2 => disjoint_dominated hT hvw hwv h1 h2
  have hab : a < b := hac.trans hcb
  -- A link below `w` crosses the boundary of the span of `a` and `b`.
  have hcS : c ∈ Set.uIcc a b := Set.mem_uIcc.mpr (.inl ⟨hac.le, hcb.le⟩)
  have hdS : d ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le, Set.mem_Icc]
    exact λ h => absurd h.2 (not_le.mpr hbd)
  obtain ⟨p, q, hLpq, hwp, hwq, hpS, hqS⟩ := exists_link_across hwc hwd hcS hdS
  rw [Set.uIcc_of_le hab.le, Set.mem_Icc] at hpS hqS
  push Not at hqS
  have hap : a < p := lt_of_le_of_ne hpS.1 (λ h => hdis hva (h ▸ hwp))
  have hpb : p < b := lt_of_le_of_ne hpS.2 (λ h => hdis hvb (h ▸ hwp))
  -- Any link below `v` crossing that link's span contradicts planarity.
  have hfin : ∀ {p' q' : Fin n}, Linked g p' q' → Dominates g v p' →
      p' ∈ Set.uIcc p q → q' ∉ Set.uIcc p q → False := by
    intro p' q' hL' hvp' hin hout
    exact hPl.no_strict_straddle hLpq hL' hin
      (λ h => hdis hvp' (h ▸ hwp)) (λ h => hdis hvp' (h ▸ hwq)) hout
  have hqa0 : q ≠ a := λ h => hdis hva (h ▸ hwq)
  rcases lt_or_gt_of_ne hqa0 with hqa | hqa
  · have h1 : a ∈ Set.uIcc p q := Set.mem_uIcc.mpr (.inr ⟨hqa.le, hap.le⟩)
    have h2 : b ∉ Set.uIcc p q := by
      rw [Set.uIcc_comm, Set.uIcc_of_le (hqa.trans hap).le, Set.mem_Icc]
      exact λ h => absurd h.2 (not_le.mpr hpb)
    obtain ⟨_, _, hL', hvp', _, hin, hout⟩ := exists_link_across hva hvb h1 h2
    exact hfin hL' hvp' hin hout
  · have hbq : b < q := hqS hqa.le
    have h1 : b ∈ Set.uIcc p q := Set.mem_uIcc.mpr (.inl ⟨hpb.le, hbq.le⟩)
    have h2 : a ∉ Set.uIcc p q := by
      rw [Set.uIcc_of_le (hpb.trans hbq).le, Set.mem_Icc]
      exact λ h => absurd h.1 (not_le.mpr hap)
    obtain ⟨_, _, hL', hvp', _, hin, hout⟩ := exists_link_across hvb hva h1 h2
    exact hfin hL' hvp' hin hout

/-- Every projective tree is well-nested, via planarity. -/
theorem Graph.IsProjective.isWellNested (hT : g.IsTree) (hP : g.IsProjective) :
    g.IsWellNested := (hP.isPlanar hT).isWellNested hT

end DependencyGrammar
