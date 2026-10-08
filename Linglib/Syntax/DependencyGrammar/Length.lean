/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.WordOrder
public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Set.Card

/-!
# Dependency length

The length of a dependency is the distance in words between head and dependent. This file defines
the total dependency length of a graph, transports a graph along a permutation of its positions,
and defines the distance from a head to the nearest word of a dependent's yield, dependency length
measured to the boundary of the dependent's phrase. On a projective tree that distance is one
more than the sizes of the yields of the sibling dependents between head and dependent: it is the
block measure `WordOrder.Arrangement.boundaryDist` with yields as blocks.

## Main definitions

* `Graph.totalLength`: the sum of `Nat.dist` over the arcs.
* `Graph.map`: a graph transported along a permutation of its positions; `Graph.mirror` and
  `Graph.linearize` read it in reverse and in a given order.
* `Graph.yieldDist`: the distance from a position to the nearest word of a yield.
* `WordOrder.Arrangement.boundaryDist`: the distance in words between two constituents of given
  lengths in an arrangement.

## Main results

* `Graph.totalLength_map`: transport along an isometry preserves total dependency length.
* `Graph.yieldDist_eq_one_add_sum`: on a projective tree, the yield distance from a head to a
  dependent is one more than the yield sizes of the dependents between them.

## References

* [futrell-levy-gibson-2020]
* [fedzechkina-chu-jaeger-2018]
-/

@[expose] public section

namespace WordOrder.Arrangement

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (a : Arrangement α n) (ℓ : α → ℕ)
  (x y : α)

/-- The distance in words between the closest boundaries of `x` and `y` when each element `c` is
`ℓ c` words long, which is one more than the words of the elements between them and zero from an
element to itself. -/
def boundaryDist : ℕ :=
  if x = y then 0 else
    1 + ∑ c with a.Precedes x c ∧ a.Precedes c y ∨ a.Precedes y c ∧ a.Precedes c x, ℓ c

@[simp] theorem boundaryDist_self : a.boundaryDist ℓ x x = 0 := by simp [boundaryDist]

theorem boundaryDist_comm : a.boundaryDist ℓ x y = a.boundaryDist ℓ y x := by
  simp only [boundaryDist, eq_comm (a := x), or_comm]

/-- Mirroring preserves every distance. -/
@[simp] theorem boundaryDist_mirror : a.mirror.boundaryDist ℓ x y = a.boundaryDist ℓ x y := by
  simp only [boundaryDist, precedes_mirror, and_comm, or_comm]

end WordOrder.Arrangement

namespace DependencyGrammar

open Relation

variable {n : ℕ}

/-- Total dependency length sums `Nat.dist` over all arcs, the quantity dependency-length
    minimisation is about. -/
def Graph.totalLength (g : Graph n) : Nat :=
  ∑ v : Fin n, ∑ w ∈ g.children v, Nat.dist v w

/-- Total dependency length reads only the arc structure, never the
    tokens. -/
theorem Graph.totalLength_words (g : Graph n) (words' : Fin n → Morphology.Word) :
    Graph.totalLength { g with words := words' } = g.totalLength := rfl

/-! ### Transport: same structure, different linearization -/

/-- `g.map σ` transports `g` along the position permutation `σ`. Arcs, tokens and root move
    together, so the labeled structure is unchanged and only the linearization varies. -/
def Graph.map (g : Graph n) (σ : Equiv.Perm (Fin n)) : Graph n :=
  { words := g.words ∘ σ.symm
    label := fun v w ↦ g.label (σ.symm v) (σ.symm w)
    root := σ g.root }

@[simp] theorem Graph.map_adj (g : Graph n) (σ : Equiv.Perm (Fin n))
    (v w : Fin n) : (g.map σ).Adj v w ↔ g.Adj (σ.symm v) (σ.symm w) :=
  Iff.rfl

/-- The mirror image, transported along position reversal. -/
def Graph.mirror (g : Graph n) : Graph n := g.map Fin.revPerm

/-- Transport along an isometry of the positions preserves total dependency length. -/
theorem Graph.totalLength_map (g : Graph n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ v w : Fin n, Nat.dist (σ v) (σ w) = Nat.dist v w) :
    (g.map σ).totalLength = g.totalLength := by
  unfold totalLength
  simp only [Graph.children, Finset.sum_filter]
  refine Fintype.sum_equiv σ.symm _ _ (fun v ↦ ?_)
  refine Fintype.sum_equiv σ.symm _ _ (fun w ↦ ?_)
  simp only [map_adj]
  by_cases h : g.Adj (σ.symm v) (σ.symm w) <;>
    simp [h, ← hσ (σ.symm v) (σ.symm w)]

/-- Position reversal preserves `Nat.dist`. -/
theorem _root_.Fin.dist_rev_rev (v w : Fin n) :
    Nat.dist v.rev w.rev = Nat.dist v w := by
  have hv := v.isLt
  have hw := w.isLt
  simp only [Nat.dist, Fin.val_rev]
  omega

/-- The mirror image of a graph has the same total dependency length —
    the head-final preference is the exact mirror of the head-initial one
    ([futrell-levy-gibson-2020], examples (7)–(8)). -/
theorem Graph.totalLength_mirror (g : Graph n) :
    g.mirror.totalLength = g.totalLength :=
  g.totalLength_map _ Fin.dist_rev_rev

/-- The graph read in the order `order`, which lists every position once. The token at
    position `p` is the token of `g` at `order[p]`, arcs and root following. -/
def Graph.linearize (g : Graph n) (order : List (Fin n)) (h : order.Perm (List.finRange n)) :
    Graph n :=
  g.map ((finCongr (h.length_eq.trans List.length_finRange).symm).trans
    ((h.nodup_iff.mpr (List.nodup_finRange n)).getEquivOfForallMemList order
      fun x ↦ h.mem_iff.mpr (List.mem_finRange x))).symm

theorem Graph.linearize_words (g : Graph n) (order : List (Fin n))
    (h : order.Perm (List.finRange n)) (p : Fin n) :
    (g.linearize order h).words p =
      g.words (order.get (Fin.cast (h.length_eq.trans List.length_finRange).symm p)) :=
  rfl

/-! ### Arc length and the dependent's phrase -/

/-- An arc to the far end of the dependent's own phrase is at least as long as the phrase:
    when every position the dependent dominates lies between the head and the dependent, the
    arc's length bounds their number. Direction is free for a one-word phrase and costly for a
    long one. -/
theorem Graph.ncard_yield_le_dist (g : Graph n) {v w : Fin n} (hv : v ∉ g.yield w)
    (h : ∀ x ∈ g.yield w, x ∈ Set.uIcc v w) : (g.yield w).ncard ≤ Nat.dist v w := by
  have hsub : g.yield w ⊆ Set.uIcc v w \ {v} := Set.subset_sdiff_singleton h hv
  refine (Set.ncard_le_ncard hsub).trans (le_of_eq ?_)
  rw [Set.ncard_sdiff_singleton_of_mem Set.left_mem_uIcc, Set.ncard_uIcc, Fin.card_uIcc,
    Nat.add_sub_cancel]
  simp only [Nat.dist]
  omega

/-! ### Distance to a phrase -/

theorem Graph.toFinset_yield_nonempty (g : Graph n) (w : Fin n) : (g.yield w).toFinset.Nonempty :=
  ⟨w, by simp [ReflTransGen.refl]⟩

/-- The distance from `v` to the nearest word of the yield of `w`, dependency length measured to
the closest boundary of the dependent's phrase. -/
def Graph.yieldDist (g : Graph n) (v w : Fin n) : ℕ :=
  (g.yield w).toFinset.inf' (g.toFinset_yield_nonempty w) fun x ↦ Nat.dist v x

/-- The distance to a phrase is at most the distance to its head. -/
theorem Graph.yieldDist_le_dist (g : Graph n) (v w : Fin n) : g.yieldDist v w ≤ Nat.dist v w :=
  Finset.inf'_le _ (by simp [ReflTransGen.refl])

variable {g : Graph n} {v w : Fin n}

/-- An order-connected set through a point strictly between `a` and `b` and avoiding both lies
strictly between them. -/
private theorem _root_.Set.OrdConnected.between {S : Set (Fin n)} (hS : S.OrdConnected) {a b x y : Fin n}
    (hx : x ∈ S) (hy : y ∈ S) (hxab : a < x ∧ x < b ∨ b < x ∧ x < a) (ha : a ∉ S)
    (hb : b ∉ S) : a < y ∧ y < b ∨ b < y ∧ y < a := by
  have key : ∀ z, (x ≤ z ∧ z ≤ y ∨ y ≤ z ∧ z ≤ x) → z ∈ S := fun z hz ↦
    hS.uIcc_subset hx hy (Set.mem_uIcc.2 hz)
  by_contra hc
  rcases hxab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases le_or_gt y a with hya | hay
    · exact ha (key a (Or.inr ⟨hya, h1.le⟩))
    · exact hb (key b (Or.inl ⟨h2.le, not_lt.1 fun hyb ↦ hc (Or.inl ⟨hay, hyb⟩)⟩))
  · rcases le_or_gt y b with hyb | hby
    · exact hb (key b (Or.inr ⟨hyb, h1.le⟩))
    · exact ha (key a (Or.inl ⟨h2.le, not_lt.1 fun hya ↦ hc (Or.inr ⟨hby, hya⟩)⟩))

private theorem card_between {a b : Fin n} (hab : a ≠ b) :
    (Finset.univ.filter fun x ↦ a < x ∧ x < b ∨ b < x ∧ x < a).card + 1 = Nat.dist a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · have e : (Finset.univ.filter fun x ↦ a < x ∧ x < b ∨ b < x ∧ x < a) = Finset.Ioo a b := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo, Fin.lt_def] at h ⊢
      omega
    rw [e, Fin.card_Ioo]
    simp only [Nat.dist, Fin.lt_def] at h ⊢
    omega
  · have e : (Finset.univ.filter fun x ↦ a < x ∧ x < b ∨ b < x ∧ x < a) = Finset.Ioo b a := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo, Fin.lt_def] at h ⊢
      omega
    rw [e, Fin.card_Ioo]
    simp only [Nat.dist, Fin.lt_def] at h ⊢
    omega

/-- On a projective tree the distance from a head to the nearest word of a dependent's phrase is
one more than the phrase sizes of the dependents between them. -/
theorem Graph.yieldDist_eq_one_add_sum (hT : g.IsTree) (hP : g.IsProjective) (h : g.Adj v w) :
    g.yieldDist v w = 1 + ∑ u ∈ g.children v with (v < u ∧ u < w ∨ w < u ∧ u < v),
      (g.yield u).ncard := by
  classical
  obtain ⟨m, hmY, hm⟩ := Finset.exists_mem_eq_inf' (g.toFinset_yield_nonempty w)
    fun x ↦ Nat.dist v x
  have hmY : m ∈ g.yield w := by simpa using hmY
  have hvY := hT.notMem_yield_of_adj h
  have hmin : ∀ y ∈ g.yield w, Nat.dist v m ≤ Nat.dist v y := fun y hy ↦
    hm ▸ Finset.inf'_le _ (by simpa using hy)
  have hgap : ∀ y ∈ g.yield w, ¬ (v < y ∧ y < m ∨ m < y ∧ y < v) := by
    intro y hy hb
    have := hmin y hy
    simp only [Nat.dist, Fin.lt_def] at this hb
    omega
  -- m lies between v and every point of the phrase
  have hside : ∀ y ∈ g.yield w, v < m ∧ m ≤ y ∨ y ≤ m ∧ m < v := by
    intro y hy
    have hvm : v ≠ m := fun e ↦ hvY (e ▸ hmY)
    have hy' : ¬ (m < v ∧ v < y ∨ y < v ∧ v < m) := fun hb ↦
      hvY ((hP w).uIcc_subset hmY hy (Set.mem_uIcc.2 (by
        rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [exact Or.inl ⟨h1.le, h2.le⟩;
          exact Or.inr ⟨h1.le, h2.le⟩])))
    have hg := hgap y hy
    have hyv : y ≠ v := fun e ↦ hvY (e ▸ hy)
    simp only [Fin.lt_def, Fin.le_def, ne_eq, Fin.ext_iff] at hg hy' hyv hvm ⊢
    omega
  have hiff : ∀ x, (v < x ∧ x < m ∨ m < x ∧ x < v) ↔
      ∃ u ∈ g.children v, (v < u ∧ u < w ∨ w < u ∧ u < v) ∧ x ∈ g.yield u := by
    intro x
    constructor
    · intro hx
      have hxv : x ∈ g.yield v := (hP v).uIcc_subset .refl (ReflTransGen.head h hmY)
        (Set.mem_uIcc.2 (by
          rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [exact Or.inl ⟨h1.le, h2.le⟩;
            exact Or.inr ⟨h1.le, h2.le⟩]))
      have hne : x ≠ v := by rintro rfl; simp at hx
      obtain ⟨u, hvu, hxu⟩ := g.exists_adj_mem_yield hxv hne
      have hxY : x ∉ g.yield w := fun hxY ↦ hgap x hxY hx
      have huw : u ≠ w := by rintro rfl; exact hxY hxu
      have hdis := hT.disjoint_yield_of_adj hvu h huw
      have hb := (hP u).between hxu (ReflTransGen.refl) hx (hT.notMem_yield_of_adj hvu)
        (Set.disjoint_right.1 hdis hmY)
      have hs := hside w ReflTransGen.refl
      refine ⟨u, by simpa using hvu, ?_, hxu⟩
      simp only [Fin.lt_def, Fin.le_def] at hb hs ⊢
      omega
    · rintro ⟨u, hu, hb, hxu⟩
      have hvu : g.Adj v u := by simpa using hu
      have huw : u ≠ w := by rintro rfl; simp at hb
      have hdis := hT.disjoint_yield_of_adj hvu h huw
      have huY : u ∉ g.yield w := Set.disjoint_left.1 hdis ReflTransGen.refl
      have hs := hside w ReflTransGen.refl
      -- u lies strictly between v and m
      have hum : v < u ∧ u < m ∨ m < u ∧ u < v := by
        have hmw : ¬ (m ≤ u ∧ u ≤ w ∨ w ≤ u ∧ u ≤ m) := fun hc ↦
          huY ((hP w).uIcc_subset hmY ReflTransGen.refl (Set.mem_uIcc.2 hc))
        simp only [Fin.lt_def, Fin.le_def] at hb hs hmw ⊢
        omega
      exact (hP u).between ReflTransGen.refl hxu hum (hT.notMem_yield_of_adj hvu)
        (Set.disjoint_right.1 hdis hmY)
  have hvm : v ≠ m := fun e ↦ hvY (e ▸ hmY)
  have hT' : (Finset.univ.filter fun x ↦ v < x ∧ x < m ∨ m < x ∧ x < v) =
      (g.children v |>.filter fun u ↦ v < u ∧ u < w ∨ w < u ∧ u < v).biUnion
        fun u ↦ Finset.univ.filter (· ∈ g.yield u) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hiff]
    constructor
    · rintro ⟨u, hu, hb, hx⟩; exact ⟨u, ⟨hu, hb⟩, hx⟩
    · rintro ⟨u, ⟨hu, hb⟩, hx⟩; exact ⟨u, hu, hb, hx⟩
  have hdisj : ((g.children v |>.filter fun u ↦ v < u ∧ u < w ∨ w < u ∧ u < v) : Set (Fin n)
      ).PairwiseDisjoint fun u ↦ Finset.univ.filter (· ∈ g.yield u) := by
    intro u hu u' hu' hne
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Graph.mem_children] at hu hu'
    simpa [Function.onFun, Finset.disjoint_filter] using
      Set.disjoint_left.1 (hT.disjoint_yield_of_adj hu.1 hu'.1 hne)
  rw [Graph.yieldDist, hm, ← card_between hvm, hT', Finset.card_biUnion hdisj, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext; simp

end DependencyGrammar
