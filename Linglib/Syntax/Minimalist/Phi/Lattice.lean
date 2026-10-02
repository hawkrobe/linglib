/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sups

/-!
# Phi lattices and their operations

In Harbour's calculus a feature denotes a lattice of groups, the nonempty sets of some atoms,
and its values act on the lattice of its host. The positive value adds the feature's lattice
pairwise, which is mathlib's pointwise join `⊻` of set families (`Finset.sups`, Harbour's `⊕`);
the negative value subtracts the feature lattice's maximum from every group. When one feature
specification denotes a proper subset of another, Lexical Complementarity confines the larger to
the difference, a set difference `\`. Toosarvandani reuses the calculus for animacy, where the
lattice of a feature added to the lattice of a larger atom set gives the groups containing one of
its atoms.

## Main definitions

* `Minimalist.Phi.Lattice.nePowerset`: the lattice of groups of a set of atoms.
* `Minimalist.Phi.Lattice.ominus`: the negative action of a feature.
* `Minimalist.Phi.Lattice.act`: the action of a feature with a given value.
* `Minimalist.Phi.Lattice.containing`: the groups containing an atom of a given set.

## Main results

* `Minimalist.Phi.Lattice.nePowerset_sups_nePowerset`,
  `Minimalist.Phi.Lattice.nePowerset_sups_containing`: along an entailment chain, adding a
  feature's lattice gives the groups containing one of its atoms.
* `Minimalist.Phi.Lattice.mem_containing_sdiff_containing_iff`: Lexical Complementarity
  between two such denotations.

## References

* [harbour-2016]
* [toosarvandani-2023]
-/

@[expose] public section

open scoped FinsetFamily

namespace Minimalist.Phi.Lattice

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### The lattice of groups -/

/-- The lattice of groups of `atoms` is its nonempty subsets. -/
def nePowerset (atoms : Finset α) : Finset (Finset α) := atoms.powerset.erase ∅

theorem mem_nePowerset_iff {X s : Finset α} : s ∈ nePowerset X ↔ s.Nonempty ∧ s ⊆ X := by
  simp [nePowerset, nonempty_iff_ne_empty]

theorem nePowerset_mono {s t : Finset α} (h : s ⊆ t) : nePowerset s ⊆ nePowerset t :=
  erase_subset_erase ∅ (powerset_mono.mpr h)

/-- The groups of a set of atoms are closed under union. -/
theorem supClosed_nePowerset (X : Finset α) : SupClosed (nePowerset X : Set (Finset α)) :=
  fun s hs t ht ↦ by
    rw [mem_coe, mem_nePowerset_iff] at hs ht ⊢
    exact ⟨hs.1.mono subset_union_left, union_subset hs.2 ht.2⟩

/-! ### The actions of a feature -/

/-- The negative action of a feature lattice `F` on `G` subtracts the maximum of `F` from every
element of `G`. The empty set may result; the host head discards it. -/
def ominus (F G : Finset (Finset α)) : Finset (Finset α) := G.image (· \ F.sup id)

theorem mem_ominus_iff {F G : Finset (Finset α)} {z : Finset α} :
    z ∈ ominus F G ↔ ∃ g ∈ G, g \ F.sup id = z := mem_image

theorem ominus_subset {F G G' : Finset (Finset α)} (h : G ⊆ G') :
    ominus F G ⊆ ominus F G' :=
  image_subset_image h

/-- `act sign F G` is the action of the feature lattice `F` on `G` with the value `sign`,
positive or negative. -/
def act (sign : Bool) (F G : Finset (Finset α)) : Finset (Finset α) :=
  if sign then F ⊻ G else ominus F G

@[simp] theorem act_true (F G : Finset (Finset α)) : act true F G = F ⊻ G := rfl
@[simp] theorem act_false (F G : Finset (Finset α)) : act false F G = ominus F G := rfl

/-! ### Groups containing an atom -/

/-- `containing X Y` is the set of groups of `Y` that contain an atom of `X`. -/
def containing (X Y : Finset α) : Finset (Finset α) :=
  (nePowerset Y).filter fun s ↦ (s ∩ X).Nonempty

theorem mem_containing_iff {X Y s : Finset α} :
    s ∈ containing X Y ↔ s ⊆ Y ∧ (s ∩ X).Nonempty := by
  rw [containing, mem_filter, mem_nePowerset_iff]
  exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨h.2.mono inter_subset_left, h.1⟩, h.2⟩⟩

theorem containing_mono {X X' Y : Finset α} (h : X ⊆ X') :
    containing X Y ⊆ containing X' Y := fun _ hs ↦
  mem_containing_iff.2 ⟨(mem_containing_iff.1 hs).1,
    (mem_containing_iff.1 hs).2.mono (inter_subset_inter (Subset.refl _) h)⟩

/-- Adding the lattice of `X` to the lattice of `Y ⊇ X` gives the groups of `Y` containing an
atom of `X`. -/
theorem nePowerset_sups_nePowerset {X Y : Finset α} (h : X ⊆ Y) :
    nePowerset X ⊻ nePowerset Y = containing X Y := by
  ext s
  rw [mem_sups, mem_containing_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [mem_nePowerset_iff] at hx hy
    exact ⟨union_subset (hx.2.trans h) hy.2, hx.1.mono (subset_inter subset_union_left hx.2)⟩
  · rintro ⟨hs, hX⟩
    exact ⟨s ∩ X, mem_nePowerset_iff.2 ⟨hX, inter_subset_right⟩, s,
      mem_nePowerset_iff.2 ⟨hX.mono inter_subset_left, hs⟩, union_eq_right.2 inter_subset_left⟩

/-- Along an entailment chain `X ⊆ Y ⊆ Z`, adding the lattice of `X` to the groups of `Z`
containing a `Y`-atom gives the groups containing an `X`-atom. -/
theorem nePowerset_sups_containing {X Y Z : Finset α} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    nePowerset X ⊻ containing Y Z = containing X Z := by
  ext s
  rw [mem_sups, mem_containing_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [mem_nePowerset_iff] at hx
    rw [mem_containing_iff] at hy
    exact ⟨union_subset (hx.2.trans (hXY.trans hYZ)) hy.1,
      hx.1.mono (subset_inter subset_union_left hx.2)⟩
  · rintro ⟨hs, hX⟩
    exact ⟨s ∩ X, mem_nePowerset_iff.2 ⟨hX, inter_subset_right⟩, s,
      mem_containing_iff.2 ⟨hs, hX.mono (inter_subset_inter (Subset.refl _) hXY)⟩,
      union_eq_right.2 inter_subset_left⟩

/-- Lexical Complementarity against a more specified sibling leaves the groups containing a
`Y`-atom but no `X`-atom. -/
theorem mem_containing_sdiff_containing_iff {X Y Z s : Finset α} :
    s ∈ containing Y Z \ containing X Z ↔ s ⊆ Z ∧ (s ∩ Y).Nonempty ∧ ¬ (s ∩ X).Nonempty := by
  rw [mem_sdiff, mem_containing_iff, mem_containing_iff]
  exact ⟨fun h ↦ ⟨h.1.1, h.1.2, fun hX ↦ h.2 ⟨h.1.1, hX⟩⟩,
    fun h ↦ ⟨⟨h.1, h.2.1⟩, fun h' ↦ h.2.2 h'.2⟩⟩

/-- Disjoint atom sets give incomparable denotations, neither more specified than the other. -/
theorem containing_not_subset_of_disjoint {X Y Z : Finset α} (hd : Disjoint X Y)
    (hX : X.Nonempty) (hXZ : X ⊆ Z) :
    ¬ containing X Z ⊆ containing Y Z := by
  obtain ⟨x, hx⟩ := hX
  intro h
  obtain ⟨y, hy⟩ := (mem_containing_iff.1
    (h (mem_containing_iff.2 ⟨singleton_subset_iff.2 (hXZ hx), ⟨x, by simp [hx]⟩⟩))).2
  rw [mem_inter, mem_singleton] at hy
  exact disjoint_left.1 hd hx (hy.1 ▸ hy.2)

end Minimalist.Phi.Lattice
