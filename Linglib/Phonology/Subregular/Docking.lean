/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.WindowFormula
public import Linglib.Phonology.Subregular.Dependence

/-!
# Docking processes

A **docking process** is the positional rewrite of the subregular program
([chandlee-2014], [chandlee-jardine-2019]) with its context left semantic: what docking does to
a position's symbol, and a decidable predicate saying at which positions of a word it docks;
the other positions keep their symbol. It is the string function a relabelling transduction
computes, and the object over which locality is stated once: when the context is a
quantifier-free formula bounded by `l` back and `r` forward, the output at a position reads
only that window, so the map depends boundedly on both sides in the sense of
`Subregular.BoundedDependence`.

## Main definitions

* `Docking`, `Docking.map` — the process and its rewrite; `Docking.support`, the docking set.
* `Docking.ofQF` — the process with a quantifier-free context.

## Main results

* `Docking.map_getElem?` — the rewrite pointwise.
* `Docking.ofQF_map_getElem?_congr` — with a bounded guard, the output at a position reads
  only the guard's window.
* `Docking.ofQF_boundedDependence` — hence bounded dependence on both sides.

## References

* [chandlee-2014]
* [chandlee-jardine-2019]
-/

@[expose] public section

namespace Subregular

/-- A docking process over the alphabet `α`: what docking does to a position's symbol, and the
context predicate saying at which positions of a word it docks; the other positions keep
their symbol. -/
structure Docking (α : Type*) where
  /-- The change docked at a position. -/
  dock : α → α
  /-- Position `i` of `w` is docked at. -/
  Docks : List α → ℕ → Prop
  /-- Docking positions are in-domain. -/
  lt_length : ∀ {w : List α} {i : ℕ}, Docks w i → i < w.length
  /-- The context predicate is decidable, so the map computes. -/
  decDocks : ∀ w i, Decidable (Docks w i)

namespace Docking

variable {α : Type*} (P : Docking α) {w : List α} {i : ℕ}

instance (w : List α) (i : ℕ) : Decidable (P.Docks w i) := P.decDocks w i

/-- The induced rewrite: the change docked exactly at the docking positions. -/
def map (w : List α) : List α := w.mapIdx fun i a => if P.Docks w i then P.dock a else a

@[simp] theorem map_nil : P.map [] = [] := rfl

@[simp] theorem map_length : (P.map w).length = w.length := by simp [map]

theorem map_getElem? :
    (P.map w)[i]? = w[i]?.map fun a => if P.Docks w i then P.dock a else a := by
  simp [map, List.getElem?_mapIdx]

theorem map_getElem?_of_docks (h : P.Docks w i) : (P.map w)[i]? = w[i]?.map P.dock := by
  simp [map_getElem?, h]

theorem map_getElem?_of_not_docks (h : ¬ P.Docks w i) : (P.map w)[i]? = w[i]? := by
  simp [map_getElem?, h]

/-- The docking positions of `w`, as a finite set. -/
def support (w : List α) : Finset ℕ := (Finset.range w.length).filter (P.Docks w)

@[simp] theorem mem_support : i ∈ P.support w ↔ P.Docks w i := by
  simp only [support, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact P.lt_length

/-! ### Quantifier-free contexts -/

variable [DecidableEq α]

/-- The docking process whose context is a quantifier-free formula. -/
def ofQF (φ : WindowFormula α) (dock : α → α) : Docking α where
  dock := dock
  Docks w i := i < w.length ∧ φ.Realize w i
  lt_length h := h.1
  decDocks _ _ := inferInstance

/-- With a guard bounded by `l` back and `r` forward, the output at a position reads only the
input on that window. -/
theorem ofQF_map_getElem?_congr {φ : WindowFormula α} {l r : ℕ} (hφ : φ.Bounded l r) (dock : α → α)
    {w w' : List α} (hlen : w.length = w'.length)
    (hag : ∀ j, i - l ≤ j → j ≤ i + r → w[j]? = w'[j]?) :
    ((ofQF φ dock).map w)[i]? = ((ofQF φ dock).map w')[i]? := by
  rw [map_getElem?, map_getElem?]
  by_cases hi : i < w.length
  · have hi' : i < w'.length := hlen ▸ hi
    have hR : φ.Realize w i ↔ φ.Realize w' i :=
      WindowFormula.Bounded.realize_congr hi hi'
        (fun j hj ↦ ⟨Iff.rfl, fun _ ↦ hag _ (by omega) (by omega)⟩)
        (fun j hj ↦ ⟨by rw [hlen], hag _ (by omega) (by omega)⟩) hφ
    simp only [ofQF, hag i (by omega) (by omega), hi, hi', hR]
  · have hi' : ¬ i < w'.length := hlen ▸ hi
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_eq_none (Nat.le_of_not_lt hi')]

/-- A quantifier-free docking process with a bounded guard depends boundedly on the left. -/
theorem ofQF_boundedDependence_left {φ : WindowFormula α} {l r : ℕ} (hφ : φ.Bounded l r)
    (dock : α → α) : BoundedDependence (ofQF φ dock).map .left :=
  ⟨l, fun i n x y hxy ↦ ofQF_map_getElem?_congr hφ dock (by simp) fun j h1 _ ↦ by
    simp only [List.getElem?_ofFn]
    split_ifs with h
    · rw [hxy ⟨j, h⟩ (by simpa using h1)]
    · rfl⟩

/-- A quantifier-free docking process with a bounded guard depends boundedly on the right. -/
theorem ofQF_boundedDependence_right {φ : WindowFormula α} {l r : ℕ} (hφ : φ.Bounded l r)
    (dock : α → α) : BoundedDependence (ofQF φ dock).map .right :=
  ⟨r, fun i n x y hxy ↦ ofQF_map_getElem?_congr hφ dock (by simp) fun j _ h2 ↦ by
    simp only [List.getElem?_ofFn]
    split_ifs with h
    · rw [hxy ⟨j, h⟩ (by simpa using h2)]
    · rfl⟩

end Docking

end Subregular
