/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.TakeDrop

/-!
# Tonal surfacing processes

A **surfacing process** bundles the analysis [jardine-2016] gives tone-string maps: a
marked tone value, and a context predicate `Surfaces w i` saying position `i` of `w`
surfaces with it. The induced rewrite `Surfacing.map` writes the marked tone exactly at
the surfacing positions and the default elsewhere; `Surfacing.support` is the surfacing
set. Owning the context predicate on the process is what lets rival processes coexist:
unbounded tonal plateauing (`Tone.Plateauing.utp`) and Copperbelt Bemba high-tone
spreading (`Studies/Yolyan2025`) instantiate the same structure with very different
predicates — plateauing's is convex and its map a closure operator, spreading's is
neither — so only the genuinely shared API lives here.

The laws are the shared minimum: surfacing positions are in-domain (`lt_length`), the
marked tone is faithful — an underlying marked tone always surfaces (`surfaces_of_hi`) —
and the two written values are distinct (`hi_ne_lo`), which makes the pointwise
characterizations (`map_getElem?_hi_iff`, `map_getElem?_lo_iff`) read the map exactly.
-/

namespace Tone

/-- A tonal surfacing process over the alphabet `α`: a marked tone `hi`, a default `lo`,
and the context predicate saying which positions of a word surface with the mark. -/
structure Surfacing (α : Type*) where
  /-- The marked (surfacing) tone value. -/
  hi : α
  /-- The default value written at non-surfacing positions. -/
  lo : α
  /-- Position `i` of `w` surfaces with the marked tone. -/
  Surfaces : List α → ℕ → Prop
  /-- The two written values are distinct. -/
  hi_ne_lo : hi ≠ lo
  /-- Surfacing positions are in-domain. -/
  lt_length : ∀ {w : List α} {i : ℕ}, Surfaces w i → i < w.length
  /-- Faithfulness: an underlying marked tone surfaces. -/
  surfaces_of_hi : ∀ {w : List α} {i : ℕ}, w[i]? = some hi → Surfaces w i
  /-- The context predicate is decidable, so the map computes. -/
  decSurfaces : ∀ w i, Decidable (Surfaces w i)

namespace Surfacing

variable {α : Type*} (P : Surfacing α) {w : List α} {i j : ℕ}

instance (w : List α) (i : ℕ) : Decidable (P.Surfaces w i) := P.decSurfaces w i

/-- The induced rewrite: the marked tone exactly at the surfacing positions. -/
def map (w : List α) : List α := w.mapIdx fun i _ => if P.Surfaces w i then P.hi else P.lo

@[simp] theorem map_nil : P.map [] = [] := rfl

@[simp] theorem map_length : (P.map w).length = w.length := by simp [map]

theorem map_getElem? :
    (P.map w)[i]? = w[i]?.map fun _ => if P.Surfaces w i then P.hi else P.lo := by
  simp [map, List.getElem?_mapIdx]

theorem map_getElem?_hi_iff : (P.map w)[j]? = some P.hi ↔ P.Surfaces w j := by
  rw [map_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, -, ha⟩
    by_contra hs
    rw [if_neg hs] at ha
    exact P.hi_ne_lo ha.symm
  · exact fun hs => ⟨w[j]'(P.lt_length hs), List.getElem?_eq_getElem (P.lt_length hs),
      if_pos hs⟩

theorem map_getElem?_lo_iff :
    (P.map w)[j]? = some P.lo ↔ j < w.length ∧ ¬ P.Surfaces w j := by
  rw [map_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, hout⟩
    refine ⟨(List.getElem?_eq_some_iff.mp ha).1, fun hs => ?_⟩
    rw [if_pos hs] at hout
    exact P.hi_ne_lo hout
  · exact fun ⟨hj, hs⟩ => ⟨w[j], List.getElem?_eq_getElem hj, if_neg hs⟩

/-- Faithfulness at the map level: an underlying marked tone survives. -/
theorem map_getElem?_hi_of_getElem?_hi (h : w[i]? = some P.hi) :
    (P.map w)[i]? = some P.hi :=
  P.map_getElem?_hi_iff.mpr (P.surfaces_of_hi h)

/-! ### The surfacing set -/

/-- The surfacing positions of `w`, as a finite set. -/
def support (w : List α) : Finset ℕ := (Finset.range w.length).filter (P.Surfaces w)

@[simp] theorem mem_support : j ∈ P.support w ↔ P.Surfaces w j := by
  simp only [support, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact P.lt_length

/-- The map writes the indicator word of its support. -/
theorem map_eq_indicator :
    P.map w = (List.range w.length).map fun i => if i ∈ P.support w then P.hi else P.lo :=
  List.ext_getElem (by simp [map]) fun i h₁ h₂ => by simp [map, mem_support]

end Surfacing

end Tone
