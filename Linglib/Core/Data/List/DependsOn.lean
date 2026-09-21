/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Order.Interval.Set.Basic
public import Linglib.Core.Data.List.TakeDrop

/-!
# `DependsOn` for functions on lists

mathlib's `DependsOn f s` says a function on `Π i, α i` is determined by the coordinates in
`s`. A function `g : List α → γ` is not on a Π-type, but on each fibre `Fin n → α` the
composite `g ∘ List.ofFn` is, so "`g` depends only on the positions in `K`" is
`∀ n, DependsOn (g ∘ List.ofFn) (Fin.val ⁻¹' K)`. `List.forall_dependsOn_ofFn_iff` unpacks that
into the word-pair form consumers use: equal-length lists whose `getElem?` functions are
`Set.EqOn` on `K` have equal images. [UPSTREAM] candidate for
`Mathlib/Logic/Function/DependsOn.lean`.

## Main results

* `List.forall_dependsOn_ofFn_iff`: the word-pair form of fibrewise `DependsOn`.
* `Set.EqOn.take_eq`, `Set.EqOn.drop_eq`, `Set.EqOn.getElem?_eq`: agreement of `getElem?` on
  `Set.Iic j` or `Set.Ici j` transports prefixes and suffixes, in dot-notation form.
-/

@[expose] public section

namespace List

variable {α γ : Type*} {K : Set ℕ}

/-- `g ∘ List.ofFn` depends on the positions in `K` on every fibre exactly when equal-length
lists agreeing on `K` have equal images under `g`. -/
theorem forall_dependsOn_ofFn_iff (g : List α → γ) :
    (∀ n, DependsOn (fun x : Fin n → α ↦ g (ofFn x)) (Fin.val ⁻¹' K)) ↔
      ∀ ⦃u v : List α⦄, u.length = v.length → Set.EqOn (u[·]?) (v[·]?) K → g u = g v := by
  constructor
  · intro h u v hlen hag
    have hu : u = ofFn fun i : Fin u.length ↦ u[i] := ofFn_getElem.symm
    have hv : v = ofFn fun i : Fin u.length ↦ v[i]'(hlen ▸ i.2) := by
      apply ext_getElem (by simp [hlen])
      intro i h1 h2
      simp
    refine (congrArg g hu).trans ((h u.length fun i hi ↦ ?_).trans (congrArg g hv).symm)
    have hi' : u[(i : ℕ)]? = v[(i : ℕ)]? := hag hi
    rw [getElem?_eq_getElem i.2, getElem?_eq_getElem (show (i : ℕ) < v.length by omega)] at hi'
    exact Option.some_injective _ hi'
  · intro h n f f' hff'
    refine h (by simp) fun k hk ↦ ?_
    simp only [List.getElem?_ofFn]
    split_ifs with hkn
    · exact congrArg some (hff' ⟨k, hkn⟩ hk)
    · rfl

end List

namespace Set.EqOn

variable {α : Type*} {u v : List α} {i j : ℕ}

/-- The pointwise application of window agreement, stated in `getElem?` form so it rewrites
cleanly. -/
theorem getElem?_eq {s : Set ℕ} {k : ℕ} (h : Set.EqOn (u[·]?) (v[·]?) s) (hk : k ∈ s) :
    u[k]? = v[k]? := h hk

/-- Agreement on positions up to `j` transports prefixes of length at most `j + 1`. -/
theorem take_eq (h : Set.EqOn (u[·]?) (v[·]?) (Set.Iic j)) (hij : i ≤ j + 1) :
    u.take i = v.take i :=
  List.ext_take_getElem? fun _ hk ↦ h (Set.mem_Iic.mpr (by omega))

/-- Agreement on positions from `j` transports suffixes from `j` on. -/
theorem drop_eq (h : Set.EqOn (u[·]?) (v[·]?) (Set.Ici j)) (hij : j ≤ i) :
    u.drop i = v.drop i :=
  List.ext_drop_getElem? fun _ hk ↦ h (Set.mem_Ici.mpr (by omega))

end Set.EqOn
