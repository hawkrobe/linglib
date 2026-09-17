/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.DependsOn

/-!
# `DependsOn` through `List.ofFn`

A list is a length together with a tuple, `List.equivSigmaTuple : List α ≃ Σ n, Fin n → α`, so
a function `g : List α → γ` is a family of functions on the Π-types `Fin n → α`, one per
length, and mathlib's `DependsOn` applies to each. `List.forall_dependsOn_ofFn_iff` unpacks
"`g ∘ List.ofFn` depends on the positions in `K` on every fibre" into the word-pair form:
equal-length lists agreeing at every position in `K` have equal images. [UPSTREAM] candidate
for `Mathlib/Data/List/OfFn.lean`.
-/

namespace List

variable {α γ : Type*} {K : Set ℕ}

/-- `g ∘ List.ofFn` depends on the positions in `K` on every fibre exactly when equal-length
lists agreeing at every position in `K` have equal images under `g`. -/
theorem forall_dependsOn_ofFn_iff (g : List α → γ) :
    (∀ n, DependsOn (fun x : Fin n → α ↦ g (ofFn x)) (Fin.val ⁻¹' K)) ↔
      ∀ ⦃u v : List α⦄, u.length = v.length → (∀ k ∈ K, u[k]? = v[k]?) → g u = g v := by
  constructor
  · intro h u v hlen hag
    have hu : u = ofFn fun i : Fin u.length ↦ u[i] := ofFn_getElem.symm
    have hv : v = ofFn fun i : Fin u.length ↦ v[i]'(hlen ▸ i.2) := by
      apply ext_getElem (by simp [hlen])
      intro i h1 h2
      simp
    refine (congrArg g hu).trans ((h u.length fun i hi ↦ ?_).trans (congrArg g hv).symm)
    have hi' := hag i hi
    rw [getElem?_eq_getElem i.2, getElem?_eq_getElem (show (i : ℕ) < v.length by omega)] at hi'
    exact Option.some_injective _ hi'
  · intro h n f f' hff'
    refine h (by simp) fun k hk ↦ ?_
    simp only [List.getElem?_ofFn]
    split_ifs with hkn
    · exact congrArg some (hff' ⟨k, hkn⟩ hk)
    · rfl

end List
