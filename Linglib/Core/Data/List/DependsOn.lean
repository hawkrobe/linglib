/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.DependsOn
import Mathlib.Order.Interval.Set.Basic
import Linglib.Core.Data.List.TakeDrop

/-!
# Functions on lists determined by a set of positions

`List.DependsOn g K` says that `g : List α → γ` is determined by the entries at the positions
in `K`: equal-length inputs whose `getElem?` functions are `Set.EqOn` on `K` have equal images.
It is the length-stratified form of mathlib's `DependsOn` on `Π i, α i`:
`List.dependsOn_iff_forall_dependsOn_ofFn` identifies it with `DependsOn` of `g ∘ List.ofFn`
on every fibre `Fin n → α`, and `List.dependsOn_iff_factorsThrough` is the factor-through
characterization of `dependsOn_iff_factorsThrough`. [UPSTREAM] candidate for
`Mathlib/Data/List/DependsOn.lean`.

## Main definitions

* `List.DependsOn`: `g` depends only on the positions in `K`.
* `List.DependsAt`: the pointwise form at one input, so that `DependsOn g K` is definitionally
  `∀ w, DependsAt g K w`.

## Main results

* `List.dependsOn_iff_forall_dependsOn_ofFn`, `List.dependsOn_iff_factorsThrough`,
  `List.DependsOn.mono`: the two characterizations and monotonicity in the position set.
* `Set.EqOn.take_eq`, `Set.EqOn.drop_eq`, `Set.EqOn.getElem?_eq`: agreement of `getElem?` on
  `Set.Iic j` or `Set.Ici j` transports prefixes and suffixes, in dot-notation form.
-/

namespace List

variable {α γ : Type*} {g : List α → γ} {K K' : Set ℕ}

/-- `g` is determined by the input positions in `K`: equal-length inputs agreeing on `K` have
equal images. -/
def DependsOn (g : List α → γ) (K : Set ℕ) : Prop :=
  ∀ ⦃u v : List α⦄, u.length = v.length → Set.EqOn (u[·]?) (v[·]?) K → g u = g v

theorem DependsOn.mono (hKK' : K ⊆ K') (h : DependsOn g K) : DependsOn g K' :=
  fun _ _ hl hag ↦ h hl (hag.mono hKK')

/-- `g` is determined at `w` by the positions in `K`: any equal-length list agreeing with `w`
on `K` has the same image. `DependsOn g K` is definitionally `∀ w, DependsAt g K w`. -/
def DependsAt (g : List α → γ) (K : Set ℕ) (w : List α) : Prop :=
  ∀ ⦃v : List α⦄, w.length = v.length → Set.EqOn (w[·]?) (v[·]?) K → g w = g v

/-- `List.DependsOn` is mathlib's `DependsOn` of `g ∘ List.ofFn` on every fibre `Fin n → α`. -/
theorem dependsOn_iff_forall_dependsOn_ofFn :
    DependsOn g K ↔
      ∀ n, _root_.DependsOn (fun f : Fin n → α ↦ g (ofFn f)) {i | (i : ℕ) ∈ K} := by
  constructor
  · intro h n f f' hff'
    refine h (by simp) fun k hk ↦ ?_
    simp only [List.getElem?_ofFn]
    split_ifs with hkn
    · exact congrArg some (hff' ⟨k, hkn⟩ hk)
    · rfl
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

/-- `g` factors through the input's length and its restriction to `K`. -/
theorem dependsOn_iff_factorsThrough :
    DependsOn g K ↔
      Function.FactorsThrough g (fun u : List α ↦ (u.length, K.domRestrict (u[·]?))) := by
  constructor
  · intro h u v huv
    rw [Prod.mk.injEq] at huv
    exact h huv.1 fun k hk ↦ congrFun huv.2 ⟨k, hk⟩
  · intro h u v hlen hag
    exact h (Prod.ext hlen (funext fun k ↦ hag k.2))

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
