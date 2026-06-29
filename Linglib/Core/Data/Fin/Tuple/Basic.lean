/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# `Fin.appendMap`: `Fin.append` as a bifunctor on index maps

`[UPSTREAM]` candidate for `Mathlib/Data/Fin/Tuple/Basic.lean`. Mathlib has
`Fin.append` (the action of `+` on *tuples*) and its naturality only for `Fin.cast`
maps; it lacks the action of `+` on arbitrary index *maps*. `Fin.appendMap f g`
routes a `Fin (m + n)` index through `f` on the left block and `g` on the right,
and is functorial (`appendMap_id`/`appendMap_comp`) with `Fin.append` natural in it
(`append_comp_appendMap`).
-/

namespace Fin

variable {m m' m'' n n' n'' : ℕ}

/-- The action of `+` on index maps: `f` on the left block, `g` on the right. -/
def appendMap (f : Fin m → Fin m') (g : Fin n → Fin n') : Fin (m + n) → Fin (m' + n') :=
  finSumFinEquiv ∘ Sum.map f g ∘ finSumFinEquiv.symm

@[simp] theorem appendMap_castAdd (f : Fin m → Fin m') (g : Fin n → Fin n') (i : Fin m) :
    appendMap f g (Fin.castAdd n i) = Fin.castAdd n' (f i) := by
  simp [appendMap]

@[simp] theorem appendMap_natAdd (f : Fin m → Fin m') (g : Fin n → Fin n') (j : Fin n) :
    appendMap f g (Fin.natAdd m j) = Fin.natAdd m' (g j) := by
  simp [appendMap]

/-- Value characterisation: left-block indices route through `f`, right-block
    (shifted) through `g`. -/
theorem appendMap_val (f : Fin m → Fin m') (g : Fin n → Fin n') (k : Fin (m + n)) :
    (appendMap f g k : ℕ) =
      if h : (k : ℕ) < m then (f ⟨k, h⟩ : ℕ)
      else (g ⟨(k : ℕ) - m, by have := k.2; omega⟩ : ℕ) + m' := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · rw [dif_pos (by simp)]; simp
  · rw [dif_neg (by simp)]; simp; omega

/-- Value of a **common-codomain** `Fin.append` (the copairing `Fin (m + n) → Fin p`)
    at a raw index: left-block indices route through `u`, right-block (shifted)
    through `v`. The copairing analogue of `appendMap_val`. -/
theorem append_val {p : ℕ} (u : Fin m → Fin p) (v : Fin n → Fin p) (k : Fin (m + n)) :
    (Fin.append u v k).val =
      if h : (k : ℕ) < m then (u ⟨k, h⟩).val
      else (v ⟨(k : ℕ) - m, by have := k.2; omega⟩).val := by
  refine Fin.addCases (fun a => ?_) (fun a => ?_) k
  · rw [Fin.append_left, dif_pos (by simp)]; simp
  · rw [Fin.append_right, dif_neg (by simp)]; congr 1; simp

@[simp] theorem appendMap_id : appendMap (id : Fin m → _) (id : Fin n → _) = id := by
  simp [appendMap]

theorem appendMap_comp (f : Fin m → Fin m') (f' : Fin m' → Fin m'')
    (g : Fin n → Fin n') (g' : Fin n' → Fin n'') :
    appendMap (f' ∘ f) (g' ∘ g) = appendMap f' g' ∘ appendMap f g := by
  funext k; simp [appendMap, Equiv.symm_apply_apply, Sum.map_map]

/-- **`Fin.append` is natural in its index maps**: a block-routing map intertwines
    the two appended tuples. The label-preservation core for concatenation. -/
theorem append_comp_appendMap {α : Type*} {a : Fin m → α} {a' : Fin m' → α}
    {b : Fin n → α} {b' : Fin n' → α} {f : Fin m → Fin m'} {g : Fin n → Fin n'}
    (hf : a' ∘ f = a) (hg : b' ∘ g = b) :
    Fin.append a' b' ∘ appendMap f g = Fin.append a b := by
  subst hf hg
  funext k
  simp only [Function.comp_apply]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp

end Fin
