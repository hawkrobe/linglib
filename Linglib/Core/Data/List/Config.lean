/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

/-!
# Lists as blank-padded two-sided families

`List.config w` reads a list as a function `ℤ → Option α`: the entries of `w` on
`[0, w.length)` and `none` elsewhere. `List.window k w i` is the width-`k` slice of that
function starting at `i`. Position-indexed statements about lists then replace the
bookkeeping of factors of a padded list: a window entry is an entry or a blank according to a
single interval test.

## Main definitions

* `List.config`: the two-sided family of a list.
* `List.window`: a width-`k` slice of `List.config`, as a `List.ofFn`.

## Main results

* `List.config_of_nonneg`, `List.config_of_neg`, `List.config_natCast`: the two cases of
  `List.config` and the `ℕ` specialization.
* `List.config_eq_none_iff` and `List.bounds_of_config_eq_some`: an entry is blank exactly
  outside `[0, w.length)`.
* `List.eq_of_config_agree` and `List.take_eq_of_config_agree`: extensionality for lists and
  their prefixes through `List.config`.
* `List.window_eq_window_iff`: two windows agree exactly when their entries do.

## Implementation notes

The nearest mathlib notion is `Turing.Tape.nth` on `Turing.Tape.mk₁`, a two-sided tape padded
with `default`; over `Option α` that blank is `none`. Reading a list through the tape would
route every lemma through the `Turing.ListBlank` quotient for a lookup that is one `if`, so the
family is defined directly.
-/

namespace List

variable {α : Type*} {w y u v : List α} {i q : ℤ} {a : α} {k : ℕ}

/-- The two-sided family of a list: its entries on `[0, w.length)`, `none` elsewhere. -/
def config (w : List α) : ℤ → Option α :=
  fun i ↦ if 0 ≤ i then w[i.toNat]? else none

theorem config_of_nonneg (h : 0 ≤ i) : w.config i = w[i.toNat]? := ite_eq_left h

theorem config_of_neg (h : i < 0) : w.config i = none := ite_eq_right (by omega)

@[simp] theorem config_natCast (w : List α) (n : ℕ) : w.config n = w[n]? := by
  simp [config]

@[simp] theorem config_nil : ([] : List α).config i = none := by
  simp [config]

theorem config_eq_none_iff : w.config i = none ↔ i < 0 ∨ (w.length : ℤ) ≤ i := by
  rcases lt_or_ge i 0 with h | h
  · simp [config_of_neg h, h]
  · rw [config_of_nonneg h, getElem?_eq_none_iff]
    omega

theorem bounds_of_config_eq_some (h : w.config i = some a) : 0 ≤ i ∧ i < w.length := by
  rcases lt_or_ge i 0 with h0 | h0
  · simp [config_of_neg h0] at h
  · rw [config_of_nonneg h0] at h
    exact ⟨h0, by have := (getElem?_eq_some_iff.mp h).1; omega⟩

/-- Agreement of the families up to the length of `w` forces equality. -/
theorem eq_of_config_agree (h : ∀ j : ℤ, j ≤ (w.length : ℤ) → y.config j = w.config j) :
    y = w := by
  have hy : y.length ≤ w.length := by
    have h1 := h (w.length : ℤ) le_rfl
    rwa [config_natCast, config_natCast, getElem?_eq_none le_rfl, getElem?_eq_none_iff] at h1
  refine ext_getElem? fun n ↦ ?_
  rcases lt_or_ge n w.length with hn | hn
  · simpa using h n (by omega)
  · rw [getElem?_eq_none hn, getElem?_eq_none (by omega)]

/-- Agreement of the families below `c` transfers prefixes of length `c`. -/
theorem take_eq_of_config_agree {c : ℕ}
    (h : ∀ j : ℤ, j < (c : ℤ) → y.config j = w.config j) : y.take c = w.take c := by
  refine ext_getElem? fun n ↦ ?_
  rcases lt_or_ge n c with hn | hn
  · rw [getElem?_take_of_lt hn, getElem?_take_of_lt hn]
    simpa using h n (by omega)
  · rw [getElem?_take_eq_none hn, getElem?_take_eq_none hn]

theorem config_append_left (h : i < (u.length : ℤ)) : (u ++ v).config i = u.config i := by
  rcases lt_or_ge i 0 with h0 | h0
  · rw [config_of_neg h0, config_of_neg h0]
  · rw [config_of_nonneg h0, config_of_nonneg h0, getElem?_append_left (by omega)]

theorem config_take {c : ℕ} (h : i < (c : ℤ)) : (w.take c).config i = w.config i := by
  rcases lt_or_ge i 0 with h0 | h0
  · rw [config_of_neg h0, config_of_neg h0]
  · rw [config_of_nonneg h0, config_of_nonneg h0, getElem?_take_of_lt (by omega)]

/-! ### Windows -/

/-- The width-`k` window of `w` at `i`: its family restricted to `[i, i + k)`. -/
def window (k : ℕ) (w : List α) (i : ℤ) : List (Option α) :=
  ofFn fun j : Fin k ↦ w.config (i + (j : ℕ))

@[simp] theorem length_window : (window k w i).length = k := by simp [window]

theorem getElem?_window {j : ℕ} (h : j < k) :
    (window k w i)[j]? = some (w.config (i + j)) := by
  simp [window, h]

theorem window_eq_window_iff :
    window k w i = window k y q ↔ ∀ j : ℕ, j < k → w.config (i + j) = y.config (q + j) := by
  simp [window, ofFn_inj, funext_iff, Fin.forall_iff]

end List
