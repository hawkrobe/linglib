/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

/-!
# Words as blank-padded indexed families

`List.config` reads a word as a two-sided indexed family `ℤ → Option α`: letters on
`[0, w.length)`, blank (`none`) elsewhere; `List.window k w i` is its width-`k` slice
at `i`. Position-indexed statements about words replace factor-of-augmented-word
bookkeeping: a window entry is a letter or a blank according to a single interval
test, so occurrence pinning is interval arithmetic.

[UPSTREAM] candidate: `Mathlib.Data.List`, on the `List.toFinsupp` precedent — a list
as an indexed family with a default.
-/

namespace List

variable {α : Type*} {w y u v : List α} {i q : ℤ} {a : α} {k : ℕ}

/-- The two-sided configuration of a word: letters on `[0, w.length)`, blank
elsewhere. -/
def config (w : List α) : ℤ → Option α :=
  fun i => if 0 ≤ i then w[i.toNat]? else none

@[simp] lemma config_natCast (w : List α) (n : ℕ) : w.config n = w[n]? := by
  simp [config]

lemma config_neg (h : i < 0) : w.config i = none := by
  rw [config, if_neg (by omega)]

@[simp] lemma config_nil : ([] : List α).config i = none := by
  rw [config]
  split_ifs <;> simp

lemma config_eq_none_iff : w.config i = none ↔ i < 0 ∨ (w.length : ℤ) ≤ i := by
  rw [config]
  split_ifs with h0
  · rw [List.getElem?_eq_none_iff]
    omega
  · exact iff_of_true rfl (.inl (by omega))

lemma bounds_of_config_eq_some (h : w.config i = some a) : 0 ≤ i ∧ i < w.length := by
  rw [config] at h
  split_ifs at h with h0
  exact ⟨h0, by have := (List.getElem?_eq_some_iff.mp h).1; omega⟩

lemma getElem?_of_config_eq_some (h : w.config i = some a) : w[i.toNat]? = some a := by
  rw [config] at h
  split_ifs at h with h0
  exact h

/-- Agreement of configurations up to the word's length forces equality. -/
lemma eq_of_config_agree (h : ∀ j : ℤ, j ≤ (w.length : ℤ) → y.config j = w.config j) :
    y = w := by
  have hy : y.length ≤ w.length := by
    have h1 := h (w.length : ℤ) le_rfl
    rw [config_natCast, config_natCast, List.getElem?_eq_none le_rfl,
      List.getElem?_eq_none_iff] at h1
    exact h1
  apply List.ext_getElem?
  intro n
  rcases lt_or_ge n w.length with hn | hn
  · have := h n (by omega)
    rwa [config_natCast, config_natCast] at this
  · rw [List.getElem?_eq_none hn, List.getElem?_eq_none (by omega)]

/-- Agreement of configurations below `c` transfers `c`-prefixes. -/
lemma take_eq_of_config_agree {c : ℕ}
    (h : ∀ j : ℤ, j < (c : ℤ) → y.config j = w.config j) : y.take c = w.take c := by
  apply List.ext_getElem?
  intro n
  rcases lt_or_ge n c with hn | hn
  · rw [List.getElem?_take_of_lt hn, List.getElem?_take_of_lt hn]
    have := h n (by omega)
    rwa [config_natCast, config_natCast] at this
  · rw [List.getElem?_take_eq_none hn, List.getElem?_take_eq_none hn]

lemma config_append_left (h : i < (u.length : ℤ)) : (u ++ v).config i = u.config i := by
  rw [config, config]
  split_ifs with h0
  · rw [List.getElem?_append_left (by omega)]
  · rfl

lemma config_take {c : ℕ} (h : i < (c : ℤ)) : (w.take c).config i = w.config i := by
  rw [config, config]
  split_ifs with h0
  · rw [List.getElem?_take_of_lt (by omega)]
  · rfl

/-! ### Windows -/

/-- The width-`k` window of `w` at `i`: the configuration restricted to `[i, i + k)`. -/
def window (k : ℕ) (w : List α) (i : ℤ) : List (Option α) :=
  List.ofFn fun j : Fin k => w.config (i + (j : ℕ))

@[simp] lemma length_window : (window k w i).length = k := by simp [window]

lemma getElem?_window {j : ℕ} (h : j < k) :
    (window k w i)[j]? = some (w.config (i + j)) := by
  rw [window, List.getElem?_ofFn]
  simp [h]

lemma window_eq_window_iff :
    window k w i = window k y q ↔ ∀ j : ℕ, j < k → w.config (i + j) = y.config (q + j) := by
  constructor
  · intro h j hj
    have := congrArg (fun l => l[j]?) h
    simp only [getElem?_window hj] at this
    exact Option.some_injective _ this
  · intro h
    apply List.ext_getElem?
    intro j
    rcases lt_or_ge j k with hj | hj
    · rw [getElem?_window hj, getElem?_window hj, h j hj]
    · rw [List.getElem?_eq_none (by simpa using hj),
        List.getElem?_eq_none (by simpa using hj)]

end List
