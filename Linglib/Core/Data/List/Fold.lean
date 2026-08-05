/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic

/-!
# Folds over Boolean accumulation

A fold that ors in a predicate computes `any`, and one that ands it in computes `all`,
from any starting accumulator and in either direction. Candidates for the fold section
of core's `Init.Data.List.Lemmas` (the op-specific sibling of `List.foldl_max`).
-/

namespace List

variable {α : Type*} {p : α → Bool} {b : Bool} {l : List α}

theorem foldl_or : l.foldl (fun r a => r || p a) b = (b || l.any p) := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.or_assoc]

theorem foldr_or : l.foldr (fun a r => r || p a) b = (b || l.any p) := by
  induction l with
  | nil => simp
  | cons x xs ih => rw [foldr_cons, ih, any_cons]; ac_rfl

theorem foldl_and : l.foldl (fun r a => r && p a) b = (b && l.all p) := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.and_assoc]

theorem foldr_and : l.foldr (fun a r => r && p a) b = (b && l.all p) := by
  induction l with
  | nil => simp
  | cons x xs ih => rw [foldr_cons, ih, all_cons]; ac_rfl

end List
