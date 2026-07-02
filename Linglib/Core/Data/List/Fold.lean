/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic

/-!
# Folds over Boolean accumulation

A left fold that ors in a predicate computes `any`, from any starting accumulator.
Candidate for `Mathlib/Data/List/Basic.lean`.
-/

namespace List

theorem foldl_or {α : Type*} (p : α → Bool) (acc : Bool) (l : List α) :
    l.foldl (fun r a => r || p a) acc = (acc || l.any p) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.or_assoc]

end List
