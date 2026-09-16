/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Zip

/-!
# `revzip` of a mapped list

`revzip` commutes with `map`, componentwise. `[UPSTREAM]` candidate; eventual mathlib home
`Mathlib.Data.List.Zip`.
-/

namespace List

variable {α β : Type*}

theorem revzip_map (f : α → β) (l : List α) :
    (l.map f).revzip = l.revzip.map (Prod.map f f) := by
  rw [revzip, revzip, ← map_reverse, zip_map]

end List
