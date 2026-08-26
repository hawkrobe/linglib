/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fin.VecNotation

/-!
# Mapping a function over `![…]`

`[UPSTREAM]` candidate for `Mathlib/Data/Fin/VecNotation.lean`. The η-expanded
forms of `Fin.comp_cons` and of the empty case, stated on the lambda
`fun i => f (![a, …] i)` so that `simp` pushes `f` into a vector literal.
-/

namespace Matrix

variable {α β : Type*} {n : ℕ}

theorem comp_vecCons (f : α → β) (a : α) (v : Fin n → α) :
    (fun i => f (vecCons a v i)) = vecCons (f a) fun i => f (v i) :=
  Fin.comp_cons f a v

theorem comp_vecEmpty (f : α → β) : (fun i => f (![] i)) = (![] : Fin 0 → β) :=
  funext fun i => i.elim0

end Matrix
