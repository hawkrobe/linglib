/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.End`, where `Function.End` is defined.
-/
import Mathlib.Algebra.Group.End
import Mathlib.Data.Finite.Prod

/-!
# Finiteness of the endomorphism monoid

`Function.End α` is a plain `def` for `α → α`, so instance search does not see through it.
-/

/-- `Function.End α` is a plain `def`, so `Finite` does not see through it to `α → α`. -/
instance Function.End.instFinite {α : Type*} [Finite α] : Finite (Function.End α) :=
  inferInstanceAs (Finite (α → α))
