/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Opposites`, where `MulOpposite` is defined.
-/
import Mathlib.Algebra.Opposites
import Mathlib.Data.Finite.Defs

/-!
# Finiteness of the multiplicative opposite

`MulOpposite α` carries no multiplication of its own here: it is finite exactly when `α` is.
-/

instance MulOpposite.instFinite {α : Type*} [Finite α] : Finite αᵐᵒᵖ :=
  Finite.of_equiv α MulOpposite.opEquiv
