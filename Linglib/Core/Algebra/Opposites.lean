/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: mathlib has neither instance; the ones for `Additive` and `Multiplicative`
are in `Mathlib.Algebra.Group.TypeTags.Finite`.
-/
module

public import Mathlib.Algebra.Opposites
public import Mathlib.Basic.Finite.Defs

/-!
# `Finite` and `Infinite` are preserved by `MulOpposite` and `AddOpposite`
-/

@[expose] public section

namespace MulOpposite

variable {α : Type*}

@[to_additive]
instance instFinite [Finite α] : Finite αᵐᵒᵖ := .of_equiv α opEquiv

@[to_additive]
instance instInfinite [Infinite α] : Infinite αᵐᵒᵖ := opEquiv.infinite_iff.mp ‹_›

end MulOpposite
