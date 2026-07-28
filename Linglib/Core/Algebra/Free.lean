/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Free`. Upstreaming requires `@[to_additive]` with a
`FreeAddSemigroup.toList` counterpart, as every declaration in that file is additivized.
-/
import Mathlib.Algebra.Free

/-!
# The word underlying a free-semigroup element

`FreeSemigroup α` is presented in mathlib as a `head`/`tail` pair, with no conversion to `List α`.
`FreeSemigroup.toList` supplies it; the free semigroup is the nonempty words, so the conversion is
`head :: tail` and multiplication becomes concatenation.
-/

namespace FreeSemigroup

variable {α : Type*}

/-- The nonempty word underlying a free-semigroup element. -/
def toList (u : FreeSemigroup α) : List α := u.head :: u.tail

@[simp] theorem toList_mul (u v : FreeSemigroup α) :
    (u * v).toList = u.toList ++ v.toList := rfl

end FreeSemigroup
