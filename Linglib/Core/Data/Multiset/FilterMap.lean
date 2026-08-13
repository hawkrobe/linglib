/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Order.Group.Multiset

/-!
# `Multiset.filterMap` as a bundled hom

`[UPSTREAM]` candidate: the `filterMap` analogue of
`Multiset.mapAddMonoidHom`.
-/

namespace Multiset

variable {α β : Type*}

/-- `Multiset.filterMap` as an additive monoid hom. -/
def filterMapAddMonoidHom (f : α → Option β) : Multiset α →+ Multiset β where
  toFun s := s.filterMap f
  map_zero' := Multiset.filterMap_zero f
  map_add' s t := Multiset.filterMap_add f s t

@[simp] theorem coe_filterMapAddMonoidHom (f : α → Option β) :
    ⇑(filterMapAddMonoidHom f) = filterMap f := rfl

@[simp] theorem filterMapAddMonoidHom_apply (f : α → Option β) (s : Multiset α) :
    filterMapAddMonoidHom f s = s.filterMap f := rfl

end Multiset
