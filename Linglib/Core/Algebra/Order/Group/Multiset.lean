/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Group.Multiset

/-!
# `Multiset.filterMap` as an additive monoid hom

`Multiset.filterMapAddMonoidHom` bundles `Multiset.filterMap f` as an additive monoid hom, as
`Multiset.mapAddMonoidHom` bundles `Multiset.map f`, so that `map_sum`, `map_list_sum` and
`map_nsmul` apply to it. `[UPSTREAM]` candidate; eventual mathlib home
`Mathlib.Algebra.Order.Group.Multiset`.
-/

@[expose] public section

namespace Multiset

variable {α β : Type*}

/-- `Multiset.filterMap` as an `AddMonoidHom`. -/
@[simps]
def filterMapAddMonoidHom (f : α → Option β) : Multiset α →+ Multiset β where
  toFun := filterMap f
  map_zero' := filterMap_zero f
  map_add' := filterMap_add f

@[simp] theorem coe_filterMapAddMonoidHom (f : α → Option β) :
    ⇑(filterMapAddMonoidHom f) = filterMap f := rfl

end Multiset
