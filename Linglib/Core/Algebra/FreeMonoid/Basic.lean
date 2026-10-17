/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.FreeMonoid.Basic`, next to `FreeMonoid.map`.
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Filtering the letters of a free monoid

`FreeMonoid.filter p` keeps the letters satisfying `p` and erases the others. It is the monoid
endomorphism that `List.filter p` induces on `FreeMonoid α`, and unlike `FreeMonoid.map` it is
erasing: it can send a nonempty word to `1`.

## Main definitions

* `FreeMonoid.filter`: the erasing endomorphism keeping the letters that satisfy `p`.

## References

* [pin-mfa]
-/

@[expose] public section

namespace FreeMonoid

variable {α : Type*} (p : α → Bool)

/-- The endomorphism of the free monoid keeping the letters that satisfy `p`. -/
def filter : FreeMonoid α →* FreeMonoid α where
  toFun w := ofList (w.toList.filter p)
  map_one' := rfl
  map_mul' x y := List.filter_append x.toList y.toList

@[simp] theorem toList_filter (w : FreeMonoid α) : (filter p w).toList = w.toList.filter p := rfl

@[simp] theorem filter_ofList (w : List α) : filter p (ofList w) = ofList (w.filter p) := rfl

end FreeMonoid
