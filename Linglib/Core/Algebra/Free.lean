/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Left combs in a free magma

An element of a free magma is a left comb when every product in it has a generator as its right
factor. A left comb is thus built from one generator by multiplying on the right by one
generator at a time, and it is the bracketing `((a * b) * c) * d` of its generators.

## Main definitions

* `FreeMagma.IsLeftComb`: the element is a left comb.

## Main results

* `FreeMagma.isLeftComb_foldl_mul_of`: multiplying on the right by generators preserves and
  reflects being a left comb.
* `FreeMagma.toList_lift_foldl_mul_of`: multiplying on the right by generators appends them to
  the list of generators.
-/

@[expose] public section

namespace FreeMagma

variable {α : Type*}

/-- An element of a free magma is a left comb when every product in it has a generator as its
right factor. -/
def IsLeftComb : FreeMagma α → Prop
  | of _ => True
  | mul x (of _) => IsLeftComb x
  | mul _ (mul _ _) => False

instance decidableIsLeftComb : (x : FreeMagma α) → Decidable (IsLeftComb x)
  | of _ => isTrue trivial
  | mul x (of _) => decidableIsLeftComb x
  | mul _ (mul _ _) => isFalse id

@[simp] theorem isLeftComb_of (a : α) : IsLeftComb (of a) := trivial

@[simp] theorem isLeftComb_mul_of (x : FreeMagma α) (a : α) :
    IsLeftComb (x * of a) ↔ IsLeftComb x := Iff.rfl

@[simp] theorem not_isLeftComb_mul_mul (x y z : FreeMagma α) : ¬ IsLeftComb (x * (y * z)) := id

theorem isLeftComb_foldl_mul_of (x : FreeMagma α) (l : List α) :
    IsLeftComb (l.foldl (· * of ·) x) ↔ IsLeftComb x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem toList_lift_foldl_mul_of (x : FreeMagma α) (l : List α) :
    (lift FreeMonoid.of (l.foldl (· * of ·) x)).toList = (lift FreeMonoid.of x).toList ++ l := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih]

end FreeMagma
