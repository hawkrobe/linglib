/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic
import Linglib.Core.Data.List.Destutter

/-!
# The destutter quotient monoid of a free monoid

For `[DecidableEq α]`, `List.destutter (· ≠ ·)` collapses each maximal run of equal adjacent
elements to one; the lists it fixes are exactly the `List.IsChain (· ≠ ·)` lists (no two
adjacent elements equal). Under **append-then-destutter** these form a monoid, and
`List.destutter (· ≠ ·)` is the quotient homomorphism out of the free monoid:
`{l // l.IsChain (· ≠ ·)} ≃* FreeMonoid α ⧸ ker`.

## Main definitions

* `List.destutterConcat` — append, then `destutter (· ≠ ·)`; the monoid multiplication.
* `Monoid {l : List α // l.IsChain (· ≠ ·)}` — the destutter quotient monoid.
* `FreeMonoid.destutterHom` — the quotient map `FreeMonoid α →* {l // l.IsChain (· ≠ ·)}`.
* `FreeMonoid.destutterCon` — its kernel congruence on the free monoid.
* `FreeMonoid.destutterQuotientEquiv` — first isomorphism `FreeMonoid α ⧸ ker ≃* {l // …}`.

## Implementation notes

The `destutter`-vs-`++` congruence lemmas live in `Core.Data.List.Destutter` (candidates
for `Mathlib.Data.List.Destutter`); this file adds the monoid/quotient layer (candidate for
`Mathlib.Algebra.FreeMonoid`). Nothing here is specific to any application; the phonological
Obligatory Contour Principle (`Phonology.OCP`) is one consumer, reading this as
autosegmental tier fusion.
-/

namespace List

variable {α : Type*} [DecidableEq α]

/-- **Append then destutter**: concatenate, then collapse the single run that may form at
the seam. The multiplication of the destutter quotient monoid. -/
def destutterConcat (x y : List α) : List α := (x ++ y).destutter (· ≠ ·)

/-- `destutterConcat` outputs are stutter-free. -/
theorem isChain_destutterConcat (x y : List α) :
    (destutterConcat x y).IsChain (· ≠ ·) := isChain_destutter (· ≠ ·) (x ++ y)

/-- `destutterConcat` is associative — inherited from `++` through `destutter`. -/
theorem destutterConcat_assoc (x y z : List α) :
    destutterConcat (destutterConcat x y) z = destutterConcat x (destutterConcat y z) := by
  simp only [destutterConcat, destutter_append_left, destutter_append_right, List.append_assoc]

theorem nil_destutterConcat (x : List α) :
    destutterConcat [] x = x.destutter (· ≠ ·) := by simp [destutterConcat]

theorem destutterConcat_nil (x : List α) :
    destutterConcat x [] = x.destutter (· ≠ ·) := by simp [destutterConcat]

/-- `destutter (· ≠ ·)` carries `(List α, ++)` onto `(·, destutterConcat)`. -/
theorem destutter_append_eq_destutterConcat (x y : List α) :
    (x ++ y).destutter (· ≠ ·)
      = destutterConcat (x.destutter (· ≠ ·)) (y.destutter (· ≠ ·)) := by
  rw [destutterConcat, ← destutter_append_destutter]

/-! ### The bundled quotient monoid -/

instance : Mul {l : List α // l.IsChain (· ≠ ·)} :=
  ⟨fun a b => ⟨destutterConcat a b, isChain_destutterConcat _ _⟩⟩

instance : One {l : List α // l.IsChain (· ≠ ·)} := ⟨⟨[], isChain_nil⟩⟩

@[simp] theorem coe_mul (a b : {l : List α // l.IsChain (· ≠ ·)}) :
    ((a * b : {l : List α // l.IsChain (· ≠ ·)}) : List α) = destutterConcat a b := rfl

omit [DecidableEq α] in
@[simp] theorem coe_one :
    ((1 : {l : List α // l.IsChain (· ≠ ·)}) : List α) = [] := rfl

/-- The destutter quotient monoid: `destutterConcat` multiplication, `[]` unit. -/
instance : Monoid {l : List α // l.IsChain (· ≠ ·)} where
  mul_assoc a b c := Subtype.ext <| by simp [destutterConcat_assoc]
  one_mul a := Subtype.ext <| by simp [nil_destutterConcat, destutter_of_isChain _ _ a.2]
  mul_one a := Subtype.ext <| by simp [destutterConcat_nil, destutter_of_isChain _ _ a.2]

end List

namespace FreeMonoid

open List

variable {α : Type*} [DecidableEq α]

/-- The **destutter quotient map**: send a free-monoid word to its `destutter (· ≠ ·)`
normal form. `List.destutter_append_destutter` is its `map_mul`. -/
def destutterHom : FreeMonoid α →* {l : List α // l.IsChain (· ≠ ·)} where
  toFun l := ⟨l.toList.destutter (· ≠ ·), isChain_destutter _ _⟩
  map_one' := Subtype.ext (by simp [FreeMonoid.toList_one])
  map_mul' x y := Subtype.ext <| by
    simp [FreeMonoid.toList_mul, List.destutter_append_eq_destutterConcat]

theorem destutterHom_surjective :
    Function.Surjective (destutterHom : FreeMonoid α →* {l : List α // l.IsChain (· ≠ ·)}) :=
  fun c => ⟨FreeMonoid.ofList c.1, Subtype.ext <| by
    simp only [destutterHom, MonoidHom.coe_mk, OneHom.coe_mk, FreeMonoid.toList_ofList]
    exact destutter_of_isChain _ _ c.2⟩

/-- The destutter congruence on the free monoid: the kernel of `destutterHom`. -/
def destutterCon : Con (FreeMonoid α) := Con.ker destutterHom

/-- **First isomorphism theorem** for the destutter quotient: the abstract quotient
`FreeMonoid α ⧸ ker` is the concrete stutter-free model `{l // l.IsChain (· ≠ ·)}`. -/
noncomputable def destutterQuotientEquiv :
    (destutterCon (α := α)).Quotient ≃* {l : List α // l.IsChain (· ≠ ·)} :=
  Con.quotientKerEquivOfSurjective destutterHom destutterHom_surjective

end FreeMonoid
