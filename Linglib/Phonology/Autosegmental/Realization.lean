/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Linglib.Phonology.Autosegmental.AR

/-!
# Autosegmental realization of strings

The **realization** of a string maps each symbol to its autosegmental graph primitive
and concatenates them ([jardine-2019]'s mapping `g`): `realize g₀ w = ∏ (w.map g₀)` in
the concatenation monoid `Monoid (AR α β)`.

This is a string→AR **monoid homomorphism** (`realize_append`), the exact analogue —
one categorical level up — of the string→tier-string projection
`TierProjection.apply` (= `List.filterMap`, also concat-distributing): both are
free-monoid homomorphisms built from a per-symbol map, used to define a subregular
class as a *preimage* (`Phonology/Autosegmental/ASL.lean` for the realization,
`Subregular.Language.TierStrictlyLocal` for the projection). The realization keeps the
association structure the tier projection discards — see [jardine-2019] on `ASL` vs
`TSL`.
-/

namespace Autosegmental

variable {S : Type*} {α β : Type*}

/-- **Realize** a string as an autosegmental representation: concatenate the graph
    primitives `g₀ a` of its symbols ([jardine-2019]'s `g`). -/
def realize (g₀ : S → AR α β) (w : List S) : AR α β := (w.map g₀).prod

@[simp] theorem realize_nil (g₀ : S → AR α β) : realize g₀ [] = AR.empty := rfl

@[simp] theorem realize_cons (g₀ : S → AR α β) (a : S) (w : List S) :
    realize g₀ (a :: w) = (g₀ a).concat (realize g₀ w) := rfl

/-- **The realization is a monoid homomorphism**: it distributes over concatenation —
    the string→AR analogue of `TierProjection.apply_append`. -/
theorem realize_append (g₀ : S → AR α β) (xs ys : List S) :
    realize g₀ (xs ++ ys) = (realize g₀ xs).concat (realize g₀ ys) := by
  simp only [realize, List.map_append, List.prod_append]; rfl

end Autosegmental
