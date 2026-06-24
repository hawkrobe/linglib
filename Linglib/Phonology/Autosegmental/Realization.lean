/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.FreeMonoid.Basic
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

/-! ### Tier projections

The realization composed with a tier accessor is itself a free-monoid hom into that
tier's free monoid: `upperProj g₀` sends a string to the concatenation of its symbols'
upper tiers (the underlying list of `realize g₀ w`'s upper tier), and likewise
`lowerProj`. These factor the realization's tier content through `FreeMonoid` and are
the bridge used to place link-free `ASL` sets in `SF` (`Studies.Jardine2019`): a
per-tier factor constraint on the realization is the `comap` of a factor language along
the tier projection. -/

/-- The upper-tier realization as a free-monoid hom `FreeMonoid S →* FreeMonoid α`:
each symbol maps to its primitive's upper tier, concatenated. -/
def upperProj (g₀ : S → AR α β) : FreeMonoid S →* FreeMonoid α :=
  FreeMonoid.lift (fun s => FreeMonoid.ofList (g₀ s).upper.toList)

/-- The lower-tier realization as a free-monoid hom `FreeMonoid S →* FreeMonoid β`. -/
def lowerProj (g₀ : S → AR α β) : FreeMonoid S →* FreeMonoid β :=
  FreeMonoid.lift (fun s => FreeMonoid.ofList (g₀ s).lower.toList)

@[simp] theorem upperProj_of (g₀ : S → AR α β) (s : S) :
    upperProj g₀ (FreeMonoid.of s) = FreeMonoid.ofList (g₀ s).upper.toList :=
  FreeMonoid.lift_eval_of _ _

@[simp] theorem lowerProj_of (g₀ : S → AR α β) (s : S) :
    lowerProj g₀ (FreeMonoid.of s) = FreeMonoid.ofList (g₀ s).lower.toList :=
  FreeMonoid.lift_eval_of _ _

/-- The upper tier of a realization is its upper projection: `(realize g₀ w).upper`'s
underlying list is `upperProj g₀ w`. -/
theorem realize_upper_toList (g₀ : S → AR α β) (w : List S) :
    (realize g₀ w).upper.toList = upperProj g₀ (FreeMonoid.ofList w) := by
  induction w with
  | nil => rw [realize_nil, show FreeMonoid.ofList ([] : List S) = 1 from rfl, map_one]; rfl
  | cons s w ih =>
    rw [realize_cons, AR.concat_upper, LabeledTuple.toList_concat, ih, FreeMonoid.ofList_cons,
      map_mul, upperProj_of]
    rfl

/-- The lower tier of a realization is its lower projection. -/
theorem realize_lower_toList (g₀ : S → AR α β) (w : List S) :
    (realize g₀ w).lower.toList = lowerProj g₀ (FreeMonoid.ofList w) := by
  induction w with
  | nil => rw [realize_nil, show FreeMonoid.ofList ([] : List S) = 1 from rfl, map_one]; rfl
  | cons s w ih =>
    rw [realize_cons, AR.concat_lower, LabeledTuple.toList_concat, ih, FreeMonoid.ofList_cons,
      map_mul, lowerProj_of]
    rfl

end Autosegmental
