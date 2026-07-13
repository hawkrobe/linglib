/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Linglib.Phonology.Autosegmental.NormalForm

/-!
# Realization of strings as representations

[jardine-2019]'s mapping `g`: each symbol denotes a representation primitive and
a string denotes their iterated tensor. The monoid-homomorphism content lives on
the skeleton of the precedence-preserving wide subcategory `PrecAR`, where
concatenation is strictly associative; broad categorical isomorphism forgets the
arcs and is too coarse to preserve tier words.

## Main definitions

* `PrecAR`, `AR.cls`: representations with the classical precedence-preserving
  morphisms, and the monoid of their isomorphism classes.
* `AR.realize`, `AR.tierProj`: the realization as iterated tensor, and its per-tier
  projections as free-monoid homomorphisms.

## Main results

* `AR.cls_normalize`: normal forms represent their class.
* `AR.tierWord_realize`: tier content of a realization is compositional.
-/

namespace Autosegmental

open CategoryTheory

variable {ι : Type*} {τ : ι → Type*}

/-! ### The monoid of representations up to isomorphism -/

section IsoClasses
open scoped MonoidalCategory

/-- Representations with the classical precedence-preserving morphisms. -/
abbrev PrecAR (ι : Type*) (τ : ι → Type*) :=
  WideSubcategory (AR.precPreserving (t := (Sigma.fst : ((i : ι) × τ i) → ι)))

/-- A full isomorphism is an isomorphism of the precedence-preserving category;
    both directions preserve arcs. -/
noncomputable def AR.fullIsoToWideIso {A B : TieredAR ι τ}
    (e : Graph.Iso A.obj B.obj) : (⟨A⟩ : PrecAR ι τ) ≅ ⟨B⟩ :=
  CategoryTheory.isoMk (AR.mkIso e) e.toHom_precPreserving e.symm.toHom_precPreserving

/-- The class of a representation, its isomorphism class in the skeleton of the
    precedence-preserving category. -/
noncomputable def AR.cls
    (A : TieredAR ι τ) :
    Skeleton (PrecAR ι τ) :=
  toSkeleton ⟨A⟩

/-- Concatenation of classes is the class of the tensor. -/
theorem AR.cls_tensor
    (A B : TieredAR ι τ) :
    AR.cls (A ⊗ B) = AR.cls A * AR.cls B :=
  CategoryTheory.Skeleton.toSkeleton_tensorObj (⟨A⟩ : PrecAR ι τ) ⟨B⟩

/-- Normal forms represent their class. -/
theorem AR.cls_normalize {X : TieredAR ι τ}
    [Finite X.obj.V] : AR.cls (X.normalize) = AR.cls X :=
  Quotient.sound ⟨AR.fullIsoToWideIso X.normalizeFullIso⟩

end IsoClasses

/-! ### Realization of strings -/

section Realize
open scoped MonoidalCategory

variable {S : Type*}

/-- Realize a string as a representation: the iterated tensor of its symbols'
    primitives ([jardine-2019]'s `g`). -/
noncomputable def AR.realize (g₀ : S → TieredAR ι τ)
    (w : List S) : TieredAR ι τ :=
  (w.map g₀).foldr (· ⊗ ·) (𝟙_ _)

@[simp] theorem AR.realize_nil (g₀ : S → TieredAR ι τ) :
    AR.realize g₀ [] = 𝟙_ _ := rfl

@[simp] theorem AR.realize_cons (g₀ : S → TieredAR ι τ)
    (a : S) (w : List S) : AR.realize g₀ (a :: w) = g₀ a ⊗ AR.realize g₀ w := rfl

end Realize

/-! ### Tier content of realizations -/

section RealizeTierWord
open scoped MonoidalCategory

variable {S : Type*}
variable (g₀ : S → TieredAR ι τ)

instance AR.realize.instFinite [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    Finite (AR.realize g₀ w).obj.V := by
  induction w with
  | nil => exact inferInstanceAs (Finite PEmpty)
  | cons a w ih => exact inferInstanceAs (Finite ((g₀ a).obj.V ⊕ (AR.realize g₀ w).obj.V))

/-- The tier word of a realized string is the concatenation of its symbols' tier words. -/
theorem AR.tierWord_realize [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
    (AR.realize g₀ w).tierWord i = (w.map fun s => (g₀ s).tierWord i).flatten := by
  induction w with
  | nil => simp
  | cons a w ih =>
    calc (AR.realize g₀ (a :: w)).tierWord i
        = (g₀ a ⊗ AR.realize g₀ w).tierWord i := rfl
      _ = ((a :: w).map fun s => (g₀ s).tierWord i).flatten := by simp [ih]

/-- The tier-`i` projection of a realization, as a free-monoid homomorphism:
    each symbol contributes its primitive's tier word. -/
noncomputable def AR.tierProj [∀ s, Finite (g₀ s).obj.V] (i : ι) :
    FreeMonoid S →* FreeMonoid (τ i) :=
  FreeMonoid.lift fun s => FreeMonoid.ofList ((g₀ s).tierWord i)

/-- `AR.tierProj` packages `tierWord`: on a word it is the realized tier word. -/
theorem AR.tierProj_ofList [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
    AR.tierProj g₀ i (FreeMonoid.ofList w) = FreeMonoid.ofList ((AR.realize g₀ w).tierWord i) := by
  induction w with
  | nil => simp [AR.realize_nil]
  | cons a w ih =>
    rw [show FreeMonoid.ofList (a :: w) = FreeMonoid.of a * FreeMonoid.ofList w from rfl,
      map_mul, ih]
    calc FreeMonoid.ofList ((g₀ a).tierWord i) * FreeMonoid.ofList ((AR.realize g₀ w).tierWord i)
        = FreeMonoid.ofList ((g₀ a).tierWord i ++ (AR.realize g₀ w).tierWord i) := rfl
      _ = _ := by rw [← AR.tierWord_tensor i]; rfl

end RealizeTierWord

end Autosegmental
