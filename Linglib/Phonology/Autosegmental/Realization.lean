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

/-- Representations with the classical precedence-preserving morphisms. -/
abbrev PrecAR (ι : Type*) (τ : ι → Type*) :=
  WideSubcategory (AR.precPreserving (t := (Sigma.fst : ((i : ι) × τ i) → ι)))

namespace AR

open scoped MonoidalCategory

variable {S : Type*} (g₀ : S → TieredAR ι τ)

/-! ### The monoid of representations up to isomorphism -/

/-- A full isomorphism is an isomorphism of the precedence-preserving category;
    both directions preserve arcs. -/
noncomputable def fullIsoToWideIso {A B : TieredAR ι τ}
    (e : Graph.Iso A.obj B.obj) : (⟨A⟩ : PrecAR ι τ) ≅ ⟨B⟩ :=
  CategoryTheory.isoMk (mkIso e) e.toHom_precPreserving e.symm.toHom_precPreserving

/-- The class of a representation, its isomorphism class in the skeleton of the
    precedence-preserving category. -/
noncomputable def cls (A : TieredAR ι τ) : Skeleton (PrecAR ι τ) :=
  toSkeleton ⟨A⟩

/-- Concatenation of classes is the class of the tensor. -/
theorem cls_tensor (A B : TieredAR ι τ) : cls (A ⊗ B) = cls A * cls B :=
  CategoryTheory.Skeleton.toSkeleton_tensorObj (⟨A⟩ : PrecAR ι τ) ⟨B⟩

/-- Normal forms represent their class. -/
theorem cls_normalize {X : TieredAR ι τ} [Finite X.obj.V] :
    cls (X.normalize) = cls X :=
  Quotient.sound ⟨fullIsoToWideIso X.normalizeFullIso⟩

/-! ### Realization of strings -/

/-- Realize a string as a representation: the iterated tensor of its symbols'
    primitives ([jardine-2019]'s `g`). -/
noncomputable def realize (w : List S) : TieredAR ι τ :=
  (w.map g₀).foldr (· ⊗ ·) (𝟙_ _)

@[simp] theorem realize_nil : realize g₀ [] = 𝟙_ _ := rfl

@[simp] theorem realize_cons (a : S) (w : List S) :
    realize g₀ (a :: w) = g₀ a ⊗ realize g₀ w := rfl

/-! ### Tier content of realizations -/

instance realize.instFinite [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    Finite (realize g₀ w).obj.V := by
  induction w with
  | nil => exact inferInstanceAs (Finite PEmpty)
  | cons a w ih => exact inferInstanceAs (Finite ((g₀ a).obj.V ⊕ (realize g₀ w).obj.V))

/-- The tier word of a realized string is the concatenation of its symbols' tier words. -/
theorem tierWord_realize [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
    (realize g₀ w).tierWord i = (w.map fun s => (g₀ s).tierWord i).flatten := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

/-- The tier-`i` projection of a realization, as a free-monoid homomorphism:
    each symbol contributes its primitive's tier word. -/
noncomputable def tierProj [∀ s, Finite (g₀ s).obj.V] (i : ι) :
    FreeMonoid S →* FreeMonoid (τ i) :=
  FreeMonoid.lift fun s => FreeMonoid.ofList ((g₀ s).tierWord i)

@[simp] theorem tierProj_of [∀ s, Finite (g₀ s).obj.V] (i : ι) (a : S) :
    tierProj g₀ i (FreeMonoid.of a) = FreeMonoid.ofList ((g₀ a).tierWord i) := rfl

/-- `tierProj` packages `tierWord`: on a word it is the realized tier word. -/
theorem tierProj_ofList [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
    tierProj g₀ i (FreeMonoid.ofList w) = FreeMonoid.ofList ((realize g₀ w).tierWord i) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [FreeMonoid.ofList_cons, FreeMonoid.ofList_append, ih]

end AR

end Autosegmental
