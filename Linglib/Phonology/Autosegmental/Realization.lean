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
* `AR.tierWord_realize`, `AR.link_realize`: tier content and links of a realization are
  compositional — each link lives inside one symbol's primitive at that symbol's tier
  offsets (`AR.tierOffset`).
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

@[simp] theorem tierLength_realize [∀ s, Finite (g₀ s).obj.V] (i : ι) (w : List S) :
    (realize g₀ w).tierLength i = (w.map fun s => (g₀ s).tierLength i).sum := by
  rw [← length_tierWord, tierWord_realize, List.length_flatten, List.map_map]
  simp [Function.comp_def]

/-! ### Links of realizations -/

variable [∀ s, Finite (g₀ s).obj.V]

/-- The tier-`i` offset of the `k`-th symbol of `w` in its realization: the tier-`i` content
of the prefix before it. -/
noncomputable def tierOffset (i : ι) (w : List S) (k : ℕ) : ℕ :=
  (realize g₀ (w.take k)).tierLength i

@[simp] theorem tierOffset_zero (i : ι) (w : List S) : tierOffset g₀ i w 0 = 0 := by
  simp [tierOffset]

@[simp] theorem tierOffset_cons_succ (i : ι) (a : S) (w : List S) (k : ℕ) :
    tierOffset g₀ i (a :: w) (k + 1) = (g₀ a).tierLength i + tierOffset g₀ i w k := by
  simp [tierOffset, List.take_succ_cons]

/-- Links of a realization are blockwise: a link lives inside one symbol's primitive, at
that symbol's tier offsets — the link half of `tierWord_realize`. -/
theorem link_realize (i j : ι) (w : List S) (p q : ℕ) :
    (realize g₀ w).link i j p q ↔
      ∃ k, ∃ hk : k < w.length, tierOffset g₀ i w k ≤ p ∧ tierOffset g₀ j w k ≤ q ∧
        (g₀ w[k]).link i j (p - tierOffset g₀ i w k) (q - tierOffset g₀ j w k) := by
  induction w generalizing p q with
  | nil => simp
  | cons a w ih =>
    rw [show (realize g₀ (a :: w)).link i j p q ↔ (g₀ a ⊗ realize g₀ w).link i j p q from
      Iff.rfl, link_tensor, ih]
    constructor
    · rintro (h | ⟨hp, hq, k, hk, hpk, hqk, h⟩)
      · exact ⟨0, by simp, by simp, by simp, by simpa using h⟩
      · exact ⟨k + 1, by simpa using hk, by simp; omega, by simp; omega,
          by simpa [Nat.sub_sub] using h⟩
    · rintro ⟨_ | k, hk, hpk, hqk, h⟩
      · exact Or.inl (by simpa using h)
      · simp only [tierOffset_cons_succ, List.getElem_cons_succ] at hpk hqk h
        exact Or.inr ⟨by omega, by omega, k, by simpa using hk, by omega, by omega,
          by simpa [Nat.sub_sub] using h⟩

/-- With one tier-`j` position per symbol, tier-`j` positions of the realization are the
string's positions: a link at position `q` is a link inside the `q`-th symbol's primitive. -/
theorem link_realize_of_tierLength_eq_one {j : ι} (hj : ∀ s, (g₀ s).tierLength j = 1)
    (i : ι) (w : List S) (p q : ℕ) :
    (realize g₀ w).link i j p q ↔
      ∃ hq : q < w.length, tierOffset g₀ i w q ≤ p ∧
        (g₀ w[q]).link i j (p - tierOffset g₀ i w q) 0 := by
  have hoff : ∀ k ≤ w.length, tierOffset g₀ j w k = k := fun k hk => by
    simp [tierOffset, hj, hk]
  rw [link_realize]
  constructor
  · rintro ⟨k, hk, hpk, hqk, h⟩
    rw [hoff k hk.le] at hqk h
    obtain ⟨-, hlt, -⟩ := id h
    rw [hj] at hlt
    obtain rfl : k = q := by omega
    exact ⟨hk, hpk, by simpa using h⟩
  · rintro ⟨hq, hpq, h⟩
    exact ⟨q, hq, hpq, by rw [hoff q hq.le], by simpa [hoff q hq.le] using h⟩

/-- The tier-`i` projection of a realization, as a free-monoid homomorphism:
    each symbol contributes its primitive's tier word. -/
noncomputable def tierProj (i : ι) : FreeMonoid S →* FreeMonoid (τ i) :=
  FreeMonoid.lift fun s => FreeMonoid.ofList ((g₀ s).tierWord i)

@[simp] theorem tierProj_of (i : ι) (a : S) :
    tierProj g₀ i (FreeMonoid.of a) = FreeMonoid.ofList ((g₀ a).tierWord i) := rfl

/-- `tierProj` packages `tierWord`: on a word it is the realized tier word. -/
theorem tierProj_ofList (i : ι) (w : List S) :
    tierProj g₀ i (FreeMonoid.ofList w) = FreeMonoid.ofList ((realize g₀ w).tierWord i) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [FreeMonoid.ofList_cons, FreeMonoid.ofList_append, ih]

end AR

end Autosegmental
