/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.GroupTheory.Congruence.Hom`, extending its `section Mul`.
Upstreaming needs `@[to_additive]` on each declaration, and the monoid `Con.lift`/`Con.map`
should then be re-derived from these, as `Con.mk'` already is from `Con.mkMulHom`.
-/
import Mathlib.GroupTheory.Congruence.Hom

/-!
# Homomorphisms on a congruence quotient of a magma

Mathlib's `Con` API for quotient homomorphisms — `Con.lift`, `Con.kerLift`, `Con.map` and the
isomorphism theorems — lives in `section MulOneClass` and is `MonoidHom`-valued. Its `section Mul`
provides only `Con.mkMulHom`, `Con.ker`, `Con.mapGen`, `Con.mapOfSurjective` and
`Con.correspondence`. This file supplies the `MulHom`-valued lift, kernel lift and map, which is
what a quotient argument over a bare `Semigroup` needs.

Homomorphisms are *consumed* through `MulHomClass` and *produced* as concrete `→ₙ*`, following
`Con.ker` and `Con.mapOfSurjective`.

## Main definitions

* `Con.liftMulHom`: the homomorphism induced on the quotient by one constant on the classes.
* `Con.kerLiftMulHom`: the injective homomorphism induced by `f` on the quotient by its kernel.
* `Con.mapMulHom`: the surjection `c.Quotient →ₙ* d.Quotient` induced by `c ≤ d`.

## Main results

* `Con.kerLiftMulHom_injective`: the kernel lift is injective — the divisor half of the first
  isomorphism theorem, which is what closure-under-quotient arguments actually consume.
-/

variable {M N : Type*} [Mul M] [Mul N] {F : Type*} [FunLike F M N] [MulHomClass F M N]

namespace Con

variable (c : Con M)

/-- The homomorphism on `c.Quotient` induced by a homomorphism constant on `c`'s classes. -/
def liftMulHom (f : F) (H : c ≤ Con.ker f) : c.Quotient →ₙ* N where
  toFun x := Con.liftOn x f fun _ _ h => H h
  map_mul' x y := Con.induction_on₂ x y fun _ _ => by
    dsimp only [← Con.coe_mul, Con.liftOn_coe]
    rw [map_mul]

@[simp] theorem liftMulHom_coe (f : F) (H : c ≤ Con.ker f) (x : M) :
    c.liftMulHom f H (x : c.Quotient) = f x := rfl

theorem liftMulHom_surjective_of_surjective {f : F} (H : c ≤ Con.ker f)
    (hf : Function.Surjective f) : Function.Surjective (c.liftMulHom f H) := fun y =>
  have ⟨w, hw⟩ := hf y
  ⟨(w : c.Quotient), hw⟩

variable {c}

/-- The homomorphism induced by `f` on the quotient by its kernel. -/
def kerLiftMulHom (f : F) : (Con.ker f).Quotient →ₙ* N := liftMulHom _ f le_rfl

@[simp] theorem kerLiftMulHom_coe (f : F) (x : M) :
    kerLiftMulHom f (x : (Con.ker f).Quotient) = f x := rfl

/-- **The kernel lift is injective.** This is the half of the first isomorphism theorem that
quotient arguments consume: it exhibits `(ker f).Quotient` as a sub-object of `N`. -/
theorem kerLiftMulHom_injective (f : F) : Function.Injective (kerLiftMulHom f) := by
  rintro ⟨x⟩ ⟨y⟩ h
  exact Con.eq _ |>.2 <| (Con.ker_rel f).2 h

theorem kerLiftMulHom_surjective_of_surjective {f : F} (hf : Function.Surjective f) :
    Function.Surjective (kerLiftMulHom f) := liftMulHom_surjective_of_surjective _ le_rfl hf

variable (c)

/-- The surjection of quotients induced by a coarsening `c ≤ d`. -/
def mapMulHom (d : Con M) (h : c ≤ d) : c.Quotient →ₙ* d.Quotient :=
  c.liftMulHom (d.mkMulHom) (by rw [Con.ker_mkMulHom_eq]; exact h)

@[simp] theorem mapMulHom_coe (d : Con M) (h : c ≤ d) (x : M) :
    c.mapMulHom d h (x : c.Quotient) = (x : d.Quotient) := rfl

theorem mapMulHom_surjective (d : Con M) (h : c ≤ d) :
    Function.Surjective (c.mapMulHom d h) := fun x => by
  rcases x with ⟨x⟩; exact ⟨(x : c.Quotient), rfl⟩

end Con
