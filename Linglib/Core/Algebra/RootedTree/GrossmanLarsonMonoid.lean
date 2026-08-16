/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningDuality
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# Grossman-Larson monoid structure
[grossman-larson-1989] [foissy-2021] [oudom-guin-2008]

Associativity of the Grossman-Larson product and the
`Semigroup`/`Monoid` instances. Foissy coassociativity of Δ^ρ
(`Coproduct/Pruning.lean`) transports back through the GL/CK duality
(`ConnesKreimer.pairing_product_assoc`): over `ℤ` the symmetry-weighted
pairing separates points, giving associativity, and `ConnesKreimer.map`
base change descends the basis case through `ℤ → ℕ → R` to any
`CommSemiring` (the product's structure constants are ℕ-valued).

## Main results (all `α : Type*`-generic)

* `mul_assoc_basis`, `mul_assoc` — associativity, `R`-generic.
* `instSemigroup`, `instMonoid` instances.

`[UPSTREAM]` candidate.
-/


namespace GrossmanLarson

variable {α : Type*} [DecidableEq α]

/-- Associativity over `ℤ`: the pairing form
    `ConnesKreimer.pairing_product_assoc` plus separation. -/
private theorem product_assoc_int (x y z : GrossmanLarson ℤ α) :
    product (product x y) z = product x (product y z) :=
  (ext_pairing_right fun w => ConnesKreimer.pairing_product_assoc x y z w).symm

/-- **Basis-level associativity** (`R`-generic): the `ℤ` case descends
    through `ConnesKreimer.map` base change — along `ℕ → ℤ` by
    injectivity, then along `Nat.cast : ℕ → R`. -/
theorem mul_assoc_basis {R : Type*} [CommSemiring R]
    (F₁ F₂ F₃ : Forest (Nonplanar α)) :
    ((of' F₁ : GrossmanLarson R α) * of' F₂) * of' F₃ =
      of' F₁ * (of' F₂ * of' F₃) := by
  have hℕ : ((of' F₁ : GrossmanLarson ℕ α) * of' F₂) * of' F₃ =
      of' F₁ * (of' F₂ * of' F₃) := by
    refine ConnesKreimer.map_injective (Nat.castRingHom ℤ) Nat.cast_injective ?_
    simp only [mul_def, map_product, map_of']
    exact product_assoc_int _ _ _
  have h := congrArg (ConnesKreimer.map (Nat.castRingHom R)) hℕ
  simpa only [mul_def, map_product, map_of'] using h

/-- **Associativity** (`R`-generic): trilinear reduction of
    `mul_assoc_basis`, one `ConnesKreimer.lhom_ext'` per slot. -/
theorem mul_assoc {R : Type*} [CommSemiring R]
    (x y z : GrossmanLarson R α) :
    x * y * z = x * (y * z) := by
  show product (product x y) z = product x (product y z)
  have h₁ : ∀ F₁ F₂ : Forest (Nonplanar α),
      product (product (of' (R := R) F₁) (of' F₂)) =
        (product (of' F₁)).comp (product (of' F₂)) := fun F₁ F₂ =>
    ConnesKreimer.lhom_ext' fun F₃ => mul_assoc_basis F₁ F₂ F₃
  have h₂ : ∀ (F₁ : Forest (Nonplanar α)) (w : GrossmanLarson R α),
      (product.flip w).comp (product (of' (R := R) F₁)) =
        (product (of' F₁)).comp (product.flip w) := fun F₁ w =>
    ConnesKreimer.lhom_ext' fun F₂ => LinearMap.congr_fun (h₁ F₁ F₂) w
  have h₃ : ∀ w y : GrossmanLarson R α,
      (product.flip w).comp (product.flip y) = product.flip (product y w) :=
    fun w y => ConnesKreimer.lhom_ext' fun F₁ => LinearMap.congr_fun (h₂ F₁ w) y
  exact LinearMap.congr_fun (h₃ z y) x

/-! ### `Semigroup` and `Monoid` instances

With associativity proved, register the typeclass instances. The
underlying `Mul` is the existing `instMul` from `GrossmanLarson.lean`
(so no `Semigroup.mul`-vs-`instMul` diamond). `One` is forwarded from
`ConnesKreimer` via `instOne` (also in `GrossmanLarson.lean`). -/

/- Low priority: `GrossmanLarson` is a semireducible alias of `ConnesKreimer`,
so these instances can capture `ConnesKreimer`-goals carrying metavariables
(hijacking the meta via alias unfolding). Low priority keeps CK-native
instances winning first. -/
noncomputable instance (priority := 50) instSemigroup {R : Type*} [CommSemiring R] :
    Semigroup (GrossmanLarson R α) where
  mul := (· * ·)
  mul_assoc := mul_assoc

noncomputable instance (priority := 50) instMonoid {R : Type*} [CommSemiring R] :
    Monoid (GrossmanLarson R α) where
  one := 1
  one_mul := one_mul
  mul_one := mul_one

end GrossmanLarson
