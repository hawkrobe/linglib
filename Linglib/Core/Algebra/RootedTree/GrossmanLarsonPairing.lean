/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Combinatorics.RootedTree.Aut
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Symmetry-weighted pairing for GL ↔ CK duality
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{grossman-larson-1989}
@cite{marcolli-chomsky-berwick-2025}

The pairing `⟨·, ·⟩ : H × H → R` (where `H = ConnesKreimer R (Nonplanar α)`)
realizes the duality between the Connes-Kreimer (CK) and
Grossman-Larson (GL) Hopf algebras on the shared carrier. By
Foissy 2018 (hal-01924416, §4.2), GL associativity ⇔ Δ^c
coassociativity via the pairing — the Δ^c proof in R.7 transports the
GL proof from `GrossmanLarson.lean` (R.5) through this duality.

## MCB targets

The pairing is the **bridge** that makes the GL framework
(`GrossmanLarson.lean`) usable to prove MCB's coassociativity claims:

* **Lemma 1.2.10** (Δ^c bialgebra): coassoc transported via this
  pairing from `GrossmanLarson.product_assoc`.
* **Lemma 1.7.3** (Insertion Lie ↔ primitives in `H^∨`): the dual Lie
  bracket on `H^∨` is induced by this pairing; MCB's binary `◁_e`
  (Def 1.7.1) is its binary specialization after `1 − α` quotient.
* **Δ^d** (MCB Def 1.2.5) and Δ^ρ (Lemma 1.2.11): same pairing
  framework, different extraction policies. See
  `memory/project_mcb_unification_rationale.md`.

## The pairing (Foissy 2018 §4.2)

For nonplanar rooted trees, the pairing on basis elements is
*symmetry-weighted*:
```
⟨of' F, of' G⟩ = if F = G then |Aut(F)| else 0
```
where `Aut(F)` is the automorphism group of `F` as a multiset of trees
(i.e., the product `∏_T |Aut(T)|^{m_T(F)} · m_T(F)!` over distinct
trees `T` with multiplicities `m_T(F)`, where `Aut(T)` is the rooted-
tree automorphism group of `T`).

Bilinearly extended to `H →ₗ[R] H →ₗ[R] R`. The pairing is
**symmetric** (because the underlying ⟨·,·⟩ on basis is symmetric in
F, G) and **non-degenerate** (the basis vectors are mutually orthogonal
with non-zero diagonal, so no non-zero element pairs to 0 with all
others — at least when `R` is characteristic-0; over `ℤ` there are
torsion subtleties when |Aut(F)| = 0 or non-invertible).

## Status

`[UPSTREAM]` candidate. Open `sorry`s: `pairing` definition,
`pairing_of'_of'` evaluation, `pairing_symm`, `pairing_nondegenerate`.
The aut-cardinality substrate `Nonplanar.autCard` /
`Nonplanar.forestAutCard` lives in
`Linglib/Core/Combinatorics/RootedTree/Aut.lean` (re-exported here as
`treeAutCard` / `forestAutCard`) — it has its own `sorry` for the
implementation, which doesn't block proving the pairing's API
properties.
-/

namespace RootedTree

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### Automorphism count

The cardinality of the automorphism group of a rooted nonplanar tree
(or forest) is the symmetry weight in the pairing. The actual
substrate for these is in
`Linglib/Core/Combinatorics/RootedTree/Aut.lean` — re-exported here
under the `GrossmanLarson` namespace for use in the pairing. -/

/-- Re-export `Nonplanar.autCard` for use in the pairing. -/
noncomputable def treeAutCard (t : Nonplanar α) : ℕ :=
  Nonplanar.autCard t

/-- Re-export `Nonplanar.forestAutCard` for use in the pairing. -/
noncomputable def forestAutCard (F : Forest (Nonplanar α)) : ℕ :=
  Nonplanar.forestAutCard F

/-! ### The bilinear pairing -/

/-- The **symmetry-weighted pairing** `⟨·, ·⟩ : H × H → R`. On basis
    elements, `⟨of' F, of' G⟩ = if F = G then forestAutCard F else 0`
    (in `R`, via `Nat.cast`). Bilinearly extended via `Finsupp.lift`. -/
noncomputable def pairing :
    ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) →ₗ[R] R :=
  letI : DecidableEq (Forest (Nonplanar α)) := Classical.decEq _
  Finsupp.lift _ R (Forest (Nonplanar α)) (fun F =>
    Finsupp.lift R R (Forest (Nonplanar α)) (fun G =>
      if F = G then (forestAutCard F : R) else 0))

@[simp] theorem pairing_of'_of' (F G : Forest (Nonplanar α)) :
    pairing (R := R) (ConnesKreimer.of' (R := R) F)
                     (ConnesKreimer.of' (R := R) G) =
      (letI : Decidable (F = G) := Classical.dec _
       if F = G then (forestAutCard F : R) else 0) := by
  letI : DecidableEq (Forest (Nonplanar α)) := Classical.decEq _
  show (Finsupp.lift _ R (Forest (Nonplanar α)) (fun F' =>
    Finsupp.lift R R (Forest (Nonplanar α)) (fun G' =>
      if F' = G' then (forestAutCard F' : R) else 0)))
    (Finsupp.single F 1 : Forest (Nonplanar α) →₀ R) (ConnesKreimer.of' G) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index]
  · rw [one_smul]
    show (Finsupp.lift R R (Forest (Nonplanar α)) (fun G' =>
        if F = G' then (forestAutCard F : R) else 0))
        (Finsupp.single G 1 : Forest (Nonplanar α) →₀ R) = _
    rw [Finsupp.lift_apply, Finsupp.sum_single_index]
    · simp only [one_smul]
    · simp
  · simp

/-- The pairing is symmetric. Reduces by bilinearity to the basis case,
    where `pairing_of'_of'` shows both sides are `if F = G then
    forestAutCard F else 0` — same value (the `F = G` case forces it). -/
theorem pairing_symm (x y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) x y = pairing y x := by
  refine Finsupp.induction_linear x ?_ ?_ ?_
  · show pairing (R := R) (0 : ConnesKreimer R (Nonplanar α)) y =
        pairing y (0 : ConnesKreimer R (Nonplanar α))
    rw [LinearMap.map_zero, LinearMap.zero_apply, LinearMap.map_zero]
  · intro x₁ x₂ ih₁ ih₂
    let x₁' : ConnesKreimer R (Nonplanar α) := x₁
    let x₂' : ConnesKreimer R (Nonplanar α) := x₂
    show pairing (R := R) (x₁' + x₂') y = pairing y (x₁' + x₂')
    rw [map_add, LinearMap.add_apply, ih₁, ih₂, map_add]
  · intro F r
    refine Finsupp.induction_linear y ?_ ?_ ?_
    · let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      show pairing (R := R) x_single (0 : ConnesKreimer R (Nonplanar α)) =
          pairing (0 : ConnesKreimer R (Nonplanar α)) x_single
      rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
    · intro y₁ y₂ ih₁ ih₂
      let y₁' : ConnesKreimer R (Nonplanar α) := y₁
      let y₂' : ConnesKreimer R (Nonplanar α) := y₂
      let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      show pairing (R := R) x_single (y₁' + y₂') = pairing (y₁' + y₂') x_single
      rw [map_add, LinearMap.map_add, LinearMap.add_apply, ih₁, ih₂]
    · intro G s
      let x_single : ConnesKreimer R (Nonplanar α) := Finsupp.single F r
      let y_single : ConnesKreimer R (Nonplanar α) := Finsupp.single G s
      show pairing (R := R) x_single y_single = pairing y_single x_single
      have hx : x_single = r • (ConnesKreimer.of' (R := R) F) := by
        show (Finsupp.single F r : ConnesKreimer R (Nonplanar α)) =
              r • (Finsupp.single F 1 : ConnesKreimer R (Nonplanar α))
        exact (Finsupp.smul_single_one F r).symm
      have hy : y_single = s • (ConnesKreimer.of' (R := R) G) := by
        show (Finsupp.single G s : ConnesKreimer R (Nonplanar α)) =
              s • (Finsupp.single G 1 : ConnesKreimer R (Nonplanar α))
        exact (Finsupp.smul_single_one G s).symm
      rw [hx, hy]
      simp only [LinearMap.map_smul, LinearMap.smul_apply, pairing_of'_of']
      by_cases h : F = G
      · subst h; ring
      · have h' : G ≠ F := fun heq => h heq.symm
        simp [h, h']

/-- The pairing vanishes on `0`. Free from linearity. -/
@[simp] theorem pairing_zero_left (y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) 0 y = 0 := by
  simp only [LinearMap.map_zero, LinearMap.zero_apply]

/-- The pairing vanishes on `0` (right). -/
@[simp] theorem pairing_zero_right (x : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) x 0 = 0 :=
  LinearMap.map_zero _

/-- Each pairing against a basis element `of' G` extracts the coefficient
    of `G` in `x`, weighted by `forestAutCard G`. Proof: reduce to basis
    via `Finsupp.induction_linear` on `x`, then `pairing_of'_of'`. -/
theorem pairing_apply_of' (x : ConnesKreimer R (Nonplanar α))
    (G : Forest (Nonplanar α)) :
    pairing (R := R) x (ConnesKreimer.of' G) =
      (x : Forest (Nonplanar α) →₀ R) G * (forestAutCard G : R) := by
  refine Finsupp.induction_linear x ?_ ?_ ?_
  · show pairing (R := R) (0 : ConnesKreimer R (Nonplanar α))
                          (ConnesKreimer.of' G) =
        (0 : Forest (Nonplanar α) →₀ R) G * (forestAutCard G : R)
    rw [pairing_zero_left, Finsupp.zero_apply, zero_mul]
  · intro x₁ x₂ ih₁ ih₂
    let x₁' : ConnesKreimer R (Nonplanar α) := x₁
    let x₂' : ConnesKreimer R (Nonplanar α) := x₂
    show pairing (R := R) (x₁' + x₂') (ConnesKreimer.of' G) =
        (((x₁' + x₂') : ConnesKreimer R (Nonplanar α)) :
          Forest (Nonplanar α) →₀ R) G * (forestAutCard G : R)
    rw [map_add, LinearMap.add_apply, ih₁, ih₂]
    show (x₁' : Forest (Nonplanar α) →₀ R) G * (forestAutCard G : R) +
        (x₂' : Forest (Nonplanar α) →₀ R) G * (forestAutCard G : R) =
        ((x₁' + x₂') : Forest (Nonplanar α) →₀ R) G * (forestAutCard G : R)
    show x₁ G * (forestAutCard G : R) + x₂ G * (forestAutCard G : R) =
        (x₁ + x₂) G * (forestAutCard G : R)
    rw [Finsupp.add_apply, add_mul]
  · intro F r
    have hx : (Finsupp.single F r : ConnesKreimer R (Nonplanar α)) =
              r • (ConnesKreimer.of' (R := R) F) := by
      show (Finsupp.single F r : ConnesKreimer R (Nonplanar α)) =
            r • (Finsupp.single F 1 : ConnesKreimer R (Nonplanar α))
      exact (Finsupp.smul_single_one F r).symm
    rw [hx]
    simp only [LinearMap.map_smul, LinearMap.smul_apply, pairing_of'_of']
    letI : DecidableEq (Forest (Nonplanar α)) := Classical.decEq _
    by_cases h : F = G
    · subst h
      rw [if_pos rfl, smul_eq_mul]
      show r * (forestAutCard F : R) =
          (r • (Finsupp.single F 1 : Forest (Nonplanar α) →₀ R)) F *
            (forestAutCard F : R)
      rw [Finsupp.smul_apply, Finsupp.single_eq_same]
      ring
    · rw [if_neg h, smul_zero]
      show 0 =
          (r • (Finsupp.single F 1 : Forest (Nonplanar α) →₀ R)) G *
            (forestAutCard G : R)
      rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg h, smul_zero, zero_mul]

/-- **Non-degeneracy** of the pairing over `CharZero R` with no zero
    divisors. If `pairing x y = 0` for all `y`, then `x = 0`. Uses
    `pairing_apply_of'` (coefficient extraction) + `forestAutCard_pos`
    (positivity) + `Nat.cast_ne_zero` (CharZero R has no Nat-cast torsion)
    + `mul_eq_zero` (NoZeroDivisors R).

    Holds for any commutative ring with characteristic 0 and no zero
    divisors (e.g. `ℤ`, `ℚ`, `ℝ`, `ℂ`, any field of char 0). -/
theorem pairing_nondegenerate
    [CharZero R] [NoZeroDivisors R] (x : ConnesKreimer R (Nonplanar α))
    (h : ∀ y, pairing (R := R) x y = 0) : x = 0 := by
  apply Finsupp.ext (M := R)
  intro G
  have hG : pairing (R := R) x (ConnesKreimer.of' G) = 0 := h _
  rw [pairing_apply_of'] at hG
  have hauts_ne : (Nonplanar.forestAutCard G : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nonplanar.forestAutCard_pos G).ne'
  show (x : Forest (Nonplanar α) →₀ R) G = 0
  rcases mul_eq_zero.mp hG with hx | hx
  · exact hx
  · exact absurd hx hauts_ne

end GrossmanLarson

end RootedTree
