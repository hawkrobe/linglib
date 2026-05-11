/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Combinatorics.RootedTree.Aut

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
    (in `R`, via `Nat.cast`). Bilinearly extended. -/
noncomputable def pairing :
    ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) →ₗ[R] R := sorry

@[simp] theorem pairing_of'_of' (F G : Forest (Nonplanar α)) :
    pairing (R := R) (ConnesKreimer.of' (R := R) F)
                     (ConnesKreimer.of' (R := R) G) =
      (letI : Decidable (F = G) := Classical.dec _
       if F = G then (forestAutCard F : R) else 0) := by
  sorry

/-- The pairing is symmetric. **TODO**: proof. Reduces to
    `forestAutCard F = forestAutCard F` on the diagonal. -/
theorem pairing_symm (x y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) x y = pairing y x := by
  sorry

/-- The pairing vanishes on `0`. Free from linearity. -/
@[simp] theorem pairing_zero_left (y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) 0 y = 0 := by
  simp only [LinearMap.map_zero, LinearMap.zero_apply]

/-- The pairing vanishes on `0` (right). -/
@[simp] theorem pairing_zero_right (x : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) x 0 = 0 :=
  LinearMap.map_zero _

/-- **Non-degeneracy** (over a field of characteristic 0, or any `R`
    where every `forestAutCard F` is a non-zero-divisor). If `pairing x y
    = 0` for all `y`, then `x = 0`. **TODO**: proof + correct
    hypothesis on `R`. -/
theorem pairing_nondegenerate
    [CharZero R] (x : ConnesKreimer R (Nonplanar α))
    (h : ∀ y, pairing (R := R) x y = 0) : x = 0 := by
  sorry

end GrossmanLarson

end RootedTree
