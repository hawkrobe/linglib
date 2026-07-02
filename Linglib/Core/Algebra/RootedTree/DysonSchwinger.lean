/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar

set_option autoImplicit false

/-!
# Dyson-Schwinger equations on `ConnesKreimer R (Nonplanar α)` — MCB §1.17
[marcolli-chomsky-berwick-2025]

MCB §1.17 ("Merge and Combinatorial Recursions in Physics") draws a
structural parallel between two recursive equations:

* **Eq 1.17.1** (Hochschild 1-cocycle): for the deletion-style coproduct
  `Δ^ρ` and the grafting operator `B+_a`, `Δ^ρ ∘ B+_a = B+_a ⊗ 1 +
  (id ⊗ B+_a) ∘ Δ^ρ`. This is the central algebraic property of `B+_a`
  that makes the Connes-Kreimer construction work.
* **Eq 1.17.2** (combinatorial Dyson-Schwinger in physics):
  `X = B+_a(P(X))`, where `P` is a polynomial / linear operator on the
  Hopf algebra. The classical case `P(X) = 1 + X²` gives the famous
  Foissy / Bergbauer-Kreimer "ladder" trees of perturbative QFT.
* **Eq 1.17.3** (Merge fixed-point): `X = M(X, X)`, where `M` is the
  linguistic Merge operator on syntactic objects (also MCB §1.10
  Prop 1.10.2). The book's claim is that this linguistic recursion has
  the same formal shape as Eq 1.17.2.

This file provides the algebraic substrate (Eq 1.17.1 + 1.17.2 + an
algebraic quadratic DS analog of Eq 1.17.3). The fully linguistic
Eq 1.17.3 (interpreted as a type-level recursion on `SyntacticObject`)
belongs in `Syntax/Minimalist/` — those Studies files
consume this substrate.

## §1.17.1: B+ as Hochschild 1-cocycle for Δ^ρ

Already proven as `comulTreeN_node_cocycle` /
`comulAlgHomN_bPlusLin_cocycle` in `Coproduct/PruningNonplanar.lean`.
Surfaced here with an MCB-citation alias for citation discovery.

## §1.17.2: The Dyson-Schwinger map and equation

For `P : H →ₗ[R] H` a linear self-map and `a : α` a root label, the
**Dyson-Schwinger map** is

  `dsMap P a := bPlusLin a ∘ₗ P`

A **DS solution** for `(P, a)` is an `X : H` satisfying `X = dsMap P a X`,
equivalently `X = B+_a(P(X))`. The classical existence theorem
(Foissy 2008) requires the degree-completion of `H` (formal power series
in the grading variable) and is out of scope for this substrate file.

## §1.17.3 algebraic analog

The quadratic case `X = B+_a(X * X)` is the direct algebraic analog of
MCB Eq 1.17.3. It is not literally `X = M(X, X)` (which is a type-level
claim about `SyntacticObject`), but it captures the same recursion
shape in the CK algebra.

## Status

`[UPSTREAM]` candidate. Sorry-free. Pure substrate built on
`PruningNonplanar.lean` (B+ + Δ^ρ).
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ## §1: B+ as Hochschild 1-cocycle (MCB Eq 1.17.1)

Re-export of `comulTreeN_node_cocycle` and `comulAlgHomN_bPlusLin_cocycle`
under MCB-anchored names. The substantive content was proven in
`Coproduct/PruningNonplanar.lean` (Phase A.7-γ). -/

/-- **MCB Eq 1.17.1** (Hochschild 1-cocycle property of `B+_a` for `Δ^ρ`,
    basis-level form). For every forest `F : Forest (Nonplanar α)`,
    applying `Δ^ρ` after `B+_a` (i.e., `comulTreeN ∘ Nonplanar.node a`)
    decomposes as the explicit primitive term plus the right-channel
    application of `B+_a` to `comulForestN F`.

    This is the central algebraic property of `B+_a`; it makes
    `(ConnesKreimer R (Nonplanar α), Δ^ρ, ε)` a graded connected
    Hopf algebra (Foissy clean coassoc + antipode by induction). -/
theorem mcb_1_17_1_hochschild_cocycle_basis (a : α) (F : Forest (Nonplanar α)) :
    comulTreeN (R := R) (Nonplanar.node a F) =
      ofTree (Nonplanar.node a F) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulForestN F) :=
  comulTreeN_node_cocycle a F

/-- **MCB Eq 1.17.1** lifted to the algebra-hom level on tree basis
    elements. Re-export of `comulAlgHomN_bPlusLin_cocycle`. -/
theorem mcb_1_17_1_hochschild_cocycle_algHom (a : α) (F : Forest (Nonplanar α)) :
    comulAlgHomN (R := R) (bPlusLin (R := R) a (of' F)) =
      bPlusLin (R := R) a (of' F) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulAlgHomN (of' F)) :=
  comulAlgHomN_bPlusLin_cocycle a F

/-! ## §2: The Dyson-Schwinger map and equation (MCB Eq 1.17.2)

For a linear endomorphism `P : H →ₗ[R] H` and a root label `a : α`,
`dsMap P a := bPlusLin a ∘ₗ P` is the DS self-map. -/

/-- The **Dyson-Schwinger map** `T_{P,a}(X) := B+_a(P(X))` for a linear
    operator `P` and root label `a`. -/
noncomputable def dsMap
    (P : ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α))
    (a : α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  bPlusLin (R := R) a ∘ₗ P

@[simp] theorem dsMap_apply
    (P : ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α))
    (a : α) (X : ConnesKreimer R (Nonplanar α)) :
    dsMap P a X = bPlusLin (R := R) a (P X) := rfl

/-- **MCB Eq 1.17.2**: an element `X : H` is a **Dyson-Schwinger
    solution** for the pair `(P, a)` if it is a fixed point of the
    DS map, i.e., `X = B+_a(P(X))`. -/
def IsDSSolution
    (P : ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α))
    (a : α) (X : ConnesKreimer R (Nonplanar α)) : Prop :=
  X = dsMap P a X

theorem IsDSSolution.def
    (P : ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α))
    (a : α) (X : ConnesKreimer R (Nonplanar α)) :
    IsDSSolution P a X ↔ X = bPlusLin (R := R) a (P X) := Iff.rfl

/-- `dsMap` is additive in `P`. -/
theorem dsMap_add
    (P Q : ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α))
    (a : α) :
    dsMap (P + Q) a = dsMap P a + dsMap Q a := by
  refine LinearMap.ext fun X => ?_
  show bPlusLin (R := R) a ((P + Q) X) =
       bPlusLin (R := R) a (P X) + bPlusLin (R := R) a (Q X)
  rw [LinearMap.add_apply, map_add]

/-- `dsMap` commutes with scalar multiplication. -/
theorem dsMap_smul (r : R)
    (P : ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α))
    (a : α) :
    dsMap (r • P) a = r • dsMap P a := by
  refine LinearMap.ext fun X => ?_
  show bPlusLin (R := R) a ((r • P) X) = r • bPlusLin (R := R) a (P X)
  rw [LinearMap.smul_apply, map_smul]

/-- `dsMap` is zero on the zero operator. -/
@[simp] theorem dsMap_zero (a : α) :
    dsMap (0 : ConnesKreimer R (Nonplanar α) →ₗ[R]
                ConnesKreimer R (Nonplanar α)) a = 0 := by
  refine LinearMap.ext fun X => ?_
  show bPlusLin (R := R) a ((0 : ConnesKreimer R (Nonplanar α) →ₗ[R] _) X) = 0
  rw [LinearMap.zero_apply, map_zero]

/-- For the zero operator `P = 0`, the unique DS solution is `X = 0`
    (since `dsMap 0 a X = B+_a(0) = 0` for all `X`). -/
theorem isDSSolution_zero_iff_zero (a : α) (X : ConnesKreimer R (Nonplanar α)) :
    IsDSSolution (0 : ConnesKreimer R (Nonplanar α) →ₗ[R]
                      ConnesKreimer R (Nonplanar α)) a X ↔ X = 0 := by
  unfold IsDSSolution
  rw [dsMap_zero, LinearMap.zero_apply]

/-! ## §3: Quadratic Dyson-Schwinger (algebraic analog of MCB Eq 1.17.3)

The equation `X = B+_a(X * X)` is the direct algebraic analog of
MCB Eq 1.17.3 (`X = M(X, X)`). Not a `dsMap` instance — multiplication
by `X` is bilinear, not linear, so this lives outside the linear DS
framework.

The two-tree-product solution `X = ofTree (Nonplanar.node a {T, T})`
for a fixed `T` is structurally a "two-children-with-same-subtree"
recursion. -/

/-- The **quadratic Dyson-Schwinger** predicate: `X = B+_a(X * X)`.
    Algebraic analog of MCB Eq 1.17.3 `X = M(X, X)`. -/
def IsQuadDSSolution (a : α) (X : ConnesKreimer R (Nonplanar α)) : Prop :=
  X = bPlusLin (R := R) a (X * X)

/-- `0` is trivially a quadratic-DS solution (since `0 * 0 = 0` and
    `B+_a(0) = 0`). -/
theorem zero_isQuadDSSolution (a : α) :
    IsQuadDSSolution (R := R) a (0 : ConnesKreimer R (Nonplanar α)) := by
  unfold IsQuadDSSolution
  rw [mul_zero, map_zero]

/-! ## §4: Sanity tests -/

/-- Sanity: for `P = id`, the DS map is exactly `B+_a`. -/
example (a : α) :
    dsMap (LinearMap.id : ConnesKreimer R (Nonplanar α) →ₗ[R]
              ConnesKreimer R (Nonplanar α)) a =
      bPlusLin (R := R) a := by
  refine LinearMap.ext fun X => ?_
  show bPlusLin (R := R) a
        ((LinearMap.id : ConnesKreimer R (Nonplanar α) →ₗ[R] _) X) =
       bPlusLin (R := R) a X
  rw [LinearMap.id_apply]

/-- Sanity: a leaf `ofTree (Nonplanar.leaf a)` is the DS solution of
    `(id, a)` shifted by the zero-arity base case. The fixed-point
    equation `X = B+_a(X)` at `X = 0` reduces to `0 = B+_a(0) = 0`,
    which holds; at `X = ofTree (leaf a)`, it would require
    `ofTree (leaf a) = B+_a(ofTree (leaf a)) = ofTree (node a {leaf a})`,
    which fails (the LHS has 1 vertex, the RHS has 2). So `0` is the
    unique solution among basis vectors. -/
example (a : α) :
    IsDSSolution (LinearMap.id : ConnesKreimer R (Nonplanar α) →ₗ[R]
                      ConnesKreimer R (Nonplanar α))
                  a (0 : ConnesKreimer R (Nonplanar α)) := by
  unfold IsDSSolution
  show (0 : ConnesKreimer R (Nonplanar α)) =
       dsMap LinearMap.id a (0 : ConnesKreimer R (Nonplanar α))
  rw [dsMap_apply, LinearMap.id_apply, map_zero]

end ConnesKreimer

end RootedTree
