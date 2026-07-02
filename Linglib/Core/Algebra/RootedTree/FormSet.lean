/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar

set_option autoImplicit false

/-!
# FormSet operators `FS^(k)` — MCB Def 1.16.1
[marcolli-chomsky-berwick-2025]

The **FormSet** operator family on workspaces, introduced in MCB §1.16
(book p. 141–146). FormSet is a structure-formation operation that
groups subsets of workspace components into a single new structure via
the grafting operator `B`, without unrolling its constituents to
accessible terms (unlike Merge, which does both grafting and
accessible-term extraction).

## The MCB formula (Def 1.16.1, book p. 143)

`FS^(k) = ⊔ ∘ (B ⊗ id) ∘ Π_(k) ∘ Δ_P`

where:
- `Δ_P` is the **primitive coproduct**: `Δ_P(T) = T ⊗ 1 + 1 ⊗ T` for
  single trees, extended multiplicatively `Δ_P(F) = ⊔_a Δ_P(T_a)`.
  Distinct from Δ^c / Δ^d / Δ^ρ (much simpler — coassoc + algebra-hom
  follow by construction, no Foissy axiom needed).
- `Π_(k) = γ_(k) ⊗ id` where `γ_(k)(F) = F` if F has exactly `k`
  components, else 0.
- `B` (MCB Def 1.3.2): the grafting operator F ↦ tree with fresh root.
  In our typed substrate this is exactly `bPlusLin a` from
  `PruningNonplanar.lean` (parameterized by a root label `a`).
- `⊔` is the workspace product (CK multiplication on forests).

## What FS^(k) does

For F = T₁ ⊔ … ⊔ T_n:
1. `Δ_P(F)` decomposes into `2^n` tensor terms (each T_i is primitive,
   so each Δ_P(T_i) = T_i ⊗ 1 + 1 ⊗ T_i has 2 summands).
2. `Π_(k)` selects only the terms whose left channel has exactly `k`
   components.
3. `B ⊗ id` grafts those `k` components into a new tree with a fresh
   root (labeled `a` in our typed setting).
4. `⊔` multiplies with the right-channel remainder.

The result is a workspace where some subset of `k` components has been
"glued together" by the new root.

## FS^(k) is NOT k-ary Merge (MCB §1.16.2)

* k-ary Merge `M_k` maps `T_1, …, T_k ∈ T^(k)` (k-ary syntactic objects)
  to a k-ary tree. FormSet maps **binary** workspaces to **binary
  extended** workspaces (the grouping is k-ary but the components stay
  binary).
* Merge can be undone by accessible-term extraction. FormSet's groupings
  are atomic for subsequent computation.

## Status

`[UPSTREAM]` candidate (the `comulPrim` primitive coproduct + `bPlusLin`
grafting are general Hopf-algebra-of-rooted-trees constructions, not
linguistics-specific).

Lemma 1.16.5 (Δ^ω extends to extended workspaces F̃^R) deferred — needs
a new "extended forest" type.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ## §1: The grafting operator `B` (MCB Def 1.3.2)

In our typed `Nonplanar α` substrate, `B` needs a root label parameter.
This is exactly the existing `bPlusLin a` (Hochschild 1-cocycle for
Δ^ρ; reused here as the FormSet grafting operator). -/

/-- The **grafting operator** `B` (MCB Def 1.3.2): create a new tree
    with a fresh root labeled `a` and the forest `F` as children.

    Identical to `bPlus a F = Nonplanar.node a F`; this name highlights
    the FormSet usage. -/
noncomputable def graft (a : α) (F : Forest (Nonplanar α)) : Nonplanar α :=
  Nonplanar.node a F

/-- The **grafting operator linearly extended**: re-export `bPlusLin`
    from `PruningNonplanar.lean` under the FormSet-flavored name. -/
noncomputable def graftLin (a : α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  bPlusLin (R := R) a

@[simp] theorem graftLin_of' (a : α) (F : Forest (Nonplanar α)) :
    graftLin (R := R) a (of' F) = ofTree (graft a F) := by
  show bPlusLin (R := R) a (of' F) = ofTree (Nonplanar.node a F)
  exact bPlusLin_of' a F

/-! ## §2: The primitive coproduct `Δ_P` (MCB Remark 1.16.2)

`Δ_P` treats every basis tree as primitive: `Δ_P(T) = T ⊗ 1 + 1 ⊗ T`.
Extended multiplicatively to forests by `Δ_P(F + G) = Δ_P(F) · Δ_P(G)`,
so for `F = ⊔_a T_a`, `Δ_P(F) = ∏_a (T_a ⊗ 1 + 1 ⊗ T_a)`.

Distinct from Δ^c / Δ^d / Δ^ρ (which extract subforests). Coassoc +
algebra-hom by construction — no Foissy axiom needed. -/

/-- Per-tree primitive coproduct: `T ↦ ofTree T ⊗ 1 + 1 ⊗ ofTree T`. -/
noncomputable def primTensor (T : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
    (1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ofTree T

/-- Forest-level primitive coproduct: `F ↦ ∏_{T ∈ F} primTensor T`. -/
noncomputable def comulPrimForest (F : Forest (Nonplanar α)) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (F.map (primTensor (R := R))).prod

@[simp] theorem comulPrimForest_zero :
    comulPrimForest (R := R) (0 : Forest (Nonplanar α)) = 1 := by
  simp only [comulPrimForest, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulPrimForest_add (F G : Forest (Nonplanar α)) :
    comulPrimForest (R := R) (F + G) =
      comulPrimForest (R := R) F * comulPrimForest (R := R) G := by
  unfold comulPrimForest
  rw [Multiset.map_add, Multiset.prod_add]

/-- `comulPrimForest` as a `Multiplicative (Forest (Nonplanar α)) →* …`. -/
noncomputable def comulPrimMonoidHom :
    Multiplicative (Forest (Nonplanar α)) →*
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) where
  toFun F := comulPrimForest (R := R) F.toAdd
  map_one' := comulPrimForest_zero
  map_mul' F G := comulPrimForest_add F.toAdd G.toAdd

/-- The **primitive coproduct** `Δ_P` as an algebra hom. -/
noncomputable def comulPrim :
    ConnesKreimer R (Nonplanar α) →ₐ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.lift comulPrimMonoidHom

@[simp] theorem comulPrim_apply_of' (F : Forest (Nonplanar α)) :
    comulPrim (R := R) (α := α) (of' F) = comulPrimForest F := by
  rw [comulPrim, ConnesKreimer.lift_of']
  rfl

@[simp] theorem comulPrim_apply_ofTree (T : Nonplanar α) :
    comulPrim (R := R) (α := α) (ofTree T) =
      ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
        (1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ofTree T := by
  unfold ofTree
  rw [comulPrim_apply_of']
  show comulPrimForest ({T} : Forest (Nonplanar α)) = _
  show (Multiset.map (primTensor (R := R)) ({T} : Multiset (Nonplanar α))).prod = _
  rw [Multiset.map_singleton, Multiset.prod_singleton]
  rfl

/-! ## §3: The k-component projection `Π_(k)` (MCB book p. 142)

`γ_(k)(F) = F` if F has exactly `k` components, else 0. Linearly
extended to `ConnesKreimer R (Nonplanar α)`. Then `Π_(k) = γ_(k) ⊗ id`
on the left channel of the coproduct output. -/

/-- The **k-component projection** `γ_(k)` on `ConnesKreimer R (Nonplanar α)`:
    on basis `of' F`, returns `of' F` if `F.card = k`, else 0. -/
noncomputable def projectKComponent (k : ℕ) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.linearLift
    (fun F => if F.card = k then (of' F : ConnesKreimer R (Nonplanar α)) else 0)

@[simp] theorem projectKComponent_of'_eq (k : ℕ) (F : Forest (Nonplanar α))
    (h : F.card = k) :
    projectKComponent (R := R) k (of' F) = of' F := by
  rw [projectKComponent, ConnesKreimer.linearLift_of', if_pos h]

@[simp] theorem projectKComponent_of'_ne (k : ℕ) (F : Forest (Nonplanar α))
    (h : F.card ≠ k) :
    projectKComponent (R := R) k (of' F) = 0 := by
  rw [projectKComponent, ConnesKreimer.linearLift_of', if_neg h]

/-! ## §4: The FormSet operator `FS^(k)` (MCB Def 1.16.1)

`FS^(k) = ⊔ ∘ (B ⊗ id) ∘ Π_(k) ∘ Δ_P` where `⊔` is CK multiplication
(lifted to a LinearMap from the tensor product). -/

/-- The CK multiplication as a LinearMap from `H ⊗ H → H`. -/
noncomputable def mulLin :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) :=
  LinearMap.mul' R (ConnesKreimer R (Nonplanar α))

/-- **MCB Def 1.16.1**: the FormSet operator `FS^(k)` of arity `k`,
    parameterized by a root label `a : α` for the grafting operator `B`.

    `FS^(k)(F) = ⊔ ∘ (B ⊗ id) ∘ (Π_(k) ⊗ id) ∘ Δ_P (F)`

    The book uses `k ≥ 3` (the binary/unary cases reduce to Merge);
    we don't enforce this here, since the formula is well-defined for
    any `k ≥ 0`. -/
noncomputable def formSet (a : α) (k : ℕ) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  mulLin (R := R) (α := α) ∘ₗ
    ((graftLin (R := R) a).rTensor _) ∘ₗ
    ((projectKComponent (R := R) k).rTensor _) ∘ₗ
    (comulPrim (R := R) (α := α)).toLinearMap

/-! ## §5: Basic API + sanity tests -/

@[simp] theorem formSet_apply (a : α) (k : ℕ) (x : ConnesKreimer R (Nonplanar α)) :
    formSet (R := R) a k x =
      mulLin (((graftLin (R := R) a).rTensor _)
        (((projectKComponent (R := R) k).rTensor _) (comulPrim x))) := rfl

/-- On a singleton tree `T`, `Δ_P(T) = T ⊗ 1 + 1 ⊗ T`. The left channel
    has cardinality 1 (`{T}.card`) and cardinality 0 (empty forest).
    For `k = 1`, only the `T ⊗ 1` summand survives Π_(1); grafting gives
    `ofTree (graft a {T}) ⊗ 1`, and `⊔` produces `ofTree (graft a {T})`. -/
example (a : α) (T : Nonplanar α) :
    formSet (R := R) a 1 (ofTree T) =
      ofTree (graft a ({T} : Forest (Nonplanar α))) := by
  show mulLin (((graftLin (R := R) a).rTensor _)
        (((projectKComponent (R := R) 1).rTensor _) (comulPrim (ofTree T)))) = _
  rw [comulPrim_apply_ofTree]
  -- Distribute rTensor / mulLin over the sum and reduce.
  have h1 : projectKComponent (R := R) 1 (ofTree T) = ofTree T := by
    have : (({T} : Forest (Nonplanar α))).card = 1 := by
      simp [Multiset.card_singleton]
    exact projectKComponent_of'_eq 1 ({T} : Forest (Nonplanar α)) this
  have h0 : projectKComponent (R := R) 1 (1 : ConnesKreimer R (Nonplanar α)) = 0 := by
    have hne : ((0 : Forest (Nonplanar α))).card ≠ 1 := by simp
    have := projectKComponent_of'_ne (R := R) 1 (0 : Forest (Nonplanar α)) hne
    simpa using this
  simp only [map_add, LinearMap.rTensor_tmul, h1, h0,
             TensorProduct.zero_tmul, add_zero, mulLin,
             LinearMap.mul'_apply, mul_one]
  -- Bridge `graftLin a (ofTree T) = ofTree (graft a {T})` via `ofTree T = of' {T}`.
  show graftLin (R := R) a (of' ({T} : Forest (Nonplanar α))) = _
  exact bPlusLin_of' a ({T} : Forest (Nonplanar α))

end ConnesKreimer

end RootedTree
