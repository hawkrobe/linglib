/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Algebra.RootedTree.PreLie.Nonplanar
import Mathlib.Data.Multiset.Bind
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

/-!
# The Grossman-Larson product on `H = ConnesKreimer ℤ (Nonplanar α)`
@cite{grossman-larson-1989}
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{oudom-guin-2008}

The Grossman-Larson product `⋆ : H → H → H` is the associative
non-commutative product on the (commutative) algebra `H` of forests of
nonplanar rooted trees. By Foissy 2018/2021, `(H, ⋆, Δ_⊔)` is a Hopf
algebra dual to the Connes-Kreimer Hopf algebra `(H, ⊔, Δ^c)` (with `⊔`
the disjoint-union product and `Δ^c` the contraction-extraction
coproduct used in MCB).

This file constructs `⋆` directly via a combinatorial recursion (Foissy
2021 Theorem 5.1), bypassing the abstract Guin-Oudom isomorphism
`(S(InsertionAlgebra α), ⋆) ≃ U(InsertionAlgebra α)_Lie` that would
otherwise need PBW (which mathlib lacks; see
`Linglib/Core/Algebra/PreLie/GuinOudom.lean` C3 deferment note). The
combinatorial route gives associativity directly via induction on
forests, no PBW required.

## The formula (Foissy 2021 Theorem 5.1, untyped specialization)

For forest `F : H` and trees `T₁, …, Tₙ : Nonplanar α`:

```
F ⋆ (T₁ ⊔ ⋯ ⊔ Tₙ) = ∑_{I ⊆ [n]} (F • ∏_{i ∈ I} Tᵢ) · ∏_{i ∉ I} Tᵢ
```

where:
- `·` is the commutative product on `H` (forest disjoint union ⊔, lifted bilinearly)
- `F • G` is the **insertion operator**: insert each tree of `G` at any
  vertex of `F`, summed over choices of vertex sequences (defined below)
- `F • 1 = F` (empty insertion is identity)
- `F • (T · G) = (F • T) • G` (insert one tree at a time, associatively
  on the right operand)
- `F • T` for `T` a single tree = `Σ_{v ∈ V(F)} F[v ↦ insertAt(T, v)]`
  (replace the tree of `F` containing `v` with that tree with `T`
  grafted at `v` as a new child)

**Recursive form** (cleaner for Lean):
```
F ⋆ 1 = F
F ⋆ (T · F') = (F ⋆ F') · T + (F • T) ⋆ F'
```

For trees on both sides:
```
T₁ ⋆ T₂ = T₁ · T₂ + (T₁ • T₂)
        = forest{T₁, T₂} + ∑_{v ∈ V(T₁)} singleton_forest{insertAt(T₂, v, T₁)}
```

## Reduction to the existing pre-Lie substrate

The single-tree insertion `T₁ • T₂ : H` for `T₁, T₂ : Nonplanar α`
matches the existing `Nonplanar.insertSum T₂ T₁ : Multiset (Nonplanar α)`
(R.3 substrate, sorry-free), embedded in `H` via `ofForest`.
**Note the argument swap**: `Nonplanar.insertSum T₁ T₂` grafts `T₁` at
vertices of `T₂`, but Foissy 2021's `T₁ • T₂` grafts `T₂` at vertices
of `T₁`. So `T₁ • T₂ = embed (Nonplanar.insertSum T₂ T₁)`.

For forests, `F • T` extends bilinearly across the trees of `F`:
`(S₁ ⊔ ⋯ ⊔ Sₘ) • T = Σⱼ {S₁, …, Sⱼ₋₁, insertAt(T, vⱼ, Sⱼ), Sⱼ₊₁, …, Sₘ}`
summed over `vⱼ ∈ V(Sⱼ)`.

## Implementation roadmap

- ✅ **R.5.1**: `glInsertTree : Nonplanar α → H →ₗ[ℤ] H` — single-tree
  insertion `T ↦ (F ↦ F • T)`, defined via `Nonplanar.insertSum` lifted
  through `of'`. ℤ-linear in F. (Cons-decomp lemma deferred to R.5.1.5.)
- **R.5.1.5**: Leibniz cons decomposition for `glInsertTreeForest`
  (see §3 below).
- **R.5.2**: `glInsert : H →ₗ[ℤ] H →ₗ[ℤ] H` — `F ↦ G ↦ F • G`.
  Recursion on `G` via `F • (T · G') = (F • T) • G'`. Needs cons-decomp.
- **R.5.3**: `gl : H →ₗ[ℤ] H →ₗ[ℤ] H` — `F ↦ G ↦ F ⋆ G`. Recursion on
  `G` via `F ⋆ (T · G') = (F ⋆ G') · T + (F • T) ⋆ G'`.
- **R.5.4**: Right-unitality `F ⋆ 1 = F`.
- **R.5.5**: Associativity `(F₁ ⋆ F₂) ⋆ F₃ = F₁ ⋆ (F₂ ⋆ F₃)` by induction
  on F₃ (the cleanest case, using the recursive formula directly).
- **R.5.6**: Bundle as `Mul`/`Semigroup`/`Ring` instance on a type alias
  `HGL := H` (since H already has a different `Mul` from `AddMonoidAlgebra`,
  the disjoint-union product). Mirror our `InsertionAlgebra α := Nonplanar α →₀ ℤ`
  pattern.

## Status

R.5.1 landed: `glInsertTreeForest`, `glInsertTree`, plus the basic
`_zero` and `_of'` simp lemmas. Sorry-free. Cons-decomp deferred.

## Out of scope (deferred)

- The full Hopf algebra structure on `(HGL, ⋆, Δ_⊔)`. Just `⋆` here.
- The pairing `⟨·, ·⟩ : H × H → ℤ` for GL ↔ CK duality (R.6).
- The `Δ^c` coassoc theorem on `H` via duality (R.7).
- Specialization of the abstract `★ : S(L) →ₗ S(L)` from
  `Linglib/Core/Algebra/PreLie/GuinOudom.lean` to this concrete `⋆`
  (would require PBW; deferred indefinitely).
-/

namespace RootedTree

namespace ConnesKreimer.GrossmanLarson

variable {α : Type*}

/-! ## §1: Single-tree insertion at a forest (R.5.1)

The basic combinatorial action: given a tree `T` and a forest
`F = {S₁, …, Sₘ} : Forest (Nonplanar α)`, sum over each occurrence of
a tree `Sⱼ ∈ F` (with multiplicity) and each grafting summand `S' ∈
Nonplanar.insertSum T Sⱼ` the basis vector for the resulting forest
`{S₁, …, Sⱼ₋₁, S', Sⱼ₊₁, …, Sₘ}`.

Reduction to existing substrate: `Nonplanar.insertSum T Sⱼ` (R.3
substrate, sorry-free) gives the multiset of trees obtained by grafting
`T` at each vertex of `Sⱼ`. **Argument-swap convention**: Foissy 2021's
`F • T` (graft `T` into `F`) is `Nonplanar.insertSum T S` (which grafts
the FIRST argument into the SECOND).

`Multiset.erase` requires `DecidableEq`; we use `Classical.decEq`
locally so consumers do not need to thread a `DecidableEq (Nonplanar α)`
hypothesis. The function is `noncomputable` regardless. -/

/-- `glInsertTreeForest T F`: forest-level insertion of `T` at each
    occurrence of each tree of `F`. Sum of basis vectors. -/
noncomputable def glInsertTreeForest
    (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    ConnesKreimer ℤ (Nonplanar α) :=
  letI : DecidableEq (Nonplanar α) := Classical.decEq _
  ((F.bind (fun S =>
    (Nonplanar.insertSum T S).map
      (fun S' => of' (R := ℤ) (S' ::ₘ F.erase S)))).sum)

/-- Empty forest has no insertion sites. -/
@[simp] theorem glInsertTreeForest_zero (T : Nonplanar α) :
    glInsertTreeForest T (0 : Forest (Nonplanar α)) = 0 := by
  unfold glInsertTreeForest
  simp

/-! ## §2: Bilinear extension to `H` (R.5.1)

Lift the basis-level `glInsertTreeForest T` to a ℤ-linear map on
`H = ConnesKreimer ℤ (Nonplanar α) = Forest (Nonplanar α) →₀ ℤ` via
`Finsupp.linearCombination`. The result is automatically additive in
its `H`-argument; bilinearity in `T` is left to a later sub-commit
(R.5.2 will likely promote `glInsertTree` to a `Nonplanar α → H →ₗ[ℤ] H`
and then to a bilinear `H →ₗ[ℤ] H →ₗ[ℤ] H` via R.5's `glInsert`). -/

/-- `glInsertTree T : H →ₗ[ℤ] H`: ℤ-linear extension of the forest-level
    insertion `glInsertTreeForest T`. -/
noncomputable def glInsertTree (T : Nonplanar α) :
    ConnesKreimer ℤ (Nonplanar α) →ₗ[ℤ] ConnesKreimer ℤ (Nonplanar α) :=
  Finsupp.linearCombination ℤ (glInsertTreeForest T)

/-- `glInsertTree T 0 = 0` (linearity). -/
@[simp] theorem glInsertTree_zero (T : Nonplanar α) :
    glInsertTree T (0 : ConnesKreimer ℤ (Nonplanar α)) = 0 :=
  LinearMap.map_zero _

/-- Basis identity: `glInsertTree T (of' F) = glInsertTreeForest T F`. -/
@[simp] theorem glInsertTree_of' (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    glInsertTree T (of' (R := ℤ) F) = glInsertTreeForest T F := by
  show Finsupp.linearCombination ℤ (glInsertTreeForest T)
        (Finsupp.single F 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-! ## §3: Deferred for R.5.1.5 — Leibniz cons decomposition

The Leibniz-style decomposition over multiset cons,
```
glInsertTreeForest T (S ::ₘ F) =
  ((Nonplanar.insertSum T S).map (fun S' => of' (S' ::ₘ F))).sum +
  of' {S} * glInsertTreeForest T F
```
is the load-bearing lemma for R.5.2's `glInsert` recursion. Proof
sketch: `Multiset.cons_bind` + `Multiset.erase_cons_head` for the
front term; for the tail term, use `(S ::ₘ F).erase S₀ = S ::ₘ F.erase S₀`
(case-split on `S₀ = S`, using `Multiset.cons_erase` when `S₀ = S` to
reconcile both sides through F), then factor `of' {S} *` out via
`Multiset.sum_map_mul_left` and `of'_add`. Uses the Classical
`DecidableEq` instance from `glInsertTreeForest`'s `letI`; care
required to ensure both sides invoke the same instance. Deferred to a
focused R.5.1.5 sub-commit. -/

end ConnesKreimer.GrossmanLarson

end RootedTree
