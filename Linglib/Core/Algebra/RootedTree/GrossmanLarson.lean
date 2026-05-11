/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Algebra.RootedTree.PreLie.Nonplanar

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

- **R.5.1**: `gl_insert_tree : Nonplanar α → H → H` — single-tree
  insertion `T ↦ (F ↦ F • T)`, defined via `Nonplanar.insertSum` lifted
  through `ofForest`. Bilinear in F.
- **R.5.2**: `gl_insert : H → H → H` — `F ↦ G ↦ F • G`. Recursion on `G`
  via the formula `F • (T · G') = (F • T) • G'`. Need to verify
  well-definedness on multisets (since G is a multiset, not a list).
- **R.5.3**: `gl : H → H → H` — `F ↦ G ↦ F ⋆ G`. Recursion on `G` via
  the formula `F ⋆ (T · G') = (F ⋆ G') · T + (F • T) ⋆ G'`.
- **R.5.4**: Right-unitality `F ⋆ 1 = F`.
- **R.5.5**: Associativity `(F₁ ⋆ F₂) ⋆ F₃ = F₁ ⋆ (F₂ ⋆ F₃)` by induction
  on F₃ (the cleanest case, using the recursive formula directly).
- **R.5.6**: Bundle as `Mul`/`Semigroup`/`Ring` instance on a type alias
  `HGL := H` (since H already has a different `Mul` from `AddMonoidAlgebra`,
  the disjoint-union product). Mirror our `InsertionAlgebra α := Nonplanar α →₀ ℤ`
  pattern.

## Status

Stub: roadmap only. R.5.1 will be the first concrete sub-commit.

## Out of scope (deferred)

- The full Hopf algebra structure on `(HGL, ⋆, Δ_⊔)`. Just `⋆` here.
- The pairing `⟨·, ·⟩ : H × H → ℤ` for GL ↔ CK duality (R.6).
- The `Δ^c` coassoc theorem on `H` via duality (R.7).
- Specialization of the abstract `★ : S(L) →ₗ S(L)` from
  `Linglib/Core/Algebra/PreLie/GuinOudom.lean` to this concrete `⋆`
  (would require PBW; deferred indefinitely).
-/

namespace ConnesKreimer.GrossmanLarson

variable {α : Type*}

-- R.5.1+ implementations land here in subsequent commits.

end ConnesKreimer.GrossmanLarson
