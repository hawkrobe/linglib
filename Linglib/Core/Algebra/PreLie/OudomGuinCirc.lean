/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.PreLie.GuinOudom
import Linglib.Core.RingTheory.Bialgebra.SymmetricAlgebra
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

set_option autoImplicit false

/-!
# The Oudom-Guin ○ operation on `SymmetricAlgebra R L`
@cite{oudom-guin-2008}

For a pre-Lie algebra `L`, this file constructs the canonical extension
of the pre-Lie product `· : L × L → L` to a bilinear operation
`○ : S(L) × S(L) → S(L)` satisfying the three defining equations of
Oudom-Guin (2008) Proposition 2.7:

* `(i)`   `A ○ 1 = A`
* `(ii)`  `T ○ (B * X) = (T ○ B) ○ X − T ○ (B ○ X)`  (for `T ∈ L`)
* `(iii)` `(A * B) ○ C = (A ○ C₍₁₎) * (B ○ C₍₂₎)`  (where `Δ(C) = Σ C₍₁₎ ⊗ C₍₂₎`)

These equations uniquely determine `○`. From `○`, the Oudom-Guin product
`★ : S(L) × S(L) → S(L)`, `A ★ B := (A ○ B₍₁₎) * B₍₂₎` (Definition 2.9), is
associative (Lemma 2.10), making `(S(L), ★, Δ)` a Hopf algebra
isomorphic to `U(L_Lie)` (Theorem 2.12).

## Why this file (and not `GuinOudom.lean`)

The sibling file `GuinOudom.lean` follows the *Manchon route*: build
`η : U(L_Lie) → S(L)` directly via the `M` operator and obtain `★` as the
transferred UEA product. That route requires `η` to be an isomorphism
(classical PBW), which mathlib does not yet have, so the Manchon-route
`★` is currently blocked.

This file follows the *Oudom-Guin route*: define `○` and `★` directly on
`S(L)`, prove `★` associative via Lemma 2.10's 6-line algebraic chain
(using Prop 2.7's defining equations + cocommutativity of `Δ`). **No PBW
is required for associativity.**

## Status

**Scaffold (2026-05-16).** The construction of `oudomGuinCirc` itself is
sorry-fenced (Q1 of the pre-Lie PBW pivot per
`scratch/pivot_to_prelie_pbw.md`). Substantive future work:

1. Construct `oudomGuinCirc` satisfying the three defining equations.
   Either (a) via direct recursive construction on the symmetric-algebra
   quotient of the tensor algebra, or (b) via a future mathlib coproduct
   on `SymmetricAlgebra` + a clever lift.
2. Prove uniqueness from the defining equations.

The interface (defining equations + Prop 2.8.v + Lemma 2.10) is stable
and consumers (`Q2/Q3/Q4/Q5/Q6` of the pivot) can build against it.

## References

* @cite{oudom-guin-2008} — original construction, §2.
* @cite{manchon-2011} — survey, Theorem 1.1 (Manchon route, alternative).
* @cite{chapoton-livernet-2001} — free pre-Lie algebra = rooted trees.

## Convention

Right pre-Lie (`RightPreLieAlgebra` from Tapia 2025), matching
`GuinOudom.lean`. Pre-Lie product written as `*` on `L`. Oudom-Guin's
`○` notation is reserved for the extension to `S(L)`.
-/

namespace PreLie

namespace OudomGuinCirc

variable {R : Type*} [CommRing R]
variable {L : Type*} [RightPreLieRing L] [RightPreLieAlgebra R L]

/-! ## §1: The `○` operation on `S(L) × S(L) → S(L)`

Oudom-Guin (2008) Proposition 2.7's defining equations characterize a
unique bilinear extension of the pre-Lie product `· : L × L → L` to an
operation `○ : S(L) × S(L) → S(L)`. The construction is recursive on
the length of the left argument (using equation `(iii)` for the
reduction step), with the base case `T ○ A` for `T ∈ L` given by
Def 2.4's recursion on the length of `A`.

This abstract operation is `noncomputable` and uses the coproduct
`Δ : S(L) → S(L) ⊗ S(L)` provided by `Linglib.Core.RingTheory.Bialgebra.
SymmetricAlgebra` (Q1a — landed 2026-05-16). Each `x ∈ L` is primitive
under `Δ`. -/

/-- The **Oudom-Guin ○ operation** on `S(L)`. Bilinear extension of the
    pre-Lie product `· : L × L → L` satisfying Prop 2.7's defining
    equations.

    **TODO**: construct via recursive lift. Blocked on a coproduct
    structure on `SymmetricAlgebra R L` (mathlib upstream). See module
    docstring. -/
noncomputable def oudomGuinCirc :
    SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L →ₗ[R]
      SymmetricAlgebra R L :=
  sorry

/-- Notation for the Oudom-Guin ○ operation. -/
scoped infix:75 " ○ " => fun A B => oudomGuinCirc A B

/-! ## §2: Defining equations (Prop 2.7)

Oudom-Guin's Proposition 2.7 states that the three equations below
uniquely characterize `○`. We state each as a theorem. With the
construction sorry-fenced, these are also sorry-fenced (they witness
that the construction satisfies the defining equations). -/

/-- **Prop 2.7 (i)**: right unit. `A ○ 1 = A` for all `A ∈ S(L)`. -/
theorem circ_one_right (A : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) A 1 = A := by
  sorry

/-- **Prop 2.7 (ii)**: recursive equation for `T ∈ L` on the left.
    `T ○ (B · X) = (T ○ B) ○ X − T ○ (B ○ X)` for `T, X ∈ L`,
    `B ∈ S(L)`.

    This is the Def 2.4 recursion lifted to the symmetric-algebra
    setting. The `X` on the right is `ι(X) ∈ S(L)`. -/
theorem circ_T_mul (T : L) (B : SymmetricAlgebra R L) (X : L) :
    oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)
        (B * SymmetricAlgebra.ι R L X) =
      oudomGuinCirc (R := R)
          (oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T) B)
          (SymmetricAlgebra.ι R L X) -
      oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)
          (oudomGuinCirc (R := R) B (SymmetricAlgebra.ι R L X)) := by
  sorry

/-- **Prop 2.7 (iii)**: distributivity via `Δ`. `(A * B) ○ C =
    Σ (A ○ C₍₁₎) · (B ○ C₍₂₎)` (Sweedler-summed over the coproduct).

    This is the defining equation that extends `○` from `L × S(L)` to
    `S(L) × S(L)` on the left argument.

    Stated via `Coalgebra.comul` from Q1a's `Bialgebra` instance on
    `SymmetricAlgebra R L`. -/
theorem circ_mul_distrib_via_comul (A B C : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) (A * B) C =
      (LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
        TensorProduct.map (oudomGuinCirc A) (oudomGuinCirc B))
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C) := by
  sorry

/-! ## §3: Reduction to `L × L` pre-Lie product

When both arguments are images of `L` under `ι`, the OG `○` agrees with
the original pre-Lie product on `L`. -/

/-- `ι(T) ○ ι(X) = ι(T * X)` for `T, X ∈ L`. The pre-Lie product on `L`
    lifts to `S(L)` via `ι`. -/
theorem circ_ι_ι (T X : L) :
    oudomGuinCirc (R := R) (SymmetricAlgebra.ι R L T)
        (SymmetricAlgebra.ι R L X) =
      SymmetricAlgebra.ι R L (T * X) := by
  -- Direct from Def 2.4 + Prop 2.7.i.
  -- Specifically: T ○ ι(X) = T ○ (1 * ι(X)) = (T ○ 1) ○ ι(X) − T ○ (1 ○ ι(X))
  --             = ι(T) ○ ι(X) − T ○ (ε(X) · 1)
  --             = T*X (after evaluating ε(X) = 0 for X ∈ L of positive degree).
  -- Requires unfolding via Prop 2.7.i and the L × L base case identification.
  sorry

/-- `1 ○ A = ε(A) · 1` for `A ∈ S(L)`. The counit map appears here.
    (Prop 2.8 (i) in Oudom-Guin.) -/
theorem one_circ (A : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) (1 : SymmetricAlgebra R L) A =
      (SymmetricAlgebra.algebraMapInv (M := L) A) • (1 : SymmetricAlgebra R L) := by
  -- From Prop 2.7.iii with A = B = 1 (using Δ(C) = ...): 1 ○ C = ε(C) · 1.
  sorry

/-- **Prop 2.8 (ii)**: counit and `○` commute. `ε(A ○ B) = ε(A) · ε(B)`.

    Follows from Prop 2.7.iii at `A` or `B` constant (`one_circ`-style
    argument). Used by Q2's algebraMap base case to reduce `ε((B ○ C₁) C₂)`
    via the counit law. -/
theorem counit_circ (A B : SymmetricAlgebra R L) :
    SymmetricAlgebra.algebraMapInv (M := L) (oudomGuinCirc (R := R) A B) =
      (SymmetricAlgebra.algebraMapInv (M := L) A) *
      (SymmetricAlgebra.algebraMapInv (M := L) B) := by
  sorry

/-! **Prop 2.8 (iii)**: `Δ` commutes with `○` — `Δ(A ○ B) = Σ (A₍₁₎ ○ B₍₁₎)
⊗ (A₍₂₎ ○ B₍₂₎)`, Sweedler-summed over both coproducts.

This is the OG paper's Sweedler identity used in Prop 2.8.v's `mul` case
to identify LHS and RHS expansions; combined with `IsCocomm`
(cocommutativity, now available from
`Linglib/Core/RingTheory/Bialgebra/SymmetricAlgebra.lean`) to swap inner
indexing.

**Lean statement deferred** pending the right mathlib idiom for the
4-fold tensor reshuffling `(S⊗S) ⊗ (S⊗S) → S⊗S`. The natural form would
be:

```
Coalgebra.comul (A ○ B) =
  (TensorProduct.map oudomGuinCirc oudomGuinCirc).comp
    (Algebra.TensorProduct.tensorTensorTensorComm ...).comp
    ... (Coalgebra.comul A, Coalgebra.comul B)
```

but mathlib's `tensorTensorTensorComm` is in `TensorProduct.AssocLeft`
or similar and the exact composition needs care. Future cleanup. -/

/-! ## §4: Prop 2.8.v — the key inductive lemma

`(A ○ B) ○ C = A ○ ((B ○ C₍₁₎) · C₍₂₎)`. Proved by induction on the
length of `A` (Oudom-Guin paper page 7).

This is THE substantive lemma needed for Lemma 2.10's proof of `★`
associativity.

### Proof structure (per OG paper p. 7)

By `SymmetricAlgebra.induction` on `A`:

- **`algebraMap r` (rank 0, A = r · 1)**: both sides reduce to
  `r · ε(B) · ε(C) · 1` via `one_circ` (Prop 2.8.i), `counit_circ`
  (Prop 2.8.ii), and the counit law `ε(C₍₁₎) · ε(C₍₂₎) = ε(C)`.

- **`ι T` (rank 1, A = ι(T) for T ∈ L)**: the rank-1 OG identity. By
  Def 2.4 + Prop 2.7.ii (`circ_T_mul`), inductive on B's length. This
  is the deepest sub-case; depends on the construction of
  `oudomGuinCirc` at `T ∈ L`.

- **`mul A₁ A₂` (with IH on both)**: OG's main chain (p. 7):
  ```
  ((A₁ * A₂) ○ B) ○ C
    = ((A₁ ○ B₍₁₎)(A₂ ○ B₍₂₎)) ○ C         [Prop 2.7.iii]
    = ((A₁ ○ B₍₁₎) ○ C₍₁₎)((A₂ ○ B₍₂₎) ○ C₍₂₎)  [Prop 2.7.iii again]
    = (A₁ ○ ((B₍₁₎ ○ C₍₁₎₍₁₎) C₍₁₎₍₂₎))(A₂ ○ ((B₍₂₎ ○ C₍₂₎₍₁₎) C₍₂₎₍₂₎))  [IH]
    = (A₁ * A₂) ○ ((B ○ C₍₁₎) C₍₂₎)         [Prop 2.7.iii reversed + Δ identity]
  ```
  The final step uses Prop 2.8.iii (`comul_circ`) + `IsCocomm`:
  `Δ((C ○ D₁)D₂) = (C₁ ○ D₁)D₂ ⊗ (C₂ ○ D₃)D₄` after cocommutative
  reindexing.

- **`add A₁ A₂` (with IH on both)**: linearity of `oudomGuinCirc`. -/

/-- **Prop 2.8 (v)** of Oudom-Guin (2008). The inductive key for Lemma
    2.10's proof of `★` associativity.

    `(A ○ B) ○ C = A ○ ((B ○ C₍₁₎) · C₍₂₎)`, Sweedler-summed over the
    coproduct of `C`. -/
theorem circ_assoc_via_comul (A B C : SymmetricAlgebra R L) :
    oudomGuinCirc (R := R) (oudomGuinCirc A B) C =
      oudomGuinCirc A
        ((LinearMap.mul' R (SymmetricAlgebra R L) ∘ₗ
          TensorProduct.map (oudomGuinCirc B) LinearMap.id)
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) C)) := by
  -- See proof structure docstring above. Each induction case is its own
  -- sub-sorry — modular when `oudomGuinCirc` (Q1b) and Prop 2.7.iii
  -- (`circ_mul_distrib_via_comul`) are constructed.
  induction A using SymmetricAlgebra.induction with
  | algebraMap r =>
    -- A = r · 1. Both sides reduce to `r · ε(B) · ε(C) · 1` via
    -- one_circ, counit_circ, and the counit law `ε(C₁)·ε(C₂) = ε(C)`.
    sorry
  | ι T =>
    -- A = ι(T) for T ∈ L. Rank-1 OG identity. Inductive on B's length
    -- using Prop 2.7.ii (`circ_T_mul`). Deepest sub-case.
    sorry
  | mul A₁ A₂ ih₁ ih₂ =>
    -- A = A₁ * A₂. Main chain from OG p. 7: uses Prop 2.7.iii (twice)
    -- + IH on A₁ and A₂ + Prop 2.8.iii (`comul_circ`) + `IsCocomm`.
    sorry
  | add A₁ A₂ ih₁ ih₂ =>
    -- Linearity of `oudomGuinCirc` in the first argument.
    simp only [map_add, LinearMap.add_apply]
    rw [ih₁, ih₂]

/-! ## §5: The Oudom-Guin ★ product on `S(L)` (Q3)

Oudom-Guin (2008) Definition 2.9 defines the `★` product on `S(L)`
by `A ★ B := (A ○ B₍₁₎) · B₍₂₎`, Sweedler-summed over the coproduct.

Lemma 2.10 shows `★` is associative (and makes `(S(L), ★, Δ)` a Hopf
algebra). The proof is 6 lines of algebra using Prop 2.7.iii
(`circ_mul_distrib_via_comul`), Prop 2.8.v (`circ_assoc_via_comul`,
Q2), and cocommutativity of `Δ` (`Coalgebra.IsCocomm` — landed
sorry-free in Q1a's Bialgebra file). -/

/-- The **Oudom-Guin ★ product** on `S(L)` (Oudom-Guin 2008 Def 2.9):
    `A ★ B := (A ○ B₍₁₎) · B₍₂₎`, Sweedler-summed over `Δ(B)`. -/
noncomputable def oudomGuinStar (A B : SymmetricAlgebra R L) :
    SymmetricAlgebra R L :=
  LinearMap.mul' R (SymmetricAlgebra R L)
    (TensorProduct.map (oudomGuinCirc (R := R) A) LinearMap.id
      (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B))

/-- Notation for the Oudom-Guin ★ product. -/
scoped infix:70 " ★ " => oudomGuinStar

@[simp]
theorem oudomGuinStar_def (A B : SymmetricAlgebra R L) :
    oudomGuinStar (R := R) A B =
      LinearMap.mul' R (SymmetricAlgebra R L)
        (TensorProduct.map (oudomGuinCirc (R := R) A) LinearMap.id
          (Coalgebra.comul (R := R) (A := SymmetricAlgebra R L) B)) :=
  rfl

/-- **Oudom-Guin Lemma 2.10**: the `★` product is associative.

    Proof structure (6-line algebraic chain from OG paper p. 7):
    ```
    (A ★ B) ★ C
      = (((A ○ B₁) · B₂) ○ C₁) · C₂                [def of ★]
      = ((A ○ B₁) ○ C₁) · (B₂ ○ C₂) · C₃          [Prop 2.7.iii]
      = (A ○ ((B₁ ○ C₁) · C₂)) · (B₂ ○ C₃) · C₄   [Prop 2.8.v / Q2]
      = (A ○ ((B₁ ○ C₁) · C₃)) · (B₂ ○ C₂) · C₄   [cocomm of Δ — Q1a]
      = A ★ ((B ○ C₁) · C₂)                        [def of ★ + Prop 2.7.iii]
      = A ★ (B ★ C)                                [def of ★]
    ```

    Sorry-fenced: depends on `circ_mul_distrib_via_comul` (Prop 2.7.iii)
    and `circ_assoc_via_comul` (Prop 2.8.v / Q2). Both are sorry'd
    pending the construction of `oudomGuinCirc` (Q1b). Once Q1b lands,
    the 6-line chain becomes concrete Sweedler manipulations
    (~50-100 LOC in Lean, given Lean's verbosity with TensorProduct). -/
theorem oudomGuinStar_assoc (A B C : SymmetricAlgebra R L) :
    oudomGuinStar (oudomGuinStar A B) C = oudomGuinStar A (oudomGuinStar B C) := by
  sorry

end OudomGuinCirc

end PreLie
