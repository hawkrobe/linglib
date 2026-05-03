import Linglib.Core.Algebra.ConnesKreimer.Coproduct
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Connes-Kreimer Bialgebra Instance on `Hc R α` @cite{marcolli-chomsky-berwick-2025} @cite{foissy-2002}

Registers the Connes-Kreimer bialgebra structure on `Hc R α` via
`Bialgebra.ofAlgHom`. The three laws (coassociativity of `Δ^c`,
left-counit, right-counit) are stated here; the proofs are
`sorry`-stubbed pending the cuts-of-cuts bijection argument
(@cite{foissy-2002} §2 for decorated planar trees; the analogous
argument for nonplanar binary trees is what M-C-B Lemma 1.2.10
delegates to via @cite{connes-kreimer-1998} for Feynman graphs).

## Status

- `comul_coassoc` — sorry. Cuts-of-cuts bijection.
- `counit_rTensor` — sorry. Easier; only the empty cut contributes.
- `counit_lTensor` — sorry. Symmetric to `counit_rTensor`.

The instance `instBialgebra : Bialgebra R (Hc R α)` is registered
unconditionally (modulo the sorries) so downstream code can use
typeclass projections (`Coalgebra.comul`, `Bialgebra.counit`) that
resolve to `comulAlgHom.toLinearMap` / `counit.toLinearMap`.

## Why this works typeclass-wise

`Hc R α` is `def`-defined (not `abbrev`) in `Defs.lean`, giving us a
distinct typeclass slot from the underlying `AddMonoidAlgebra R (Forest α)`.
mathlib's `AddMonoidAlgebra.instBialgebra` (group-like coproduct
Δ(F) = F ⊗ F) applies to the underlying type only; our
Connes-Kreimer instance applies to the wrapper. No conflict — this
is the mathlib `MonoidAlgebra` pattern.

## Proof strategy for the deferred sorries

**Counit laws** (`counit_rTensor`, `counit_lTensor`):
Reduce to basis-vector identity via `AddMonoidAlgebra.algHom_ext`.
For each basis element `Finsupp.single F 1` (= forestToHc F):
- `(ε ⊗ id) ∘ Δ^c (Finsupp.single F 1)` expands through
  `AddMonoidAlgebra.lift` to `(ε ⊗ id) (comulMonoidHom F)`.
- For `F` a singleton `{T}`: `comulForest {T} = comulTree T`.
- `comulTree T = forestToHc {T} ⊗ 1 + Σ_c (forestToHc (cutForest c)) ⊗ (forestToHc {remainder c})`.
- `(ε ⊗ id)` projects: `ε(forestToHc F') = if F' = ∅ then 1 else 0` (definition of `counit`).
- Only the empty-cut term `(forestToHc ∅) ⊗ (forestToHc {T})` survives.
- After `lid.symm` cast, this equals `forestToHc {T}` ✓.
- The general (non-singleton) case follows from multiplicativity.

**Coassociativity** (`comul_coassoc`):
The cuts-of-cuts bijection (@cite{foissy-2002} §2 / @cite{connes-kreimer-1998}):
- LHS `(Δ^c ⊗ id) ∘ Δ^c (T)` = sum over (cut C of T, then cut C' of cutForest C).
- RHS `(id ⊗ Δ^c) ∘ Δ^c (T)` = sum over (cut C of T, then cut C'' of remainder T/^c F_C).
- Bijection: a "double cut" of T corresponds to a pair of cuts (C₁, C₂)
  with C₁ "above" C₂ in the tree partial order. The bijection
  reorganizes which is "primary" (extracted first) without changing
  the resulting triple-tensor term.
- Substantial Lean implementation: define a `DoubleCut T : Type` data
  type, construct the bijection both ways, prove triple-tensor
  equality term-by-term.

Estimated effort: counit laws ~30-50 LOC each (1-2 sessions); coassoc
~hundreds of LOC + new combinatorial helpers (~5-10 sessions). Stage 1
delivers the instance scaffolding + proof strategy; the proofs
themselves are deferred.
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type} [DecidableEq α]

/-- Coassociativity of the Connes-Kreimer contraction coproduct Δ^c.
    @cite{marcolli-chomsky-berwick-2025} Lemma 1.2.10.

    Proof strategy: cuts-of-cuts bijection (@cite{foissy-2002} §2).
    See module docstring for details. -/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
        (AlgHom.id R (Hc R α))).comp comulAlgHom)
    = (Algebra.TensorProduct.map (AlgHom.id R (Hc R α)) comulAlgHom).comp comulAlgHom := by
  sorry

/-- Right-tensor counit law: `(ε ⊗ id) ∘ Δ^c = lid.symm`.

    Only the term where the left tensor channel is the empty forest
    (i.e., the explicit `1 ⊗ T` primitive in `comulTree`) survives the
    counit projection. -/
theorem counit_rTensor :
    (Algebra.TensorProduct.map (counit : Hc R α →ₐ[R] R)
      (AlgHom.id R (Hc R α))).comp comulAlgHom
    = (Algebra.TensorProduct.lid R (Hc R α)).symm.toAlgHom := by
  -- Stage 1 attempt: reduce to basis-vector identity.
  -- Using `AddMonoidAlgebra.algHom_ext`, suffices to show for each
  -- `F : Forest α`: `LHS (Finsupp.single F 1) = RHS (Finsupp.single F 1)`.
  -- Then by `Multiset.induction` on F: empty case and singleton-prepend case.
  -- For the singleton case `F = {T}`, expand `comulTree T` term-by-term:
  -- only the "1 ⊗ T" primitive survives the counit projection on the left.
  -- Full proof requires careful tensor-product algebra; deferred.
  sorry

/-- Left-tensor counit law: `(id ⊗ ε) ∘ Δ^c = rid.symm`.

    Only the term where the right tensor channel is the empty forest
    (i.e., the explicit `T ⊗ 1` primitive in `comulTree`) survives the
    counit projection. -/
theorem counit_lTensor :
    (Algebra.TensorProduct.map (AlgHom.id R (Hc R α))
      (counit : Hc R α →ₐ[R] R)).comp comulAlgHom
    = (Algebra.TensorProduct.rid R R (Hc R α)).symm.toAlgHom := by
  sorry

/-- The Connes-Kreimer bialgebra structure on `Hc R α`.

    Registered as an `instance` because `Hc R α` is `def`-wrapped
    (not `abbrev`-wrapped) — no conflict with mathlib's group-like
    `AddMonoidAlgebra.instBialgebra` which applies only to the
    underlying `AddMonoidAlgebra R (Forest α)`. -/
noncomputable instance instBialgebra : Bialgebra R (Hc R α) :=
  Bialgebra.ofAlgHom comulAlgHom counit comul_coassoc counit_rTensor counit_lTensor

end ConnesKreimer
