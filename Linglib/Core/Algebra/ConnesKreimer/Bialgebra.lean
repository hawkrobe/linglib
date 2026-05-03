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

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ## Helper lemmas: how `comulAlgHom` and `counit` act on basis vectors -/

/-- `comulAlgHom` applied to the basis vector `Finsupp.single F 1`
    equals `comulForest F`. Follows from `AddMonoidAlgebra.lift_single`. -/
@[simp] theorem comulAlgHom_apply_single (F : Forest α) :
    comulAlgHom (R := R) (α := α) (Finsupp.single F 1) = comulForest F := by
  show AddMonoidAlgebra.lift R _ _ comulMonoidHom (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-- `counit` applied to the basis vector `Finsupp.single F 1` equals
    `1` if `F` is the empty forest, `0` otherwise. -/
@[simp] theorem counit_apply_single (F : Forest α) :
    counit (R := R) (α := α) (Finsupp.single F 1)
      = if F = 0 then (1 : R) else 0 := by
  show AddMonoidAlgebra.lift R _ _ counitMonoidHom (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-! ## Bialgebra laws -/

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
  -- The two AlgHoms agree on every basis vector `Finsupp.single F 1`.
  apply AddMonoidAlgebra.algHom_ext
  intro F
  -- LHS factors through `comulForest F` via `comulAlgHom_apply_single`.
  -- RHS is `lid.symm.toAlgHom (single F 1) = 1 ⊗ₜ single F 1`.
  -- Strategy: induction on F; both sides reduce to `1 ⊗ₜ single F 1`.
  -- Empty case: `comulForest 0 = 1`; `(map counit id) 1 = 1 ⊗ₜ 1`;
  --   `lid.symm (single 0 1) = 1 ⊗ₜ single 0 1 = 1 ⊗ₜ 1` via `one_def`.
  -- Cons case: `comulForest (T ::ₘ F') = comulTree T * comulForest F'`;
  --   apply mul-distributivity of `(map counit id)` (it's an AlgHom);
  --   IH gives `(map counit id) (comulForest F') = 1 ⊗ₜ single F' 1`;
  --   singleton case `(map counit id) (comulTree T) = 1 ⊗ₜ single {T} 1`
  --   needs `comulTree` term-by-term: only the empty cut survives counit
  --   projection (since `cutForest_empty = 0` and `counit (single 0 1) = 1`).
  --
  -- Genuine multi-session proof effort due to def-Hc/Finsupp/TensorProduct
  -- interplay; helpers above are the prerequisite landed scaffolding.
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

    **Currently a `def`, not an `instance`.** The mathlib-PR audit
    flagged registering an `instance` whose proof obligations are
    `sorry` as unacceptable practice (downstream typeclass-resolved
    code would silently inherit unproven laws). Demoted to `def` until
    Stage 1a/1b discharge the three sorries.

    Downstream code that wants the Bialgebra structure can opt in
    locally via `letI := ConnesKreimer.bialgebraStructure (R := R) (α := α)`.
    Direct access to the algebraic operators stays available by name:
    `comulAlgHom`, `comulDelAlgHom`, `counit`.

    Once `comul_coassoc`, `counit_rTensor`, `counit_lTensor` are
    proven, promote back to `instance`. -/
noncomputable def bialgebraStructure : Bialgebra R (Hc R α) :=
  Bialgebra.ofAlgHom comulAlgHom counit comul_coassoc counit_rTensor counit_lTensor

end ConnesKreimer
