/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Submonoid.Operations`, beside
`MulEquiv.ofLeftInverse'`.
-/
import Mathlib.Algebra.Group.Submonoid.Operations

/-!
# `MulEquiv.ofInjective'`

An injective monoid homomorphism is a `MulEquiv` onto its range — the `MulOneClass`
counterpart of the group-level `MonoidHom.ofInjective`, packaging `MulEquiv.ofLeftInverse'`
at an injectivity hypothesis. Primed like `MulEquiv.ofLeftInverse'`: the unprimed name is
reserved for the `f.range` version.
-/

/-- An injective monoid homomorphism is a `MulEquiv` onto its range — the `MulOneClass`
counterpart of `MonoidHom.ofInjective`. -/
@[to_additive /-- An injective additive monoid homomorphism is an `AddEquiv` onto its
range. -/]
noncomputable def MulEquiv.ofInjective' {M N : Type*} [MulOneClass M] [MulOneClass N]
    {f : M →* N} (hf : Function.Injective f) : M ≃* MonoidHom.mrange f :=
  MulEquiv.ofLeftInverse' f (Function.leftInverse_invFun hf)
