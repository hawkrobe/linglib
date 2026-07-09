/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Hopf algebra structure on `SymmetricAlgebra R M`

When `R` is a commutative ring, `SymmetricAlgebra R M` carries a Hopf
algebra structure extending the bialgebra structure from
`Mathlib.RingTheory.Bialgebra.SymmetricAlgebra`. The
**antipode** is the algebra homomorphism

    `S(ι x) = −ι x`   for `x : M`,

extended multiplicatively. Equivalently, `S` is the unique algebra
endomorphism of `S(M)` whose restriction to `M` is negation.

The `CommRing R` requirement is essential: negation on `SymmetricAlgebra R M`
is gated by `CommRing R` in mathlib (`SymmetricAlgebra/Basic.lean`); it
cannot be loosened to `[CommSemiring R] [AddCommGroup M]` without a
separate upstream PR providing a `Ring (SymmetricAlgebra R M)` instance
under those hypotheses.

## Main definitions

* `SymmetricAlgebra.antipodeAlgHom` — the antipode as an algebra
  homomorphism, lifted from `-ι R M : M →ₗ[R] S(M)`.
* `SymmetricAlgebra.instHopfAlgebra` — the
  `HopfAlgebra R (SymmetricAlgebra R M)` instance, registered via
  `HopfAlgebra.ofAlgHom`.

## Status

**`[UPSTREAM]` candidate.** Natural home is
`Mathlib/RingTheory/HopfAlgebra/SymmetricAlgebra.lean`, completing the
`Bialgebra`/`HopfAlgebra` pair alongside the sibling
`Mathlib/RingTheory/Bialgebra/SymmetricAlgebra.lean`.

When upstreaming, replace the imports with
```
module
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
```
plus `@[expose] public section`.
-/

set_option autoImplicit false

namespace SymmetricAlgebra

variable (R : Type*) [CommRing R] (M : Type*) [AddCommMonoid M] [Module R M]

open scoped TensorProduct

noncomputable section

/-! ### Antipode -/

/-- The **antipode** of `SymmetricAlgebra R M` as an algebra
    homomorphism: `S(ι x) = −ι x` for `x : M`, extended multiplicatively.
    -/
def antipodeAlgHom : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M :=
  lift (-ι R M)

@[simp]
theorem antipodeAlgHom_ι (x : M) : antipodeAlgHom R M (ι R M x) = -ι R M x := by
  simp [antipodeAlgHom, lift_ι_apply]

/-! ### Hopf algebra instance

`HopfAlgebra.ofAlgHom` (defined for commutative bialgebras at
`Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean`) consumes the
antipode as an AlgHom and reduces the antipode axioms to AlgHom-level
equations. Each axiom is checked on generators via
`SymmetricAlgebra.algHom_ext`:

* `(S ⊗ id) ∘ Δ (ι x) = (-ι x) · 1 + 1 · ι x = 0 = ε(ι x) · 1`,
* symmetrically for the right antipode law. -/

instance instHopfAlgebra : HopfAlgebra R (SymmetricAlgebra R M) :=
  HopfAlgebra.ofAlgHom (antipodeAlgHom R M)
    (by ext x; simp [algebraMapInv_ι])
    (by ext x; simp [algebraMapInv_ι])

end

end SymmetricAlgebra
