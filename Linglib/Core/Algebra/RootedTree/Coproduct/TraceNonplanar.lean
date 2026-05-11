/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.Trace
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing
import Mathlib.RingTheory.Bialgebra.Basic

set_option autoImplicit false

/-!
# Δ^c on `ConnesKreimer R (Nonplanar (α ⊕ β))` via descent + duality
@cite{marcolli-chomsky-berwick-2025}
@cite{foissy-typed-decorated-rooted-trees-2018}

The decorated coproduct Δ^c (contraction-extraction with trace
placeholders) descended from the planar version `comulCAlgHomP` in
`Coproduct/Trace.lean` to `Nonplanar` trees. Coassociativity is
proved via Foissy 2018 §4.2 GL-CK duality: GL associativity (`product`
in `GrossmanLarson.lean`) ⇔ Δ^c coassociativity, transported through
the symmetry-weighted pairing in `GrossmanLarsonPairing.lean`.

## MCB target: Lemma 1.2.10

`comulCN_coassoc` + `Bialgebra` instance closes MCB Lemma 1.2.10 (the
graded bialgebra structure of `(V(F_{SO_0}), ⊔, Δ^c)`). The GL/duality
route is the **unification approach** that also enables Δ^d (Def 1.2.5,
via different extraction policy + projection) and Δ^ρ (Lemma 1.2.11,
currently parallel — to be unified at R.8). See
`memory/project_mcb_unification_rationale.md` for why this matters
architecturally (avoids ~thousands of LOC of duplication).

The descent layer mirrors `Coproduct/PruningNonplanar.lean`'s descent
of Δ^ρ. The duality-based coassoc proof is the *new* technique that
handles Δ^c — for which Foissy clean coassoc (used for Δ^ρ) does NOT
work (B+ is not a Hochschild 1-cocycle for Δ^c; see CHANGELOG entry
0.230.944 R.0 patch and `project_phase_e3_db_plan.md`).

## Construction

1. **Descent of `cutSummandsCP`** through `Nonplanar.mk`. Mirrors the
   `Pruning` descent but threads the trace-encoder `τ`.
2. **`comulCTreeN`, `comulCForestN`, `comulCAlgHomN`** — Nonplanar
   tree/forest-level Δ^c, packaged as algebra hom.
3. **Coassoc via duality** (Foissy 2018 §4.2): the duality theorem
   `pairing (gl x y) z = pairing x (Δ^c z) (after suitable
   ⊗-evaluation)` lets us transport `gl_assoc` (R.5.5) to Δ^c coassoc.
4. **Bialgebra instance**: counit + counit-multiplicativity from CK,
   coassoc from duality.

## Status

`[UPSTREAM]` candidate. Skeleton API only. All proofs `sorry`. Builds
on R.5 GL substrate (sorry'd `mul_assoc`) and R.6 pairing substrate
(sorry'd everywhere). Proper proofs land once R.5 + R.6 are sorry-free.
-/

namespace RootedTree

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### Descent of cut-summand enumeration -/

/-- Nonplanar version of `cutSummandsCP`: descended through
    `Nonplanar.mk`. **TODO**: implementation + descent invariance proof
    mirroring `Coproduct/PruningNonplanar.lean`'s `cutSummandsN`. -/
noncomputable def cutSummandsCN (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) :=
  sorry

/-! ### Nonplanar tree- and forest-level Δ^c -/

/-- The Nonplanar tree-level Δ^c coproduct. -/
noncomputable def comulCTreeN (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar (α ⊕ β)))
  + ((cutSummandsCN τ T).map
      (fun p => ConnesKreimer.of' (R := R) p.1 ⊗ₜ[R] ConnesKreimer.ofTree p.2)).sum

/-- The Nonplanar forest-level Δ^c (multiplicative extension). -/
noncomputable def comulCForestN (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  (F.map (comulCTreeN (R := R) τ)).prod

@[simp] theorem comulCForestN_zero (τ : Nonplanar (α ⊕ β) → β) :
    comulCForestN (R := R) τ (0 : Forest (Nonplanar (α ⊕ β))) = 1 := by
  simp only [comulCForestN, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulCForestN_add (τ : Nonplanar (α ⊕ β) → β)
    (F G : Forest (Nonplanar (α ⊕ β))) :
    comulCForestN (R := R) τ (F + G) =
      comulCForestN (R := R) τ F * comulCForestN (R := R) τ G := by
  unfold comulCForestN
  rw [Multiset.map_add, Multiset.prod_add]

/-- Forest-level Δ^c as a `MonoidHom` from `Multiplicative (Forest ...)`. -/
noncomputable def comulCMonoidHomN (τ : Nonplanar (α ⊕ β) → β) :
    Multiplicative (Forest (Nonplanar (α ⊕ β))) →*
      (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Nonplanar (α ⊕ β))) where
  toFun F := comulCForestN (R := R) τ F.toAdd
  map_one' := comulCForestN_zero τ
  map_mul' F G := comulCForestN_add τ F.toAdd G.toAdd

/-- The **Δ^c coproduct on `ConnesKreimer R (Nonplanar (α ⊕ β))`** as
    an algebra hom, parameterized by the trace encoder `τ`. -/
noncomputable def comulCAlgHomN (τ : Nonplanar (α ⊕ β) → β) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  AddMonoidAlgebra.lift R
    ((ConnesKreimer R (Nonplanar (α ⊕ β))) ⊗[R]
      (ConnesKreimer R (Nonplanar (α ⊕ β))))
    (Forest (Nonplanar (α ⊕ β))) (comulCMonoidHomN τ)

@[simp] theorem comulCAlgHomN_apply_of' (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.of' F) = comulCForestN τ F := by
  show AddMonoidAlgebra.lift R _ _ (comulCMonoidHomN τ)
        (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-! ### Duality bridge: GL associativity ↔ Δ^c coassociativity

The headline of R.6+R.7. The pairing `⟨·, ·⟩` from
`GrossmanLarsonPairing.lean` realizes a non-degenerate bilinear form on
`H × H → R`. By extending to `H ⊗ H → R` via `pairing₂ x⊗y w⊗z =
pairing x w · pairing y z`, the GL product `⋆` and Δ^c are paired:
```
pairing (product x y) z = pairing₂ (x ⊗ y) (Δ^c z)
```
This identity makes GL associativity equivalent to Δ^c coassociativity.
The Δ^c coassoc theorem (`comulCN_coassoc` below) follows from GL
associativity (`GrossmanLarson.mul_assoc`) by transporting through this
duality. **TODO**: state + prove. -/

/-- The "tensor-extended" pairing `H ⊗ H → R`, defined by bilinearity
    from `pairing` on basis tensors. **TODO**: implementation + main
    duality theorem `pairing (product x y) z = pairing₂ (x ⊗ y) (Δ^c z)`. -/
noncomputable def pairing₂ (τ : Nonplanar (α ⊕ β) → β) :
    (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
      ConnesKreimer R (Nonplanar (α ⊕ β))) →ₗ[R]
    (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
      ConnesKreimer R (Nonplanar (α ⊕ β))) →ₗ[R] R :=
  sorry

/-- **The duality theorem**: `pairing (product x y) z = pairing₂ (x ⊗ y)
    (Δ^c z)`. The bridge that transports GL associativity to Δ^c
    coassociativity. **TODO**: proof. Uses the Foissy 2018 §4.2
    combinatorial identity relating cut summands of `z` to grafting
    sites of `x ⋆ y`. -/
theorem pairing_gl_eq_pairing_coproduct_C
    (τ : Nonplanar (α ⊕ β) → β)
    (x y z : ConnesKreimer R (Nonplanar (α ⊕ β))) :
    GrossmanLarson.pairing
        (GrossmanLarson.product x y) z =
      pairing₂ (R := R) τ
        (x ⊗ₜ[R] y)
        (comulCAlgHomN (R := R) τ z) := by
  sorry

/-! ### Coassociativity of Δ^c on Nonplanar (via duality) -/

/-- **Coassociativity of `comulCAlgHomN`**. Proved by transporting
    `GrossmanLarson.mul_assoc` through `pairing_gl_eq_pairing_coproduct_C`
    + `pairing_nondegenerate`. **TODO**: proof. -/
theorem comulCN_coassoc (τ : Nonplanar (α ⊕ β) → β) :
    TensorProduct.assoc R
        (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β))) ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap.rTensor _ ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap =
    (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _ ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap := by
  sorry

/-! ### Counit + Bialgebra instance (deferred)

The counit on `ConnesKreimer R (Nonplanar (α ⊕ β))` is inherited from
`ConnesKreimer.counit` (extracts the empty-forest coefficient). Together
with `comulCAlgHomN` and `comulCN_coassoc`, this would give a
`CoalgebraStruct`/`Coalgebra` and ultimately a `Bialgebra` instance.

**The `Bialgebra` / `Coalgebra` typeclass instances are NOT registered
here** — they would close over all the open `sorry`s (`cutSummandsCN`,
`comulCN_coassoc`, ...), which is the typeclass-poisoning anti-pattern
flagged by the auditor for R.5's `Semigroup`/`Monoid`. They land once
the underlying `comulCN_coassoc` is sorry-free. -/

end RootedTree
