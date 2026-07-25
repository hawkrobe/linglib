/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.EquivFin

/-!
# Universe transfer for finite-type existentials

`∃ (σ : Type) (_ : Fintype σ), P σ` is the canonical shape of machine-computability
classes: states exist at `Type 0`, and a finite type is equivalent to `ULift (Fin n)`
in any universe. `exists_fintype_congr` moves such an existential across universes
along any equivalence-stable predicate transport, giving each class its
universe-polymorphic characterization from a single lemma; `exists_fintype₂_congr` is
the two-type version for machines with a pair of state spaces.

[UPSTREAM] candidate: `Mathlib.Computability.DFA`, as the shared form of its private
`Language.isRegular_iff.helper` once a second machine-computability class needs it —
the two-predicate statement (a universe-polymorphic predicate cannot be abstracted, so
each call site passes the same transport at two universe instantiations) makes it
pattern infrastructure rather than a `Data/Fintype` lemma.
-/

/-- Transports a finite-type existential across universes: any finite type is
equivalent to a `ULift (Fin n)` in the target universe, so an equivalence-stable
predicate can follow it there. -/
theorem exists_fintype_congr.{u, v} {P : Type u → Prop} {Q : Type v → Prop}
    (hPQ : ∀ {σ : Type u} {τ : Type v}, σ ≃ τ → P σ → Q τ)
    (hQP : ∀ {σ : Type v} {τ : Type u}, σ ≃ τ → Q σ → P τ) :
    (∃ (σ : Type u) (_ : Fintype σ), P σ) ↔ ∃ (σ : Type v) (_ : Fintype σ), Q σ :=
  ⟨fun ⟨σ, _, h⟩ => ⟨ULift (Fin (Fintype.card σ)), inferInstance,
      hPQ ((Fintype.equivFin σ).trans Equiv.ulift.symm) h⟩,
   fun ⟨σ, _, h⟩ => ⟨ULift (Fin (Fintype.card σ)), inferInstance,
      hQP ((Fintype.equivFin σ).trans Equiv.ulift.symm) h⟩⟩

/-- The two-type version of `exists_fintype_congr`, for machines with a pair of state
spaces. -/
theorem exists_fintype₂_congr.{u₁, u₂, v₁, v₂} {P : Type u₁ → Type u₂ → Prop}
    {Q : Type v₁ → Type v₂ → Prop}
    (hPQ : ∀ {σ₁ : Type u₁} {τ₁ : Type v₁} {σ₂ : Type u₂} {τ₂ : Type v₂},
      σ₁ ≃ τ₁ → σ₂ ≃ τ₂ → P σ₁ σ₂ → Q τ₁ τ₂)
    (hQP : ∀ {σ₁ : Type v₁} {τ₁ : Type u₁} {σ₂ : Type v₂} {τ₂ : Type u₂},
      σ₁ ≃ τ₁ → σ₂ ≃ τ₂ → Q σ₁ σ₂ → P τ₁ τ₂) :
    (∃ (σ₁ : Type u₁) (_ : Fintype σ₁) (σ₂ : Type u₂) (_ : Fintype σ₂), P σ₁ σ₂)
      ↔ ∃ (σ₁ : Type v₁) (_ : Fintype σ₁) (σ₂ : Type v₂) (_ : Fintype σ₂), Q σ₁ σ₂ :=
  ⟨fun ⟨σ₁, _, σ₂, _, h⟩ => ⟨ULift (Fin (Fintype.card σ₁)), inferInstance,
      ULift (Fin (Fintype.card σ₂)), inferInstance,
      hPQ ((Fintype.equivFin σ₁).trans Equiv.ulift.symm)
        ((Fintype.equivFin σ₂).trans Equiv.ulift.symm) h⟩,
   fun ⟨σ₁, _, σ₂, _, h⟩ => ⟨ULift (Fin (Fintype.card σ₁)), inferInstance,
      ULift (Fin (Fintype.card σ₂)), inferInstance,
      hQP ((Fintype.equivFin σ₁).trans Equiv.ulift.symm)
        ((Fintype.equivFin σ₂).trans Equiv.ulift.symm) h⟩⟩
