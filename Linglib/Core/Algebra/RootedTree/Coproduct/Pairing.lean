/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# Tensor-extended Grossman-Larson/Connes-Kreimer pairings
[foissy-typed-decorated-rooted-trees-2018]

The symmetry-weighted pairing `⟨·, ·⟩` from `GrossmanLarsonPairing.lean`
extended to the tensor square (`pairing₂`) and cube (`pairing₃`), with
nondegeneracy over `[CharZero R] [NoZeroDivisors R]` lifted from the
binary `pairing_nondegenerate` via the natural basis of
`CK = (Forest T) →₀ R`.

These are the instruments of the GL/CK duality proof of Δ^ρ
coassociativity (`Coproduct/PruningDuality.lean`): the duality theorem
pairs the GL product against Δ^ρ through `pairing₂`, and
`pairing₃_unique` transports `GrossmanLarson.mul_assoc` to
coassociativity. No analogous duality holds for the trace coproduct Δ^c
(see the Trace-coherence section of `Coproduct/TraceNonplanar.lean`).
-/

namespace ConnesKreimer

open scoped TensorProduct
open GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### Tensor-extended pairings

The pairing `⟨·, ·⟩` from `GrossmanLarsonPairing.lean` extends to the
tensor square (`pairing₂`) and cube (`pairing₃`). These power the GL/CK
duality for the deletion coproduct Δ^ρ (`Coproduct/PruningDuality.lean`:
`⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`). For the trace variant Δ^c no
such duality holds — the trunk of a proper cut contains trace-marker
leaves that GL grafting can never produce — so Δ^c coassociativity
(`comulCN_coassoc`, `Coproduct/TraceNonplanar.lean`) is a separate
combinatorial statement. -/

/-- The **tensor-extended pairing** `H ⊗ H →ₗ H ⊗ H →ₗ R`, defined by
    `pairing₂ (x ⊗ y) (w ⊗ z) = pairing x w * pairing y z` and extended
    bilinearly.

    Implementation: reshuffle `(x⊗y)⊗(w⊗z)` to `(x⊗w)⊗(y⊗z)` via
    `tensorTensorTensorComm`; apply `TP.map pair pair` where
    `pair = TP.lift pairing : H ⊗ H →ₗ R`; contract via `mul' R R`;
    curry the result.

    Decoration-free: works on `ConnesKreimer R (Nonplanar α)` for any
    `α`. Consumed by the Δ^ρ duality (`Coproduct/PruningDuality.lean`). -/
noncomputable def pairing₂ [DecidableEq α] :
    (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) →ₗ[R]
    (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) →ₗ[R] R :=
  let pair : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)
                →ₗ[R] R :=
    TensorProduct.lift pairing
  TensorProduct.curry <|
    LinearMap.mul' R R ∘ₗ
      TensorProduct.map pair pair ∘ₗ
      (TensorProduct.tensorTensorTensorComm R
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))).toLinearMap

/-- Evaluation of `pairing₂` on pure tensors: `pairing₂ (x ⊗ y) (w ⊗ z) =
    pairing x w * pairing y z`. -/
@[simp] theorem pairing₂_tmul_tmul [DecidableEq α]
    (x y w z : ConnesKreimer R (Nonplanar α)) :
    pairing₂ (R := R) (x ⊗ₜ y) (w ⊗ₜ z) =
      pairing x w * pairing y z := by
  rfl

/-- The **triple-tensor pairing** `H ⊗ (H ⊗ H) →ₗ H ⊗ (H ⊗ H) →ₗ R`,
    defined on pure tensors by
    `pairing₃ (a ⊗ (b ⊗ c)) (x ⊗ (y ⊗ z)) = pairing a x · pairing b y · pairing c z`.

    Consumed by the Δ^ρ duality chain (`Coproduct/PruningDuality.lean`):
    coassociativity is transported through `pairing₃_unique` by pairing
    against arbitrary `x ⊗ (y ⊗ z)` triple tensors.

    Implementation: pairing on the first factor times `pairing₂` on the
    second factor; both extended bilinearly. -/
noncomputable def pairing₃ [DecidableEq α] :
    (ConnesKreimer R (Nonplanar α) ⊗[R]
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))) →ₗ[R]
    (ConnesKreimer R (Nonplanar α) ⊗[R]
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))) →ₗ[R] R :=
  let pair1 : ConnesKreimer R (Nonplanar α) ⊗[R]
                ConnesKreimer R (Nonplanar α) →ₗ[R] R :=
    TensorProduct.lift pairing
  let pair2 : (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
                ⊗[R] (ConnesKreimer R (Nonplanar α) ⊗[R]
                      ConnesKreimer R (Nonplanar α)) →ₗ[R] R :=
    TensorProduct.lift pairing₂
  TensorProduct.curry <|
    LinearMap.mul' R R ∘ₗ
      TensorProduct.map pair1 pair2 ∘ₗ
      (TensorProduct.tensorTensorTensorComm R
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α) ⊗[R]
          ConnesKreimer R (Nonplanar α))).toLinearMap

/-- Evaluation of `pairing₃` on pure tensors. -/
@[simp] theorem pairing₃_tmul_tmul_tmul [DecidableEq α]
    (a b c x y z : ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (a ⊗ₜ (b ⊗ₜ c)) (x ⊗ₜ (y ⊗ₜ z)) =
      pairing a x *
        (pairing b y * pairing c z) := by
  rfl

/-! ### Reduction helpers: `pairing₃` on shifted-tensor forms

Two reduction lemmas that express `pairing₃ (x ⊗ (y ⊗ z'))` evaluated on
shifted tensor forms in terms of `pairing₂` and binary `pairing`,
consumed by the Δ^ρ duality chain in `Coproduct/PruningDuality.lean`.
Both are proved by `TensorProduct.induction_on`, reducing to the
pure-tensor case where `pairing₃_tmul_tmul_tmul` and
`pairing₂_tmul_tmul` agree. -/

/-- `pairing₃ (x ⊗ (y ⊗ z')) ∘ assoc` on a `(U ⊗ c)`-shape tensor:
    factors as `pairing₂ (x ⊗ y) U * pairing z' c`. Generic in `α`
    (the trace decoration is irrelevant). -/
lemma pairing₃_assoc_tmul [DecidableEq α]
    (x y z' : ConnesKreimer R (Nonplanar α))
    (U : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
    (c : ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((TensorProduct.assoc R _ _ _) (U ⊗ₜ[R] c)) =
      pairing₂ (R := R) (x ⊗ₜ[R] y) U * pairing z' c := by
  induction U using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.assoc_tmul, pairing₃_tmul_tmul_tmul,
               pairing₂_tmul_tmul, _root_.mul_assoc]
  | add U₁ U₂ ih₁ ih₂ =>
    rw [TensorProduct.add_tmul, map_add, map_add, ih₁, ih₂, map_add, add_mul]

/-- `pairing₃ (x ⊗ (y ⊗ z'))` on a `(a ⊗ S)`-shape tensor: factors as
    `pairing x a * pairing₂ (y ⊗ z') S`. Generic in `α`. -/
lemma pairing₃_tmul_apply [DecidableEq α]
    (x y z' a : ConnesKreimer R (Nonplanar α))
    (S : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z')) (a ⊗ₜ[R] S) =
      pairing x a * pairing₂ (R := R) (y ⊗ₜ[R] z') S := by
  induction S using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
    simp only [pairing₃_tmul_tmul_tmul, pairing₂_tmul_tmul]
  | add S₁ S₂ ih₁ ih₂ =>
    rw [TensorProduct.tmul_add, map_add, ih₁, ih₂, map_add, mul_add]

/-! ### Nondegeneracy of `pairing₂` and `pairing₃` (lifted from binary)

`pairing₂` and `pairing₃` are nondegenerate over `[CharZero R]
[NoZeroDivisors R]`, lifted from binary `pairing_nondegenerate` via the
natural basis of `CK = (Forest T) →₀ R`. -/

/-- Bilinear extension: `pairing₃ (of' F ⊗ s) (of' G ⊗ t) = pairing (of' F)
    (of' G) * pairing₂ s t` for arbitrary `s, t ∈ CK ⊗ CK`. Proven via
    `TensorProduct.induction_on` on `s` and `t`, reducing to the pure-tensor
    case where `pairing₃_tmul_tmul_tmul` and `pairing₂_tmul_tmul` agree. -/
private theorem pairing₃_of'_tmul_of'_tmul [DecidableEq α] (F G : Forest (Nonplanar α))
    (s t : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R)
        (ConnesKreimer.of' F ⊗ₜ[R] s)
        (ConnesKreimer.of' G ⊗ₜ[R] t) =
      pairing (ConnesKreimer.of' (R := R) F)
                              (ConnesKreimer.of' G) *
        pairing₂ (R := R) s t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul y z =>
      simp only [pairing₃_tmul_tmul_tmul, pairing₂_tmul_tmul]
    | add t₁ t₂ ih₁ ih₂ =>
      -- pairing₃ is linear in 2nd arg (map_add); also `of' G ⊗ ·` distributes.
      rw [TensorProduct.tmul_add, map_add, ih₁, ih₂, map_add, mul_add]
  | add s₁ s₂ ih₁ ih₂ =>
    -- pairing₃ is linear in 1st arg, via map_add at the outer; same for pairing₂.
    rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply, ih₁, ih₂,
        map_add, LinearMap.add_apply, mul_add]

/-- Nondegeneracy of `pairing₂`, lifted from the binary
    `pairing_nondegenerate` along the natural basis of
    `CK = (Forest T) →₀ R`. -/
private theorem pairing₂_nondegenerate [DecidableEq α]
    [CharZero R] [NoZeroDivisors R]
    (U : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
    (h : ∀ x y : ConnesKreimer R (Nonplanar α),
      pairing₂ (R := R) (x ⊗ₜ[R] y) U = 0) : U = 0 := by
  classical
  let ℬ : Module.Basis (Forest (Nonplanar α)) R (ConnesKreimer R (Nonplanar α)) :=
    ConnesKreimer.basisSingleOne
  obtain ⟨c, hc⟩ : ∃ c : Forest (Nonplanar α) →₀ ConnesKreimer R (Nonplanar α),
      c.sum (fun F U_F => ℬ F ⊗ₜ[R] U_F) = U :=
    TensorProduct.eq_repr_basis_left ℬ U
  have hℬ : ∀ G : Forest (Nonplanar α),
      (ℬ G : ConnesKreimer R (Nonplanar α)) = ConnesKreimer.of' G := fun _ =>
    ConnesKreimer.basisSingleOne_apply _
  have hc_zero : ∀ F, c F = 0 := by
    intro F
    apply pairing_nondegenerate (c F)
    intro y
    rw [pairing_symm]
    have h_aut_ne : (Nonplanar.forestAutCard F : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nonplanar.forestAutCard_pos F).ne'
    have h_eval := h (ConnesKreimer.of' F) y
    rw [← hc] at h_eval
    rw [map_finsuppSum (pairing₂ (R := R) (ConnesKreimer.of' F ⊗ₜ[R] y))] at h_eval
    simp only [hℬ, pairing₂_tmul_tmul, pairing_of'_of'] at h_eval
    rw [Finsupp.sum_eq_single F
          (fun G _ hGF => by rw [if_neg (fun heq => hGF heq.symm), zero_mul])
          (fun _ => by rw [LinearMap.map_zero, mul_zero])] at h_eval
    rw [if_pos rfl] at h_eval
    rcases mul_eq_zero.mp h_eval with h' | h'
    · exact absurd h' h_aut_ne
    · exact h'
  have hc_zero' : c = 0 := Finsupp.ext hc_zero
  rw [← hc, hc_zero', Finsupp.sum_zero_index]

/-- Nondegeneracy of `pairing₃`, lifted from `pairing₂_nondegenerate`
    along the basis of the outer tensor factor. -/
theorem pairing₃_nondegenerate [DecidableEq α]
    [CharZero R] [NoZeroDivisors R]
    (U : ConnesKreimer R (Nonplanar α) ⊗[R]
          (ConnesKreimer R (Nonplanar α) ⊗[R]
            ConnesKreimer R (Nonplanar α)))
    (h : ∀ t, pairing₃ (R := R) t U = 0) : U = 0 := by
  classical
  let ℬ : Module.Basis (Forest (Nonplanar α)) R
        (ConnesKreimer R (Nonplanar α)) :=
    ConnesKreimer.basisSingleOne
  obtain ⟨c, hc⟩ : ∃ c : Forest (Nonplanar α) →₀
        (ConnesKreimer R (Nonplanar α) ⊗[R]
          ConnesKreimer R (Nonplanar α)),
      c.sum (fun F U_F => ℬ F ⊗ₜ[R] U_F) = U :=
    TensorProduct.eq_repr_basis_left ℬ U
  have hℬ : ∀ G : Forest (Nonplanar α),
      (ℬ G : ConnesKreimer R (Nonplanar α)) = ConnesKreimer.of' G :=
    fun _ => ConnesKreimer.basisSingleOne_apply _
  have hc_zero : ∀ F, c F = 0 := by
    intro F
    apply pairing₂_nondegenerate (c F)
    intro x y
    have h_aut_ne : (Nonplanar.forestAutCard F : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nonplanar.forestAutCard_pos F).ne'
    have h_eval := h (ConnesKreimer.of' F ⊗ₜ[R] (x ⊗ₜ[R] y))
    rw [← hc] at h_eval
    rw [map_finsuppSum
          (pairing₃ (R := R) (ConnesKreimer.of' F ⊗ₜ[R] (x ⊗ₜ[R] y)))] at h_eval
    simp only [hℬ, pairing₃_of'_tmul_of'_tmul, pairing_of'_of'] at h_eval
    rw [Finsupp.sum_eq_single F
          (fun G _ hGF => by rw [if_neg (fun heq => hGF heq.symm), zero_mul])
          (fun _ => by rw [LinearMap.map_zero, mul_zero])] at h_eval
    rw [if_pos rfl] at h_eval
    rcases mul_eq_zero.mp h_eval with h' | h'
    · exact absurd h' h_aut_ne
    · exact h'
  have hc_zero' : c = 0 := Finsupp.ext hc_zero
  rw [← hc, hc_zero', Finsupp.sum_zero_index]

/-! ### Equality form of nondegeneracy

`pairing₃_unique`: two tensors that pair the same against every test
vector are equal. Follows from `pairing₃_nondegenerate` via
`U = V ↔ U - V = 0`, requiring `AddCommGroup` on the triple tensor.

**Single ring hypothesis**: this theorem lives in its own section with
`[CommRing R₁]` only (NOT [CommSemiring R] from the file's top section +
[CommRing R] added on top — those create two CommSemiring R instances
that don't unify). The `AddCommGroup` on the wrapper comes from the
global `ConnesKreimer.instCommRing`. -/

section PairingUnique
variable {R₁ : Type*} [CommRing R₁] {α₁ : Type*}

theorem pairing₃_unique [DecidableEq α₁] [CharZero R₁] [NoZeroDivisors R₁]
    (U V : ConnesKreimer R₁ (Nonplanar α₁) ⊗[R₁]
          (ConnesKreimer R₁ (Nonplanar α₁) ⊗[R₁]
            ConnesKreimer R₁ (Nonplanar α₁)))
    (h : ∀ t, pairing₃ (R := R₁) t U = pairing₃ (R := R₁) t V) : U = V := by
  rw [← sub_eq_zero]
  apply pairing₃_nondegenerate
  intro t
  rw [map_sub, h t, sub_self]

end PairingUnique

end ConnesKreimer
