/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.BigOperators.Ring.Multiset

set_option autoImplicit false

/-!
# Shuffle coproduct on `ConnesKreimer R T`
@cite{oudom-guin-2008}
@cite{foissy-typed-decorated-rooted-trees-2018}

The **shuffle coproduct** Δ on `ConnesKreimer R T = R[Multiset T]` makes
each tree-singleton `of' {t}` primitive: `Δ(of' {t}) = of' {t} ⊗ 1 + 1 ⊗ of' {t}`.
Extended multiplicatively over the commutative disjoint-union product,
this gives `Δ(of' F) = Σ_{F₁ ⊆ F} of' F₁ ⊗ of' (F - F₁)` for any forest `F`.

This is the polynomial-algebra coproduct viewing
`R[Multiset T] = SymAlg(R[T])` with each generator of `T` primitive.
It is DIFFERENT from mathlib's `AddMonoidAlgebra.instBialgebra` (which
gives the group-like coproduct `Δ(of' F) = of' F ⊗ of' F`).

The shuffle Δ is the substrate for Oudom-Guin 2004's algebraic
construction of the Grossman-Larson product on `S(L)` for any pre-Lie
algebra L (specialized here to `L = InsertionAlgebra α` and
`S(L) = ConnesKreimer R (Nonplanar α)`).

## File scope

- §1: `comulShuffle` definition + basis form.
- §2: counit-like behavior (`comulShuffle 1`).
- §3: algebra-hom property (`comulShuffle (x · y) = comulShuffle x · comulShuffle y`).
- §4: cocommutativity.
- §5: coassociativity.

## Status

`[UPSTREAM]` candidate. Substrate scaffold; proofs in flight.
-/

open TensorProduct

namespace RootedTree

namespace ConnesKreimer

variable {R : Type*} [CommSemiring R] {T : Type*}

/-! ### §1: `comulShuffle` — the polynomial coproduct -/

/-- The shuffle coproduct on `ConnesKreimer R T`. On the basis element
    `of' F` for `F : Forest T = Multiset T`, gives
    `Σ_{F₁ ⊆ F} of' F₁ ⊗ of' (F - F₁)` via the powerset of `F`.

    Each tree-singleton `of' {t} = ofTree t` is primitive:
    `Δ(of' {t}) = of' {t} ⊗ 1 + 1 ⊗ of' {t}`.

    Extends linearly via `Finsupp.lsum` to the full algebra. -/
noncomputable def comulShuffle [DecidableEq T] :
    ConnesKreimer R T →ₗ[R] ConnesKreimer R T ⊗[R] ConnesKreimer R T :=
  Finsupp.lsum R (fun F : Forest T =>
    { toFun := fun r => r • (F.powerset.map fun F₁ =>
        (of' (R := R) F₁) ⊗ₜ[R] (of' (R := R) (F - F₁))).sum
      map_add' := fun r₁ r₂ => by simp [add_smul]
      map_smul' := fun c r => by simp [mul_smul] })

@[simp] theorem comulShuffle_of' [DecidableEq T] (F : Forest T) :
    comulShuffle (R := R) (of' F) =
      (F.powerset.map fun F₁ =>
        (of' (R := R) F₁) ⊗ₜ[R] (of' (R := R) (F - F₁))).sum := by
  show Finsupp.lsum R _ (Finsupp.single F (1 : R)) = _
  rw [Finsupp.lsum_single]
  show (1 : R) • (F.powerset.map fun F₁ =>
        (of' (R := R) F₁) ⊗ₜ[R] (of' (R := R) (F - F₁))).sum = _
  rw [one_smul]

/-! ### §2: Counit-like behavior on `1 = of' 0` -/

/-- `comulShuffle 1 = 1 ⊗ 1`. Reflects that `1 ∈ ConnesKreimer R T` is
    a grouplike element (or equivalently, the empty forest's only
    sub-multiset partition is `(0, 0)`). -/
@[simp] theorem comulShuffle_one [DecidableEq T] :
    comulShuffle (R := R) (1 : ConnesKreimer R T) =
      (1 : ConnesKreimer R T) ⊗ₜ[R] (1 : ConnesKreimer R T) := by
  show comulShuffle (R := R) (of' (R := R) (0 : Forest T)) = _
  rw [comulShuffle_of']
  show ((0 : Forest T).powerset.map fun F₁ =>
        (of' (R := R) F₁) ⊗ₜ[R] (of' (R := R) ((0 : Forest T) - F₁))).sum = _
  rw [Multiset.powerset_zero, Multiset.map_singleton, Multiset.sum_singleton]
  rw [Multiset.sub_zero, of'_zero]

/-! ### §3: Algebra-hom property — Δ is multiplicative

The shuffle Δ is an R-algebra hom from `ConnesKreimer R T` to
`ConnesKreimer R T ⊗[R] ConnesKreimer R T` (where the target has the
tensor-product algebra structure). Equivalently:
`Δ(of' (F + G)) = Δ(of' F) · Δ(of' G)`.

Combinatorially: `(F+G).powerset = F.powerset.bind (fun F₁ => G.powerset.map (fun G₁ => F₁ + G₁))`
(via the bijection that splits each sub-multiset of F+G into its F-part
and G-part). -/

/-- Helper: `Multiset.powerset` distributes over `+`. For `F G : Multiset T`,
    `(F + G).powerset = F.powerset.bind (fun F₁ => G.powerset.map (fun G₁ => F₁ + G₁))`
    as multisets. Proved by induction on `F` via `Multiset.powerset_cons`. -/
theorem _root_.Multiset.powerset_add (F G : Multiset T) :
    (F + G).powerset =
      F.powerset.bind (fun F₁ => G.powerset.map (fun G₁ => F₁ + G₁)) := by
  induction F using Multiset.induction_on with
  | empty =>
    simp [Multiset.powerset_zero, Multiset.singleton_bind]
  | cons a s ih =>
    rw [Multiset.cons_add, Multiset.powerset_cons, Multiset.powerset_cons,
        Multiset.add_bind]
    have h₂ : Multiset.map (Multiset.cons a) ((s + G).powerset) =
              (Multiset.map (Multiset.cons a) s.powerset).bind
                (fun F₁ => G.powerset.map (fun G₁ => F₁ + G₁)) := by
      rw [Multiset.bind_map, ih, Multiset.map_bind]
      apply Multiset.bind_congr
      intros s₁ _
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intros G₁ _
      show Multiset.cons a (s₁ + G₁) = Multiset.cons a s₁ + G₁
      rw [Multiset.cons_add]
    rw [h₂, ih]

/-- **Basis form** of the algebra-hom property:
    `Δ(of' F · of' G) = Δ(of' F) · Δ(of' G)`.

    Uses `Multiset.powerset_add` to relate `(F + G).powerset` to the bind
    of `F.powerset` and `G.powerset`, and `tsub_add_tsub_comm` to factor
    `(F + G) - (F₁ + G₁) = (F - F₁) + (G - G₁)` for `F₁ ≤ F, G₁ ≤ G`. -/
theorem comulShuffle_mul_of' [DecidableEq T] (F G : Forest T) :
    comulShuffle (R := R) ((of' F : ConnesKreimer R T) * of' G) =
      comulShuffle (R := R) (of' F) * comulShuffle (R := R) (of' G) := by
  rw [← of'_add, comulShuffle_of', comulShuffle_of', comulShuffle_of',
      Multiset.powerset_add, Multiset.map_bind, Multiset.sum_bind]
  -- Goal: (F.powerset.map (fun F₁ => ((G.powerset.map (fun G₁ => F₁ + G₁)).map (...)).sum)).sum
  --     = ((F.powerset.map (fun F₁ => of' F₁ ⊗ of' (F - F₁))).sum) *
  --       ((G.powerset.map (fun G₁ => of' G₁ ⊗ of' (G - G₁))).sum)
  rw [← Multiset.sum_map_mul_right]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intros F₁ hF₁
  -- Inner: ((G.powerset.map (fun G₁ => F₁ + G₁)).map (fun H => of' H ⊗ of' (F+G - H))).sum
  --      = (of' F₁ ⊗ of' (F - F₁)) * (G.powerset.map (fun G₁ => of' G₁ ⊗ of' (G - G₁))).sum
  rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intros G₁ hG₁
  -- Goal: ((fun H => of' H ⊗ of' (F+G - H)) ∘ (fun G₁ => F₁ + G₁)) G₁
  --     = (of' F₁ ⊗ of' (F - F₁)) * (of' G₁ ⊗ of' (G - G₁))
  show (of' (R := R) (F₁ + G₁) : ConnesKreimer R T) ⊗ₜ[R]
       (of' (R := R) (F + G - (F₁ + G₁)) : ConnesKreimer R T) =
       ((of' (R := R) F₁ : ConnesKreimer R T) ⊗ₜ[R] of' (R := R) (F - F₁)) *
       ((of' (R := R) G₁ : ConnesKreimer R T) ⊗ₜ[R] of' (R := R) (G - G₁))
  -- Simplify (F+G) - (F₁+G₁) = (F-F₁) + (G-G₁) using F₁ ≤ F, G₁ ≤ G.
  have hF₁_le : F₁ ≤ F := Multiset.mem_powerset.mp hF₁
  have hG₁_le : G₁ ≤ G := Multiset.mem_powerset.mp hG₁
  rw [show F + G - (F₁ + G₁) = (F - F₁) + (G - G₁) from
        (tsub_add_tsub_comm hF₁_le hG₁_le).symm]
  rw [of'_add, of'_add]
  rw [Algebra.TensorProduct.tmul_mul_tmul]

/-- AddMonoidHom form of `F ↦ comulShuffle (F * G)` (G fixed). -/
private noncomputable def comulShuffleMulLHom [DecidableEq T] (G : ConnesKreimer R T) :
    ConnesKreimer R T →+ ConnesKreimer R T ⊗[R] ConnesKreimer R T :=
  (comulShuffle (R := R)).toAddMonoidHom.comp
    (AddMonoidHom.mulRight (G : ConnesKreimer R T))

/-- AddMonoidHom form of `F ↦ comulShuffle F * comulShuffle G` (G fixed). -/
private noncomputable def comulShuffleMulRHom [DecidableEq T] (G : ConnesKreimer R T) :
    ConnesKreimer R T →+ ConnesKreimer R T ⊗[R] ConnesKreimer R T :=
  (AddMonoidHom.mulRight (comulShuffle (R := R) G)).comp
    (comulShuffle (R := R)).toAddMonoidHom

@[simp] private theorem comulShuffleMulLHom_apply [DecidableEq T]
    (F G : ConnesKreimer R T) :
    comulShuffleMulLHom G F = comulShuffle (R := R) (F * G) := rfl

@[simp] private theorem comulShuffleMulRHom_apply [DecidableEq T]
    (F G : ConnesKreimer R T) :
    comulShuffleMulRHom G F = comulShuffle (R := R) F * comulShuffle (R := R) G := rfl

/-- The shuffle coproduct is an algebra hom on `ConnesKreimer R T`:
    `Δ(F · G) = Δ(F) · Δ(G)` in the tensor algebra
    `ConnesKreimer R T ⊗[R] ConnesKreimer R T`. Bilinear lift of
    `comulShuffle_mul_of'` via two nested `Finsupp.addHom_ext` reductions to
    basis singletons (mirrors `assoc_symm` in `PreLie/Algebra.lean`). -/
theorem comulShuffle_mul [DecidableEq T] (F G : ConnesKreimer R T) :
    comulShuffle (R := R) (F * G) =
      comulShuffle (R := R) F * comulShuffle (R := R) G := by
  -- Outer: reduce F to `Finsupp.single F₀ r` via addHom_ext.
  have hF : comulShuffleMulLHom (R := R) G = comulShuffleMulRHom (R := R) G := by
    refine Finsupp.addHom_ext fun F₀ r => ?_
    set sF : ConnesKreimer R T := Finsupp.single F₀ r with sF_def
    show comulShuffleMulLHom G sF = comulShuffleMulRHom G sF
    rw [comulShuffleMulLHom_apply, comulShuffleMulRHom_apply]
    -- Inner: reduce G to `Finsupp.single G₀ s` via addHom_ext on the
    -- AddMonoidHom `G ↦ comulShuffle (sF * G)` vs `G ↦ comulShuffle sF * comulShuffle G`.
    have hG : (comulShuffle (R := R)).toAddMonoidHom.comp (AddMonoidHom.mulLeft sF) =
              (AddMonoidHom.mulLeft (comulShuffle (R := R) sF)).comp
                (comulShuffle (R := R)).toAddMonoidHom := by
      refine Finsupp.addHom_ext fun G₀ s => ?_
      set sG : ConnesKreimer R T := Finsupp.single G₀ s with sG_def
      show comulShuffle (sF * sG) = comulShuffle sF * comulShuffle sG
      rw [show sF = r • of' (R := R) F₀ from (Finsupp.smul_single_one F₀ r).symm,
          show sG = s • of' (R := R) G₀ from (Finsupp.smul_single_one G₀ s).symm]
      rw [smul_mul_smul_comm, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
          smul_mul_smul_comm]
      congr 1
      exact comulShuffle_mul_of' F₀ G₀
    have hGapp := DFunLike.congr_fun hG G
    show comulShuffle (sF * G) = comulShuffle sF * comulShuffle G
    exact hGapp
  have hFapp := DFunLike.congr_fun hF F
  rw [comulShuffleMulLHom_apply, comulShuffleMulRHom_apply] at hFapp
  exact hFapp

/-! ### §4: Cocommutativity

The shuffle Δ is cocommutative: swapping the two tensor factors leaves
Δ unchanged. This follows from the involution `F₁ ↦ F - F₁` on
`F.powerset`. -/

/-- `s.powerset` is invariant under the complement map `s' ↦ s - s'`.
    Standard mathlib-style helper; an involution on `s.powerset`.

    `[UPSTREAM]` candidate. -/
theorem _root_.Multiset.powerset_map_sub_self {β : Type*} [DecidableEq β]
    (s : Multiset β) :
    s.powerset.map (fun s' => s - s') = s.powerset := by
  induction s using Multiset.induction with
  | empty => rfl
  | cons a t ih =>
    rw [Multiset.powerset_cons, Multiset.map_add]
    have h1 : t.powerset.map (fun s' => (a ::ₘ t) - s') =
        t.powerset.map (fun s' => a ::ₘ (t - s')) :=
      Multiset.map_congr rfl fun C₁ hC₁ =>
        Multiset.cons_sub_of_le a (Multiset.mem_powerset.mp hC₁)
    have h2 : (t.powerset.map (Multiset.cons a)).map (fun s' => (a ::ₘ t) - s') =
        t.powerset.map (fun s' => t - s') := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intros C₁ _
      show (a ::ₘ t) - (a ::ₘ C₁) = t - C₁
      rw [Multiset.sub_cons, Multiset.erase_cons_head]
    rw [h1, h2, ih]
    rw [show (fun s' => a ::ₘ (t - s')) = (Multiset.cons a) ∘ (fun s' => t - s') from
        funext (fun _ => rfl), ← Multiset.map_map, ih]
    exact Multiset.add_comm _ _

/-- Reindex a partition-sum over `C.powerset` using the involution `C₁ ↦ C - C₁`.

    For any `f : Multiset T → Multiset T → β` (β an additive comm monoid),
    summing `f C₁ (C - C₁)` over partitions equals summing `f (C - C₁) C₁`.

    Used in cocommutativity proofs and in Oudom-Guin Lemma 2.10's chain. -/
theorem _root_.Multiset.powerset_partition_swap {β : Type*} [AddCommMonoid β] {T' : Type*}
    [DecidableEq T'] (C : Multiset T') (f : Multiset T' → Multiset T' → β) :
    (C.powerset.map fun C₁ => f C₁ (C - C₁)).sum =
      (C.powerset.map fun C₁ => f (C - C₁) C₁).sum := by
  conv_rhs =>
    rw [show C.powerset = C.powerset.map (fun s' => C - s') from
        (Multiset.powerset_map_sub_self C).symm]
  rw [Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intros s' hs'
  show f s' (C - s') = f (C - (C - s')) (C - s')
  congr 1
  exact (tsub_tsub_cancel_of_le (Multiset.mem_powerset.mp hs')).symm

/-- **3-piece partition swap (positions 2, 3)**: enumerating triples
    `(C₁, C₂, C₃)` with `C₁ + C₂ + C₃ = C` (encoded as `C₁ ⊆ C` and
    `C₂ ⊆ C - C₁`, with `C₃ := C - C₁ - C₂`) is invariant under swapping
    the second and third pieces.

    Used in Oudom-Guin Lemma 2.10's chain to swap the "going to A
    directly (sibling of B_(2))" piece with the "going into B_(2)" piece
    of C. Direct application of `Multiset.powerset_partition_swap` to
    the inner sum at fixed `C₁`. -/
theorem _root_.Multiset.powerset_triple_swap_23
    {β : Type*} [AddCommMonoid β] {T' : Type*} [DecidableEq T']
    (C : Multiset T') (f : Multiset T' → Multiset T' → Multiset T' → β) :
    (C.powerset.bind fun C₁ =>
      (C - C₁).powerset.map fun C₂ => f C₁ C₂ (C - C₁ - C₂)).sum =
    (C.powerset.bind fun C₁ =>
      (C - C₁).powerset.map fun C₂ => f C₁ (C - C₁ - C₂) C₂).sum := by
  rw [Multiset.sum_bind, Multiset.sum_bind]
  apply congr_arg Multiset.sum
  apply Multiset.map_congr rfl
  intros C₁ _
  exact Multiset.powerset_partition_swap (C - C₁) (fun D E => f C₁ D E)

/-- **Basis-level cocommutativity**: the partition sum is invariant under
    tensor swap. Direct corollary of `Multiset.powerset_partition_swap`. -/
theorem comulShuffle_comm_multiset [DecidableEq T] (F : Forest T) :
    (F.powerset.map fun F₁ =>
        (of' (R := R) F₁ : ConnesKreimer R T) ⊗ₜ[R]
          (of' (R := R) (F - F₁) : ConnesKreimer R T)).sum =
    (F.powerset.map fun F₁ =>
        (of' (R := R) (F - F₁) : ConnesKreimer R T) ⊗ₜ[R]
          (of' (R := R) F₁ : ConnesKreimer R T)).sum :=
  Multiset.powerset_partition_swap F
    (fun X Y => (of' (R := R) X : ConnesKreimer R T) ⊗ₜ[R]
                  (of' (R := R) Y : ConnesKreimer R T))

/-- Helper: `swap` distributes through the powerset-sum form of `comulShuffle`. -/
private theorem swap_comulShuffle_powerset [DecidableEq T] (F : Forest T) :
    (TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T))
      ((F.powerset.map fun F₁ : Forest T =>
          (of' (R := R) F₁ : ConnesKreimer R T) ⊗ₜ[R]
            (of' (R := R) (F - F₁) : ConnesKreimer R T)).sum) =
    (F.powerset.map fun F₁ : Forest T =>
        (of' (R := R) (F - F₁) : ConnesKreimer R T) ⊗ₜ[R]
          (of' (R := R) F₁ : ConnesKreimer R T)).sum := by
  set swapHom : ConnesKreimer R T ⊗[R] ConnesKreimer R T →+
                  ConnesKreimer R T ⊗[R] ConnesKreimer R T :=
    (TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T)).toLinearMap.toAddMonoidHom
  show swapHom _ = _
  rw [swapHom.map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intros F₁ _
  show (TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T))
        ((of' (R := R) F₁) ⊗ₜ[R] (of' (R := R) (F - F₁))) =
       (of' (R := R) (F - F₁)) ⊗ₜ[R] (of' (R := R) F₁)
  exact TensorProduct.comm_tmul R _ _ _ _

/-- Cocommutativity of `comulShuffle`: `swap ∘ Δ = Δ` where `swap` is
    the tensor-product flip. Lifted from basis form `comulShuffle_comm_multiset`
    via single-variable `Finsupp.addHom_ext` reduction. -/
theorem comulShuffle_comm [DecidableEq T] :
    (TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T)).toLinearMap.comp
      (comulShuffle (R := R)) = comulShuffle (R := R) := by
  ext F
  show (TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T))
        (comulShuffle (R := R) F) = comulShuffle (R := R) F
  have h : ((TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T)).toLinearMap.comp
              (comulShuffle (R := R))).toAddMonoidHom =
            (comulShuffle (R := R)).toAddMonoidHom := by
    refine Finsupp.addHom_ext fun F₀ r => ?_
    set sF : ConnesKreimer R T := Finsupp.single F₀ r with sF_def
    show (TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T))
          (comulShuffle (R := R) sF) = comulShuffle (R := R) sF
    rw [show sF = r • of' (R := R) F₀ from (Finsupp.smul_single_one F₀ r).symm]
    rw [LinearMap.map_smul, map_smul]
    congr 1
    rw [comulShuffle_of']
    rw [swap_comulShuffle_powerset (R := R) F₀]
    exact (comulShuffle_comm_multiset F₀).symm
  exact DFunLike.congr_fun h F

/-! ### §5: Coassociativity

`(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. Combinatorially: summing over partitions
of F into 3 pieces (via nested powerset) gives the same result whether
you split the first or the second piece in the inner step.

Stated below pointwise on basis elements (avoiding tensor-LinearMap
typeclass synthesis hazards). The full LinearMap form follows by
linearity. -/

/-- **Substrate**: nested-powerset reparameterization. The two iteration orders
    over (F₁, F₁_a) with F₁_a ⊆ F₁ ⊆ F vs (G₁, G₂_a) with G₁ ⊆ F, G₂_a ⊆ F - G₁
    enumerate the same multiset of pairs, where the bijection is
    `(F₁, F₁_a) ↦ (G₁ = F₁_a, G₂_a = F₁ - F₁_a)`.

    `[UPSTREAM]` candidate. -/
theorem _root_.Multiset.powerset_powerset_pair_swap {α : Type*} [DecidableEq α]
    (F : Multiset α) :
    F.powerset.bind (fun F₁ : Multiset α =>
      F₁.powerset.map (fun A : Multiset α => (A, F₁ - A))) =
    F.powerset.bind (fun A : Multiset α =>
      (F - A).powerset.map (fun B : Multiset α => (A, B))) := by
  induction F using Multiset.induction with
  | empty =>
    rw [Multiset.powerset_zero]
    simp [Multiset.singleton_bind]
  | cons a s ih =>
    rw [Multiset.powerset_cons, Multiset.add_bind, Multiset.add_bind]
    rw [Multiset.bind_map]
    -- Split LHS into 3 parts via inner powerset_cons:
    -- LHS = s.powerset.bind (fun F₁' => F₁'.powerset.map (fun A => (A, F₁' - A))) [a ∉ F₁ case]
    --     + s.powerset.bind (fun F₁' => (a ::ₘ F₁').powerset.map (...)) [a ∈ F₁ case]
    -- Inner (a ∈ F₁) splits via powerset_cons of (a ::ₘ F₁'):
    --   (a ::ₘ F₁').powerset = F₁'.powerset + F₁'.powerset.map (cons a)
    --   For A ∈ F₁'.powerset (a ∉ A): (a ::ₘ F₁') - A = a ::ₘ (F₁' - A)
    --   For A = a ::ₘ A' (a ∈ A): (a ::ₘ F₁') - A = F₁' - A'
    have h_inner_split : ∀ F₁' : Multiset α,
        (a ::ₘ F₁').powerset.map (fun A => (A, (a ::ₘ F₁') - A)) =
        F₁'.powerset.map (fun A => (A, a ::ₘ (F₁' - A))) +
        F₁'.powerset.map (fun A' => (a ::ₘ A', F₁' - A')) := by
      intro F₁'
      rw [Multiset.powerset_cons, Multiset.map_add]
      congr 1
      · refine Multiset.map_congr rfl fun A hA => ?_
        congr 1
        exact Multiset.cons_sub_of_le a (Multiset.mem_powerset.mp hA)
      · rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun A' _ => ?_
        show (Multiset.cons a A', (a ::ₘ F₁') - (a ::ₘ A')) = (a ::ₘ A', F₁' - A')
        rw [Multiset.sub_cons, Multiset.erase_cons_head]
    -- Apply h_inner_split inside the second LHS bind
    rw [show (s.powerset.bind fun F₁' => (a ::ₘ F₁').powerset.map (fun A => (A, (a ::ₘ F₁') - A))) =
            (s.powerset.bind fun F₁' =>
              F₁'.powerset.map (fun A => (A, a ::ₘ (F₁' - A))) +
              F₁'.powerset.map (fun A' => (a ::ₘ A', F₁' - A'))) from
          Multiset.bind_congr fun F₁' _ => h_inner_split F₁']
    rw [Multiset.bind_add]
    -- Rewrite each LHS piece using LHS_for_s.map (fun p => ...)
    have h_lhs_part2 : (s.powerset.bind fun F₁' =>
                          F₁'.powerset.map (fun A => (A, a ::ₘ (F₁' - A)))) =
        (s.powerset.bind fun F₁' =>
          F₁'.powerset.map (fun A => (A, F₁' - A))).map (fun p => (p.1, a ::ₘ p.2)) := by
      rw [Multiset.map_bind]
      refine Multiset.bind_congr fun F₁' _ => ?_
      rw [Multiset.map_map]; rfl
    have h_lhs_part3 : (s.powerset.bind fun F₁' =>
                          F₁'.powerset.map (fun A' => (a ::ₘ A', F₁' - A'))) =
        (s.powerset.bind fun F₁' =>
          F₁'.powerset.map (fun A' => (A', F₁' - A'))).map (fun p => (a ::ₘ p.1, p.2)) := by
      rw [Multiset.map_bind]
      refine Multiset.bind_congr fun F₁' _ => ?_
      rw [Multiset.map_map]; rfl
    rw [h_lhs_part2, h_lhs_part3, ih]
    -- Now LHS = RHS_for_s + (RHS_for_s).map (p ↦ (p.1, a ::ₘ p.2)) + (RHS_for_s).map (p ↦ (a ::ₘ p.1, p.2))
    -- Compute RHS for (a ::ₘ s) similarly.
    -- RHS = ((a ::ₘ s).powerset.bind fun A => ((a ::ₘ s) - A).powerset.map (fun B => (A, B)))
    --     = s.powerset.bind ... [a ∉ A case]
    --       + (s.powerset.map (cons a)).bind ... [a ∈ A case]
    rw [Multiset.bind_map]
    -- For the "a ∉ A" piece: A ⊆ s, so (a ::ₘ s) - A = a ::ₘ (s - A).
    have h_a_notin_A : ∀ A : Multiset α, A ∈ s.powerset →
        ((a ::ₘ s) - A).powerset.map (fun B => (A, B)) =
        (s - A).powerset.map (fun B => (A, B)) +
        (s - A).powerset.map (fun B' => (A, a ::ₘ B')) := by
      intros A hA
      have hA_le : A ≤ s := Multiset.mem_powerset.mp hA
      rw [show (a ::ₘ s) - A = a ::ₘ (s - A) from Multiset.cons_sub_of_le a hA_le]
      rw [Multiset.powerset_cons, Multiset.map_add]
      congr 1
      rw [Multiset.map_map]; rfl
    -- Apply for the "a ∉ A" branch
    rw [show (s.powerset.bind fun A => ((a ::ₘ s) - A).powerset.map (fun B => (A, B))) =
            (s.powerset.bind fun A =>
              (s - A).powerset.map (fun B => (A, B)) +
              (s - A).powerset.map (fun B' => (A, a ::ₘ B'))) from
          Multiset.bind_congr h_a_notin_A]
    rw [Multiset.bind_add]
    -- For the "a ∈ A" branch: A = cons a A', A' ⊆ s, (a ::ₘ s) - (a ::ₘ A') = s - A'.
    have h_rhs_part3 : (s.powerset.bind fun A' =>
                          ((a ::ₘ s) - (a ::ₘ A')).powerset.map (fun B => (a ::ₘ A', B))) =
        (s.powerset.bind fun A' => (s - A').powerset.map (fun B => (A', B))).map
          (fun p => (a ::ₘ p.1, p.2)) := by
      rw [Multiset.map_bind]
      refine Multiset.bind_congr fun A' _ => ?_
      rw [show (a ::ₘ s) - (a ::ₘ A') = s - A' from by
            rw [Multiset.sub_cons, Multiset.erase_cons_head]]
      rw [Multiset.map_map]; rfl
    rw [h_rhs_part3]
    -- The "a ∈ A, a ∉ B" piece via map identity
    have h_rhs_part2 : (s.powerset.bind fun A => (s - A).powerset.map (fun B' => (A, a ::ₘ B'))) =
        (s.powerset.bind fun A => (s - A).powerset.map (fun B => (A, B))).map
          (fun p => (p.1, a ::ₘ p.2)) := by
      rw [Multiset.map_bind]
      refine Multiset.bind_congr fun A _ => ?_
      rw [Multiset.map_map]; rfl
    rw [h_rhs_part2]
    -- Both LHS and RHS now: (RHS_for_s) + (RHS_for_s).map (p ↦ (p.1, a ::ₘ p.2)) + (RHS_for_s).map (p ↦ (a ::ₘ p.1, p.2))
    -- LHS form: A + B + C where A is base, B is the lift in 2nd slot, C is the lift in 1st slot.
    -- RHS form: A + B + C where A is base, B is the lift in 2nd slot, C is the lift in 1st slot.
    -- abel handles the reordering.
    abel

/-- Coassociativity on basis: applied to `of' F`, summing over double
    partitions gives the same triple tensor whether we partition the
    left or right side first.

    `Σ_{F₁ + F₂ = F, F₁_a + F₁_b = F₁} of' F₁_a ⊗ of' F₁_b ⊗ of' F₂`
    `= Σ_{G₁ + G₂ = F, G₂_a + G₂_b = G₂} of' G₁ ⊗ of' G₂_a ⊗ of' G₂_b`

    Both equal `Σ_{F_a + F_b + F_c = F} of' F_a ⊗ of' F_b ⊗ of' F_c`.
    Direct corollary of `Multiset.powerset_powerset_pair_swap`. -/
theorem comulShuffle_coassoc_basis [DecidableEq T] (F : Forest T) :
    (F.powerset.map fun F₁ : Forest T =>
      (F₁.powerset.map fun F₁_a : Forest T =>
        (of' (R := R) F₁_a) ⊗ₜ[R]
          (of' (R := R) (F₁ - F₁_a)) ⊗ₜ[R]
          (of' (R := R) (F - F₁))).sum).sum =
    (F.powerset.map fun G₁ : Forest T =>
      ((F - G₁).powerset.map fun G₂_a : Forest T =>
        (of' (R := R) G₁) ⊗ₜ[R]
          (of' (R := R) G₂_a) ⊗ₜ[R]
          (of' (R := R) (F - G₁ - G₂_a))).sum).sum := by
  -- Convert nested map.sum to bind, apply pair-swap substrate, convert back.
  rw [show (F.powerset.map fun F₁ : Forest T =>
            (F₁.powerset.map fun F₁_a : Forest T =>
              (of' (R := R) F₁_a) ⊗ₜ[R]
                (of' (R := R) (F₁ - F₁_a)) ⊗ₜ[R]
                (of' (R := R) (F - F₁))).sum).sum =
          (F.powerset.bind fun F₁ : Forest T =>
            F₁.powerset.map fun F₁_a : Forest T =>
              (of' (R := R) F₁_a) ⊗ₜ[R]
                (of' (R := R) (F₁ - F₁_a)) ⊗ₜ[R]
                (of' (R := R) (F - F₁))).sum from by
        rw [Multiset.sum_bind]]
  rw [show (F.powerset.map fun G₁ : Forest T =>
            ((F - G₁).powerset.map fun G₂_a : Forest T =>
              (of' (R := R) G₁) ⊗ₜ[R]
                (of' (R := R) G₂_a) ⊗ₜ[R]
                (of' (R := R) (F - G₁ - G₂_a))).sum).sum =
          (F.powerset.bind fun G₁ : Forest T =>
            (F - G₁).powerset.map fun G₂_a : Forest T =>
              (of' (R := R) G₁) ⊗ₜ[R]
                (of' (R := R) G₂_a) ⊗ₜ[R]
                (of' (R := R) (F - G₁ - G₂_a))).sum from by
        rw [Multiset.sum_bind]]
  -- Now both sides are `(bind ... map ...).sum`. Reformulate via the pair-swap.
  have h_bind_LHS : (F.powerset.bind fun F₁ : Forest T =>
            F₁.powerset.map fun F₁_a : Forest T =>
              (of' (R := R) F₁_a) ⊗ₜ[R]
                (of' (R := R) (F₁ - F₁_a)) ⊗ₜ[R]
                (of' (R := R) (F - F₁))) =
          (F.powerset.bind fun F₁ : Forest T =>
            F₁.powerset.map fun F₁_a : Forest T => (F₁_a, F₁ - F₁_a)).map
              (fun p : Forest T × Forest T =>
                (of' (R := R) p.1) ⊗ₜ[R] (of' (R := R) p.2) ⊗ₜ[R]
                  (of' (R := R) (F - (p.1 + p.2)))) := by
    rw [Multiset.map_bind]
    refine Multiset.bind_congr fun F₁ hF₁ => ?_
    have hF₁_le : F₁ ≤ F := Multiset.mem_powerset.mp hF₁
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun F₁_a hF₁_a => ?_
    have hF₁_a_le : F₁_a ≤ F₁ := Multiset.mem_powerset.mp hF₁_a
    show (of' (R := R) F₁_a) ⊗ₜ[R] (of' (R := R) (F₁ - F₁_a)) ⊗ₜ[R] (of' (R := R) (F - F₁)) =
         (of' (R := R) F₁_a) ⊗ₜ[R] (of' (R := R) (F₁ - F₁_a)) ⊗ₜ[R]
           (of' (R := R) (F - (F₁_a + (F₁ - F₁_a))))
    rw [show F₁_a + (F₁ - F₁_a) = F₁ from by
          rw [add_comm, tsub_add_cancel_of_le hF₁_a_le]]
  have h_bind_RHS : (F.powerset.bind fun G₁ : Forest T =>
            (F - G₁).powerset.map fun G₂_a : Forest T =>
              (of' (R := R) G₁) ⊗ₜ[R]
                (of' (R := R) G₂_a) ⊗ₜ[R]
                (of' (R := R) (F - G₁ - G₂_a))) =
          (F.powerset.bind fun G₁ : Forest T =>
            (F - G₁).powerset.map fun G₂_a : Forest T => (G₁, G₂_a)).map
              (fun p : Forest T × Forest T =>
                (of' (R := R) p.1) ⊗ₜ[R] (of' (R := R) p.2) ⊗ₜ[R]
                  (of' (R := R) (F - (p.1 + p.2)))) := by
    rw [Multiset.map_bind]
    refine Multiset.bind_congr fun G₁ _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun G₂_a _ => ?_
    show (of' (R := R) G₁) ⊗ₜ[R] (of' (R := R) G₂_a) ⊗ₜ[R] (of' (R := R) (F - G₁ - G₂_a)) =
         (of' (R := R) G₁) ⊗ₜ[R] (of' (R := R) G₂_a) ⊗ₜ[R]
           (of' (R := R) (F - (G₁ + G₂_a)))
    rw [show F - G₁ - G₂_a = F - (G₁ + G₂_a) from (tsub_add_eq_tsub_tsub F G₁ G₂_a).symm]
  rw [h_bind_LHS, h_bind_RHS]
  congr 2
  exact Multiset.powerset_powerset_pair_swap F

end ConnesKreimer

end RootedTree
