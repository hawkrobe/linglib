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

/-- The shuffle coproduct is an algebra hom on `ConnesKreimer R T`:
    `Δ(F · G) = Δ(F) · Δ(G)` in the tensor algebra
    `ConnesKreimer R T ⊗[R] ConnesKreimer R T`.

    **TODO**: lift from basis form `comulShuffle_mul_of'` via bilinearity. -/
theorem comulShuffle_mul [DecidableEq T] (F G : ConnesKreimer R T) :
    comulShuffle (R := R) (F * G) =
      comulShuffle (R := R) F * comulShuffle (R := R) G := by
  sorry

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

/-- Cocommutativity of `comulShuffle`: `swap ∘ Δ = Δ` where `swap` is
    the tensor-product flip.

    **TODO**: prove via `comulShuffle_comm_multiset` + LinearMap distribution
    over multiset sums. Awaiting cleaner mathlib API for `LinearEquiv` push
    inside Multiset.sum. -/
theorem comulShuffle_comm [DecidableEq T] :
    (TensorProduct.comm R (ConnesKreimer R T) (ConnesKreimer R T)).toLinearMap.comp
      (comulShuffle (R := R)) = comulShuffle (R := R) := by
  sorry

/-! ### §5: Coassociativity

`(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. Combinatorially: summing over partitions
of F into 3 pieces (via nested powerset) gives the same result whether
you split the first or the second piece in the inner step.

Stated below pointwise on basis elements (avoiding tensor-LinearMap
typeclass synthesis hazards). The full LinearMap form follows by
linearity. -/

/-- Coassociativity on basis: applied to `of' F`, summing over double
    partitions gives the same triple tensor whether we partition the
    left or right side first.

    `Σ_{F₁ + F₂ = F, F₁_a + F₁_b = F₁} of' F₁_a ⊗ of' F₁_b ⊗ of' F₂`
    `= Σ_{G₁ + G₂ = F, G₂_a + G₂_b = G₂} of' G₁ ⊗ of' G₂_a ⊗ of' G₂_b`

    Both equal `Σ_{F_a + F_b + F_c = F} of' F_a ⊗ of' F_b ⊗ of' F_c`. -/
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
  sorry

end ConnesKreimer

end RootedTree
