/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Linglib.Core.Combinatorics.RootedTree.Aut
public import Mathlib.Tactic.Ring

/-!
# The symmetry-weighted pairing on forests

This file defines the pairing on `H = ConnesKreimer R (UnorderedTree α)` that makes the forests an
orthogonal basis, each forest paired with itself to its number of symmetries:
`⟨of' F, of' G⟩ = if F = G then |Aut F| else 0`. Foissy uses this pairing in his dual
construction of the Connes–Kreimer coproduct; here it makes the Grossman–Larson product dual to
the pruning coproduct (`Coproduct/PruningDuality.lean`).

## Main definitions

* `GrossmanLarson.pairing`: the symmetry-weighted pairing.
* `GrossmanLarson.pairing₂`: its extension to `H ⊗ H`.

## Main results

* `GrossmanLarson.pairing_symm`: the pairing is symmetric.
* `GrossmanLarson.pairing_of'`: pairing with a forest takes the coefficient of that forest,
  times its number of symmetries.
* `GrossmanLarson.pairing_nondegenerate`: the pairing is nondegenerate over a ring of
  characteristic zero without zero divisors.
* `GrossmanLarson.pairing_of'_mul`, `GrossmanLarson.pairing_product_of'_mul_of'`: pairing against
  a Connes–Kreimer product splits a basis forest over its antidiagonal, and splits both factors of
  a Grossman–Larson product.

## References

* [foissy-2021]
* [grossman-larson-1989]
* [oudom-guin-2008]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### The bilinear pairing -/

/-- `pairing (of' F) (of' G)` is the number of symmetries of `F` when `F = G`, and `0`
otherwise. -/
noncomputable def pairing :
    ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) →ₗ[R] R :=
  ConnesKreimer.linearLift fun F ↦ ConnesKreimer.linearLift fun G ↦
    if F = G then (forestAutCard F : R) else 0

@[simp] theorem pairing_of'_of' (F G : Forest (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' F) (ConnesKreimer.of' G) =
      (if F = G then (forestAutCard F : R) else 0) := by
  simp [pairing]

/-- The pairing is symmetric. -/
theorem pairing_symm (x y : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) x y = pairing y x := by
  have h : pairing (R := R) (α := α) = pairing.flip := by
    ext F G
    rcases eq_or_ne F G with rfl | h
    · simp
    · simp [h, h.symm]
  exact congr($h x y)

@[simp] theorem pairing_zero_left (y : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) 0 y = 0 := by
  simp only [LinearMap.map_zero, LinearMap.zero_apply]

@[simp] theorem pairing_zero_right (x : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) x 0 = 0 :=
  LinearMap.map_zero _

/-- Pairing against the unit gives the counit, the coefficient of the empty forest. -/
theorem pairing_one_right (w : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) w (1 : ConnesKreimer R (UnorderedTree α)) =
      (ConnesKreimer.counit : ConnesKreimer R (UnorderedTree α) →ₐ[R] R) w := by
  have h : (pairing (R := R)).flip (1 : ConnesKreimer R (UnorderedTree α)) =
      (ConnesKreimer.counit : ConnesKreimer R (UnorderedTree α) →ₐ[R] R).toLinearMap := by
    ext F
    rcases eq_or_ne F 0 with rfl | h <;> simp [← ConnesKreimer.of'_zero, *]
  exact congr($h w)

/-- Pairing with `of' F` takes the coefficient of `F`, weighted by the symmetries of `F`. -/
theorem pairing_of' (F : Forest (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' F) = (forestAutCard F : R) • ConnesKreimer.lcoeff R F := by
  ext G
  rcases eq_or_ne F G with rfl | h
  · simp [ConnesKreimer.coeff_of']
  · simp [ConnesKreimer.coeff_of', h, h.symm]

/-- Pairing against `of' G` gives the coefficient of `G`, weighted by the symmetries of `G`. -/
theorem pairing_apply_of' (x : ConnesKreimer R (UnorderedTree α))
    (G : Forest (UnorderedTree α)) :
    pairing (R := R) x (ConnesKreimer.of' G) =
      x.coeff G * (forestAutCard G : R) := by
  rw [pairing_symm, pairing_of', LinearMap.smul_apply, ConnesKreimer.lcoeff_apply, smul_eq_mul,
    mul_comm]

/-- Over a ring of characteristic zero without zero divisors, the pairing is nondegenerate. -/
theorem pairing_nondegenerate
    [CharZero R] [NoZeroDivisors R] (x : ConnesKreimer R (UnorderedTree α))
    (h : ∀ y, pairing (R := R) x y = 0) : x = 0 := by
  refine ConnesKreimer.ext_coeff fun G => ?_
  rw [ConnesKreimer.coeff_zero]
  have hG : pairing (R := R) x (ConnesKreimer.of' G) = 0 := h _
  rw [pairing_apply_of'] at hG
  have hauts_ne : (UnorderedTree.forestAutCard G : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr (UnorderedTree.forestAutCard_pos G).ne'
  rcases mul_eq_zero.mp hG with hx | hx
  · exact hx
  · exact absurd hx hauts_ne

section Ring
variable {R : Type*} [CommRing R] [CharZero R] [NoZeroDivisors R]

/-- Elements that pair equally against everything are equal. -/
theorem ext_pairing_right {x y : ConnesKreimer R (UnorderedTree α)}
    (h : ∀ z, pairing (R := R) x z = pairing y z) : x = y :=
  sub_eq_zero.mp <| pairing_nondegenerate _ fun z => by
    rw [map_sub, LinearMap.sub_apply, h, sub_self]

end Ring

/-! ### Product rule

Pairing against a Connes–Kreimer product splits the basis forest over its antidiagonal; the
weights recombine by `UnorderedTree.forestAutCard_add`. -/

/-- `⟨W, C₁ · C₂⟩` is the sum, over the splittings `W = W₁ + W₂`, of `⟨W₁, C₁⟩ · ⟨W₂, C₂⟩`. -/
theorem pairing_of'_mul_of' (W C₁ C₂ : Forest (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' W)
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      ((Multiset.antidiagonal W).map (fun p =>
        pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
        pairing (R := R) (ConnesKreimer.of' p.2) (ConnesKreimer.of' C₂))).sum := by
  -- Step 1: collapse `of' C₁ * of' C₂` to `of' (C₁ + C₂)`, then evaluate
  -- the pairing on the diagonal.
  rw [← ConnesKreimer.of'_add, pairing_of'_of']
  -- Step 2: simplify each term on the RHS via `pairing_of'_of'`.
  have h_rhs_simp :
      ((Multiset.antidiagonal W).map (fun p =>
          pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
          pairing (R := R) (ConnesKreimer.of' p.2) (ConnesKreimer.of' C₂))).sum =
      ((Multiset.antidiagonal W).map (fun p =>
          (if p.1 = C₁ then (forestAutCard p.1 : R) else 0) *
          (if p.2 = C₂ then (forestAutCard p.2 : R) else 0))).sum := by
    congr 1
    refine Multiset.map_congr rfl ?_
    intro p _
    rw [pairing_of'_of', pairing_of'_of']
  rw [h_rhs_simp]
  -- Step 3: split on whether `W = C₁ + C₂` using `split_ifs` to handle the
  by_cases hW : W = C₁ + C₂
  · -- W = C₁ + C₂. LHS = forestAutCard W.
    rw [ite_eq_left hW]
    -- Use `filter_eq'` to extract the (C₁, C₂) summand.
    -- Each term: nonzero only when p = (C₁, C₂).
    -- Rewrite via filter (· = (C₁,C₂)) + filter (· ≠ ...).
    have h_partition :
        ((Multiset.antidiagonal W).map (fun p =>
            (if p.1 = C₁ then (forestAutCard p.1 : R) else 0) *
            (if p.2 = C₂ then (forestAutCard p.2 : R) else 0))).sum =
        ((((Multiset.antidiagonal W).filter (· = (C₁, C₂))).map (fun p =>
            (if p.1 = C₁ then (forestAutCard p.1 : R) else 0) *
            (if p.2 = C₂ then (forestAutCard p.2 : R) else 0))).sum) +
        ((((Multiset.antidiagonal W).filter (· ≠ (C₁, C₂))).map (fun p =>
            (if p.1 = C₁ then (forestAutCard p.1 : R) else 0) *
            (if p.2 = C₂ then (forestAutCard p.2 : R) else 0))).sum) := by
      rw [← Multiset.sum_add, ← Multiset.map_add]
      congr 1
      rw [Multiset.filter_add_not]
    rw [h_partition]
    -- Vanishing piece: every p ≠ (C₁, C₂) in antidiagonal W gives a 0 term.
    have h_vanish :
        ((((Multiset.antidiagonal W).filter (· ≠ (C₁, C₂))).map (fun p =>
            (if p.1 = C₁ then (forestAutCard p.1 : R) else 0) *
            (if p.2 = C₂ then (forestAutCard p.2 : R) else 0))).sum) = 0 := by
      rw [show ((((Multiset.antidiagonal W).filter (· ≠ (C₁, C₂))).map (fun p =>
              (if p.1 = C₁ then (forestAutCard p.1 : R) else 0) *
              (if p.2 = C₂ then (forestAutCard p.2 : R) else 0))).sum)
            = ((((Multiset.antidiagonal W).filter (· ≠ (C₁, C₂))).map (fun _ =>
              (0 : R))).sum) from ?_]
      · simp
      refine congr_arg _ (Multiset.map_congr rfl ?_)
      intro p hp
      rw [Multiset.mem_filter] at hp
      obtain ⟨hp_mem, hp_ne⟩ := hp
      have hp_sum : p.1 + p.2 = W := Multiset.mem_antidiagonal.mp hp_mem
      -- If p.1 = C₁ then p.1 + p.2 = W = C₁ + C₂, so p.2 = C₂, contradicting `p ≠ (C₁, C₂)`.
      by_cases h1 : p.1 = C₁
      · have h2 : p.2 = C₂ := by
          have heq : p.1 + p.2 = C₁ + C₂ := hp_sum.trans hW
          rw [h1] at heq
          exact add_left_cancel heq
        exact absurd (Prod.ext h1 h2) hp_ne
      · rw [ite_eq_right h1, zero_mul]
    rw [h_vanish, add_zero]
    -- Surviving piece: `filter (· = (C₁,C₂)) (antidiagonal W) = replicate (count ...) (C₁,C₂)`.
    subst hW
    rw [Multiset.filter_eq']
    rw [Multiset.map_replicate, Multiset.sum_replicate]
    -- Goal: forestAutCard (C₁+C₂) = count • ((if True then ... else 0) * (if True then ... else 0))
    simp only [↓reduceIte]
    rw [nsmul_eq_mul]
    -- Goal: ↑(forestAutCard (C₁+C₂)) = ↑(count ...) * (↑(forestAutCard C₁) * ↑(forestAutCard C₂))
    -- Use S1 cast to R.
    have hS1 := UnorderedTree.forestAutCard_add C₁ C₂
    have hcast := congr_arg (Nat.cast (R := R)) hS1
    push_cast at hcast
    -- hcast : ↑forestAutCard (C₁+C₂) = ↑count * (↑forestAutCard C₁ * ↑forestAutCard C₂)
    -- `forestAutCard` here is the GL re-export of `UnorderedTree.forestAutCard`.
    show (UnorderedTree.forestAutCard (C₁ + C₂) : R) =
        ((Multiset.count (C₁, C₂) (Multiset.antidiagonal (C₁ + C₂)) : ℕ) : R) *
          ((UnorderedTree.forestAutCard C₁ : R) * (UnorderedTree.forestAutCard C₂ : R))
    -- Decidable instances on Forest = Multiset (UnorderedTree α) are unique up to
    -- propositional equality; `convert` closes the residual.
    convert hcast using 4
  · -- W ≠ C₁ + C₂. LHS = 0. The if now uses the ambient instance.
    simp only [ite_eq_right hW]
    -- Every p ∈ antidiagonal W has p.1 + p.2 = W ≠ C₁ + C₂. So at every p, the term is 0.
    symm
    -- Rewrite the map via map_congr so each term becomes 0; then sum of all-zeros = 0.
    have h_each_zero :
        ((Multiset.antidiagonal W).map (fun p =>
            (if p.1 = C₁ then (forestAutCard p.1 : R) else 0) *
            (if p.2 = C₂ then (forestAutCard p.2 : R) else 0))).sum =
          ((Multiset.antidiagonal W).map (fun _ => (0 : R))).sum := by
      congr 1
      refine Multiset.map_congr rfl ?_
      intro p hp_mem
      have hp_sum : p.1 + p.2 = W := Multiset.mem_antidiagonal.mp hp_mem
      by_cases h1 : p.1 = C₁
      · by_cases h2 : p.2 = C₂
        · exfalso
          apply hW
          rw [← hp_sum, h1, h2]
        · rw [ite_eq_left h1, ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    rw [h_each_zero]
    -- Sum of all-zeros = 0.
    simp [Multiset.map_const']

/-- Pairing a basis forest against a product splits the forest over its antidiagonal. -/
theorem pairing_of'_mul (W : Forest (UnorderedTree α))
    (z₁ z₂ : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' W) (z₁ * z₂) =
      ((Multiset.antidiagonal W).map (fun p =>
        pairing (R := R) (ConnesKreimer.of' p.1) z₁ *
        pairing (R := R) (ConnesKreimer.of' p.2) z₂)).sum := by
  induction z₁ using ConnesKreimer.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, ha, hb, Multiset.sum_map_add]
  | single F r =>
    induction z₂ using ConnesKreimer.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [mul_add, map_add, ha, hb, Multiset.sum_map_add]
    | single G s =>
      simp only [← ConnesKreimer.smul_of', smul_mul_smul_comm, map_smul, smul_eq_mul,
        pairing_of'_mul_of', mul_mul_mul_comm r, Multiset.sum_map_mul_left]

/-- Pairing a Grossman–Larson product against a Connes–Kreimer product splits both of its
factors, `⟨A ⋆ B, C₁ · C₂⟩ = Σ_{A = A₁ + A₂} Σ_{B = B₁ + B₂} ⟨A₁ ⋆ B₁, C₁⟩ ⟨A₂ ⋆ B₂, C₂⟩`. -/
theorem pairing_product_of'_mul_of' (A B C₁ C₂ : Forest (UnorderedTree α)) :
    pairing (R := R) (product (ConnesKreimer.of' A) (ConnesKreimer.of' B))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      ((A.antidiagonal ×ˢ B.antidiagonal).map fun pq ↦
        pairing (R := R) (product (ConnesKreimer.of' pq.1.1) (ConnesKreimer.of' pq.2.1))
            (ConnesKreimer.of' C₁) *
          pairing (R := R) (product (ConnesKreimer.of' pq.1.2) (ConnesKreimer.of' pq.2.2))
            (ConnesKreimer.of' C₂)).sum := by
  have h (A B : Forest (UnorderedTree α)) (z : ConnesKreimer R (UnorderedTree α)) :
      pairing (R := R) (product (ConnesKreimer.of' A) (ConnesKreimer.of' B)) z =
        ((productMultiset A B).map fun W ↦ pairing (R := R) (ConnesKreimer.of' W) z).sum := by
    change pairing.flip z _ = _
    rw [product_of'_of', map_multiset_sum, Multiset.map_map]
    rfl
  rw [h, Multiset.map_congr rfl fun W _ ↦ pairing_of'_mul W _ _, ← Multiset.sum_bind,
    ← Multiset.map_bind, productMultiset_bind_antidiagonal, Multiset.map_bind, Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ ↦ ?_)
  rw [h, h, ← Multiset.sum_map_product_mul]

open scoped TensorProduct

/-! ### The pairing on `H ⊗ H`

The duality with the pruning coproduct is stated on `H ⊗ H`. No such duality holds for a coproduct
that leaves marker leaves in the trunk, since grafting never produces them. -/

/-- `pairing₂` is the pairing on `H ⊗ H` with `pairing₂ (x ⊗ y) (w ⊗ z) = ⟨x, w⟩ * ⟨y, z⟩`. -/
noncomputable def pairing₂ :
    (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) →ₗ[R]
    (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) →ₗ[R] R :=
  let pair : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)
                →ₗ[R] R :=
    TensorProduct.lift pairing
  TensorProduct.curry <|
    LinearMap.mul' R R ∘ₗ
      TensorProduct.map pair pair ∘ₗ
      (TensorProduct.tensorTensorTensorComm R
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))).toLinearMap

@[simp] theorem pairing₂_tmul_tmul
    (x y w z : ConnesKreimer R (UnorderedTree α)) :
    pairing₂ (R := R) (x ⊗ₜ y) (w ⊗ₜ z) =
      pairing x w * pairing y z := by
  rfl

end GrossmanLarson

