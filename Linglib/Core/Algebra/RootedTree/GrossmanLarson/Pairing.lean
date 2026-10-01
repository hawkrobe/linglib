/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
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
* `GrossmanLarson.pairing₂`, `GrossmanLarson.pairing₃`: its extensions to `H ⊗ H` and
  `H ⊗ (H ⊗ H)`.

## Main results

* `GrossmanLarson.pairing_symm`: the pairing is symmetric.
* `GrossmanLarson.pairing_nondegenerate`: it is nondegenerate over a ring of characteristic zero
  without zero divisors, and so are `pairing₂` and `pairing₃`.
* `GrossmanLarson.pairing_of'_mul`: pairing against a Connes–Kreimer product splits the basis
  forest over its antidiagonal.

## References

* [foissy-2021]
* [grossman-larson-1989]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### The bilinear pairing -/

omit [DecidableEq α] in
/-- `pairingAux` is the symmetry-weighted pairing on finitely supported functions on forests. -/
noncomputable def pairingAux :
    (Forest (UnorderedTree α) →₀ R) →ₗ[R] (Forest (UnorderedTree α) →₀ R) →ₗ[R] R :=
  Finsupp.lift _ R (Forest (UnorderedTree α)) (fun F =>
    Finsupp.lift R R (Forest (UnorderedTree α)) (fun G =>
      if F = G then (forestAutCard F : R) else 0))

private theorem pairingAux_single_single (F G : Forest (UnorderedTree α)) :
    pairingAux (R := R) (Finsupp.single F 1) (Finsupp.single G 1) =
      (if F = G then (forestAutCard F : R) else 0) := by
  show (Finsupp.lift _ R (Forest (UnorderedTree α)) (fun F' =>
    Finsupp.lift R R (Forest (UnorderedTree α)) (fun G' =>
      if F' = G' then (forestAutCard F' : R) else 0)))
    (Finsupp.single F 1 : Forest (UnorderedTree α) →₀ R) (Finsupp.single G 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index]
  · rw [one_smul]
    show (Finsupp.lift R R (Forest (UnorderedTree α)) (fun G' =>
        if F = G' then (forestAutCard F : R) else 0))
        (Finsupp.single G 1 : Forest (UnorderedTree α) →₀ R) = _
    rw [Finsupp.lift_apply, Finsupp.sum_single_index]
    · simp only [one_smul]
    · simp
  · simp

omit [DecidableEq α] in
/-- `pairing (of' F) (of' G)` is the number of symmetries of `F` when `F = G`, and `0`
otherwise. -/
noncomputable def pairing :
    ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) →ₗ[R] R :=
  pairingAux.compl₁₂
    ((AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
      (ConnesKreimer.toFinsuppAlgEquiv (R := R) (T := UnorderedTree α)).toLinearMap)
    ((AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
      (ConnesKreimer.toFinsuppAlgEquiv (R := R) (T := UnorderedTree α)).toLinearMap)

private theorem pairing_apply (x y : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) x y = pairingAux x.toFinsupp.coeff y.toFinsupp.coeff := rfl

@[simp] theorem pairing_of'_of' (F G : Forest (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' (R := R) F)
                     (ConnesKreimer.of' (R := R) G) =
      (if F = G then (forestAutCard F : R) else 0) := by
  rw [pairing_apply, ConnesKreimer.toFinsupp_of', ConnesKreimer.toFinsupp_of']
  exact pairingAux_single_single F G

/-- The pairing is symmetric. -/
theorem pairing_symm (x y : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) x y = pairing y x := by
  refine ConnesKreimer.induction_linear x ?_ ?_ ?_
  · rw [LinearMap.map_zero, LinearMap.zero_apply, LinearMap.map_zero]
  · intro x₁ x₂ ih₁ ih₂
    rw [map_add, LinearMap.add_apply, ih₁, ih₂, map_add]
  · intro F r
    refine ConnesKreimer.induction_linear y ?_ ?_ ?_
    · rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
    · intro y₁ y₂ ih₁ ih₂
      rw [map_add, LinearMap.map_add, LinearMap.add_apply, ih₁, ih₂]
    · intro G s
      rw [show ConnesKreimer.single F r = r • ConnesKreimer.of' (R := R) F
            from ConnesKreimer.smul_single_one F r,
          show ConnesKreimer.single G s = s • ConnesKreimer.of' (R := R) G
            from ConnesKreimer.smul_single_one G s]
      simp only [LinearMap.map_smul, LinearMap.smul_apply, pairing_of'_of']
      by_cases h : F = G
      · subst h; ring
      · have h' : G ≠ F := fun heq => h heq.symm
        simp [h, h']

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
      (ConnesKreimer.counit : ConnesKreimer R (UnorderedTree α) →ₐ[R] R).toLinearMap :=
    ConnesKreimer.lhom_ext' fun F => by
      show pairing (R := R) (ConnesKreimer.of' F)
          (ConnesKreimer.of' (0 : Forest (UnorderedTree α))) =
        (ConnesKreimer.counit : ConnesKreimer R (UnorderedTree α) →ₐ[R] R)
          (ConnesKreimer.of' F)
      rw [pairing_of'_of', ConnesKreimer.counit_of']
      by_cases h : F = (0 : Forest (UnorderedTree α))
      · subst h
        rw [ite_eq_left rfl, ite_eq_left Multiset.card_zero]
        show ((UnorderedTree.forestAutCard (0 : Forest (UnorderedTree α)) : ℕ) : R) = 1
        rw [UnorderedTree.forestAutCard_zero, Nat.cast_one]
      · rw [ite_eq_right h, ite_eq_right (by simpa [Multiset.card_eq_zero] using h)]
  exact LinearMap.congr_fun h w

/-- Pairing against `of' G` gives the coefficient of `G`, weighted by the symmetries of `G`. -/
theorem pairing_apply_of' (x : ConnesKreimer R (UnorderedTree α))
    (G : Forest (UnorderedTree α)) :
    pairing (R := R) x (ConnesKreimer.of' G) =
      x.coeff G * (forestAutCard G : R) := by
  refine ConnesKreimer.induction_linear x ?_ ?_ ?_
  · simp
  · intro x₁ x₂ ih₁ ih₂
    rw [map_add, LinearMap.add_apply, ih₁, ih₂, ConnesKreimer.coeff_add, add_mul]
  · intro F r
    rw [show ConnesKreimer.single F r = r • ConnesKreimer.of' (R := R) F
          from ConnesKreimer.smul_single_one F r]
    simp only [LinearMap.map_smul, LinearMap.smul_apply, pairing_of'_of',
      ConnesKreimer.coeff_smul]
    rw [ConnesKreimer.coeff_of']
    by_cases h : F = G
    · subst h
      simp [smul_eq_mul]
    · simp [ite_eq_right h]

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
  -- First extend in z₂ at basis z₁, then in z₁.
  have aux : ∀ (C₁ : Forest (UnorderedTree α))
      (z₂ : ConnesKreimer R (UnorderedTree α)),
      pairing (R := R) (ConnesKreimer.of' W)
          (ConnesKreimer.of' C₁ * z₂) =
        ((Multiset.antidiagonal W).map (fun p =>
          pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
          pairing (R := R) (ConnesKreimer.of' p.2) z₂)).sum := by
    intro C₁ z₂
    refine ConnesKreimer.induction_linear z₂ ?_ ?_ ?_
    · show pairing (R := R) (ConnesKreimer.of' W)
          (ConnesKreimer.of' C₁ * (0 : ConnesKreimer R (UnorderedTree α))) =
        ((Multiset.antidiagonal W).map (fun p =>
          pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
          pairing (R := R) (ConnesKreimer.of' p.2)
            (0 : ConnesKreimer R (UnorderedTree α)))).sum
      rw [mul_zero, map_zero]
      symm
      refine Multiset.sum_eq_zero fun r hr => ?_
      obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
      rw [map_zero, mul_zero]
    · intro a b iha ihb
      let a' : ConnesKreimer R (UnorderedTree α) := a
      let b' : ConnesKreimer R (UnorderedTree α) := b
      show pairing (R := R) (ConnesKreimer.of' W)
          (ConnesKreimer.of' C₁ * (a' + b')) =
        ((Multiset.antidiagonal W).map (fun p =>
          pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
          pairing (R := R) (ConnesKreimer.of' p.2) (a' + b'))).sum
      rw [mul_add, map_add]
      rw [show pairing (R := R) (ConnesKreimer.of' W)
            (ConnesKreimer.of' C₁ * a') = _ from iha,
          show pairing (R := R) (ConnesKreimer.of' W)
            (ConnesKreimer.of' C₁ * b') = _ from ihb,
          ← Multiset.sum_map_add]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
      show pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
            pairing (R := R) (ConnesKreimer.of' p.2) a' +
          pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
            pairing (R := R) (ConnesKreimer.of' p.2) b' = _
      rw [map_add, mul_add]
    · intro G s
      rw [show ConnesKreimer.single G s = s • ConnesKreimer.of' (R := R) G
            from ConnesKreimer.smul_single_one G s,
          mul_smul_comm, map_smul, smul_eq_mul,
          pairing_of'_mul_of' W C₁ G]
      rw [show ((Multiset.antidiagonal W).map (fun p =>
            pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
            pairing (R := R) (ConnesKreimer.of' p.2)
              (s • ConnesKreimer.of' (R := R) G))) =
          ((Multiset.antidiagonal W).map (fun p => s *
            (pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
             pairing (R := R) (ConnesKreimer.of' p.2) (ConnesKreimer.of' G)))) from
        Multiset.map_congr rfl fun p _ => by rw [map_smul, smul_eq_mul]; ring]
      rw [Multiset.sum_map_mul_left]
  refine ConnesKreimer.induction_linear z₁ ?_ ?_ ?_
  · show pairing (R := R) (ConnesKreimer.of' W)
        ((0 : ConnesKreimer R (UnorderedTree α)) * z₂) =
      ((Multiset.antidiagonal W).map (fun p =>
        pairing (R := R) (ConnesKreimer.of' p.1)
          (0 : ConnesKreimer R (UnorderedTree α)) *
        pairing (R := R) (ConnesKreimer.of' p.2) z₂)).sum
    rw [zero_mul, map_zero]
    symm
    refine Multiset.sum_eq_zero fun r hr => ?_
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
    rw [map_zero, zero_mul]
  · intro a b iha ihb
    let a' : ConnesKreimer R (UnorderedTree α) := a
    let b' : ConnesKreimer R (UnorderedTree α) := b
    show pairing (R := R) (ConnesKreimer.of' W) ((a' + b') * z₂) =
      ((Multiset.antidiagonal W).map (fun p =>
        pairing (R := R) (ConnesKreimer.of' p.1) (a' + b') *
        pairing (R := R) (ConnesKreimer.of' p.2) z₂)).sum
    rw [add_mul, map_add]
    rw [show pairing (R := R) (ConnesKreimer.of' W) (a' * z₂) = _ from iha,
        show pairing (R := R) (ConnesKreimer.of' W) (b' * z₂) = _ from ihb,
        ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    show pairing (R := R) (ConnesKreimer.of' p.1) a' *
          pairing (R := R) (ConnesKreimer.of' p.2) z₂ +
        pairing (R := R) (ConnesKreimer.of' p.1) b' *
          pairing (R := R) (ConnesKreimer.of' p.2) z₂ = _
    rw [map_add, add_mul]
  · intro F r
    rw [show ConnesKreimer.single F r = r • ConnesKreimer.of' (R := R) F
          from ConnesKreimer.smul_single_one F r,
        smul_mul_assoc, map_smul, smul_eq_mul, aux F z₂]
    rw [show ((Multiset.antidiagonal W).map (fun p =>
          pairing (R := R) (ConnesKreimer.of' p.1)
            (r • ConnesKreimer.of' (R := R) F) *
          pairing (R := R) (ConnesKreimer.of' p.2) z₂)) =
        ((Multiset.antidiagonal W).map (fun p => r *
          (pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' F) *
           pairing (R := R) (ConnesKreimer.of' p.2) z₂))) from
      Multiset.map_congr rfl fun p _ => by rw [map_smul, smul_eq_mul]; ring]
    rw [Multiset.sum_map_mul_left]

open scoped TensorProduct

/-! ### Pairings on tensor powers

The pairing extends to `H ⊗ H` and `H ⊗ (H ⊗ H)`, where the duality with the pruning coproduct is
stated. No such duality holds for a coproduct that leaves marker leaves in the trunk, since
grafting never produces them. -/

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

/-- `pairing₃` is the pairing on `H ⊗ (H ⊗ H)` with
`pairing₃ (a ⊗ (b ⊗ c)) (x ⊗ (y ⊗ z)) = ⟨a, x⟩ * ⟨b, y⟩ * ⟨c, z⟩`. -/
noncomputable def pairing₃ :
    (ConnesKreimer R (UnorderedTree α) ⊗[R]
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))) →ₗ[R]
    (ConnesKreimer R (UnorderedTree α) ⊗[R]
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))) →ₗ[R] R :=
  let pair1 : ConnesKreimer R (UnorderedTree α) ⊗[R]
                ConnesKreimer R (UnorderedTree α) →ₗ[R] R :=
    TensorProduct.lift pairing
  let pair2 : (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
                ⊗[R] (ConnesKreimer R (UnorderedTree α) ⊗[R]
                      ConnesKreimer R (UnorderedTree α)) →ₗ[R] R :=
    TensorProduct.lift pairing₂
  TensorProduct.curry <|
    LinearMap.mul' R R ∘ₗ
      TensorProduct.map pair1 pair2 ∘ₗ
      (TensorProduct.tensorTensorTensorComm R
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α) ⊗[R]
          ConnesKreimer R (UnorderedTree α))).toLinearMap

/-- Evaluation of `pairing₃` on pure tensors. -/
@[simp] theorem pairing₃_tmul_tmul_tmul
    (a b c x y z : ConnesKreimer R (UnorderedTree α)) :
    pairing₃ (R := R) (a ⊗ₜ (b ⊗ₜ c)) (x ⊗ₜ (y ⊗ₜ z)) =
      pairing a x *
        (pairing b y * pairing c z) := by
  rfl

/-! ### `pairing₃` on reassociated tensors -/

/-- On a reassociated tensor `U ⊗ c`, `pairing₃` factors through `pairing₂` and the pairing. -/
lemma pairing₃_assoc_tmul
    (x y z' : ConnesKreimer R (UnorderedTree α))
    (U : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (c : ConnesKreimer R (UnorderedTree α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((TensorProduct.assoc R _ _ _) (U ⊗ₜ[R] c)) =
      pairing₂ (R := R) (x ⊗ₜ[R] y) U * pairing z' c := by
  induction U using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorProduct.assoc_tmul, pairing₃_tmul_tmul_tmul,
               pairing₂_tmul_tmul, _root_.mul_assoc]
  | add U₁ U₂ ih₁ ih₂ =>
    rw [TensorProduct.add_tmul, map_add, map_add, ih₁, ih₂, map_add, add_mul]

/-- On a tensor `a ⊗ S`, `pairing₃` factors through the pairing and `pairing₂`. -/
lemma pairing₃_tmul_apply
    (x y z' a : ConnesKreimer R (UnorderedTree α))
    (S : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z')) (a ⊗ₜ[R] S) =
      pairing x a * pairing₂ (R := R) (y ⊗ₜ[R] z') S := by
  induction S using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [pairing₃_tmul_tmul_tmul, pairing₂_tmul_tmul]
  | add S₁ S₂ ih₁ ih₂ =>
    rw [TensorProduct.tmul_add, map_add, ih₁, ih₂, map_add, mul_add]

/-! ### Nondegeneracy on tensor powers

Nondegeneracy of `pairing₂` and `pairing₃` follows from that of the pairing along the basis of
forests. -/

private theorem pairing₃_of'_tmul_of'_tmul (F G : Forest (UnorderedTree α))
    (s t : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    pairing₃ (R := R)
        (ConnesKreimer.of' F ⊗ₜ[R] s)
        (ConnesKreimer.of' G ⊗ₜ[R] t) =
      pairing (ConnesKreimer.of' (R := R) F)
                              (ConnesKreimer.of' G) *
        pairing₂ (R := R) s t := by
  induction s using TensorProduct.inductionOn with
  | tmul b c =>
    induction t using TensorProduct.inductionOn with
    | tmul y z =>
      simp only [pairing₃_tmul_tmul_tmul, pairing₂_tmul_tmul]
    | add t₁ t₂ ih₁ ih₂ =>
      -- pairing₃ is linear in 2nd arg (map_add); also `of' G ⊗ ·` distributes.
      rw [TensorProduct.tmul_add, map_add, ih₁, ih₂, map_add, mul_add]
  | add s₁ s₂ ih₁ ih₂ =>
    -- pairing₃ is linear in 1st arg, via map_add at the outer; same for pairing₂.
    rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply, ih₁, ih₂,
        map_add, LinearMap.add_apply, mul_add]

private theorem pairing₂_nondegenerate
    [CharZero R] [NoZeroDivisors R]
    (U : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (h : ∀ x y : ConnesKreimer R (UnorderedTree α),
      pairing₂ (R := R) (x ⊗ₜ[R] y) U = 0) : U = 0 := by
  classical
  let ℬ : Module.Basis (Forest (UnorderedTree α)) R (ConnesKreimer R (UnorderedTree α)) :=
    ConnesKreimer.basisSingleOne
  obtain ⟨c, hc⟩ : ∃ c : Forest (UnorderedTree α) →₀ ConnesKreimer R (UnorderedTree α),
      c.sum (fun F U_F => ℬ F ⊗ₜ[R] U_F) = U :=
    TensorProduct.eq_repr_basis_left ℬ U
  have hℬ : ∀ G : Forest (UnorderedTree α),
      (ℬ G : ConnesKreimer R (UnorderedTree α)) = ConnesKreimer.of' G := fun _ =>
    ConnesKreimer.basisSingleOne_apply _
  have hc_zero : ∀ F, c F = 0 := by
    intro F
    apply pairing_nondegenerate (c F)
    intro y
    rw [pairing_symm]
    have h_aut_ne : (UnorderedTree.forestAutCard F : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr (UnorderedTree.forestAutCard_pos F).ne'
    have h_eval := h (ConnesKreimer.of' F) y
    rw [← hc] at h_eval
    rw [map_finsuppSum (pairing₂ (R := R) (ConnesKreimer.of' F ⊗ₜ[R] y))] at h_eval
    simp only [hℬ, pairing₂_tmul_tmul, pairing_of'_of'] at h_eval
    rw [Finsupp.sum_eq_single F
          (fun G _ hGF => by rw [ite_eq_right (fun heq => hGF heq.symm), zero_mul])
          (fun _ => by rw [LinearMap.map_zero, mul_zero])] at h_eval
    rw [ite_eq_left rfl] at h_eval
    rcases mul_eq_zero.mp h_eval with h' | h'
    · exact absurd h' h_aut_ne
    · exact h'
  have hc_zero' : c = 0 := Finsupp.ext hc_zero
  rw [← hc, hc_zero', Finsupp.sum_zero_index]

/-- Over a ring of characteristic zero without zero divisors, `pairing₃` is nondegenerate. -/
theorem pairing₃_nondegenerate
    [CharZero R] [NoZeroDivisors R]
    (U : ConnesKreimer R (UnorderedTree α) ⊗[R]
          (ConnesKreimer R (UnorderedTree α) ⊗[R]
            ConnesKreimer R (UnorderedTree α)))
    (h : ∀ t, pairing₃ (R := R) t U = 0) : U = 0 := by
  classical
  let ℬ : Module.Basis (Forest (UnorderedTree α)) R
        (ConnesKreimer R (UnorderedTree α)) :=
    ConnesKreimer.basisSingleOne
  obtain ⟨c, hc⟩ : ∃ c : Forest (UnorderedTree α) →₀
        (ConnesKreimer R (UnorderedTree α) ⊗[R]
          ConnesKreimer R (UnorderedTree α)),
      c.sum (fun F U_F => ℬ F ⊗ₜ[R] U_F) = U :=
    TensorProduct.eq_repr_basis_left ℬ U
  have hℬ : ∀ G : Forest (UnorderedTree α),
      (ℬ G : ConnesKreimer R (UnorderedTree α)) = ConnesKreimer.of' G :=
    fun _ => ConnesKreimer.basisSingleOne_apply _
  have hc_zero : ∀ F, c F = 0 := by
    intro F
    apply pairing₂_nondegenerate (c F)
    intro x y
    have h_aut_ne : (UnorderedTree.forestAutCard F : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr (UnorderedTree.forestAutCard_pos F).ne'
    have h_eval := h (ConnesKreimer.of' F ⊗ₜ[R] (x ⊗ₜ[R] y))
    rw [← hc] at h_eval
    rw [map_finsuppSum
          (pairing₃ (R := R) (ConnesKreimer.of' F ⊗ₜ[R] (x ⊗ₜ[R] y)))] at h_eval
    simp only [hℬ, pairing₃_of'_tmul_of'_tmul, pairing_of'_of'] at h_eval
    rw [Finsupp.sum_eq_single F
          (fun G _ hGF => by rw [ite_eq_right (fun heq => hGF heq.symm), zero_mul])
          (fun _ => by rw [LinearMap.map_zero, mul_zero])] at h_eval
    rw [ite_eq_left rfl] at h_eval
    rcases mul_eq_zero.mp h_eval with h' | h'
    · exact absurd h' h_aut_ne
    · exact h'
  have hc_zero' : c = 0 := Finsupp.ext hc_zero
  rw [← hc, hc_zero', Finsupp.sum_zero_index]

end GrossmanLarson

