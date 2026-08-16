/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import Linglib.Core.Combinatorics.RootedTree.Aut
import Mathlib.Tactic.Ring

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# The symmetry-weighted GL/CK pairing
[foissy-typed-decorated-rooted-trees-2018]
[grossman-larson-1989]

The pairing `⟨·, ·⟩ : H →ₗ H →ₗ R` on `H = ConnesKreimer R (Nonplanar α)`
(Foissy 2018 §4.2), *symmetry-weighted* on the forest basis:

```
⟨of' F, of' G⟩ = if F = G then |Aut(F)| else 0
```

with the automorphism count `Nonplanar.forestAutCard`
(`Core/Combinatorics/RootedTree/Aut.lean`) as the weight. This is the
pairing under which the GL product and the pruning coproduct Δ^ρ are
adjoint (`Coproduct/PruningDuality.lean`).

## Main results

* `pairing_symm` — symmetry.
* `pairing_nondegenerate`, `ext_pairing_right` — nondegeneracy and its
  separation form, over `[CharZero R] [NoZeroDivisors R]`.
* `pairing_of'_mul_of'`, `pairing_of'_mul` — the product rule: pairing
  against a CK product decomposes over `antidiagonal` splits.
* `pairing₂`, `pairing₃` — the tensor-square and -cube extensions, with
  nondegeneracy lifted along the forest basis; the instruments through
  which the Δ^ρ duality is stated and transported.

`[UPSTREAM]` candidate. Sorry-free.
-/


namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### The bilinear pairing -/

omit [DecidableEq α] in
/-- Finsupp-level symmetry-weighted pairing on the bare forest basis. The
    public `pairing` is this transported through the Connes-Kreimer
    structure's `toFinsuppAlgEquiv`. -/
private noncomputable def pairingAux :
    (Forest (Nonplanar α) →₀ R) →ₗ[R] (Forest (Nonplanar α) →₀ R) →ₗ[R] R :=
  Finsupp.lift _ R (Forest (Nonplanar α)) (fun F =>
    Finsupp.lift R R (Forest (Nonplanar α)) (fun G =>
      if F = G then (forestAutCard F : R) else 0))

private theorem pairingAux_single_single (F G : Forest (Nonplanar α)) :
    pairingAux (R := R) (Finsupp.single F 1) (Finsupp.single G 1) =
      (if F = G then (forestAutCard F : R) else 0) := by
  show (Finsupp.lift _ R (Forest (Nonplanar α)) (fun F' =>
    Finsupp.lift R R (Forest (Nonplanar α)) (fun G' =>
      if F' = G' then (forestAutCard F' : R) else 0)))
    (Finsupp.single F 1 : Forest (Nonplanar α) →₀ R) (Finsupp.single G 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index]
  · rw [one_smul]
    show (Finsupp.lift R R (Forest (Nonplanar α)) (fun G' =>
        if F = G' then (forestAutCard F : R) else 0))
        (Finsupp.single G 1 : Forest (Nonplanar α) →₀ R) = _
    rw [Finsupp.lift_apply, Finsupp.sum_single_index]
    · simp only [one_smul]
    · simp
  · simp

omit [DecidableEq α] in
/-- The **symmetry-weighted pairing** `⟨·, ·⟩ : H × H → R`. On basis
    elements, `⟨of' F, of' G⟩ = if F = G then forestAutCard F else 0`
    (in `R`, via `Nat.cast`). Bilinearly extended, transported from the
    forest-basis `pairingAux` through `ConnesKreimer.toFinsuppAlgEquiv`. -/
noncomputable def pairing :
    ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) →ₗ[R] R :=
  pairingAux.compl₁₂
    ((AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
      (ConnesKreimer.toFinsuppAlgEquiv (R := R) (T := Nonplanar α)).toLinearMap)
    ((AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
      (ConnesKreimer.toFinsuppAlgEquiv (R := R) (T := Nonplanar α)).toLinearMap)

private theorem pairing_apply (x y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) x y = pairingAux x.toFinsupp.coeff y.toFinsupp.coeff := rfl

@[simp] theorem pairing_of'_of' (F G : Forest (Nonplanar α)) :
    pairing (R := R) (ConnesKreimer.of' (R := R) F)
                     (ConnesKreimer.of' (R := R) G) =
      (if F = G then (forestAutCard F : R) else 0) := by
  rw [pairing_apply, ConnesKreimer.toFinsupp_of', ConnesKreimer.toFinsupp_of']
  exact pairingAux_single_single F G

/-- The pairing is symmetric. Reduces by bilinearity to the basis case,
    where `pairing_of'_of'` shows both sides are `if F = G then
    forestAutCard F else 0` — same value (the `F = G` case forces it). -/
theorem pairing_symm (x y : ConnesKreimer R (Nonplanar α)) :
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

/-- The pairing vanishes on `0`. Free from linearity. -/
@[simp] theorem pairing_zero_left (y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) 0 y = 0 := by
  simp only [LinearMap.map_zero, LinearMap.zero_apply]

/-- The pairing vanishes on `0` (right). -/
@[simp] theorem pairing_zero_right (x : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) x 0 = 0 :=
  LinearMap.map_zero _

/-- Pairing against the unit extracts the counit (the coefficient of the
    empty forest): `⟨w, 1⟩ = ε w`. -/
theorem pairing_one_right (w : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) w (1 : ConnesKreimer R (Nonplanar α)) =
      (ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R) w := by
  have h : (pairing (R := R)).flip (1 : ConnesKreimer R (Nonplanar α)) =
      (ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R).toLinearMap :=
    ConnesKreimer.lhom_ext' fun F => by
      show pairing (R := R) (ConnesKreimer.of' F)
          (ConnesKreimer.of' (0 : Forest (Nonplanar α))) =
        (ConnesKreimer.counit : ConnesKreimer R (Nonplanar α) →ₐ[R] R)
          (ConnesKreimer.of' F)
      rw [pairing_of'_of', ConnesKreimer.counit_of']
      by_cases h : F = (0 : Forest (Nonplanar α))
      · subst h
        rw [if_pos rfl, if_pos Multiset.card_zero]
        show ((Nonplanar.forestAutCard (0 : Forest (Nonplanar α)) : ℕ) : R) = 1
        rw [Nonplanar.forestAutCard_zero, Nat.cast_one]
      · rw [if_neg h, if_neg (by simpa [Multiset.card_eq_zero] using h)]
  exact LinearMap.congr_fun h w

/-- Each pairing against a basis element `of' G` extracts the coefficient
    of `G` in `x`, weighted by `forestAutCard G`. Proof: reduce to basis
    via `Finsupp.induction_linear` on `x`, then `pairing_of'_of'`. -/
theorem pairing_apply_of' (x : ConnesKreimer R (Nonplanar α))
    (G : Forest (Nonplanar α)) :
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
    · simp [if_neg h]

/-- **Non-degeneracy** of the pairing over `CharZero R` with no zero
    divisors. If `pairing x y = 0` for all `y`, then `x = 0`. Uses
    `pairing_apply_of'` (coefficient extraction) + `forestAutCard_pos`
    (positivity) + `Nat.cast_ne_zero` (CharZero R has no Nat-cast torsion)
    + `mul_eq_zero` (NoZeroDivisors R).

    Holds for any commutative ring with characteristic 0 and no zero
    divisors (e.g. `ℤ`, `ℚ`, `ℝ`, `ℂ`, any field of char 0). -/
theorem pairing_nondegenerate
    [CharZero R] [NoZeroDivisors R] (x : ConnesKreimer R (Nonplanar α))
    (h : ∀ y, pairing (R := R) x y = 0) : x = 0 := by
  refine ConnesKreimer.ext_coeff fun G => ?_
  rw [ConnesKreimer.coeff_zero]
  have hG : pairing (R := R) x (ConnesKreimer.of' G) = 0 := h _
  rw [pairing_apply_of'] at hG
  have hauts_ne : (Nonplanar.forestAutCard G : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nonplanar.forestAutCard_pos G).ne'
  rcases mul_eq_zero.mp hG with hx | hx
  · exact hx
  · exact absurd hx hauts_ne

section Ring
variable {R : Type*} [CommRing R] [CharZero R] [NoZeroDivisors R]

/-- Separation form of `pairing_nondegenerate`: elements pairing equally
    against everything are equal. -/
theorem ext_pairing_right {x y : ConnesKreimer R (Nonplanar α)}
    (h : ∀ z, pairing (R := R) x z = pairing y z) : x = y :=
  sub_eq_zero.mp <| pairing_nondegenerate _ fun z => by
    rw [map_sub, LinearMap.sub_apply, h, sub_self]

end Ring

/-! ### Product rule

Pairing against a CK product decomposes over the two-sided sub-multiset
splits of the first argument (`Multiset.antidiagonal`) — the
symmetry-weighted pairing turns CK multiplication into the split
coproduct. The combinatorial heart is the multinomial identity
`Nonplanar.forestAutCard_add` (`Aut.lean`). Computationally validated
(`scratch/validate_duality.lean`, V2 battery). -/

/-- **Pairing product rule** (basis form):
    `⟨W, C₁ · C₂⟩ = Σ_{W = W₁ + W₂} ⟨W₁, C₁⟩ · ⟨W₂, C₂⟩`.

    Only the split `(C₁, C₂)` survives the diagonal pairing, with
    multiplicity `count (C₁,C₂) (antidiagonal W)`; the autCard weights
    recombine via `Nonplanar.forestAutCard_add`. -/
theorem pairing_of'_mul_of' (W C₁ C₂ : Forest (Nonplanar α)) :
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
    rw [if_pos hW]
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
      · rw [if_neg h1, zero_mul]
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
    have hS1 := Nonplanar.forestAutCard_add C₁ C₂
    have hcast := congr_arg (Nat.cast (R := R)) hS1
    push_cast at hcast
    -- hcast : ↑forestAutCard (C₁+C₂) = ↑count * (↑forestAutCard C₁ * ↑forestAutCard C₂)
    -- `forestAutCard` here is the GL re-export of `Nonplanar.forestAutCard`.
    show (Nonplanar.forestAutCard (C₁ + C₂) : R) =
        ((Multiset.count (C₁, C₂) (Multiset.antidiagonal (C₁ + C₂)) : ℕ) : R) *
          ((Nonplanar.forestAutCard C₁ : R) * (Nonplanar.forestAutCard C₂ : R))
    -- Decidable instances on Forest = Multiset (Nonplanar α) are unique up to
    -- propositional equality; `convert` closes the residual.
    convert hcast using 4
  · -- W ≠ C₁ + C₂. LHS = 0. The if now uses the ambient instance.
    simp only [if_neg hW]
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
        · rw [if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [h_each_zero]
    -- Sum of all-zeros = 0.
    simp [Multiset.map_const']

/-- **Pairing product rule** (bilinear form): pairing a basis vector
    against a product decomposes over the antidiagonal splits of the
    basis forest. Bilinear extension of `pairing_of'_mul_of'`. -/
theorem pairing_of'_mul (W : Forest (Nonplanar α))
    (z₁ z₂ : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) (ConnesKreimer.of' W) (z₁ * z₂) =
      ((Multiset.antidiagonal W).map (fun p =>
        pairing (R := R) (ConnesKreimer.of' p.1) z₁ *
        pairing (R := R) (ConnesKreimer.of' p.2) z₂)).sum := by
  -- First extend in z₂ at basis z₁, then in z₁.
  have aux : ∀ (C₁ : Forest (Nonplanar α))
      (z₂ : ConnesKreimer R (Nonplanar α)),
      pairing (R := R) (ConnesKreimer.of' W)
          (ConnesKreimer.of' C₁ * z₂) =
        ((Multiset.antidiagonal W).map (fun p =>
          pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
          pairing (R := R) (ConnesKreimer.of' p.2) z₂)).sum := by
    intro C₁ z₂
    refine ConnesKreimer.induction_linear z₂ ?_ ?_ ?_
    · show pairing (R := R) (ConnesKreimer.of' W)
          (ConnesKreimer.of' C₁ * (0 : ConnesKreimer R (Nonplanar α))) =
        ((Multiset.antidiagonal W).map (fun p =>
          pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
          pairing (R := R) (ConnesKreimer.of' p.2)
            (0 : ConnesKreimer R (Nonplanar α)))).sum
      rw [mul_zero, map_zero]
      symm
      refine Multiset.sum_eq_zero fun r hr => ?_
      obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
      rw [map_zero, mul_zero]
    · intro a b iha ihb
      let a' : ConnesKreimer R (Nonplanar α) := a
      let b' : ConnesKreimer R (Nonplanar α) := b
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
        ((0 : ConnesKreimer R (Nonplanar α)) * z₂) =
      ((Multiset.antidiagonal W).map (fun p =>
        pairing (R := R) (ConnesKreimer.of' p.1)
          (0 : ConnesKreimer R (Nonplanar α)) *
        pairing (R := R) (ConnesKreimer.of' p.2) z₂)).sum
    rw [zero_mul, map_zero]
    symm
    refine Multiset.sum_eq_zero fun r hr => ?_
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
    rw [map_zero, zero_mul]
  · intro a b iha ihb
    let a' : ConnesKreimer R (Nonplanar α) := a
    let b' : ConnesKreimer R (Nonplanar α) := b
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

/-! ### Tensor-extended pairings

The pairing `⟨·, ·⟩` above extends to the
tensor square (`pairing₂`) and cube (`pairing₃`). These power the GL/CK
duality for the deletion coproduct Δ^ρ (`Coproduct/PruningDuality.lean`:
`⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`). For the trace variant Δ^c no
such duality holds — the trunk of a proper cut contains trace-marker
leaves that GL grafting can never produce — so Δ^c coassociativity
(`comulCN_coassoc`, `Coproduct/Trace.lean`) is a separate
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
noncomputable def pairing₂ :
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
@[simp] theorem pairing₂_tmul_tmul
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
noncomputable def pairing₃ :
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
@[simp] theorem pairing₃_tmul_tmul_tmul
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
lemma pairing₃_assoc_tmul
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
lemma pairing₃_tmul_apply
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
private theorem pairing₃_of'_tmul_of'_tmul (F G : Forest (Nonplanar α))
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
private theorem pairing₂_nondegenerate
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
theorem pairing₃_nondegenerate
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

end GrossmanLarson

