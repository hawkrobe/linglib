/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Combinatorics.RootedTree.Aut
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Symmetry-weighted pairing for GL ↔ CK duality
[foissy-typed-decorated-rooted-trees-2018]
[grossman-larson-1989]
[marcolli-chomsky-berwick-2025]

The pairing `⟨·, ·⟩ : H × H → R` (where `H = ConnesKreimer R (Nonplanar α)`)
realizes the duality between the Connes-Kreimer (CK) and
Grossman-Larson (GL) Hopf algebras on the shared carrier. By
Foissy 2018 (hal-01924416, §4.2), GL associativity ⇔ Δ^c
coassociativity via the pairing — the Δ^c proof in R.7 transports the
GL proof from `GrossmanLarson.lean` (R.5) through this duality.

## MCB targets

The pairing is the **bridge** that makes the GL framework
(`GrossmanLarson.lean`) usable to prove MCB's coassociativity claims:

* **Lemma 1.2.10** (Δ^c bialgebra): coassoc transported via this
  pairing from `GrossmanLarson.product_assoc`.
* **Lemma 1.7.3** (Insertion Lie ↔ primitives in `H^∨`): the dual Lie
  bracket on `H^∨` is induced by this pairing; MCB's binary `◁_e`
  (Def 1.7.1) is its binary specialization after `1 − α` quotient.
* **Δ^d** (MCB Def 1.2.5) and Δ^ρ (Lemma 1.2.11): same pairing
  framework, different extraction policies. See
  `memory/project_mcb_unification_rationale.md`.

## The pairing (Foissy 2018 §4.2)

For nonplanar rooted trees, the pairing on basis elements is
*symmetry-weighted*:
```
⟨of' F, of' G⟩ = if F = G then |Aut(F)| else 0
```
where `Aut(F)` is the automorphism group of `F` as a multiset of trees
(i.e., the product `∏_T |Aut(T)|^{m_T(F)} · m_T(F)!` over distinct
trees `T` with multiplicities `m_T(F)`, where `Aut(T)` is the rooted-
tree automorphism group of `T`).

Bilinearly extended to `H →ₗ[R] H →ₗ[R] R`. The pairing is
**symmetric** (because the underlying ⟨·,·⟩ on basis is symmetric in
F, G) and **non-degenerate** (the basis vectors are mutually orthogonal
with non-zero diagonal, so no non-zero element pairs to 0 with all
others — at least when `R` is characteristic-0; over `ℤ` there are
torsion subtleties when |Aut(F)| = 0 or non-invertible).

## Status

`[UPSTREAM]` candidate. Sorry-free, including `pairing_nondegenerate`.
The aut-cardinality substrate `Nonplanar.autCard` /
`Nonplanar.forestAutCard` lives in
`Linglib/Core/Combinatorics/RootedTree/Aut.lean` (re-exported here as
`treeAutCard` / `forestAutCard`), also sorry-free.
-/

namespace RootedTree

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### Automorphism count

The cardinality of the automorphism group of a rooted nonplanar tree
(or forest) is the symmetry weight in the pairing. The actual
substrate for these is in
`Linglib/Core/Combinatorics/RootedTree/Aut.lean` — re-exported here
under the `GrossmanLarson` namespace for use in the pairing. -/

/-- Re-export `Nonplanar.autCard` for use in the pairing. -/
noncomputable def treeAutCard (t : Nonplanar α) : ℕ :=
  Nonplanar.autCard t

/-- Re-export `Nonplanar.forestAutCard` for use in the pairing. -/
noncomputable def forestAutCard (F : Forest (Nonplanar α)) : ℕ :=
  Nonplanar.forestAutCard F

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
    (ConnesKreimer.toFinsuppAlgEquiv (R := R) (T := Nonplanar α)).toLinearMap
    (ConnesKreimer.toFinsuppAlgEquiv (R := R) (T := Nonplanar α)).toLinearMap

private theorem pairing_apply (x y : ConnesKreimer R (Nonplanar α)) :
    pairing (R := R) x y = pairingAux x.toFinsupp y.toFinsupp := rfl

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

end GrossmanLarson

end RootedTree
