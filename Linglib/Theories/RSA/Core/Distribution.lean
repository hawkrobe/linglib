import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Field.Basic

/-!
# Distribution

Typed probability distributions with compile-time guarantees.
-/

/-- Exact probability distribution over a finite type using rational arithmetic. -/
structure ExactDist (α : Type*) [Fintype α] where
  /-- The probability mass function -/
  mass : α → ℚ
  /-- All probabilities are non-negative -/
  nonneg : ∀ x, 0 ≤ mass x
  /-- Probabilities sum to exactly 1 -/
  sum_one : ∑ x : α, mass x = 1

namespace ExactDist

variable {α : Type*} [Fintype α]

/-- Get the probability of an element. -/
@[inline] def prob (d : ExactDist α) (x : α) : ℚ := d.mass x

/-- The support: elements with positive probability. -/
def support (d : ExactDist α) : Finset α :=
  Finset.univ.filter λ x => 0 < d.mass x

/-- Support is nonempty (since masses sum to 1 > 0). -/
theorem support_nonempty (d : ExactDist α) : d.support.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hzero : ∀ x, d.mass x = 0 := by
    intro x
    by_contra hne
    have hpos : 0 < d.mass x := by
      rcases (d.nonneg x).lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd heq.symm hne
    have hmem : x ∈ d.support := by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpos
    rw [h] at hmem
    simp at hmem
  have hsum : ∑ x : α, d.mass x = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact hzero x
  rw [d.sum_one] at hsum
  exact one_ne_zero hsum

/-- All probabilities are bounded by 1. -/
theorem mass_le_one (d : ExactDist α) (x : α) : d.mass x ≤ 1 := by
  have h : d.mass x ≤ ∑ y : α, d.mass y := by
    apply Finset.single_le_sum
    · intro y _
      exact d.nonneg y
    · exact Finset.mem_univ x
  rw [d.sum_one] at h
  exact h

/-- Build a distribution from unnormalized scores. -/
def normalize (scores : α → ℚ) (hnonneg : ∀ x, 0 ≤ scores x)
    (hpos_sum : 0 < ∑ x : α, scores x) : ExactDist α where
  mass x := scores x / ∑ y : α, scores y
  nonneg x := by
    apply div_nonneg
    · exact hnonneg x
    · exact le_of_lt hpos_sum
  sum_one := by
    have hne : (∑ y : α, scores y) ≠ 0 := ne_of_gt hpos_sum
    conv_lhs =>
      arg 2
      ext x
      rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    rw [mul_inv_cancel₀ hne]

/-- Uniform distribution over a nonempty finite type. -/
def uniform [Nonempty α] : ExactDist α where
  mass _ := 1 / Fintype.card α
  nonneg _ := by
    apply div_nonneg
    · exact le_of_lt one_pos
    · exact Nat.cast_nonneg _
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hne : (Fintype.card α : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp

/-- Point mass distribution: all probability on one element. -/
def pure (x : α) [DecidableEq α] : ExactDist α where
  mass y := if y = x then 1 else 0
  nonneg y := by
    split_ifs
    · exact le_of_lt one_pos
    · exact le_refl 0
  sum_one := by
    rw [Fintype.sum_eq_single x]
    · simp only [ite_true]
    · intro y hne
      simp only [hne, ite_false]

/-- Convert ExactDist to Mathlib's PMF. Noncomputable; use for proofs. -/
noncomputable def toPMF (d : ExactDist α) : PMF α :=
  PMF.ofFintype (λ x => ENNReal.ofReal (d.mass x : ℝ)) (by
    simp only [← ENNReal.ofReal_sum_of_nonneg (λ x _ => Rat.cast_nonneg.mpr (d.nonneg x))]
    simp only [← Rat.cast_sum, d.sum_one, Rat.cast_one, ENNReal.ofReal_one])

/-- PMF probability agrees with ExactDist probability. -/
theorem toPMF_apply (d : ExactDist α) (x : α) :
    d.toPMF x = ENNReal.ofReal (d.mass x : ℝ) := by
  simp only [toPMF, PMF.ofFintype_apply]

end ExactDist

/-- Attempt to build a distribution; returns `none` if all scores are zero. -/
def ExactDist.tryNormalize {α : Type*} [Fintype α]
    (scores : α → ℚ) (hnonneg : ∀ x, 0 ≤ scores x) : Option (ExactDist α) :=
  let total := ∑ x : α, scores x
  if h : 0 < total then
    some (ExactDist.normalize scores hnonneg h)
  else
    none

/-- Convert ExactDist to List representation (noncomputable). -/
noncomputable def ExactDist.toList {α : Type*} [Fintype α] (d : ExactDist α) : List (α × ℚ) :=
  (Finset.univ : Finset α).toList.map λ x => (x, d.mass x)

/-- Convert ExactDist to List using an explicit enumeration. -/
def ExactDist.toListWith {α : Type*} [Fintype α]
    (d : ExactDist α) (elements : List α) : List (α × ℚ) :=
  elements.map λ x => (x, d.mass x)

/-- Attempt to construct ExactDist from a list distribution. -/
def ExactDist.tryFromList {α : Type*} [Fintype α] [DecidableEq α] [BEq α]
    (dist : List (α × ℚ)) : Option (ExactDist α) :=
  -- Build a function from the list
  let massOf (x : α) : ℚ := dist.find? (·.1 == x) |>.map (·.2) |>.getD 0
  -- Check all values are non-negative (using decidability)
  if hnonneg : ∀ x, 0 ≤ massOf x then
    let total := ∑ x : α, massOf x
    -- Check sum is positive (allows normalization)
    if hpos : 0 < total then
      some (ExactDist.normalize massOf hnonneg hpos)
    else
      none
  else
    none

instance {α : Type*} [Fintype α] : CoeFun (ExactDist α) (λ _ => α → ℚ) where
  coe d := d.mass
