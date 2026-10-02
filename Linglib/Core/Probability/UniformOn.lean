module

public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.Real

/-!
# The uniform measure on a finite type

Evaluation of `ProbabilityTheory.uniformOn` on a finset or on `Set.univ` at singletons and
finite sets, in `ℝ≥0∞` and on reals.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype W]

omit [Fintype W] in
/-- The uniform measure on a finset at a singleton: `1 / #A` on `A` and `0` off it. -/
theorem uniformOn_finset_apply_singleton [DecidableEq W] (A : Finset W) (w : W) :
    uniformOn ↑A {w} = if w ∈ A then (A.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases h : w ∈ A <;> simp [Finset.inter_singleton_of_mem, Finset.inter_singleton_of_notMem, h,
    div_eq_mul_inv]

theorem uniformOn_univ_apply_singleton (w : W) :
    uniformOn (Set.univ : Set W) {w} = (Fintype.card W : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton, one_div]

theorem uniformOn_univ_singleton_ne_zero (w : W) : uniformOn (Set.univ : Set W) {w} ≠ 0 := by
  rw [uniformOn_univ_apply_singleton]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem uniformOn_univ_singleton_eq (w w' : W) :
    uniformOn (Set.univ : Set W) {w} = uniformOn Set.univ {w'} := by
  rw [uniformOn_univ_apply_singleton, uniformOn_univ_apply_singleton]

theorem uniformOn_univ_real_singleton (w : W) :
    (uniformOn (Set.univ : Set W)).real {w} = (Fintype.card W : ℝ)⁻¹ := by
  rw [measureReal_def, uniformOn_univ, Measure.count_singleton, one_div,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem uniformOn_univ_real_coe_finset (s : Finset W) :
    (uniformOn (Set.univ : Set W)).real ↑s = s.card / Fintype.card W := by
  rw [measureReal_def, uniformOn_univ, Measure.count_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]

omit [Fintype W] in
/-- The uniform measure on a set at a set, on reals: the proportion of the atoms of `s` lying
in `e`, with `0 / 0 = 0` when `s` is empty. -/
theorem uniformOn_real_apply [Finite W] (s e : Set W) :
    (uniformOn s).real e = (s ∩ e).ncard / s.ncard := by
  rw [measureReal_def, uniformOn, cond_apply (Set.toFinite s).measurableSet,
    Measure.count_apply_finite _ (Set.toFinite _), Measure.count_apply_finite _ (Set.toFinite _),
    ← Set.ncard_eq_toFinset_card, ← Set.ncard_eq_toFinset_card, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast, inv_mul_eq_div]

/-- On a finite type the uniform measure gives a set, on reals, the proportion of atoms in it. -/
theorem uniformOn_univ_real_apply (A : Set W) :
    (uniformOn (Set.univ : Set W)).real A = A.ncard / Fintype.card W := by
  rw [uniformOn_real_apply, Set.univ_inter, Set.ncard_univ, Nat.card_eq_fintype_card]

/-- The uniform measure on a nonempty finite type compares two sets as their cardinalities. -/
theorem uniformOn_univ_le_iff [Nonempty W] {A B : Set W} :
    uniformOn (Set.univ : Set W) A ≤ uniformOn Set.univ B ↔ A.ncard ≤ B.ncard := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, uniformOn_univ_real_apply, uniformOn_univ_real_apply,
    div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos), Nat.cast_le]

omit [Fintype W] in
/-- The uniform measure on a subset of a finite set is absolutely continuous with respect to
the uniform measure on the set. -/
theorem uniformOn_absolutelyContinuous_of_subset {A B : Set W} (hB : B.Finite) (hAB : A ⊆ B) :
    uniformOn A ≪ uniformOn B := λ s hs => by
  rw [uniformOn_eq_zero_iff hB] at hs
  rw [uniformOn_eq_zero_iff (hB.subset hAB)]
  exact Set.eq_empty_of_subset_empty (hs ▸ Set.inter_subset_inter_left s hAB)

end MeasureTheory
