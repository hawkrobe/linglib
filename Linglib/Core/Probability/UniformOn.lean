module

public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.Real

/-!
# The uniform measure on a finite type

Evaluation of `ProbabilityTheory.uniformOn` on a finset or on `Set.univ` at singletons, finite
sets and predicates, in `ℝ≥0∞` and on reals, and the almost-everywhere filter of the uniform
measure on a finite type.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype W]

omit [Fintype W] in
/-- The uniform measure on a finset gives a singleton `1 / #A` on `A` and `0` off it. -/
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

/-- Under the uniform measure on a finite type, almost everywhere is everywhere. -/
theorem uniformOn_univ_ae_iff {p : W → Prop} :
    (∀ᵐ w ∂uniformOn (Set.univ : Set W), p w) ↔ ∀ w, p w := by
  rw [ae_iff_of_countable]
  exact ⟨fun h w ↦ h w (uniformOn_univ_singleton_ne_zero w), fun h w _ ↦ h w⟩

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
/-- The uniform measure on a set gives a set, on reals, the proportion of the atoms of `s` lying
in `e`, with `0 / 0 = 0` when `s` is empty. -/
theorem uniformOn_real_apply [Finite W] (s e : Set W) :
    (uniformOn s).real e = (s ∩ e).ncard / s.ncard := by
  rw [measureReal_def, uniformOn, cond_apply (Set.toFinite s).measurableSet,
    Measure.count_apply_finite _ (Set.toFinite _), Measure.count_apply_finite _ (Set.toFinite _),
    ← Set.ncard_eq_toFinset_card, ← Set.ncard_eq_toFinset_card, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast, inv_mul_eq_div]

omit [Fintype W] in
/-- The uniform measure on a finset gives a predicate, on reals, the proportion of the finset
satisfying it. -/
theorem uniformOn_finset_real_setOf [Finite W] (A : Finset W) (p : W → Prop) [DecidablePred p] :
    (uniformOn (A : Set W)).real {w | p w} = (A.filter p).card / A.card := by
  rw [uniformOn_real_apply, Set.ncard_coe_finset]
  congr 2
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  rfl

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
    uniformOn A ≪ uniformOn B := fun s hs ↦ by
  rw [uniformOn_eq_zero_iff hB] at hs
  rw [uniformOn_eq_zero_iff (hB.subset hAB)]
  exact Set.eq_empty_of_subset_empty (hs ▸ Set.inter_subset_inter_left s hAB)

/-! ### Proportions of a finite set

On a finite set `s` the uniform measure gives `t` the proportion `|s ∩ t| / |s|`, so a bound on the
measure is a bound on `|s ∩ t|` scaled by `|s|`. -/

section Finite

variable {s t : Set W}

omit [Fintype W] in
/-- The uniform measure on a finite set gives a set the proportion of `s` lying in it. -/
theorem uniformOn_apply_of_finite (hs : s.Finite) (t : Set W) :
    uniformOn s t = (s ∩ t).ncard / s.ncard := by
  rw [uniformOn, cond_apply hs.measurableSet, Measure.count_apply_finite _ hs,
    Measure.count_apply_finite _ (hs.inter_of_left t), ← Set.ncard_eq_toFinset_card _ hs,
    ← Set.ncard_eq_toFinset_card _ (hs.inter_of_left t), ENNReal.div_eq_inv_mul]

omit [Fintype W] in
/-- The uniform measure on a finset gives a predicate the proportion of the finset satisfying
it. -/
theorem uniformOn_finset_setOf (F : Finset W) (p : W → Prop) [DecidablePred p] :
    uniformOn (F : Set W) {x | p x} = (F.filter p).card / F.card := by
  have : (F : Set W) ∩ {x | p x} = ↑(F.filter p) := by rw [Finset.coe_filter]; rfl
  rw [uniformOn_apply_of_finite F.finite_toSet, this, Set.ncard_coe_finset, Set.ncard_coe_finset]

omit [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype W] in
private theorem ncard_ne_zero_of_nonempty (hs : s.Finite) (hne : s.Nonempty) :
    (s.ncard : ℝ≥0∞) ≠ 0 := by
  simpa using ((Set.ncard_pos hs).2 hne).ne'

omit [Fintype W] in
theorem le_uniformOn_iff (hs : s.Finite) (hne : s.Nonempty) {θ : ℝ≥0∞} :
    θ ≤ uniformOn s t ↔ θ * s.ncard ≤ (s ∩ t).ncard := by
  rw [uniformOn_apply_of_finite hs, ENNReal.le_div_iff_mul_le
    (.inl (ncard_ne_zero_of_nonempty hs hne)) (.inl (by simp))]

omit [Fintype W] in
theorem lt_uniformOn_iff (hs : s.Finite) (hne : s.Nonempty) {θ : ℝ≥0∞} :
    θ < uniformOn s t ↔ θ * s.ncard < (s ∩ t).ncard := by
  rw [uniformOn_apply_of_finite hs, ENNReal.lt_div_iff_mul_lt
    (.inl (ncard_ne_zero_of_nonempty hs hne)) (.inl (by simp))]

omit [Fintype W] in
theorem uniformOn_le_iff (hs : s.Finite) (hne : s.Nonempty) {θ : ℝ≥0∞} :
    uniformOn s t ≤ θ ↔ (s ∩ t).ncard ≤ θ * s.ncard := by
  rw [uniformOn_apply_of_finite hs, ENNReal.div_le_iff (ncard_ne_zero_of_nonempty hs hne)
    (by simp)]

omit [Fintype W] in
/-- Conditioning the uniform measure on `s` by `t` is the uniform measure on `s ∩ t`: chained
conditioning collapses, as `cond_cond_eq_cond_inter` does for `cond`. -/
theorem uniformOn_cond (hs : s.Finite) (ht : MeasurableSet t) :
    (uniformOn s)[|t] = uniformOn (s ∩ t) := by
  rw [uniformOn, uniformOn,
    cond_cond_eq_cond_inter' hs.measurableSet ht (Measure.count_apply_lt_top.2 hs).ne]

omit [Fintype W] in
/-- The uniform measure on a nonempty finite set gives `t` the measure `1` exactly when `t`
contains it. -/
theorem uniformOn_eq_one_iff (hs : s.Finite) (hne : s.Nonempty) : uniformOn s t = 1 ↔ s ⊆ t :=
  ⟨pred_true_of_uniformOn_eq_one, uniformOn_eq_one_of hs hne⟩

omit [Fintype W] in
/-- The uniform measure on a nonempty finite set gives `t` the measure `1 / |s|` exactly when
one member of `s` lies in `t`. -/
theorem uniformOn_eq_inv_ncard_iff (hs : s.Finite) (hne : s.Nonempty) :
    uniformOn s t = (s.ncard : ℝ≥0∞)⁻¹ ↔ (s ∩ t).ncard = 1 := by
  rw [uniformOn_apply_of_finite hs, ENNReal.div_eq_inv_mul]
  nth_rewrite 2 [← mul_one (s.ncard : ℝ≥0∞)⁻¹]
  rw [ENNReal.mul_right_inj (by simp) (by simpa using ncard_ne_zero_of_nonempty hs hne),
    Nat.cast_eq_one]

end Finite

end MeasureTheory
