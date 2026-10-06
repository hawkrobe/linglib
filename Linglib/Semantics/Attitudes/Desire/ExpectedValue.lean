module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability

/-!
# Expected-value desire semantics

`a wants p` iff the conditional expected value of `p` given `a`'s beliefs exceeds a
contextual threshold — [lassiter-2017]'s scalar semantics for evaluative predicates,
applied to *want* ([lassiter-2011]). `expectedValue` is the expectation of the value function
under the prior conditioned on the worlds of `p` compatible with the beliefs. It is an interval
scale (`expectedValue_affine`) and intermediate on disjoint propositions
(`expectedValue_intermediate`), from which the threshold reading derives Weakening
(`Want.union`) and, given exclusivity, the Smith Principle (`Want.inter_of_union_eq_univ`).
The bare threshold admits simultaneous `want p` and `want ¬p` (`exists_want_and_want_compl`).

## References

* [lassiter-2011]
* [lassiter-2017]
-/

@[expose] public section

namespace Desire.ExpectedValue

open MeasureTheory ProbabilityTheory

variable {W : Type*} [MeasurableSpace W] (μ : Measure W) (V : W → ℝ) (θ : ℝ) (bel p q : Set W)

/-- The expected value `E_V(p)` of `p` given the belief state is the expectation of the value
function under the prior conditioned on the worlds of `p` compatible with the beliefs. -/
noncomputable def expectedValue : ℝ := ∫ w, V w ∂μ[|bel ∩ p]

/-- `p` has positive prior mass inside the belief state when its compatible worlds do. -/
def HasPositiveBeliefMass : Prop := μ (bel ∩ p) ≠ 0

/-- `a wants p` when the expected value of `p` exceeds the threshold. -/
def Want : Prop := θ < expectedValue μ V bel p

variable {μ V θ bel p q} [IsFiniteMeasure μ]

/-- The mass of the compatible worlds of `p` times the expected value of `p` is the integral of
the value function over those worlds. -/
theorem measureReal_mul_expectedValue :
    μ.real (bel ∩ p) * expectedValue μ V bel p = ∫ w in bel ∩ p, V w ∂μ := by
  rw [expectedValue, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ← mul_assoc]
  rcases eq_or_ne (μ (bel ∩ p)) 0 with h | h
  · simp [measureReal_def, h, Measure.restrict_eq_zero.2 h]
  · rw [measureReal_def, ENNReal.toReal_inv, mul_inv_cancel₀
      (ENNReal.toReal_ne_zero.2 ⟨h, measure_ne_top _ _⟩), one_mul]

private theorem measureReal_pos (h : HasPositiveBeliefMass μ bel p) : 0 < μ.real (bel ∩ p) :=
  ENNReal.toReal_pos h (measure_ne_top _ _)

variable [Finite W] [MeasurableSingletonClass W]

/-- Over finitely many worlds, the expected value of `p` is the prior-weighted average of the
value function over the worlds of `p` compatible with the beliefs. -/
theorem expectedValue_eq_sum [Fintype W] [DecidablePred (· ∈ bel ∩ p)] :
    expectedValue μ V bel p =
      (∑ w ∈ Finset.univ.filter (· ∈ bel ∩ p), μ.real {w} * V w) /
        ∑ w ∈ Finset.univ.filter (· ∈ bel ∩ p), μ.real {w} := by
  have hden : ∑ w ∈ Finset.univ.filter (· ∈ bel ∩ p), μ.real {w} = μ.real (bel ∩ p) := by
    rw [sum_measureReal_singleton]
    congr 1
    ext w
    simp
  have hnum : ∑ w ∈ Finset.univ.filter (· ∈ bel ∩ p), μ.real {w} * V w =
      ∫ w in bel ∩ p, V w ∂μ := by
    rw [integral_fintype .of_finite, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [smul_eq_mul, measureReal_restrict_apply (measurableSet_singleton w)]
    by_cases hw : w ∈ bel ∩ p <;> simp [hw]
  rw [hden, hnum, ← measureReal_mul_expectedValue]
  rcases eq_or_ne (μ (bel ∩ p)) 0 with h | h
  · simp [expectedValue, cond_eq_zero_of_meas_eq_zero h]
  · rw [mul_div_cancel_left₀ _ (measureReal_pos h).ne']

/-- Expected value is an interval scale: a positive affine transformation of the value
function transforms expected value by the same coefficients. -/
theorem expectedValue_affine (h : HasPositiveBeliefMass μ bel p) (a b : ℝ) :
    expectedValue μ (fun w ↦ a * V w + b) bel p = a * expectedValue μ V bel p + b := by
  have := cond_isProbabilityMeasure (μ := μ) h
  simp only [expectedValue]
  rw [integral_add .of_finite .of_finite, integral_const_mul, integral_const, probReal_univ,
    one_smul]

/-- The expected value of a disjoint union lies between the expected values of the
parts. -/
theorem expectedValue_intermediate (hp : HasPositiveBeliefMass μ bel p)
    (hq : HasPositiveBeliefMass μ bel q) (hd : Disjoint p q) :
    min (expectedValue μ V bel p) (expectedValue μ V bel q) ≤ expectedValue μ V bel (p ∪ q) ∧
      expectedValue μ V bel (p ∪ q) ≤ max (expectedValue μ V bel p) (expectedValue μ V bel q) := by
  have hd' : Disjoint (bel ∩ p) (bel ∩ q) := hd.mono Set.inter_subset_right Set.inter_subset_right
  have hmp := measureReal_pos hp
  have hmq := measureReal_pos hq
  have hmass : μ.real (bel ∩ (p ∪ q)) = μ.real (bel ∩ p) + μ.real (bel ∩ q) := by
    rw [Set.inter_union_distrib_left, measureReal_union hd' (Set.toFinite _).measurableSet]
  have hsum : μ.real (bel ∩ (p ∪ q)) * expectedValue μ V bel (p ∪ q) =
      μ.real (bel ∩ p) * expectedValue μ V bel p + μ.real (bel ∩ q) * expectedValue μ V bel q := by
    rw [measureReal_mul_expectedValue, measureReal_mul_expectedValue, measureReal_mul_expectedValue,
      Set.inter_union_distrib_left,
      setIntegral_union hd' (Set.toFinite _).measurableSet Integrable.of_finite.integrableOn
        Integrable.of_finite.integrableOn]
  rw [hmass] at hsum
  constructor
  · by_contra hlt
    push Not at hlt
    nlinarith [min_le_left (expectedValue μ V bel p) (expectedValue μ V bel q),
      min_le_right (expectedValue μ V bel p) (expectedValue μ V bel q)]
  · by_contra hlt
    push Not at hlt
    nlinarith [le_max_left (expectedValue μ V bel p) (expectedValue μ V bel q),
      le_max_right (expectedValue μ V bel p) (expectedValue μ V bel q)]

/-- Weakening holds, since disjoint `p` and `q` both above threshold put their union above it. -/
theorem Want.union (hp' : HasPositiveBeliefMass μ bel p) (hq' : HasPositiveBeliefMass μ bel q)
    (hd : Disjoint p q) (hp : Want μ V θ bel p) (hq : Want μ V θ bel q) :
    Want μ V θ bel (p ∪ q) :=
  lt_of_lt_of_le (lt_min hp hq) (expectedValue_intermediate hp' hq' hd).1

/-- A disjoint union above threshold with one part at or below it has the other part
above it. -/
theorem Want.resolve_left (hp' : HasPositiveBeliefMass μ bel p)
    (hq' : HasPositiveBeliefMass μ bel q) (hd : Disjoint p q) (h : Want μ V θ bel (p ∪ q))
    (hp : ¬ Want μ V θ bel p) : Want μ V θ bel q :=
  (lt_max_iff.1 (lt_of_lt_of_le h (expectedValue_intermediate hp' hq' hd).2)).resolve_left hp

/-- The Smith Principle holds: for exhaustive `p` and `q` both above threshold, so is `p ∩ q`,
provided `want` is exclusive on `q`. -/
theorem Want.inter_of_union_eq_univ (hpq : HasPositiveBeliefMass μ bel (p ∩ q))
    (hq' : HasPositiveBeliefMass μ bel qᶜ) (huniv : p ∪ q = Set.univ) (hp : Want μ V θ bel p)
    (hex : ¬ Want μ V θ bel qᶜ) : Want μ V θ bel (p ∩ q) := by
  have hsub : qᶜ ⊆ p := Set.compl_subset_iff_union.2 (Set.union_comm _ _ ▸ huniv)
  have heq : qᶜ ∪ p ∩ q = p := by
    rw [← Set.inter_eq_right.2 hsub, Set.union_comm, Set.inter_union_compl]
  exact Want.resolve_left hq' hpq (disjoint_compl_left.mono_right Set.inter_subset_right)
    (by rw [heq]; exact hp) hex

omit [Finite W] [MeasurableSingletonClass W] [IsFiniteMeasure μ] in
/-- The bare threshold admits simultaneous `want p` and `want ¬p`. -/
theorem exists_want_and_want_compl :
    ∃ (W : Type) (_ : MeasurableSpace W) (μ : Measure W) (V : W → ℝ) (θ : ℝ) (bel p : Set W),
      Want μ V θ bel p ∧ Want μ V θ bel pᶜ := by
  refine ⟨Bool, inferInstance, Measure.count, fun b ↦ if b then 2 else 1, 0, Set.univ, {true}, ?_⟩
  have hpos (s : Set Bool) (hs : Measure.count (Set.univ ∩ s) ≠ 0) :
      0 < expectedValue Measure.count (fun b ↦ if b then (2 : ℝ) else 1) Set.univ s := by
    have := cond_isProbabilityMeasure (μ := Measure.count) hs
    refine lt_of_lt_of_le zero_lt_one ?_
    calc (1 : ℝ) = ∫ _, (1 : ℝ) ∂Measure.count[|Set.univ ∩ s] := by
          rw [integral_const, probReal_univ, smul_eq_mul, mul_one]
      _ ≤ _ := integral_mono (integrable_const 1) .of_finite fun b ↦ by cases b <;> norm_num
  exact ⟨hpos _ (by simp), hpos _ (by simp [Set.compl_def])⟩

end Desire.ExpectedValue
