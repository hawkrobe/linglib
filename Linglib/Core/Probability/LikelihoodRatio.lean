/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Event-level likelihood ratios of two measures

The likelihood ratio `μ e / ν e` of a pair of measures at an event: the
Bayes factor of the evidence `e` for the simple binary testing problem
`(μ, ν)`. Mathlib's `MeasureTheory.llr` is the *pointwise* log-ratio
`log (μ.rnDeriv ν x).toReal`; this file's ratio is its event-level
companion — the marginal likelihood ratio a Bayes factor compares, which
agrees with `exp (llr μ ν x)` at positive-mass atoms of a discrete space
and is the object Merin-style argumentation semantics needs (evidence is a
proposition, not a sample point). In the vocabulary of Degenne's
testing-lower-bounds development (upstreaming into
`Mathlib.Probability.Decision`), the pair `(μ, ν)` is `twoHypKernel μ ν`;
this file proves the ratio's algebra without any packaging. `[UPSTREAM]`
candidates.

## Main results

* `likelihoodRatio_mul_swap`: LR(μ,ν) · LR(ν,μ) = 1 at events of nonzero
  finite mass under both measures.
* `log_likelihoodRatio`: the log-ratio is a difference of surprisals.
* `likelihoodRatio_inter`: under independence in both measures, the ratio
  is multiplicative over intersections.
* `max_likelihoodRatio_lt_inter`, `likelihoodRatio_union_lt_max`,
  `one_lt_likelihoodRatio_union`: for probability measures with both events
  of ratio above one, intersection beats both events beats union beats one.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The likelihood ratio of two measures at an event, in `ℝ≥0∞`: total
division gives the boundary cases their true values — `ν e = 0 < μ e` is
infinitely strong evidence for `μ`, and 0/0 = 0. -/
noncomputable def likelihoodRatio (μ ν : Measure Ω) (e : Set Ω) : ℝ≥0∞ :=
  μ e / ν e

variable {μ ν : Measure Ω} {a b e : Set Ω}

theorem likelihoodRatio_def (μ ν : Measure Ω) (e : Set Ω) :
    likelihoodRatio μ ν e = μ e / ν e := rfl

/-- Swapping the hypotheses inverts the ratio: LR(μ,ν) · LR(ν,μ) = 1 at any
event with nonzero finite mass under both. -/
theorem likelihoodRatio_mul_swap (hμ0 : μ e ≠ 0) (hμt : μ e ≠ ∞)
    (hν0 : ν e ≠ 0) (hνt : ν e ≠ ∞) :
    likelihoodRatio μ ν e * likelihoodRatio ν μ e = 1 := by
  rw [likelihoodRatio, likelihoodRatio, div_eq_mul_inv, div_eq_mul_inv,
    mul_mul_mul_comm, mul_comm (μ e) (ν e), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hν0 hνt, ENNReal.mul_inv_cancel hμ0 hμt, one_mul]

/-- The log-likelihood ratio is a difference of surprisals:
log LR(μ,ν)(E) = (−log ν E) − (−log μ E). -/
theorem log_likelihoodRatio (hμ0 : μ e ≠ 0) (hμt : μ e ≠ ∞)
    (hν0 : ν e ≠ 0) (hνt : ν e ≠ ∞) :
    Real.log (likelihoodRatio μ ν e).toReal =
      (-Real.log (ν e).toReal) - (-Real.log (μ e).toReal) := by
  rw [likelihoodRatio, ENNReal.toReal_div,
    Real.log_div (ENNReal.toReal_ne_zero.mpr ⟨hμ0, hμt⟩)
      (ENNReal.toReal_ne_zero.mpr ⟨hν0, hνt⟩)]
  ring

/-- Under independence in both measures, the likelihood ratio is
multiplicative over intersections. -/
theorem likelihoodRatio_inter (h₁ : IndepSet a b μ) (h₂ : IndepSet a b ν)
    (hνb0 : ν b ≠ 0) (hνbt : ν b ≠ ∞) :
    likelihoodRatio μ ν (a ∩ b) = likelihoodRatio μ ν a * likelihoodRatio μ ν b := by
  rw [likelihoodRatio, likelihoodRatio, likelihoodRatio,
    h₁.measure_inter_eq_mul, h₂.measure_inter_eq_mul,
    ENNReal.mul_div_mul_comm (Or.inr hνbt) (Or.inr hνb0)]

section OrderFacts

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Intersection dominates both conjuncts: under independence in both
measures, if both events have ratio above one then so does their
intersection, strictly beyond either. -/
theorem max_likelihoodRatio_lt_inter (h₁ : IndepSet a b μ) (h₂ : IndepSet a b ν)
    (ha : 1 < likelihoodRatio μ ν a) (hb : 1 < likelihoodRatio μ ν b)
    (hνa : ν a ≠ 0) (hνb : ν b ≠ 0) :
    max (likelihoodRatio μ ν a) (likelihoodRatio μ ν b) <
      likelihoodRatio μ ν (a ∩ b) := by
  have hFinA : likelihoodRatio μ ν a ≠ ∞ :=
    (ENNReal.div_lt_top (measure_ne_top μ a) hνa).ne
  have hFinB : likelihoodRatio μ ν b ≠ ∞ :=
    (ENNReal.div_lt_top (measure_ne_top μ b) hνb).ne
  rw [likelihoodRatio_inter h₁ h₂ hνb (measure_ne_top ν b), max_lt_iff]
  constructor
  · calc likelihoodRatio μ ν a = likelihoodRatio μ ν a * 1 := (mul_one _).symm
    _ < likelihoodRatio μ ν a * likelihoodRatio μ ν b :=
        ENNReal.mul_lt_mul_right (pos_of_gt ha).ne' hFinA hb
  · calc likelihoodRatio μ ν b = 1 * likelihoodRatio μ ν b := (one_mul _).symm
    _ < likelihoodRatio μ ν a * likelihoodRatio μ ν b :=
        ENNReal.mul_lt_mul_left (pos_of_gt hb).ne' hFinB ha

/-- Arithmetic core of the union bounds: with the four masses in position,
the inclusion-exclusion ratio sits strictly between one and the larger
single-event ratio. -/
private lemma max_div_gt_or_div (pAH pBH pAnH pBnH : ℝ)
    (h1 : 0 < pAnH) (h2 : 0 < pBnH)
    (h3 : pAnH < pAH) (h4 : pBnH < pBH)
    (h5 : pAnH < 1) (h6 : pBnH < 1)
    (_h7 : pAH ≤ 1) (h8 : pBH ≤ 1) :
    max (pAH / pAnH) (pBH / pBnH) >
      (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) ∧
    (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) > 1 := by
  have hden_pos : pAnH + pBnH - pAnH * pBnH > 0 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [gt_iff_lt, max_def]; split
    · rename_i hge
      rw [div_lt_div_iff₀ hden_pos h2]
      have h_cross := (div_le_div_iff₀ h1 h2).mp hge
      nlinarith [mul_pos (mul_pos h2 (show (0:ℝ) < pBH by linarith))
        (show pAH - pAnH > 0 from by linarith)]
    · rename_i hlt; push Not at hlt
      rw [div_lt_div_iff₀ hden_pos h1]
      have h_cross := (div_le_div_iff₀ h2 h1).mp (le_of_lt hlt)
      nlinarith [mul_pos (mul_pos h1 (show (0:ℝ) < pAH by linarith))
        (show pBH - pBnH > 0 from by linarith)]
  · rw [gt_iff_lt, one_lt_div hden_pos]
    nlinarith

/-- Union bounds under independence in both measures with both ratios above
one: the union's ratio is strictly below the larger single-event ratio and
strictly above one. -/
private theorem likelihoodRatio_union_bounds (hbm : MeasurableSet b)
    (h₁ : IndepSet a b μ) (h₂ : IndepSet a b ν)
    (ha : 1 < likelihoodRatio μ ν a) (hb : 1 < likelihoodRatio μ ν b)
    (hνa : ν a ≠ 0) (hνb : ν b ≠ 0) :
    likelihoodRatio μ ν (a ∪ b) < max (likelihoodRatio μ ν a) (likelihoodRatio μ ν b) ∧
    1 < likelihoodRatio μ ν (a ∪ b) := by
  -- Real shadows of the four masses.
  set pAH := (μ a).toReal with hpAH
  set pBH := (μ b).toReal with hpBH
  set pAnH := (ν a).toReal with hpAnH
  set pBnH := (ν b).toReal with hpBnH
  have hAnH_pos : 0 < pAnH := ENNReal.toReal_pos hνa (measure_ne_top ν a)
  have hBnH_pos : 0 < pBnH := ENNReal.toReal_pos hνb (measure_ne_top ν b)
  have hAH_gt : pAnH < pAH := by
    refine (ENNReal.toReal_lt_toReal (measure_ne_top ν a) (measure_ne_top μ a)).mpr ?_
    have h := (ENNReal.lt_div_iff_mul_lt (Or.inl hνa)
      (Or.inl (measure_ne_top ν a))).mp ha
    rwa [one_mul] at h
  have hBH_gt : pBnH < pBH := by
    refine (ENNReal.toReal_lt_toReal (measure_ne_top ν b) (measure_ne_top μ b)).mpr ?_
    have h := (ENNReal.lt_div_iff_mul_lt (Or.inl hνb)
      (Or.inl (measure_ne_top ν b))).mp hb
    rwa [one_mul] at h
  have hAH_le : pAH ≤ 1 := by
    rw [hpAH, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have hBH_le : pBH ≤ 1 := by
    rw [hpBH, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have harith := max_div_gt_or_div pAH pBH pAnH pBnH hAnH_pos hBnH_pos hAH_gt hBH_gt
    (lt_of_lt_of_le hAH_gt hAH_le) (lt_of_lt_of_le hBH_gt hBH_le) hAH_le hBH_le
  -- Inclusion-exclusion in ℝ, independence-substituted.
  have hOrM : (μ (a ∪ b)).toReal = pAH + pBH - pAH * pBH := by
    have h := congrArg ENNReal.toReal (measure_union_add_inter (μ := μ) a hbm)
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      h₁.measure_inter_eq_mul, ENNReal.toReal_mul] at h
    linarith
  have hOrN : (ν (a ∪ b)).toReal = pAnH + pBnH - pAnH * pBnH := by
    have h := congrArg ENNReal.toReal (measure_union_add_inter (μ := ν) a hbm)
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      h₂.measure_inter_eq_mul, ENNReal.toReal_mul] at h
    linarith
  have hOrN_ne : ν (a ∪ b) ≠ 0 := fun h0 =>
    hνa (measure_mono_null Set.subset_union_left h0)
  have hFinA : likelihoodRatio μ ν a ≠ ∞ :=
    (ENNReal.div_lt_top (measure_ne_top μ a) hνa).ne
  have hFinB : likelihoodRatio μ ν b ≠ ∞ :=
    (ENNReal.div_lt_top (measure_ne_top μ b) hνb).ne
  have hFinOr : likelihoodRatio μ ν (a ∪ b) ≠ ∞ :=
    (ENNReal.div_lt_top (measure_ne_top μ _) hOrN_ne).ne
  have hLROr : (likelihoodRatio μ ν (a ∪ b)).toReal =
      (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) := by
    rw [likelihoodRatio, ENNReal.toReal_div, hOrM, hOrN]
  constructor
  · refine (ENNReal.toReal_lt_toReal hFinOr (by simp [hFinA, hFinB])).mp ?_
    rw [hLROr, ENNReal.toReal_max hFinA hFinB, likelihoodRatio, likelihoodRatio,
      ENNReal.toReal_div, ENNReal.toReal_div]
    exact harith.1
  · refine (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hFinOr).mp ?_
    rw [hLROr, ENNReal.toReal_one]
    exact harith.2

/-- Under independence in both measures with both ratios above one, the
union's ratio is strictly below the larger single-event ratio. -/
theorem likelihoodRatio_union_lt_max (hbm : MeasurableSet b)
    (h₁ : IndepSet a b μ) (h₂ : IndepSet a b ν)
    (ha : 1 < likelihoodRatio μ ν a) (hb : 1 < likelihoodRatio μ ν b)
    (hνa : ν a ≠ 0) (hνb : ν b ≠ 0) :
    likelihoodRatio μ ν (a ∪ b) < max (likelihoodRatio μ ν a) (likelihoodRatio μ ν b) :=
  (likelihoodRatio_union_bounds hbm h₁ h₂ ha hb hνa hνb).1

/-- Under independence in both measures with both ratios above one, the
union's ratio still exceeds one. -/
theorem one_lt_likelihoodRatio_union (hbm : MeasurableSet b)
    (h₁ : IndepSet a b μ) (h₂ : IndepSet a b ν)
    (ha : 1 < likelihoodRatio μ ν a) (hb : 1 < likelihoodRatio μ ν b)
    (hνa : ν a ≠ 0) (hνb : ν b ≠ 0) :
    1 < likelihoodRatio μ ν (a ∪ b) :=
  (likelihoodRatio_union_bounds hbm h₁ h₂ ha hb hνa hνb).2

end OrderFacts

end ProbabilityTheory
