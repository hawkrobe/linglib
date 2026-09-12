import Linglib.Studies.ZurawHayes2017

/-!
# Magri (2025): Constraint Interaction in Probabilistic Phonology

This file formalizes the characterization of [magri-2025]: within harmony-based probabilistic
phonology, a harmony function predicts the shifted-sigmoids generalization of
[zuraw-hayes-2017] and [hayes-2022], that the rates of a process governed by independent
factors fit sigmoids sharing their abscissas, equivalently that differences of logit rates
across one factor are constant across the other (§2.2), exactly when it is separable, a
product of per-constraint factors raised to the constraint weights. Maximum entropy harmony
is separable, so it predicts the generalization (§3), and any separable harmony is maximum
entropy under a rescaling of its constraints (§5). The file runs the theory on the paper's
Tagalog nasal substitution case (§2.1): the six constraints of the two-by-two square of
prefixes and stem-initial obstruents are independent, the markedness constraints insensitive
to the prefix and the faithfulness constraints to the stem (§2.3, §2.4,
`constraint_independence`), the violation differences inherit that independence
(`violDiff_consistent`), the per-cell logit rates come out in closed form
(`logitRate_row_diff`), and the separable forward direction holds at the level of
probabilities for every weighting (`me_separable_predicts_hz_tagalog`).

## Implementation notes

The two-by-two sub-square, the constraint inventory, the rates, and the constant-difference
identity are those of `Studies/ZurawHayes2017.lean`, from which the paper inherits its setup;
the converse direction, that a harmony predicting the generalization is separable, is not
formalized.

## References

* [magri-2025]
* [zuraw-hayes-2017]
* [hayes-2022]
-/

namespace Magri2025

open Core.Optimization Constraints Constraints OptimalityTheory HarmonicGrammar
open ZurawHayes2017

/-! ### Constraint independence (§2.3, §2.4) -/

set_option linter.unusedSimpArgs false in
/-- **Constraint independence**: for each fixed output, the six
    constraints satisfy `ConstraintIndependence` on the nasal substitution
    square.

    C₁–C₄ (markedness) are insensitive to row (prefix);
    C₅–C₆ (faithfulness) are insensitive to column (stem obstruent). -/
theorem constraint_independence (o : NasalSubOutput) :
    ConstraintIndependence (λ k x => (constraints k) (x, o)) nasalSubSquare := by
  intro k; fin_cases k <;> cases o <;>
    simp only [constraints, nasSub, starNC, starStemVelar,
      starStemVelarCoronal, unifMang, unifPang,
      Constraint.comap_apply, Constraint.binary,
      Zuraw2010.nasSub, Zuraw2010.starNC, Zuraw2010.starInitVelar,
      Zuraw2010.starInitCorVel, NasalSubCandidate.project,
      NasalSubInput.toStemC, NasalSubOutput.toSubSt,
      nasalSubSquare, InsensitiveToRow, InsensitiveToCol] <;>
    decide

/-! ### Violation differences -/

/-- The violation differences are consistent with the raw constraint
    profiles: `Δₖ(x) = Cₖ(x, NO) − Cₖ(x, YES)`. -/
theorem violDiff_consistent (k : Fin 6) (x : NasalSubInput) :
    violDiffProfile k x =
    ((constraints k) (x, .no) : ℤ) - ((constraints k) (x, .yes) : ℤ) := by
  fin_cases k <;> cases x <;> decide

/-! ### Logit rates (§2.2, §3)

The constant-difference identity is `ZurawHayes2017.maxent_predicts_hz_tagalog`, with closed
form `ZurawHayes2017.hz_constant_value_tagalog`; the per-cell symbolic logit rates
`LR(x) = Σₖ wₖ · Δₖ(x)` are verified here. -/

/-- `LR(maŋb) = w₁ − w₅` -/
theorem logitRate_mang_b (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) =
    w 0 - w 4 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- `LR(/maŋk/) = w₁ + w₂ − w₃ − w₄ − w₅` -/
theorem logitRate_mang_k (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    w 0 + w 1 - w 2 - w 3 - w 4 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- `LR(/paŋb/) = w₁ − w₆` -/
theorem logitRate_pang_b (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) =
    w 0 - w 5 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- `LR(/paŋk/) = w₁ + w₂ − w₃ − w₄ − w₆` -/
theorem logitRate_pang_k (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) =
    w 0 + w 1 - w 2 - w 3 - w 5 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- Per-cell rates recover `ZurawHayes2017.hz_constant_value_tagalog`'s
    constant difference `−w₂ + w₃ + w₄`; `w 2` and `w 3` are not separately
    identifiable from the b-vs-k square — only their sum matters, since
    `*[stemŋ]` and `*[stemŋ]/n` coincide on the b/k restriction. -/
theorem logitRate_row_diff (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    -w 1 + w 2 + w 3 := by
  rw [logitRate_mang_b, logitRate_mang_k]; ring

/-! ### The separable forward direction (§3, §5) -/

set_option linter.unusedSimpArgs false in
/-- **ME predicts HZ at the probability level**: the log-probability-ratio
    `log(P(YES|x)/P(NO|x))` under ME satisfies HZ's constant-difference
    identity for Tagalog nasal substitution, for *any* weight assignment.

    This instantiates `separable_predicts_hz` with `meSeparable` and the
    Tagalog constraints. Since ME rescaling is the identity
    (`meSeparable_rescale`), the rescaled violation differences reduce to
    the raw violation differences, and `violDiff_independence` provides
    the independence hypothesis. -/
theorem me_separable_predicts_hz_tagalog (w : Fin 6 → ℝ) :
    ConstantLogitDiff
      (λ x => Real.log (
        (meSeparable 6 w).eval (λ k => (constraints k) (x, .yes)) /
        (meSeparable 6 w).eval (λ k => (constraints k) (x, .no))))
      nasalSubSquare := by
  apply separable_predicts_hz
  intro k
  simp only [SeparableHarmony.rescale, meSeparable, Real.log_exp, nasalSubSquare]
  fin_cases k <;>
    simp only [constraints, nasSub, starNC, starStemVelar, starStemVelarCoronal,
      unifMang, unifPang, Constraint.comap_apply, Function.comp_apply,
      Constraint.binary, Zuraw2010.nasSub, Zuraw2010.starNC,
      Zuraw2010.starInitVelar, Zuraw2010.starInitCorVel, NasalSubCandidate.project,
      NasalSubInput.toStemC, NasalSubOutput.toSubSt] <;>
    simp

end Magri2025
