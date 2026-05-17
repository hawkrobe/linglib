import Linglib.Theories.Semantics.Modality.ThresholdOperator

/-!
# Posterior-threshold modality

A simplified posterior-based necessity operator: `must φ` iff
`P(φ) > θ` for some contextual threshold. This is the *baseline
posterior competitor* against which more sophisticated probabilistic
operators (`@cite{lassiter-2017}`, `@cite{chung-mascarenhas-2024}`,
`@cite{goodhue-2017}`, the threshold-PMF tradition) define themselves.

It is **not** a faithful Lassiter operator — Lassiter's account adds
context-conditionalization, an alternatives clause, and an epistemic /
deontic asymmetry. Use `mustPosterior` only where the goal is to expose
posterior-monotonicity as a structural constraint that necessity
accounts may or may not satisfy.

## Headline structural fact

`posterior_cannot_predict_conjunction_fallacy`: a one-line corollary
of the substrate theorem
`Semantics.Modality.ThresholdOperator.subsetFallacy_blocked_by_monotone`
applied to `posteriorEval_isPosteriorMonotone`. The modal-conjunction-
fallacy direction (sub-claim true at θ, super-claim false at θ) is
impossible under any posterior-monotone eval — and `posteriorEval` is
trivially posterior-monotone via `PMF.probOfSet_mono`.
-/

namespace Semantics.Modality.PosteriorThreshold

open PMF Semantics.Modality.ThresholdOperator
open scoped ENNReal

variable {W : Type*} [Fintype W]

/-- The posterior eval function as an `EvalFn`: just `probOfSet` packaged
in the shared shape. -/
noncomputable def posteriorEval : EvalFn W := fun p φ => p.probOfSet φ

/-- Posterior is monotone — immediate from `PMF.probOfSet_mono`. -/
theorem posteriorEval_isPosteriorMonotone :
    IsPosteriorMonotone (@posteriorEval W _) :=
  fun p _ _ hSub => probOfSet_mono p hSub

/-- Posterior-threshold necessity: `must φ` iff `P(φ) > θ`. The simplest
probability-based necessity operator. -/
def mustPosterior (p : PMF W) (φ : Set W) (θ : ℝ≥0∞) : Prop :=
  posteriorEval p φ > θ

/-- **Structural impossibility of the modal conjunction fallacy under
posterior-threshold necessity.** One-line corollary of
`subsetFallacy_blocked_by_monotone` applied to
`posteriorEval_isPosteriorMonotone`. -/
theorem posterior_cannot_predict_conjunction_fallacy
    (p : PMF W) {sub super : Set W} (hSub : sub ⊆ super) (θ : ℝ≥0∞) :
    ¬ (mustPosterior p sub θ ∧ ¬ mustPosterior p super θ) :=
  subsetFallacy_blocked_by_monotone posteriorEval_isPosteriorMonotone p hSub θ

end Semantics.Modality.PosteriorThreshold
