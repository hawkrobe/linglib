import Linglib.Core.Probability.Choice.RationalAction
import Linglib.Core.Probability.Decision.ExperimentDesign

/-!
# Hawkins et al. (2025): Relevant answers to polar questions

This file formalizes the questioner of [hawkins-etal-2025]'s PRIOR-PQ model as an experiment
designer: a polar question is an experiment whose observation is the respondent's answer, and
the questioner chooses among questions by a softmax over the expected decision value of the
answer, [lindley-1956]'s expected information gain `ObservationModel.eig` under the decision
value `decisionValue` of the questioner's decision problem.

## TODO

The respondent and the paper's experiments are not formalized here.

## References

* [hawkins-etal-2025]
* [lindley-1956]
-/

namespace HawkinsEtAl2025

open Core ProbabilityTheory

variable {W E O : Type*} [Fintype W] [Fintype O]

/-- The questioner as experiment designer: a softmax over experiments whose score is the
expected information gain, with rationality `α`. -/
noncomputable def optimalExperiment [Fintype E] (om : ObservationModel W E O) (prior : W → ℝ)
    (V : (W → ℝ) → ℝ) (α : ℝ) : RationalAction Unit E where
  score _ e := Real.exp (α * om.eig prior V e)
  score_nonneg _ _ := (Real.exp_pos _).le

end HawkinsEtAl2025
