/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.InformationTheory.Surprisal
import Linglib.Processing.Expectation.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Kernel.Defs

/-!
# Generalised surprisal

This file defines the generalised surprisal of [giulianelli-opedal-cotterell-2024] and
[giulianelli-etal-2026]. The processing cost of a unit `w` in a context `c` is a warping of the
expected score of `w` against alternatives sampled from a language model, a Markov kernel from
contexts to alternatives. Standard surprisal is the member with the negative logarithm and the
indicator score [levy-2008], and information value the member with the identity warping and a
distance score. The configuration tags of `Processing.Expectation.Defs` denote members of the
family.

## Main definitions

* `genSurprisal`, `informationValue1`, `indicatorScore`.
* `WarpingFn.denote`, `ScoringFn.denote`, `SurprisalConfig.applyTo`.

## Main results

* `standardSurprisal_denotes_surprisal`: the standard configuration denotes surprisal.
* `informationValue_applyTo_eq_informationValue1`: the information-value configurations denote
  information value.

## References

* [giulianelli-opedal-cotterell-2024]
* [giulianelli-etal-2026]
* [levy-2008]
-/

namespace Processing.PredictiveUncertainty

open InformationTheory MeasureTheory ProbabilityTheory

variable {C A W : Type*} [MeasurableSpace C] [MeasurableSpace A]

/-- Generalised surprisal: a warping of the expected score of the unit `w` against alternatives
sampled from the model `L` in the context `c`. -/
noncomputable def genSurprisal (L : Kernel C A) (warp : ℝ → ℝ) (score : A → W → C → ℝ) (c : C)
    (w : W) : ℝ :=
  warp (∫ a, score a w c ∂(L c))

/-- Information value: the expected distance from the alternatives to the unit. -/
noncomputable def informationValue1 (L : Kernel C A) (d : A → W → ℝ) (c : C) (w : W) : ℝ :=
  ∫ a, d a w ∂(L c)

theorem informationValue1_eq_genSurprisal (L : Kernel C A) (d : A → W → ℝ) (c : C) (w : W) :
    informationValue1 L d c w = genSurprisal L id (λ a w _ => d a w) c w := rfl

/-- The indicator score: one when the alternative is the unit. -/
noncomputable def indicatorScore (a w : W) (_ : C) : ℝ := ({w} : Set W).indicator 1 a

/-- The real function a warping tag denotes. -/
noncomputable def WarpingFn.denote : WarpingFn → ℝ → ℝ
  | .negLog => λ x => -Real.log x
  | .identity => id

/-- The scoring function a scoring tag denotes, given the distance and the similarity the
framework abstracts over. -/
noncomputable def ScoringFn.denote (dist sim : W → W → C → ℝ) : ScoringFn → W → W → C → ℝ
  | .indicator => indicatorScore
  | .distance => dist
  | .similarity => sim

/-- A configuration applied to a model. The horizon and the level are labels here: the horizon
enters through the model, which samples alternatives of that length. -/
noncomputable def SurprisalConfig.applyTo [MeasurableSpace W] (cfg : SurprisalConfig)
    (L : Kernel C W) (dist sim : W → W → C → ℝ) (c : C) (w : W) : ℝ :=
  genSurprisal L cfg.warp.denote (cfg.scoring.denote dist sim) c w

variable [MeasurableSpace W] (L : Kernel C W) (c : C) (w : W)

/-- The information-value configurations denote information value, with the distance read in
the context. -/
theorem informationValue_applyTo_eq_informationValue1 (dist sim : W → W → C → ℝ)
    (h : ForecastHorizon) (l : RepLevel) :
    (informationValue h l).applyTo L dist sim c w
      = informationValue1 L (λ a w' => dist a w' c) c w := rfl

variable [MeasurableSingletonClass W]

/-- The standard configuration denotes surprisal. -/
theorem standardSurprisal_denotes_surprisal :
    genSurprisal L standardSurprisal.warp.denote indicatorScore c w = surprisal (L c) w := by
  show -Real.log (∫ a, ({w} : Set W).indicator 1 a ∂(L c)) = _
  rw [integral_indicator_one (measurableSet_singleton w)]
  rfl

theorem standardSurprisal_applyTo_eq_surprisal (dist sim : W → W → C → ℝ) :
    standardSurprisal.applyTo L dist sim c w = surprisal (L c) w :=
  standardSurprisal_denotes_surprisal L c w

end Processing.PredictiveUncertainty
