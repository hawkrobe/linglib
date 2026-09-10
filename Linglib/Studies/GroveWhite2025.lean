/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Probability.Distributions.Bernoulli
import Linglib.Semantics.Attitudes.Factivity
import Linglib.Data.Examples.GroveWhite2025

/-!
# Grove and White (2025): Factivity, Presupposition Projection, and Discrete Knowledge

This file formalizes the response models of [grove-white-2025], "Factivity, presupposition
projection, and the role of discrete knowledge in gradient inference judgments", which ask
whether the gradience of projection judgments for clause-embedding predicates is resolved
indeterminacy, factivity being a discrete property of token occurrences, the Fundamental
Discreteness Hypothesis of (7a), or unresolved indeterminacy, nothing discrete separating
factive from non-factive occurrences, the Fundamental Gradience Hypothesis of (7b). The lexical
entry (13) makes *know* ambiguous between a factive reading `m` and a non-factive reading `n`,
selected by a state-level truth value, while (14) makes the factive conjunct depend on the
index instead; section 4 turns each, together with a gradient or a discrete treatment of the
complement's prior probability, into a distribution over answers to *how likely is it that φ?*
on the slider scale. The four models fitted to [degen-tonhauser-2021]'s projection data are the
completions of the two norming models of section 4.2 by the two treatments of factivity of
section 4.3: `discreteFactivity` and `whollyDiscrete` resolve factivity, `whollyGradient` and
`discreteWorld` leave it unresolved. Each is given in closed form; all four share the mean
answer, and they differ in spread, the models with a discrete component sending mass to the
endpoints of the scale, which is the shape difference behind the comparison of section 4.4,
where the discrete-factivity model fits best and the two gradient-factivity models worst.

## Implementation notes

Readings are `Factivity.factivePos` and `Factivity.nonFactivePos`, the *know* and *think*
denotations of the library's factivity substrate. Answers are measures on the unit interval;
resolved factivity is a Bernoulli draw of a reading bound through the answer, unresolved
factivity the image of the answer under the probability of the disjunction in (14), with the
token-level factivity probability taken independent of the complement. The response noise of
section 4.1, the truncated-normal likelihood, is not modelled: each model is the distribution
of the intended answer. The paper's illustrative sentences are rows of
`Data.Examples.GroveWhite2025`.

## References

* [grove-white-2025]
* [degen-tonhauser-2021]
-/

open MeasureTheory Measure ProbabilityTheory Factivity unitInterval

namespace GroveWhite2025

/-! ### The lexical entry (13) -/

/-- The two readings of a clause-embedding predicate in (13): `m` triggers the projective
inference, `n` does not. -/
inductive FactivityReading where
  | factive
  | nonfactive
  deriving DecidableEq

instance : MeasurableSpace FactivityReading := ⊤
instance : DiscreteMeasurableSpace FactivityReading := ⟨λ _ => trivial⟩

variable {W : Type*} [HasBelief W] [HasComplement W]

/-- The parent nodes of (13): reading `m` is `factivePos`, belief with the complement, and
reading `n` is `nonFactivePos`, belief alone. -/
def clauseEmbeddingSem : FactivityReading → W → Bool
  | .factive => factivePos
  | .nonfactive => nonFactivePos

/-! ### Norming models, section 4.2 -/

/-- World knowledge as unresolved indeterminacy: the complement's probability `p` under the
common ground, reported as a degree. -/
noncomputable abbrev normingGradient (p : I) : Measure I := dirac p

/-- World knowledge as resolved indeterminacy: a Bernoulli(`p`) draw of the complement's truth
at an index of the common ground, sent to the endpoints of the scale. -/
noncomputable abbrev normingDiscrete (p : I) : Measure I := Ber(1, 0, p)

/-! ### Completing a norming model by factivity, section 4.3 -/

/-- Resolved factivity: a reading of (13) is drawn with `P(m) = τ`; under `m` the complement is
entailed (`Factivity.factivePos_entails_c`) and the answer is `1`, under `n` the answer follows
`ν`. -/
noncomputable def resolvedFactivity (τ : I) (ν : Measure I) : Measure I :=
  Ber(FactivityReading.factive, FactivityReading.nonfactive, τ).bind λ
    | .factive => dirac 1
    | .nonfactive => ν

/-- Unresolved factivity: `τ` is the common-ground probability of the factivity value at the
index in (14), taken independent of the complement, so an answer `d` becomes the probability
`1 - (1 - τ) (1 - d)` of the disjunction. -/
noncomputable def unresolvedFactivity (τ : I) (ν : Measure I) : Measure I :=
  ν.map λ d => σ (σ τ * σ d)

/-- Discrete factivity, gradient world knowledge, section 4.3.1. -/
noncomputable abbrev discreteFactivity (τ p : I) : Measure I :=
  resolvedFactivity τ (normingGradient p)

/-- Discrete factivity, discrete world knowledge, section 4.3.1. -/
noncomputable abbrev whollyDiscrete (τ p : I) : Measure I :=
  resolvedFactivity τ (normingDiscrete p)

/-- Gradient factivity, gradient world knowledge, section 4.3.2. -/
noncomputable abbrev whollyGradient (τ p : I) : Measure I :=
  unresolvedFactivity τ (normingGradient p)

/-- Gradient factivity, discrete world knowledge, section 4.3.2. -/
noncomputable abbrev discreteWorld (τ p : I) : Measure I :=
  unresolvedFactivity τ (normingDiscrete p)

section Completion

variable (τ : I) (ν : Measure I)

private theorem measurable_disj : Measurable λ d : I => σ (σ τ * σ d) :=
  Measurable.subtype_mk (by fun_prop : Measurable λ d : I => 1 - (1 - (τ : ℝ)) * (1 - d))

/-- Resolved factivity is a mixture: mass `τ` at the endpoint `1`, the rest the completed
norming model. -/
theorem resolvedFactivity_eq : resolvedFactivity τ ν = toNNReal τ • dirac 1 + toNNReal (σ τ) • ν :=
  bernoulliMeasure_bind _ _ _ .of_discrete

instance [IsProbabilityMeasure ν] : IsProbabilityMeasure (resolvedFactivity τ ν) :=
  ⟨by simp [resolvedFactivity_eq]⟩

instance [IsProbabilityMeasure ν] : IsProbabilityMeasure (unresolvedFactivity τ ν) :=
  isProbabilityMeasure_map (measurable_disj τ).aemeasurable

/-- At `τ = 0` each completion is the norming model it completes; at `τ = 1` every model
answers `1`. -/
@[simp] theorem resolvedFactivity_zero : resolvedFactivity 0 ν = ν := by
  simp [resolvedFactivity_eq]

@[simp] theorem resolvedFactivity_one : resolvedFactivity 1 ν = dirac 1 := by
  simp [resolvedFactivity_eq]

@[simp] theorem unresolvedFactivity_zero : unresolvedFactivity 0 ν = ν := by
  simp [unresolvedFactivity]

@[simp] theorem unresolvedFactivity_one [IsProbabilityMeasure ν] :
    unresolvedFactivity 1 ν = dirac 1 := by
  simp [unresolvedFactivity, Measure.map_const]

end Completion

/-! ### The four models in closed form -/

section Models

variable (τ p : I)

theorem discreteFactivity_eq : discreteFactivity τ p = Ber(1, p, τ) := by
  rw [discreteFactivity, resolvedFactivity_eq, normingGradient, bernoulliMeasure_def]

theorem whollyDiscrete_eq : whollyDiscrete τ p = Ber(1, 0, σ (σ τ * σ p)) := by
  have h₁ : toNNReal τ + toNNReal (σ τ) * toNNReal p = toNNReal (σ (σ τ * σ p)) :=
    NNReal.eq (by simp [coe_symm_eq]; ring)
  have h₂ : toNNReal (σ τ) * toNNReal (σ p) = toNNReal (σ τ * σ p) := NNReal.eq (by simp)
  rw [whollyDiscrete, resolvedFactivity_eq, normingDiscrete, bernoulliMeasure_def,
    bernoulliMeasure_def, symm_symm, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, h₁,
    h₂]

theorem whollyGradient_eq : whollyGradient τ p = dirac (σ (σ τ * σ p)) :=
  Measure.map_dirac' (measurable_disj τ) p

theorem discreteWorld_eq : discreteWorld τ p = Ber(1, τ, p) := by
  simp [unresolvedFactivity]

/-! ### Mean answer

The four models share the mean `τ + (1 - τ) * p`. -/

theorem integral_discreteFactivity : ∫ d, (d : ℝ) ∂discreteFactivity τ p = τ + (1 - τ) * p := by
  simp [discreteFactivity_eq, integral_bernoulliMeasure]

theorem integral_whollyDiscrete : ∫ d, (d : ℝ) ∂whollyDiscrete τ p = τ + (1 - τ) * p := by
  simp [whollyDiscrete_eq, integral_bernoulliMeasure, coe_symm_eq]; ring

theorem integral_whollyGradient : ∫ d, (d : ℝ) ∂whollyGradient τ p = τ + (1 - τ) * p := by
  simp [whollyGradient_eq, coe_symm_eq]; ring

theorem integral_discreteWorld : ∫ d, (d : ℝ) ∂discreteWorld τ p = τ + (1 - τ) * p := by
  simp [discreteWorld_eq, integral_bernoulliMeasure]; ring

/-! ### Spread of the answer

The wholly gradient model is a single degenerate distribution; the models with a discrete
component are mixtures that put mass at the endpoints, which is what captures the dips in the
middle of the scale in section 4.4. -/

theorem variance_discreteFactivity :
    Var[λ d : I => (d : ℝ); discreteFactivity τ p] = τ * (1 - τ) * (1 - p) ^ 2 := by
  simp [discreteFactivity_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable]

theorem variance_whollyDiscrete :
    Var[λ d : I => (d : ℝ); whollyDiscrete τ p] = (τ + (1 - τ) * p) * (1 - τ) * (1 - p) := by
  simp [whollyDiscrete_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable,
    coe_symm_eq]
  ring

theorem variance_whollyGradient : Var[λ d : I => (d : ℝ); whollyGradient τ p] = 0 := by
  simp [whollyGradient_eq]

theorem variance_discreteWorld :
    Var[λ d : I => (d : ℝ); discreteWorld τ p] = p * (1 - p) * (1 - τ) ^ 2 := by
  simp [discreteWorld_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable]

end Models

end GroveWhite2025
