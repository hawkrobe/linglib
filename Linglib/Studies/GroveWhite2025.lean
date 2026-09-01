/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Probability.Distributions.Bernoulli
import Linglib.Semantics.Attitudes.Factivity

/-!
# Grove & White (2025): discrete factivity, gradient world knowledge

[grove-white-2025] ask whether the gradience of projection judgments for clause-embedding
predicates is *resolved* indeterminacy — factivity is a discrete property of token occurrences,
the Fundamental Discreteness Hypothesis (7a) — or *unresolved* indeterminacy — nothing discrete
separates factive from non-factive occurrences, the Fundamental Gradience Hypothesis (7b). The
lexical entry (13) makes `know` ambiguous between a factive reading `m` (`BEL ∧ C`) and a
non-factive reading `n` (`BEL`), selected by a state-level truth value `τ_know(s)`; the response
models of §4 turn the prior over readings and the complement's prior probability into a
distribution over answers to *how likely is it that φ?* on the slider scale `[0, 1]`.

The four models fitted to [degen-tonhauser-2021]'s projection data are the completions of the
two norming models (§4.2) by the two treatments of factivity (§4.3):

|                      | world knowledge gradient | world knowledge discrete |
|----------------------|--------------------------|--------------------------|
| factivity resolved   | `discreteFactivity`      | `whollyDiscrete`         |
| factivity unresolved | `whollyGradient`         | `discreteWorld`          |

Response noise (the truncated-normal likelihood `f(·, Φ)` of §4.1) is not modelled: each model
here is the distribution of the intended answer.

## Main definitions

* `FactivityReading`, `clauseEmbeddingSem`: the readings `m`, `n` of (13), as
  `Factivity.factivePos` and `Factivity.nonFactivePos`.
* `normingGradient p`, `normingDiscrete p`: the answer when the complement has probability `p`
  under the common ground — the degree `p` itself, or a Bernoulli(`p`) draw of the complement's
  truth at an index, sent to the endpoints of the scale.
* `resolvedFactivity τ ν`: draw a reading with `P(m) = τ`; answer `1` under `m`, `ν` under `n`.
* `unresolvedFactivity τ ν`: disjoin a token-level factivity probability `τ` with the answer `ν`.
* `discreteFactivity`, `whollyDiscrete`, `whollyGradient`, `discreteWorld`: the four models.

## Main results

* `discreteFactivity_eq`, `whollyDiscrete_eq`, `whollyGradient_eq`, `discreteWorld_eq`: each
  model in closed form.
* `resolvedFactivity_zero`, `unresolvedFactivity_zero`: at `τ = 0` each model is the norming
  model it completes; `resolvedFactivity_one`, `unresolvedFactivity_one`: at `τ = 1` every model
  answers `1`.
* `integral_discreteFactivity`, …: the four models share the mean answer `τ + (1 - τ) * p`.
* `variance_discreteFactivity`, …: they differ in spread — `whollyGradient` is deterministic, the
  models with a discrete component send mass to the endpoints. This is the shape difference behind
  the model comparison of §4.4, where `discreteFactivity` fits best and the two gradient-factivity
  models worst.

## References

* [J. Grove, A. S. White, *Factivity, presupposition projection, and the role of discrete
  knowledge in gradient inference judgments*][grove-white-2025]
* [J. Degen, J. Tonhauser, *Prior beliefs modulate projection*][degen-tonhauser-2021]
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
instance : DiscreteMeasurableSpace FactivityReading := ⟨fun _ => trivial⟩

variable {W : Type*} [HasBelief W] [HasComplement W]

/-- The parent nodes of (13): reading `m` is `factivePos` (`BEL ∧ C`), reading `n` is
`nonFactivePos` (`BEL`) — the `know` and `think` denotations of `Factivity`. -/
def clauseEmbeddingSem : FactivityReading → W → Bool
  | .factive => factivePos
  | .nonfactive => nonFactivePos

/-! ### Norming models (§4.2) -/

/-- World knowledge as unresolved indeterminacy: the complement's probability `p` under the common
ground, reported as a degree. -/
noncomputable abbrev normingGradient (p : I) : Measure I := dirac p

/-- World knowledge as resolved indeterminacy: a Bernoulli(`p`) draw of the complement's truth at
an index of the common ground, sent to the endpoints of the scale. -/
noncomputable abbrev normingDiscrete (p : I) : Measure I := Ber(1, 0, p)

/-! ### Completing a norming model by factivity (§4.3) -/

/-- Resolved factivity: a reading of (13) is drawn with `P(m) = τ`; under `m` the complement is
entailed (`Factivity.factivePos_entails_c`) and the answer is `1`, under `n` the answer follows
`ν`. -/
noncomputable def resolvedFactivity (τ : I) (ν : Measure I) : Measure I :=
  Ber(FactivityReading.factive, FactivityReading.nonfactive, τ).bind fun
    | .factive => dirac 1
    | .nonfactive => ν

/-- Unresolved factivity: `τ` is the common-ground probability of `τ_know(c_i)` in (14), taken
independent of the complement, so an answer `d` becomes the probability `1 - (1 - τ) (1 - d)` of
the disjunction. -/
noncomputable def unresolvedFactivity (τ : I) (ν : Measure I) : Measure I :=
  ν.map fun d => σ (σ τ * σ d)

/-- Discrete factivity, gradient world knowledge (§4.3.1). -/
noncomputable abbrev discreteFactivity (τ p : I) : Measure I :=
  resolvedFactivity τ (normingGradient p)

/-- Discrete factivity, discrete world knowledge (§4.3.1). -/
noncomputable abbrev whollyDiscrete (τ p : I) : Measure I :=
  resolvedFactivity τ (normingDiscrete p)

/-- Gradient factivity, gradient world knowledge (§4.3.2). -/
noncomputable abbrev whollyGradient (τ p : I) : Measure I :=
  unresolvedFactivity τ (normingGradient p)

/-- Gradient factivity, discrete world knowledge (§4.3.2). -/
noncomputable abbrev discreteWorld (τ p : I) : Measure I :=
  unresolvedFactivity τ (normingDiscrete p)

section Completion

variable (τ : I) (ν : Measure I)

private theorem measurable_disj : Measurable fun d : I => σ (σ τ * σ d) :=
  Measurable.subtype_mk (by fun_prop : Measurable fun d : I => 1 - (1 - (τ : ℝ)) * (1 - d))

theorem resolvedFactivity_eq : resolvedFactivity τ ν = toNNReal τ • dirac 1 + toNNReal (σ τ) • ν :=
  bernoulliMeasure_bind _ _ _ .of_discrete

instance [IsProbabilityMeasure ν] : IsProbabilityMeasure (resolvedFactivity τ ν) :=
  ⟨by simp [resolvedFactivity_eq]⟩

instance [IsProbabilityMeasure ν] : IsProbabilityMeasure (unresolvedFactivity τ ν) :=
  isProbabilityMeasure_map (measurable_disj τ).aemeasurable

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

/-! ### Mean answer -/

theorem integral_discreteFactivity : ∫ d, (d : ℝ) ∂discreteFactivity τ p = τ + (1 - τ) * p := by
  simp [discreteFactivity_eq, integral_bernoulliMeasure]

theorem integral_whollyDiscrete : ∫ d, (d : ℝ) ∂whollyDiscrete τ p = τ + (1 - τ) * p := by
  simp [whollyDiscrete_eq, integral_bernoulliMeasure, coe_symm_eq]; ring

theorem integral_whollyGradient : ∫ d, (d : ℝ) ∂whollyGradient τ p = τ + (1 - τ) * p := by
  simp [whollyGradient_eq, coe_symm_eq]; ring

theorem integral_discreteWorld : ∫ d, (d : ℝ) ∂discreteWorld τ p = τ + (1 - τ) * p := by
  simp [discreteWorld_eq, integral_bernoulliMeasure]; ring

/-! ### Spread of the answer -/

theorem variance_discreteFactivity :
    Var[fun d : I => (d : ℝ); discreteFactivity τ p] = τ * (1 - τ) * (1 - p) ^ 2 := by
  simp [discreteFactivity_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable]

theorem variance_whollyDiscrete :
    Var[fun d : I => (d : ℝ); whollyDiscrete τ p] = (τ + (1 - τ) * p) * (1 - τ) * (1 - p) := by
  simp [whollyDiscrete_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable,
    coe_symm_eq]
  ring

theorem variance_whollyGradient : Var[fun d : I => (d : ℝ); whollyGradient τ p] = 0 := by
  simp [whollyGradient_eq]

theorem variance_discreteWorld :
    Var[fun d : I => (d : ℝ); discreteWorld τ p] = p * (1 - p) * (1 - τ) ^ 2 := by
  simp [discreteWorld_eq, variance_bernoulliMeasure _ _ _ measurable_subtype_coe.aemeasurable]

end Models

end GroveWhite2025
