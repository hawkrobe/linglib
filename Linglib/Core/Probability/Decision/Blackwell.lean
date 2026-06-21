/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Decision.Risk.Basic

/-!
# Blackwell comparison of experiments
[blackwell-1953]

The Blackwell informativeness order on statistical experiments (data-generating
kernels), and its characterization via Bayes risk. An experiment `P : Kernel Θ 𝓧`
is **more informative** than `P' : Kernel Θ 𝓧'` when `P'` factors through `P` by a
Markov post-processing ("garbling") kernel — `IsGarblingOf P' P`.

[blackwell-1953]'s theorem ("Equivalent comparisons of experiments") states that
`P` is more informative than `P'` **iff** for every decision problem `P` attains a
Bayes risk no larger than `P'`. This file states that equivalence over mathlib's
`ProbabilityTheory.bayesRisk`.

## Status

* `IsGarblingOf` — the garbling relation.
* `bayesRisk_le_of_isGarblingOf` — the **easy direction** (data-processing): a
  garbling cannot decrease Bayes risk. Proved by specializing mathlib's
  `bayesRisk_le_bayesRisk_comp`.
* `isGarblingOf_of_forall_bayesRisk_le` — the **Blackwell–Sherman–Stein converse**:
  Bayes-risk dominance across *all* decision problems implies garbling. This is the
  deep direction (separating hyperplane / minimax over the convex set of garblings);
  currently `sorry`. It is the result mathlib's own `Probability/Decision/Risk/Basic`
  flags as awaiting a minimax theorem.
* `isGarblingOf_iff_forall_bayesRisk_le` — the [blackwell-1953] equivalence, combining
  the two directions.

## Upstreaming

This file is intended to be a `Mathlib/Probability/Decision/Blackwell.lean` candidate:
it is stated over mathlib `Kernel`/`bayesRisk` with no linglib dependencies, in the
`ProbabilityTheory` namespace. The linglib finite-`ℝ` `eig`/`questionUtility` view
(`Core/Probability/Decision/ExperimentDesign.lean`) is a downstream consumer, bridged
via `ObservationModel.toPMFKernel`.

## TODO

Prove `isGarblingOf_of_forall_bayesRisk_le`. Route: the garblings of `P` form a
convex set of kernels; if `P'` is not one of them, separate it by a continuous linear
functional (`geometric_hahn_banach_*`) realized as a decision problem (loss function),
yielding a `𝓨`/`ℓ` with `bayesRisk ℓ P' π < bayesRisk ℓ P π` — contradicting the
hypothesis. Needs compactness of the garbling set (`stdSimplex` / Markov-kernel
compactness) and a minimax/Sion step (`Mathlib/Topology/Sion.lean`).
-/

universe u

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Θ 𝓧 𝓧' : Type*} {mΘ : MeasurableSpace Θ}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'}

/-- `P'` is a **garbling** of `P` (Blackwell): there is a Markov post-processing
kernel `η` with `P' = η ∘ₖ P`. Read "`P` is at least as informative as `P'`". -/
def Kernel.IsGarblingOf (P' : Kernel Θ 𝓧') (P : Kernel Θ 𝓧) : Prop :=
  ∃ η : Kernel 𝓧 𝓧', IsMarkovKernel η ∧ P' = η ∘ₖ P

/-- **Easy direction (data-processing).** If `P'` is a garbling of `P`, then for every
decision problem the Bayes risk under `P` is no larger than under `P'`: garbling the
more-informative experiment cannot help. Specializes
`bayesRisk_le_bayesRisk_comp`. -/
theorem bayesRisk_le_of_isGarblingOf {𝓨 : Type u} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'}
    (h : P'.IsGarblingOf P) (π : Measure Θ) :
    bayesRisk ℓ P π ≤ bayesRisk ℓ P' π := by
  obtain ⟨η, hη, rfl⟩ := h
  haveI := hη
  exact bayesRisk_le_bayesRisk_comp ℓ P π η

/-- **Blackwell–Sherman–Stein converse.** If `P` attains a Bayes risk no larger than
`P'` for *every* decision problem (loss `ℓ` over an arbitrary measurable action space
`𝓨`, and prior `π`), then `P'` is a garbling of `P`.

The quantification over *all* `𝓨` is essential: dominance for a single decision
problem does not force garbling.

TODO: separating-hyperplane / minimax argument (see module docstring). -/
theorem isGarblingOf_of_forall_bayesRisk_le {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'}
    (h : ∀ {𝓨 : Type u} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ),
      bayesRisk ℓ P π ≤ bayesRisk ℓ P' π) :
    P'.IsGarblingOf P := by
  sorry

/-- **[blackwell-1953].** `P` is at least as informative as `P'` (`P'` is a garbling of
`P`) iff `P` attains a Bayes risk no larger than `P'` across every decision problem. -/
theorem isGarblingOf_iff_forall_bayesRisk_le {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} :
    P'.IsGarblingOf P ↔
      ∀ {𝓨 : Type u} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ),
        bayesRisk ℓ P π ≤ bayesRisk ℓ P' π := by
  constructor
  · intro h _ _ ℓ π
    exact bayesRisk_le_of_isGarblingOf ℓ h π
  · exact isGarblingOf_of_forall_bayesRisk_le

end ProbabilityTheory
