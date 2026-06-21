/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Decision.Risk.Basic

/-!
# Blackwell comparison of experiments

A statistical experiment is a Markov kernel `P : Kernel Θ 𝓧` generating data in `𝓧` from a
parameter in `Θ`. Experiment `P` is **at least as informative** as `P' : Kernel Θ 𝓧'` when `P'`
can be recovered from `P` by Markov post-processing ("garbling"): `P' = η ∘ₖ P` for some Markov
kernel `η`. This file develops that order and its characterization through Bayes risk.

[blackwell-1953]'s comparison theorem states that `P` is at least as informative as `P'` if and
only if, for every decision problem, the Bayes risk under `P` is no greater than under `P'`. We
state this equivalence over `ProbabilityTheory.bayesRisk`. The forward (data-processing)
direction is proved; the converse is the deep direction and is currently a `sorry` (see TODO).

## Main definitions

* `Kernel.IsGarblingOf`: `P'.IsGarblingOf P` means `P'` is a Markov garbling of `P`, i.e. `P` is
  at least as informative as `P'`.

## Main statements

* `bayesRisk_le_of_isGarblingOf`: if `P'` is a garbling of `P`, then `P` has Bayes risk no
  greater than `P'` for every decision problem (the data-processing direction).
* `isGarblingOf_of_forall_bayesRisk_le`: conversely, if `P` has Bayes risk no greater than `P'`
  for *every* decision problem, then `P'` is a garbling of `P` (the Blackwell–Sherman–Stein
  direction, finite case; currently `sorry`). False without finiteness/standard-Borel
  hypotheses.
* `isGarblingOf_iff_forall_bayesRisk_le`: the two directions combined.

## Implementation notes

The development is stated entirely over Mathlib's `Kernel` and `bayesRisk` with no further
dependencies, so it can serve as a `Mathlib.Probability.Decision.Blackwell` candidate. The
finite, `ℝ`-valued `eig` / `questionUtility` view in `Core.Probability.Decision.ExperimentDesign`
is a downstream consumer, bridged via `ObservationModel.toPMFKernel`.

The hypothesis of `isGarblingOf_of_forall_bayesRisk_le` quantifies over *all* decision problems
(every measurable action space `𝓨` and loss `ℓ : Θ → 𝓨 → ℝ≥0∞`): dominance for a single
decision problem does not force garbling.

## References

* [blackwell-1953]

## TODO

Prove `isGarblingOf_of_forall_bayesRisk_le`. Over finite spaces a kernel is a stochastic matrix
and the garblings of `P`, `{η ∘ₖ P | η Markov}`, form a compact convex polytope; if `P'` lies
outside it, a geometric Hahn–Banach separation (`geometric_hahn_banach_point_closed`) gives a
linear functional realized as a decision problem witnessing `bayesRisk ℓ P' π < bayesRisk ℓ P π`,
contradicting the hypothesis. Mathlib supplies the *analytic* pieces — `isCompact_stdSimplex`,
the `geometric_hahn_banach_*` separation lemmas, Sion's minimax theorem
(`Mathlib/Topology/Sion.lean`) — but **not** the *kernel-side* setup: there is no topology or
convexity structure on `Kernel`, so a proof must first bridge finite kernels to stochastic
matrices (`bayesRisk_fintype` gives the finite-sum form of the risk) and run the argument in
`ℝ`-vector space. That bridge is the bulk of the work and is itself a candidate mathlib
contribution.
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

/-- **Blackwell–Sherman–Stein converse** (finite case). If `P` attains a Bayes risk no
larger than `P'` for *every* decision problem (loss `ℓ` over an arbitrary measurable action
space `𝓨`, and prior `π`), then `P'` is a garbling of `P`.

Stated for finite parameter and sample spaces. The converse is **false** for general
measurable spaces — this is the finite Blackwell equivalence ([blackwell-1953]); the
standard-Borel version additionally requires the experiments to be dominated. The
quantification over *all* decision problems is essential: dominance for a single one does
not force garbling.

A proof requires convex geometry on the (finite-dimensional) space of garblings of `P`,
which Mathlib does not yet expose for kernels — see the module `TODO`. -/
theorem isGarblingOf_of_forall_bayesRisk_le
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧']
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'}
    (h : ∀ {𝓨 : Type u} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ),
      bayesRisk ℓ P π ≤ bayesRisk ℓ P' π) :
    P'.IsGarblingOf P := by
  sorry

/-- **[blackwell-1953]** (finite case). `P` is at least as informative as `P'` (`P'` is a
garbling of `P`) iff `P` attains a Bayes risk no larger than `P'` across every decision
problem. The forward direction (`bayesRisk_le_of_isGarblingOf`) holds for arbitrary spaces;
the reverse (`isGarblingOf_of_forall_bayesRisk_le`) needs finiteness. -/
theorem isGarblingOf_iff_forall_bayesRisk_le
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧']
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} :
    P'.IsGarblingOf P ↔
      ∀ {𝓨 : Type u} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ),
        bayesRisk ℓ P π ≤ bayesRisk ℓ P' π := by
  constructor
  · intro h _ _ ℓ π
    exact bayesRisk_le_of_isGarblingOf ℓ h π
  · exact isGarblingOf_of_forall_bayesRisk_le

end ProbabilityTheory
