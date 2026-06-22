/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Decision.Risk.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension

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
  direction, finite case; currently `sorry`). Requires finite spaces and that both `P` and
  `P'` are Markov kernels — false otherwise (see the theorem docstring for counterexamples).
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

variable {Θ 𝓧 𝓧' : Type*} [mΘ : MeasurableSpace Θ]
  [m𝓧 : MeasurableSpace 𝓧] [m𝓧' : MeasurableSpace 𝓧']

/-- On finite kernels, `comp` evaluated on a singleton is matrix multiplication:
`(η ∘ₖ P) θ {x'} = ∑ₓ η x {x'} · P θ {x}`. The first brick of the finite Blackwell
bridge (kernels ↔ stochastic matrices). -/
lemma comp_singleton_eq_sum [Fintype 𝓧] [MeasurableSingletonClass 𝓧]
    [MeasurableSingletonClass 𝓧']
    (η : Kernel 𝓧 𝓧') (P : Kernel Θ 𝓧) (θ : Θ) (x' : 𝓧') :
    (η ∘ₖ P) θ {x'} = ∑ x, η x {x'} * P θ {x} := by
  rw [Kernel.comp_apply' η P θ (measurableSet_singleton x'), lintegral_fintype]

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

/-! ### The garbling polytope (finite case)

Over finite spaces, the Markov garblings `{η ∘ₖ P | η Markov}` of `P`, encoded by their
singleton masses as vectors in `Θ → 𝓧' → ℝ`, form a compact convex polytope `garblingSet P`.
It is the linear image of the product of standard simplices — the stochastic matrices `η` —
under `garblingMap P`. This is the geometric substrate for the Blackwell–Sherman–Stein
converse: if `encode P'` lies outside the polytope, a separating functional realizes a
decision problem on which `P'` is strictly worse than `P`. -/

section GarblingPolytope

variable [Fintype 𝓧] [Fintype 𝓧'] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']

-- The finite-space instances below are shared across the section; not every lemma uses all.
set_option linter.unusedSectionVars false

/-- Encode an experiment `Q : Kernel Θ 𝓧'` as the real vector of its singleton masses
`(θ, x') ↦ (Q θ {x'}).toReal`. Injective on Markov (more generally finite) kernels. -/
private noncomputable def encode (Q : Kernel Θ 𝓧') : Θ → 𝓧' → ℝ :=
  fun θ x' => (Q θ {x'}).toReal

/-- The stochastic matrices `𝓧 → 𝓧' → ℝ`: each row is a probability vector. The encodings
of the Markov kernels `η : Kernel 𝓧 𝓧'`. -/
private def stochasticMatrices : Set (𝓧 → 𝓧' → ℝ) :=
  Set.univ.pi fun _ => stdSimplex ℝ 𝓧'

/-- Post-composition by a stochastic matrix, as a linear map on the matrix space:
`M ↦ (θ, x') ↦ ∑ₓ M x x' · (P θ {x}).toReal`. On `M = encode η` this is `encode (η ∘ₖ P)`
(`encode_comp`). -/
private noncomputable def garblingMap (P : Kernel Θ 𝓧) :
    (𝓧 → 𝓧' → ℝ) →ₗ[ℝ] (Θ → 𝓧' → ℝ) where
  toFun M := fun θ x' => ∑ x, M x x' * (P θ {x}).toReal
  map_add' M N := by ext θ x'; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    ext θ x'
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- The garbling polytope of `P`: the encodings of all Markov garblings `η ∘ₖ P`, realized as
the linear image of the stochastic-matrix simplex. -/
private noncomputable def garblingSet (P : Kernel Θ 𝓧) : Set (Θ → 𝓧' → ℝ) :=
  garblingMap (𝓧' := 𝓧') P '' stochasticMatrices

private theorem convex_garblingSet (P : Kernel Θ 𝓧) :
    Convex ℝ (garblingSet (𝓧' := 𝓧') P) :=
  (convex_pi fun _ _ => convex_stdSimplex ℝ 𝓧').linear_image _

private theorem isCompact_garblingSet (P : Kernel Θ 𝓧) :
    IsCompact (garblingSet (𝓧' := 𝓧') P) :=
  (isCompact_univ_pi fun _ => isCompact_stdSimplex ℝ 𝓧').image
    (garblingMap P).continuous_of_finiteDimensional

private theorem isClosed_garblingSet (P : Kernel Θ 𝓧) :
    IsClosed (garblingSet (𝓧' := 𝓧') P) :=
  (isCompact_garblingSet P).isClosed

/-- The stochastic matrix `(x, x') ↦ (η x {x'}).toReal` of a kernel `η : Kernel 𝓧 𝓧'`. -/
private noncomputable def encodeMatrix (η : Kernel 𝓧 𝓧') : 𝓧 → 𝓧' → ℝ :=
  fun x x' => (η x {x'}).toReal

/-- Encoding intertwines kernel composition with the linear garbling map:
`encode (η ∘ₖ P) = garblingMap P (encodeMatrix η)`. -/
private theorem encode_comp (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    encode (η ∘ₖ P) = garblingMap P (encodeMatrix η) := by
  ext θ x'
  show ((η ∘ₖ P) θ {x'}).toReal = ∑ x, (η x {x'}).toReal * (P θ {x}).toReal
  have hne : ∀ x ∈ Finset.univ, η x {x'} * P θ {x} ≠ ∞ := fun x _ =>
    ENNReal.mul_ne_top (measure_ne_top (η x) _) (measure_ne_top (P θ) _)
  rw [comp_singleton_eq_sum, ENNReal.toReal_sum hne]
  exact Finset.sum_congr rfl fun x _ => ENNReal.toReal_mul

/-- `encode` is injective on finite kernels: singleton masses determine the kernel. -/
private theorem encode_injective {Q Q' : Kernel Θ 𝓧'}
    [IsFiniteKernel Q] [IsFiniteKernel Q'] (hQ : encode Q = encode Q') : Q = Q' := by
  refine Kernel.ext fun θ => Measure.ext_of_singleton fun x' => ?_
  have hx := congrFun (congrFun hQ θ) x'
  simp only [encode] at hx
  rwa [ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)] at hx

/-- Build a kernel `𝓧 → 𝓧'` from a real matrix `M`: row `x` is the measure with mass
`ENNReal.ofReal (M x x')` on each `x'`. On a stochastic matrix it is Markov and inverts
`encodeMatrix`. -/
private noncomputable def buildKernel (M : 𝓧 → 𝓧' → ℝ) : Kernel 𝓧 𝓧' :=
  Kernel.ofFunOfCountable fun x => ∑ x' : 𝓧', ENNReal.ofReal (M x x') • Measure.dirac x'

private lemma buildKernel_apply (M : 𝓧 → 𝓧' → ℝ) (x : 𝓧) (y : 𝓧') :
    buildKernel M x {y} = ENNReal.ofReal (M x y) := by
  classical
  show (∑ x' : 𝓧', ENNReal.ofReal (M x x') • Measure.dirac x') {y} = ENNReal.ofReal (M x y)
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul, Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ y fun x' => ENNReal.ofReal (M x x')]
  simp

private theorem isMarkovKernel_buildKernel {M : 𝓧 → 𝓧' → ℝ}
    (hM : M ∈ stochasticMatrices) : IsMarkovKernel (buildKernel M) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have hx := Set.mem_univ_pi.mp hM x
  show (∑ x' : 𝓧', ENNReal.ofReal (M x x') • Measure.dirac x') Set.univ = 1
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x' _ => hx.1 x', hx.2, ENNReal.ofReal_one]

private theorem encodeMatrix_buildKernel {M : 𝓧 → 𝓧' → ℝ}
    (hM : M ∈ stochasticMatrices) : encodeMatrix (buildKernel M) = M := by
  ext x x'
  show (buildKernel M x {x'}).toReal = M x x'
  rw [buildKernel_apply, ENNReal.toReal_ofReal ((Set.mem_univ_pi.mp hM x).1 x')]

/-- **Step 6 of the converse.** If `encode P'` lies in the garbling polytope of `P`, its
witness stochastic matrix builds a Markov kernel `η` with `η ∘ₖ P = P'`, so `P'` is a
garbling of `P`. -/
private theorem isGarblingOf_of_encode_mem (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {P' : Kernel Θ 𝓧'} [IsMarkovKernel P'] (hmem : encode P' ∈ garblingSet P) :
    P'.IsGarblingOf P := by
  obtain ⟨M, hM, hMeq⟩ := hmem
  haveI := isMarkovKernel_buildKernel hM
  refine ⟨buildKernel M, inferInstance, encode_injective ?_⟩
  rw [encode_comp, encodeMatrix_buildKernel hM, hMeq]

end GarblingPolytope

/-- **Blackwell–Sherman–Stein converse** (finite case). If `P` attains a Bayes risk no
larger than `P'` for *every* decision problem (loss `ℓ` over an arbitrary measurable action
space `𝓨`, and prior `π`), then `P'` is a garbling of `P`.

Stated for finite parameter and sample spaces, with both experiments Markov kernels. All
three hypotheses are essential:

* The converse is **false** for general measurable spaces — this is the *finite* Blackwell
  equivalence ([blackwell-1953]); the standard-Borel version additionally requires the
  experiments to be dominated.
* `[IsMarkovKernel P]` is necessary: a defective `P` can attain low risk without being
  informative. E.g. the zero kernel `P = 0` has `bayesRisk ℓ 0 π = 0` for every loss (the
  least possible value), so it dominates every `P'`, yet `η ∘ₖ 0 = 0` forces `P' = 0`.
* `[IsMarkovKernel P']` is necessary: an over-massed `P'` inflates every risk. E.g. over a
  one-point sample space with `P' = 2 • P` one has `bayesRisk ℓ P' π = 2 • bayesRisk ℓ P π
  ≥ bayesRisk ℓ P π` for every loss, yet `P'` (mass `2`) is not `η ∘ₖ P` for any Markov `η`.

The quantification over *all* decision problems is likewise essential: dominance for a
single one does not force garbling.

A proof requires convex geometry on the (finite-dimensional) space of garblings of `P`,
which Mathlib does not yet expose for kernels — see the module `TODO`. -/
theorem isGarblingOf_of_forall_bayesRisk_le
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧']
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} [IsMarkovKernel P] [IsMarkovKernel P']
    (h : ∀ {𝓨 : Type u} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ),
      bayesRisk ℓ P π ≤ bayesRisk ℓ P' π) :
    P'.IsGarblingOf P := by
  by_cases hmem : encode P' ∈ garblingSet P
  · -- `encode P'` lies in the garbling polytope: its witness stochastic matrix builds the
    -- Markov garbling `η` with `η ∘ₖ P = P'`.
    exact isGarblingOf_of_encode_mem P hmem
  · -- `encode P'` lies outside the (compact, convex) garbling polytope, so a continuous
    -- linear functional `f` strictly separates it from every garbling of `P`.
    exfalso
    obtain ⟨f, u, hf_lt, hf_gt⟩ :=
      geometric_hahn_banach_point_closed (convex_garblingSet P) (isClosed_garblingSet P) hmem
    -- `f` is the separating hyperplane: `f (encode P') < u < f (encode (η ∘ₖ P))` for every
    -- Markov `η`. Realizing `f` as a decision problem `(𝓨, ℓ, π)` yields
    -- `bayesRisk ℓ P π > bayesRisk ℓ P' π`, contradicting `h`.
    -- TODO (step 5): the signed `f` must be split into a nonnegative loss, and the
    -- `bayesRisk`-as-infimum reconciled with the linear `f` via Sion's minimax theorem
    -- (`Mathlib/Topology/Sion.lean`); this is the mathematical core of the converse.
    sorry

/-- **[blackwell-1953]** (finite case). `P` is at least as informative as `P'` (`P'` is a
garbling of `P`) iff `P` attains a Bayes risk no larger than `P'` across every decision
problem. The forward direction (`bayesRisk_le_of_isGarblingOf`) holds for arbitrary spaces;
the reverse (`isGarblingOf_of_forall_bayesRisk_le`) needs finiteness and that both
experiments are Markov kernels. -/
theorem isGarblingOf_iff_forall_bayesRisk_le
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧']
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} [IsMarkovKernel P] [IsMarkovKernel P'] :
    P'.IsGarblingOf P ↔
      ∀ {𝓨 : Type u} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ),
        bayesRisk ℓ P π ≤ bayesRisk ℓ P' π := by
  constructor
  · intro h _ _ ℓ π
    exact bayesRisk_le_of_isGarblingOf ℓ h π
  · exact isGarblingOf_of_forall_bayesRisk_le

end ProbabilityTheory
