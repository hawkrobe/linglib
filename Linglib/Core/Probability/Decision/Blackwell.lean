/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.Decision.Risk.Basic
import Mathlib.Probability.Decision.Risk.Countable
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Count

/-!
# Blackwell comparison of experiments

A statistical experiment is a Markov kernel `P : Kernel Θ 𝓧` generating data in `𝓧` from a
parameter in `Θ`. Experiment `P` is **at least as informative** as `P' : Kernel Θ 𝓧'` when `P'`
can be recovered from `P` by Markov post-processing ("garbling"): `P' = η ∘ₖ P` for some Markov
kernel `η`. This file develops that order and its characterization through Bayes risk.

[blackwell-1953]'s comparison theorem states that `P` is at least as informative as `P'` if and
only if, for every decision problem, the Bayes risk under `P` is no greater than under `P'`. We
state and prove this equivalence over `ProbabilityTheory.bayesRisk` for finite spaces: the
forward direction is the data-processing inequality, the converse the Blackwell–Sherman–Stein
separation argument (see the implementation notes).

## Main definitions

* `Kernel.IsGarblingOf`: `P'.IsGarblingOf P` means `P'` is a Markov garbling of `P`, i.e. `P` is
  at least as informative as `P'`. Reflexive (`Kernel.IsGarblingOf.refl`) and transitive
  (`Kernel.IsGarblingOf.trans`).
* `Kernel.BlackwellDominates`: `P.BlackwellDominates P'` means `P` has Bayes risk no greater than
  `P'` for every decision problem and prior — the dual side of the Blackwell equivalence.

## Main statements

* `bayesRisk_le_of_isGarblingOf` / `blackwellDominates_of_isGarblingOf`: if `P'` is a garbling of
  `P`, then `P` Blackwell-dominates `P'` (the data-processing direction).
* `isGarblingOf_of_blackwellDominates`: conversely, if `P` Blackwell-dominates `P'`, then `P'` is a
  garbling of `P` (the Blackwell–Sherman–Stein direction, finite case). Requires finite, nonempty
  `Θ` and that both `P` and `P'` are Markov kernels — false otherwise (see the theorem docstring
  for counterexamples).
* `isGarblingOf_iff_blackwellDominates`: the two directions combined.

## Implementation notes

The development is stated entirely over Mathlib's `Kernel` and `bayesRisk` with no further
dependencies, so it can serve as a `Mathlib.Probability.Decision.Blackwell` candidate. The
finite, `ℝ`-valued `eig` / `questionUtility` view in `Core.Probability.Decision.ExperimentDesign`
is a downstream consumer: `eig_deterministicObs_eq_euv` there identifies the deterministic-
experiment value with [van-rooy-2003]'s question utility, whose refinement monotonicity is the
partition instance of `bayesRisk_deterministic_le_deterministic_comp` below.

`Kernel.BlackwellDominates` quantifies over *all* decision problems (every measurable action space
`𝓨` and loss `ℓ : Θ → 𝓨 → ℝ≥0∞`) and priors: dominance for a single one does not force garbling.
The action-space universe is pinned to `u` (the universe of `𝓧'`) because the converse proof
instantiates the dominance hypothesis at the action space `𝓨 := 𝓧'` (the identity estimator).

The converse proof encodes finite kernels as real vectors of singleton masses (`encode`) and
realizes the garblings of `P` as a compact convex polytope `garblingSet P` (the linear image of
the product of standard simplices). If `encode P'` lies outside the polytope, the geometric
Hahn–Banach theorem (`geometric_hahn_banach_point_closed`) yields a separating functional `f`;
its coordinate matrix `a θ x' = f (Pi.single θ (Pi.single x' 1))`, shifted by a constant `C` to
be nonnegative, defines a loss `ℓ θ x' = ENNReal.ofReal (a θ x' + C)` on actions `𝓧'`. Under the
uniform prior, the Bayes risk of any experiment `Q` evaluated at the identity estimator equals
`ENNReal.ofReal (|Θ|⁻¹ · f (encode Q) + C)`: the identity estimator pins `P'` to `f (encode P')`,
while every estimator for `P` produces a garbling, whose `f`-value exceeds the separation level.
This realizes `bayesRisk ℓ P' π < bayesRisk ℓ P π`, contradicting the hypothesis — no minimax
theorem is needed, the infimum is bounded below directly. All analytic inputs come from Mathlib
(`isCompact_stdSimplex`, the `geometric_hahn_banach_*` lemmas, `bayesRisk_fintype`). The
kernel-to-stochastic-matrix bridge (`encode`, `garblingMap`, `buildKernel`) is currently
`private` proof scaffolding; it is a self-contained finite-kernel ↔ row-stochastic-matrix
correspondence that would naturally graduate to its own public file when upstreamed.

## References

* [blackwell-1953]
-/

universe u

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

-- `𝓧'` (the garbled experiment's outcome space) is pinned to the universe `u` of the action-space
-- quantifier in `Kernel.BlackwellDominates`: the converse proof uses `𝓧'` itself as an action
-- space, so the two must cohabit a universe. `Θ`, `𝓧` stay fully universe-polymorphic.
variable {Θ 𝓧 : Type*} {𝓧' : Type u} [mΘ : MeasurableSpace Θ]
  [m𝓧 : MeasurableSpace 𝓧] [m𝓧' : MeasurableSpace 𝓧']

/-- On finite kernels, `comp` evaluated on a singleton is matrix multiplication:
`(η ∘ₖ P) θ {x'} = ∑ₓ η x {x'} · P θ {x}`. The first brick of the finite Blackwell
bridge (kernels ↔ stochastic matrices). -/
private lemma comp_singleton_eq_sum [Fintype 𝓧] [MeasurableSingletonClass 𝓧]
    [MeasurableSingletonClass 𝓧']
    (η : Kernel 𝓧 𝓧') (P : Kernel Θ 𝓧) (θ : Θ) (x' : 𝓧') :
    (η ∘ₖ P) θ {x'} = ∑ x, η x {x'} * P θ {x} := by
  rw [Kernel.comp_apply' η P θ (measurableSet_singleton x'), lintegral_fintype]

/-- `P'` is a **garbling** of `P` (Blackwell): there is a Markov post-processing
kernel `η` with `P' = η ∘ₖ P`. Read "`P` is at least as informative as `P'`". -/
def Kernel.IsGarblingOf (P' : Kernel Θ 𝓧') (P : Kernel Θ 𝓧) : Prop :=
  ∃ η : Kernel 𝓧 𝓧', IsMarkovKernel η ∧ P' = η ∘ₖ P

@[refl]
protected theorem Kernel.IsGarblingOf.refl (P : Kernel Θ 𝓧) [IsMarkovKernel P] :
    P.IsGarblingOf P :=
  ⟨Kernel.id, inferInstance, (Kernel.id_comp P).symm⟩

protected theorem Kernel.IsGarblingOf.trans {𝓧'' : Type*} [MeasurableSpace 𝓧'']
    {P'' : Kernel Θ 𝓧''} {P' : Kernel Θ 𝓧'} {P : Kernel Θ 𝓧}
    (h₂ : P''.IsGarblingOf P') (h₁ : P'.IsGarblingOf P) :
    P''.IsGarblingOf P := by
  obtain ⟨η₂, hη₂, rfl⟩ := h₂
  obtain ⟨η₁, hη₁, rfl⟩ := h₁
  haveI := hη₁; haveI := hη₂
  exact ⟨η₂ ∘ₖ η₁, inferInstance, (η₂.comp_assoc η₁ P).symm⟩

/-- `P` **Blackwell-dominates** `P'`: for every decision problem (action space `𝓨`, loss `ℓ`)
and prior `π`, the Bayes risk under `P` is no larger than under `P'`. The right-hand side of the
Blackwell equivalence. -/
def Kernel.BlackwellDominates (P : Kernel Θ 𝓧) (P' : Kernel Θ 𝓧') : Prop :=
  ∀ {𝓨 : Type u} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ),
    bayesRisk ℓ P π ≤ bayesRisk ℓ P' π

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

/-- **Easy direction, bundled.** A garbling of `P` is Blackwell-dominated by `P`. -/
theorem blackwellDominates_of_isGarblingOf {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'}
    (h : P'.IsGarblingOf P) : P.BlackwellDominates P' :=
  fun ℓ π => bayesRisk_le_of_isGarblingOf ℓ h π

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

/-- Each encoded singleton mass is nonnegative. -/
private theorem encode_nonneg (Q : Kernel Θ 𝓧') (θ : Θ) (x' : 𝓧') : 0 ≤ encode Q θ x' :=
  ENNReal.toReal_nonneg

/-- For a Markov kernel the encoded row masses sum to one over outcomes, hence the full encoding
sums to `Fintype.card Θ`. This is the constraint pinning every garbling to the affine slice the
loss shift exploits. -/
private theorem sum_encode_eq [Fintype Θ] (Q : Kernel Θ 𝓧') [IsMarkovKernel Q] :
    ∑ θ, ∑ x', encode Q θ x' = (Fintype.card Θ : ℝ) := by
  have hrow : ∀ θ, ∑ x', encode Q θ x' = 1 := fun θ => by
    simp only [encode]
    rw [← ENNReal.toReal_sum fun x' _ => measure_ne_top _ _, sum_measure_singleton,
      Finset.coe_univ, measure_univ, ENNReal.toReal_one]
  rw [Finset.sum_congr rfl fun θ _ => hrow θ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]

/-- The encoded stochastic matrix of a Markov kernel lies in the product of standard simplices. -/
private theorem encodeMatrix_mem (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    encodeMatrix η ∈ stochasticMatrices := by
  simp only [stochasticMatrices, Set.mem_univ_pi, stdSimplex, Set.mem_setOf_eq, encodeMatrix]
  refine fun x => ⟨fun x' => ENNReal.toReal_nonneg, ?_⟩
  rw [← ENNReal.toReal_sum fun x' _ => measure_ne_top _ _, sum_measure_singleton,
    Finset.coe_univ, measure_univ, ENNReal.toReal_one]

/-- A continuous linear functional on the finite product `Θ → 𝓧' → ℝ` is the sum of its values on
the standard basis `Pi.single θ (Pi.single x' 1)`, weighted by coordinates. -/
private theorem clm_apply_eq_sum_single [Fintype Θ] [DecidableEq Θ] [DecidableEq 𝓧']
    (f : (Θ → 𝓧' → ℝ) →L[ℝ] ℝ) (v : Θ → 𝓧' → ℝ) :
    f v = ∑ θ, ∑ x', v θ x' * f (Pi.single θ (Pi.single x' (1 : ℝ))) := by
  have hv : (∑ θ, ∑ x', v θ x' • (Pi.single θ (Pi.single x' (1 : ℝ)) : Θ → 𝓧' → ℝ)) = v := by
    funext θ₀ x'₀
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply, Pi.zero_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
  calc f v
      = f (∑ θ, ∑ x', v θ x' • (Pi.single θ (Pi.single x' (1 : ℝ)) : Θ → 𝓧' → ℝ)) := by rw [hv]
    _ = ∑ θ, ∑ x', v θ x' * f (Pi.single θ (Pi.single x' (1 : ℝ))) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [map_sum]
        exact Finset.sum_congr rfl fun x' _ => by rw [map_smul, smul_eq_mul]

/-- **Risk conversion.** Under the uniform prior on `Θ`, the Bayes risk of the experiment `Q` at
the identity estimator with the nonnegative affine loss `(θ, x') ↦ a θ x' + C` is a single
`ENNReal.ofReal` of a manifestly nonnegative real double sum. The caller linearizes that sum
against the separating functional. -/
private theorem avgRisk_id_uniform_eq [Fintype Θ] [Nonempty Θ] [MeasurableSingletonClass Θ]
    (a : Θ → 𝓧' → ℝ) {C : ℝ}
    (hC : ∀ θ x', 0 ≤ a θ x' + C) (Q : Kernel Θ 𝓧') [IsMarkovKernel Q] :
    avgRisk (fun θ x' => ENNReal.ofReal (a θ x' + C)) Q Kernel.id
        ((Fintype.card Θ : ℝ≥0∞)⁻¹ • Measure.count)
      = ENNReal.ofReal (∑ θ, (∑ x', (a θ x' + C) * encode Q θ x') * (Fintype.card Θ : ℝ)⁻¹) := by
  have hcard : (0 : ℝ) < (Fintype.card Θ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmass : ∀ θ x', Q θ {x'} = ENNReal.ofReal (encode Q θ x') := fun θ x' => by
    simp only [encode]; exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hπ : ∀ θ : Θ, ((Fintype.card Θ : ℝ≥0∞)⁻¹ • (Measure.count : Measure Θ)) {θ}
      = ENNReal.ofReal (Fintype.card Θ : ℝ)⁻¹ := fun θ => by
    simp only [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast]
  have ht : ∀ θ x', 0 ≤ (a θ x' + C) * encode Q θ x' :=
    fun θ x' => mul_nonneg (hC θ x') (encode_nonneg Q θ x')
  have hr : ∀ θ, 0 ≤ ∑ x', (a θ x' + C) * encode Q θ x' :=
    fun θ => Finset.sum_nonneg fun x' _ => ht θ x'
  rw [avgRisk_fintype]
  simp only [Kernel.id_comp, lintegral_fintype]
  rw [ENNReal.ofReal_sum_of_nonneg fun θ _ => mul_nonneg (hr θ) (inv_nonneg.mpr hcard.le)]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [hπ θ, ENNReal.ofReal_mul (hr θ)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg fun x' _ => ht θ x']
  exact Finset.sum_congr rfl fun x' _ => by rw [hmass θ x', ← ENNReal.ofReal_mul (hC θ x')]

end GarblingPolytope

/-- **Blackwell–Sherman–Stein converse, minimal-hypothesis form**. Same conclusion as
`isGarblingOf_of_blackwellDominates`, but the risk-comparison hypothesis is required only for
losses that are **everywhere finite** (`ℓ θ x' ≠ ⊤`) and **only at the uniform prior**. The
proof body constructs exactly such a loss, so this weakened form is enough to conclude that
`P'` is a garbling of `P`. Downstream users (e.g. Van Rooy's decision-theoretic converse
transported through the utility–loss duality) supply only finite-valued losses. -/
theorem isGarblingOf_of_bayesRisk_uniform_le
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧'] [Nonempty Θ]
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} [IsMarkovKernel P] [IsMarkovKernel P']
    (h : ∀ ℓ : Θ → 𝓧' → ℝ≥0∞, (∀ θ x', ℓ θ x' ≠ ⊤) →
      bayesRisk ℓ P ((Fintype.card Θ : ℝ≥0∞)⁻¹ • Measure.count) ≤
        bayesRisk ℓ P' ((Fintype.card Θ : ℝ≥0∞)⁻¹ • Measure.count)) :
    P'.IsGarblingOf P := by
  classical
  by_cases hmem : encode P' ∈ garblingSet P
  · -- `encode P'` lies in the garbling polytope: its witness stochastic matrix builds the
    -- Markov garbling `η` with `η ∘ₖ P = P'`.
    exact isGarblingOf_of_encode_mem P hmem
  · -- `encode P'` lies outside the (compact, convex) garbling polytope, so a continuous linear
    -- functional `f` strictly separates it from every garbling of `P`. We realize `f` as a
    -- (nonnegative, shifted) loss `ℓ` on actions `𝓧'`, under the uniform prior `π`; the identity
    -- estimator exhibits `P'`'s risk as `f (encode P')`, while every estimator drives `P`'s risk
    -- above `u`. Then `bayesRisk ℓ P' π < bayesRisk ℓ P π`, contradicting `h`.
    exfalso
    obtain ⟨f, u, hf_lt, hf_gt⟩ :=
      geometric_hahn_banach_point_closed (convex_garblingSet P) (isClosed_garblingSet P) hmem
    -- Coordinate matrix of the separating functional `f`, and the nonnegative shift `C`.
    set a : Θ → 𝓧' → ℝ := fun θ x' => f (Pi.single θ (Pi.single x' (1 : ℝ))) with ha_def
    set C : ℝ := ∑ θ, ∑ x', |a θ x'|
    have ha_nonneg : ∀ θ x', 0 ≤ a θ x' + C := by
      intro θ x'
      have hle : |a θ x'| ≤ C :=
        (Finset.single_le_sum (fun i _ => abs_nonneg _) (Finset.mem_univ x')).trans
          (Finset.single_le_sum (f := fun θ => ∑ x', |a θ x'|)
            (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ θ))
      linarith [neg_abs_le (a θ x')]
    have hN_pos : (0 : ℝ) < (Fintype.card Θ : ℝ) := by exact_mod_cast Fintype.card_pos
    -- The shifted loss and the uniform prior.
    set ℓ : Θ → 𝓧' → ℝ≥0∞ := fun θ x' => ENNReal.ofReal (a θ x' + C) with hℓ_def
    have hℓ_ne_top : ∀ θ x', ℓ θ x' ≠ ⊤ := fun _ _ => ENNReal.ofReal_ne_top
    set π : Measure Θ := (Fintype.card Θ : ℝ≥0∞)⁻¹ • Measure.count with hπ_def
    -- The real risk value of a Markov `Q`: a nonnegative double sum that linearizes against `f`.
    have hnn : ∀ Q : Kernel Θ 𝓧',
        0 ≤ ∑ θ, (∑ x', (a θ x' + C) * encode Q θ x') * (Fintype.card Θ : ℝ)⁻¹ := fun Q =>
      Finset.sum_nonneg fun θ _ => mul_nonneg
        (Finset.sum_nonneg fun x' _ => mul_nonneg (ha_nonneg θ x') (encode_nonneg Q θ x'))
        (inv_nonneg.mpr hN_pos.le)
    have hlin : ∀ (Q : Kernel Θ 𝓧') [IsMarkovKernel Q],
        (∑ θ, (∑ x', (a θ x' + C) * encode Q θ x') * (Fintype.card Θ : ℝ)⁻¹)
          = (Fintype.card Θ : ℝ)⁻¹ * f (encode Q) + C := by
      intro Q _
      have hcoord : (∑ θ, ∑ x', a θ x' * encode Q θ x') = f (encode Q) := by
        rw [clm_apply_eq_sum_single f (encode Q)]
        simp only [ha_def]
        exact Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun x' _ => mul_comm _ _
      have hrow : ∀ θ, ∑ x', (a θ x' + C) * encode Q θ x'
          = (∑ x', a θ x' * encode Q θ x') + C * ∑ x', encode Q θ x' := fun θ => by
        simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      rw [← Finset.sum_mul, Finset.sum_congr rfl fun θ _ => hrow θ, Finset.sum_add_distrib,
        ← Finset.mul_sum, sum_encode_eq Q, hcoord]
      field_simp [hN_pos.ne']
    -- The Bayes risk of `Q` at the identity estimator equals `ofReal ((card Θ)⁻¹ · f (encode Q) + C)`.
    have key : ∀ (Q : Kernel Θ 𝓧') [IsMarkovKernel Q],
        avgRisk ℓ Q Kernel.id π
          = ENNReal.ofReal ((Fintype.card Θ : ℝ)⁻¹ * f (encode Q) + C) := by
      intro Q _
      rw [hℓ_def, hπ_def, avgRisk_id_uniform_eq a ha_nonneg Q, hlin Q]
    -- Upper bound for `P'` (identity estimator) and its nonnegativity.
    have hP'_le : bayesRisk ℓ P' π ≤ ENNReal.ofReal ((Fintype.card Θ : ℝ)⁻¹ * f (encode P') + C) :=
      (bayesRisk_le_avgRisk ℓ P' Kernel.id π).trans_eq (key P')
    have hP'_nonneg : 0 ≤ (Fintype.card Θ : ℝ)⁻¹ * f (encode P') + C := hlin P' ▸ hnn P'
    -- Lower bound for `P`: every estimator's garbling sits above `u`.
    have hP_ge : ENNReal.ofReal ((Fintype.card Θ : ℝ)⁻¹ * u + C) ≤ bayesRisk ℓ P π := by
      rw [bayesRisk]
      refine le_iInf fun κ => le_iInf fun hκ => ?_
      haveI := hκ
      have hcomp : avgRisk ℓ P κ π = avgRisk ℓ (κ ∘ₖ P) Kernel.id π := by
        simp only [avgRisk, Kernel.id_comp]
      rw [hcomp, key (κ ∘ₖ P)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hgt : u < f (encode (κ ∘ₖ P)) := hf_gt _ (by
        rw [encode_comp]; exact Set.mem_image_of_mem _ (encodeMatrix_mem κ))
      gcongr
    -- The two bounds straddle `u`, contradicting `h`.
    have hpos : 0 < (Fintype.card Θ : ℝ)⁻¹ * u + C := by
      have := mul_lt_mul_of_pos_left hf_lt (inv_pos.mpr hN_pos)
      linarith [hP'_nonneg]
    have hlt : ENNReal.ofReal ((Fintype.card Θ : ℝ)⁻¹ * f (encode P') + C)
        < ENNReal.ofReal ((Fintype.card Θ : ℝ)⁻¹ * u + C) := by
      refine (ENNReal.ofReal_lt_ofReal_iff hpos).mpr ?_
      gcongr
    exact absurd (h ℓ hℓ_ne_top) (not_le.mpr ((hP'_le.trans_lt hlt).trans_le hP_ge))

/-- **Blackwell–Sherman–Stein converse** (finite case). If `P` Blackwell-dominates `P'` (attains a
Bayes risk no larger than `P'` for *every* decision problem and prior), then `P'` is a garbling of
`P`.

Stated for finite parameter and sample spaces, with both experiments Markov kernels. All
four hypotheses are essential:

* The converse is **false** for general measurable spaces — this is the *finite* Blackwell
  equivalence ([blackwell-1953]); the standard-Borel version additionally requires the
  experiments to be dominated.
* `[Nonempty Θ]` is necessary: with `Θ` empty every Bayes risk is `0`, so the hypothesis holds
  vacuously, yet a Markov garbling `η : Kernel 𝓧 𝓧'` need not exist when `𝓧` is nonempty and
  `𝓧'` is empty. (Nonempty `Θ` together with `[IsMarkovKernel P']` also forces `𝓧'` nonempty.)
* `[IsMarkovKernel P]` is necessary: a defective `P` can attain low risk without being
  informative. E.g. the zero kernel `P = 0` has `bayesRisk ℓ 0 π = 0` for every loss (the
  least possible value), so it dominates every `P'`, yet `η ∘ₖ 0 = 0` forces `P' = 0`.
* `[IsMarkovKernel P']` is necessary: an over-massed `P'` inflates every risk. E.g. over a
  one-point sample space with `P' = 2 • P` one has `bayesRisk ℓ P' π = 2 • bayesRisk ℓ P π
  ≥ bayesRisk ℓ P π` for every loss, yet `P'` (mass `2`) is not `η ∘ₖ P` for any Markov `η`.

The quantification over *all* decision problems is likewise essential: dominance for a
single one does not force garbling.

The proof factors through `isGarblingOf_of_bayesRisk_uniform_le`: the internal separating loss
is finite-valued, so the full universal quantification is stronger than needed. -/
theorem isGarblingOf_of_blackwellDominates
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧'] [Nonempty Θ]
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} [IsMarkovKernel P] [IsMarkovKernel P']
    (h : P.BlackwellDominates P') :
    P'.IsGarblingOf P :=
  isGarblingOf_of_bayesRisk_uniform_le fun ℓ _ => h ℓ _

/-- **[blackwell-1953]** (finite case). `P` is at least as informative as `P'` (`P'` is a
garbling of `P`) iff `P` Blackwell-dominates `P'` (no greater Bayes risk across every decision
problem). The forward direction (`blackwellDominates_of_isGarblingOf`) holds for arbitrary spaces;
the reverse (`isGarblingOf_of_blackwellDominates`) needs finiteness, nonempty `Θ`, and that both
experiments are Markov kernels. -/
theorem isGarblingOf_iff_blackwellDominates
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧'] [Nonempty Θ]
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} [IsMarkovKernel P] [IsMarkovKernel P'] :
    P'.IsGarblingOf P ↔ P.BlackwellDominates P' :=
  ⟨blackwellDominates_of_isGarblingOf, isGarblingOf_of_blackwellDominates⟩

/-! ### Deterministic experiments: partitions as kernels

A deterministic classifier `f : Θ → 𝓧` is the experiment `Kernel.deterministic f hf` — the
partition of `Θ` into the fibers of `f`, viewed as an error-free observation. Coarsening the
partition (post-composing the classifier) is a deterministic garbling, so a finer partition
Blackwell-dominates every coarsening. This is the kernel-level form of the fact that
partition-refinement monotonicity of question value ([van-rooy-2003] §4.1, formalized
ℚ-valued as `Core.DecisionTheory.DecisionProblem.questionUtility_mono_of_refines`) is a special case of
[blackwell-1953]. -/

/-- A coarsened classifier is a garbling of the classifier it factors through: the
partition of `g ∘ f` is obtained from the partition of `f` by the deterministic
post-processing `g`. -/
theorem Kernel.deterministic_comp_isGarblingOf_deterministic {𝓨 : Type*} [MeasurableSpace 𝓨]
    {f : Θ → 𝓧} {g : 𝓧 → 𝓨} (hf : Measurable f) (hg : Measurable g) :
    (Kernel.deterministic (g ∘ f) (hg.comp hf)).IsGarblingOf (Kernel.deterministic f hf) :=
  ⟨Kernel.deterministic g hg, inferInstance,
    (Kernel.deterministic_comp_deterministic hf hg).symm⟩

/-- **A finer partition is worth at least as much as any coarsening, in every decision
problem**: the Bayes risk of the experiment "observe `f θ`" is at most that of
"observe `g (f θ)`". The kernel-level [blackwell-1953] fact behind [van-rooy-2003]'s §4.1
question-utility monotonicity. -/
theorem bayesRisk_deterministic_le_deterministic_comp {𝓨 : Type u} [MeasurableSpace 𝓨]
    {𝓨' : Type u} [MeasurableSpace 𝓨']
    {f : Θ → 𝓧'} {g : 𝓧' → 𝓨} (hf : Measurable f) (hg : Measurable g)
    (ℓ : Θ → 𝓨' → ℝ≥0∞) (π : Measure Θ) :
    bayesRisk ℓ (Kernel.deterministic f hf) π ≤
      bayesRisk ℓ (Kernel.deterministic (g ∘ f) (hg.comp hf)) π :=
  bayesRisk_le_of_isGarblingOf ℓ
    (Kernel.deterministic_comp_isGarblingOf_deterministic hf hg) π

/-- **Between deterministic experiments the Blackwell order is functional factoring**:
`deterministic g` is a garbling of `deterministic f` iff `g` factors through `f`. The
mixing kernel of any garbling of a deterministic experiment is forced to be Dirac on
the range of `f`, so randomized post-processing buys nothing — the partition of `g`
must genuinely coarsen the partition of `f`. -/
theorem Kernel.deterministic_isGarblingOf_deterministic_iff {𝓨 : Type*}
    [MeasurableSpace 𝓨] [Countable 𝓧] [MeasurableSingletonClass 𝓧]
    [MeasurableSingletonClass 𝓨] [Nonempty 𝓨]
    {f : Θ → 𝓧} {g : Θ → 𝓨} (hf : Measurable f) (hg : Measurable g) :
    (Kernel.deterministic g hg).IsGarblingOf (Kernel.deterministic f hf) ↔
      ∃ ψ : 𝓧 → 𝓨, g = ψ ∘ f := by
  constructor
  · rintro ⟨η, hη, hcomp⟩
    have hpt : ∀ θ, η (f θ) = Measure.dirac (g θ) := by
      intro θ
      have h1 : (η ∘ₖ Kernel.deterministic f hf) θ = η (f θ) := by
        rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
      rw [← h1, ← hcomp, Kernel.deterministic_apply]
    have hft : Function.FactorsThrough g f := by
      intro θ θ' hff
      have h12 : Measure.dirac (g θ) = Measure.dirac (g θ') := by
        rw [← hpt θ, ← hpt θ', hff]
      by_contra hne
      have he := congrArg (λ μ : Measure 𝓨 => μ {g θ}) h12
      rw [Measure.dirac_apply' _ (measurableSet_singleton _),
        Measure.dirac_apply' _ (measurableSet_singleton _)] at he
      simp [Ne.symm hne] at he
    exact ⟨Function.extend f g (λ _ => Classical.arbitrary 𝓨),
      (hft.extend_comp _).symm⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨Kernel.deterministic ψ (measurable_of_countable ψ), inferInstance,
      (Kernel.deterministic_comp_deterministic hf (measurable_of_countable ψ)).symm⟩

/-- The average risk of any estimator `κ` on the deterministic experiment `f`,
regrouped by cell: `avgRisk = ∑_x ∑_y κ(x){y} · ∑_{θ ∈ fiber x} π{θ}·ℓ(θ, y)`.
No `IsMarkovKernel` hypothesis is needed — this is a pure algebraic rearrangement. -/
private lemma avgRisk_deterministic_fintype_eq [Fintype Θ] [Fintype 𝓧]
    [DecidableEq 𝓧] [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧]
    {𝓨 : Type u} [MeasurableSpace 𝓨] [Fintype 𝓨] [MeasurableSingletonClass 𝓨]
    {f : Θ → 𝓧} (hf : Measurable f) (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ)
    (κ : Kernel 𝓧 𝓨) :
    avgRisk ℓ (Kernel.deterministic f hf) κ π =
      ∑ x : 𝓧, ∑ y : 𝓨, κ x {y} *
        ∑ θ ∈ Finset.univ.filter (f · = x), π {θ} * ℓ θ y := by
  rw [avgRisk_fintype]
  calc ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ Kernel.deterministic f hf) θ)) * π {θ}
      = ∑ θ, ∑ y : 𝓨, κ (f θ) {y} * (π {θ} * ℓ θ y) := by
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, lintegral_fintype,
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ x, ∑ θ ∈ Finset.univ.filter (f · = x),
            ∑ y : 𝓨, κ x {y} * (π {θ} * ℓ θ y) := by
        rw [← Finset.sum_fiberwise_of_maps_to (fun θ _ => Finset.mem_univ (f θ))
              (fun θ => ∑ y : 𝓨, κ (f θ) {y} * (π {θ} * ℓ θ y))]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun θ hθ => ?_
        rw [(Finset.mem_filter.mp hθ).2]
    _ = ∑ x, ∑ y : 𝓨, κ x {y} *
            ∑ θ ∈ Finset.univ.filter (f · = x), π {θ} * ℓ θ y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]

/-- **Bayes risk of a deterministic experiment** (finite case): observing the exact
cell of `θ` under `f`, the optimal estimator picks the best action per cell, so the
Bayes risk is the sum over cells of the minimal conditional expected loss. The
utility-scale reading — risk = bound minus partition value — is
`Core.Probability.Decision.Duality`. -/
theorem bayesRisk_deterministic [Fintype Θ] [Fintype 𝓧] [DecidableEq 𝓧]
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] {𝓨 : Type u}
    [MeasurableSpace 𝓨] [Fintype 𝓨] [Nonempty 𝓨] [MeasurableSingletonClass 𝓨]
    {f : Θ → 𝓧} (hf : Measurable f) (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ)
    [IsFiniteMeasure π] :
    bayesRisk ℓ (Kernel.deterministic f hf) π =
      ∑ x : 𝓧, ⨅ y : 𝓨, ∑ θ ∈ Finset.univ.filter (f · = x), π {θ} * ℓ θ y := by
  classical
  set F : 𝓧 → 𝓨 → ℝ≥0∞ :=
    fun x y => ∑ θ ∈ Finset.univ.filter (f · = x), π {θ} * ℓ θ y with hF_def
  -- Best action per cell.
  have hbest : ∀ x : 𝓧, ∃ y : 𝓨, ∀ y' : 𝓨, F x y ≤ F x y' := fun x => by
    obtain ⟨y, _, hy⟩ :=
      Finset.exists_min_image Finset.univ (F x) Finset.univ_nonempty
    exact ⟨y, fun y' => hy y' (Finset.mem_univ y')⟩
  choose ystar hystar using hbest
  have h_meas : Measurable ystar := measurable_of_countable ystar
  have hstar_min : ∀ x, F x (ystar x) = ⨅ y : 𝓨, F x y := fun x =>
    le_antisymm (le_iInf fun y => hystar x y) (iInf_le _ _)
  refine le_antisymm ?_ ?_
  · -- `≤`: the best-response estimator `κ* = deterministic ystar` attains the RHS.
    calc bayesRisk ℓ (Kernel.deterministic f hf) π
        ≤ avgRisk ℓ (Kernel.deterministic f hf)
            (Kernel.deterministic ystar h_meas) π :=
          bayesRisk_le_avgRisk _ _ _ _
      _ = ∑ θ, ℓ θ (ystar (f θ)) * π {θ} := by
          rw [avgRisk_fintype]
          refine Finset.sum_congr rfl fun θ _ => ?_
          rw [Kernel.deterministic_comp_deterministic hf h_meas,
            Kernel.deterministic_apply, lintegral_dirac]; rfl
      _ = ∑ x, ∑ θ ∈ Finset.univ.filter (f · = x), ℓ θ (ystar (f θ)) * π {θ} :=
          (Finset.sum_fiberwise_of_maps_to (fun θ _ => Finset.mem_univ (f θ)) _).symm
      _ = ∑ x, F x (ystar x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hF_def]
          refine Finset.sum_congr rfl fun θ hθ => ?_
          rw [(Finset.mem_filter.mp hθ).2, mul_comm]
      _ = ∑ x, ⨅ y : 𝓨, F x y := Finset.sum_congr rfl fun x _ => hstar_min x
  · -- `≥`: every Markov estimator's cellwise risk exceeds the cellwise infimum.
    rw [bayesRisk]
    refine le_iInf fun κ => le_iInf fun hκ => ?_
    haveI := hκ
    rw [avgRisk_deterministic_fintype_eq hf ℓ π κ]
    refine Finset.sum_le_sum fun x _ => ?_
    calc (⨅ y : 𝓨, F x y)
        = (⨅ y : 𝓨, F x y) * 1 := (mul_one _).symm
      _ = (⨅ y : 𝓨, F x y) * κ x Set.univ := by rw [measure_univ]
      _ = (⨅ y : 𝓨, F x y) * ∑ y : 𝓨, κ x {y} := by
          congr 1
          rw [← Finset.coe_univ (α := 𝓨),
            ← sum_measure_singleton (μ := κ x) (s := Finset.univ)]
      _ = ∑ y : 𝓨, (⨅ y' : 𝓨, F x y') * κ x {y} := Finset.mul_sum _ _ _
      _ ≤ ∑ y : 𝓨, F x y * κ x {y} := by gcongr with y _; exact iInf_le _ _
      _ = ∑ y : 𝓨, κ x {y} * F x y :=
          Finset.sum_congr rfl fun y _ => mul_comm _ _

end ProbabilityTheory
