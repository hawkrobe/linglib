/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Probability.Decision.Risk.Countable
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Count

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
dependencies, so it can serve as a `Mathlib.Probability.Decision.Blackwell` candidate. On the
utility scale, `Core.Probability.Decision.ValueOfInformation` reads the data-processing direction
as the statement that garbling an experiment never raises its value of information, and
`Core.Probability.Decision.Duality` identifies the value of information of a deterministic
experiment with [van-rooy-2003]'s question utility.

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
(`StdSimplex.compactSpace`, the `geometric_hahn_banach_*` lemmas, `bayesRisk_fintype`). The
kernel-to-stochastic-matrix bridge (`encode`, `garblingMap`, `buildKernel`) is currently
`private` proof scaffolding; it is a self-contained finite-kernel ↔ row-stochastic-matrix
correspondence that would naturally graduate to its own public file when upstreamed.

## References

* [blackwell-1953]
-/

@[expose] public section

universe u

open MeasureTheory Convexity
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

/-- `P'` is a garbling of `P` when a Markov kernel `η` post-processes `P` into `P'`, so that
`P' = η ∘ₖ P` and `P` is at least as informative as `P'`. -/
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
  have := hη₁; have := hη₂
  exact ⟨η₂ ∘ₖ η₁, inferInstance, (η₂.comp_assoc η₁ P).symm⟩

/-- `P` Blackwell-dominates `P'` when, for every decision problem (an action space `𝓨` with a
loss `ℓ`) and every prior `π`, the Bayes risk under `P` is at most that under `P'`. -/
def Kernel.BlackwellDominates (P : Kernel Θ 𝓧) (P' : Kernel Θ 𝓧') : Prop :=
  ∀ {𝓨 : Type u} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ),
    bayesRisk ℓ P π ≤ bayesRisk ℓ P' π

/-- If `P'` is a garbling of `P`, the Bayes risk under `P` is at most that under `P'` in every
decision problem. -/
theorem bayesRisk_le_of_isGarblingOf {𝓨 : Type u} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'}
    (h : P'.IsGarblingOf P) (π : Measure Θ) :
    bayesRisk ℓ P π ≤ bayesRisk ℓ P' π := by
  obtain ⟨η, hη, rfl⟩ := h
  have := hη
  exact bayesRisk_le_bayesRisk_comp ℓ P π η

/-- A garbling of `P` is Blackwell-dominated by `P`. -/
theorem blackwellDominates_of_isGarblingOf {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'}
    (h : P'.IsGarblingOf P) : P.BlackwellDominates P' :=
  fun ℓ π => bayesRisk_le_of_isGarblingOf ℓ h π

/-! ### The garbling polytope (finite case)

Over finite spaces, the Markov garblings `{η ∘ₖ P | η Markov}` of `P`, encoded by their
singleton masses as vectors in `Θ → 𝓧' → ℝ`, form a compact convex polytope `garblingSet P`.
It is the linear image of the product of standard simplices — the stochastic matrices `η` —
under `garblingMap P`. If `encode P'` lies outside the polytope, a separating functional gives
a decision problem on which `P'` is strictly worse than `P`, which proves the converse. -/

section GarblingPolytope

variable [Fintype 𝓧] [Fintype 𝓧'] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']

-- The finite-space instances below are shared across the section; not every lemma uses all.
set_option linter.unusedSectionVars false

/-- `encode Q` is the real vector `(θ, x') ↦ (Q θ {x'}).toReal` of the singleton masses of the
experiment `Q`. -/
private noncomputable def encode (Q : Kernel Θ 𝓧') : Θ → 𝓧' → ℝ :=
  fun θ x' => (Q θ {x'}).toReal

/-- A stochastic matrix `𝓧 → 𝓧' → ℝ` has a probability vector in each row; these matrices
encode the Markov kernels `𝓧 → 𝓧'`. -/
private def stochasticMatrices : Set (𝓧 → 𝓧' → ℝ) :=
  Set.univ.pi fun _ => Set.range fun w : StdSimplex ℝ 𝓧' => ⇑w.weights

/-- `garblingMap P` is the linear map sending a matrix `M` to
`(θ, x') ↦ ∑ₓ M x x' · (P θ {x}).toReal`, post-composition of `P` with `M`. -/
private noncomputable def garblingMap (P : Kernel Θ 𝓧) :
    (𝓧 → 𝓧' → ℝ) →ₗ[ℝ] (Θ → 𝓧' → ℝ) where
  toFun M := fun θ x' => ∑ x, M x x' * (P θ {x}).toReal
  map_add' M N := by ext θ x'; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    ext θ x'
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- The garbling polytope of `P` is the set of encodings of the Markov garblings `η ∘ₖ P`, the
image of the stochastic matrices under `garblingMap P`. -/
private noncomputable def garblingSet (P : Kernel Θ 𝓧) : Set (Θ → 𝓧' → ℝ) :=
  garblingMap (𝓧' := 𝓧') P '' stochasticMatrices

private theorem convex_garblingSet (P : Kernel Θ 𝓧) :
    Convex ℝ (garblingSet (𝓧' := 𝓧') P) :=
  (convex_pi fun _ _ => ConvexSpace.AffineMap.convex_range
    ⟨_, (IsAffineMap.linearMap Finsupp.lcoeFun).comp (StdSimplex.isAffineMap_weights ℝ 𝓧')⟩)
    |>.linear_image _

private theorem isCompact_garblingSet (P : Kernel Θ 𝓧) :
    IsCompact (garblingSet (𝓧' := 𝓧') P) :=
  (isCompact_univ_pi fun _ =>
    isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ 𝓧').continuous).image
    (garblingMap P).continuous_of_finiteDimensional

private theorem isClosed_garblingSet (P : Kernel Θ 𝓧) :
    IsClosed (garblingSet (𝓧' := 𝓧') P) :=
  (isCompact_garblingSet P).isClosed

/-- `encodeMatrix η` is the matrix `(x, x') ↦ (η x {x'}).toReal` of a kernel `η`. -/
private noncomputable def encodeMatrix (η : Kernel 𝓧 𝓧') : 𝓧 → 𝓧' → ℝ :=
  fun x x' => (η x {x'}).toReal

/-- Encoding sends kernel composition to the garbling map,
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

/-- Finite kernels with the same encoding are equal, since singleton masses determine them. -/
private theorem encode_injective {Q Q' : Kernel Θ 𝓧'}
    [IsFiniteKernel Q] [IsFiniteKernel Q'] (hQ : encode Q = encode Q') : Q = Q' := by
  refine Kernel.ext fun θ => Measure.ext_of_singleton fun x' => ?_
  have hx := congrFun (congrFun hQ θ) x'
  simp only [encode] at hx
  rwa [ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)] at hx

/-- `buildKernel M` is the kernel whose row at `x` has mass `ENNReal.ofReal (M x x')` at each
`x'`. -/
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

/-- A row of a stochastic matrix is a probability vector. -/
private theorem stochasticMatrices_row {M : 𝓧 → 𝓧' → ℝ} (hM : M ∈ stochasticMatrices)
    (x : 𝓧) : (∀ x', 0 ≤ M x x') ∧ ∑ x', M x x' = 1 := by
  have hx := Set.mem_univ_pi.mp hM x
  rw [StdSimplex.range_toFun_comp_weights] at hx
  exact ⟨fun x' => Set.mem_iInter.mp hx.1 x', hx.2⟩

private theorem isMarkovKernel_buildKernel {M : 𝓧 → 𝓧' → ℝ}
    (hM : M ∈ stochasticMatrices) : IsMarkovKernel (buildKernel M) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have hx := stochasticMatrices_row hM x
  show (∑ x' : 𝓧', ENNReal.ofReal (M x x') • Measure.dirac x') Set.univ = 1
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x' _ => hx.1 x', hx.2, ENNReal.ofReal_one]

private theorem encodeMatrix_buildKernel {M : 𝓧 → 𝓧' → ℝ}
    (hM : M ∈ stochasticMatrices) : encodeMatrix (buildKernel M) = M := by
  ext x x'
  show (buildKernel M x {x'}).toReal = M x x'
  rw [buildKernel_apply, ENNReal.toReal_ofReal ((stochasticMatrices_row hM x).1 x')]

/-- If `encode P'` lies in the garbling polytope of `P`, the kernel built from a witnessing
stochastic matrix shows that `P'` is a garbling of `P`. -/
private theorem isGarblingOf_of_encode_mem (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {P' : Kernel Θ 𝓧'} [IsMarkovKernel P'] (hmem : encode P' ∈ garblingSet P) :
    P'.IsGarblingOf P := by
  obtain ⟨M, hM, hMeq⟩ := hmem
  have := isMarkovKernel_buildKernel hM
  refine ⟨buildKernel M, inferInstance, encode_injective ?_⟩
  rw [encode_comp, encodeMatrix_buildKernel hM, hMeq]

/-- Each encoded singleton mass is nonnegative. -/
private theorem encode_nonneg (Q : Kernel Θ 𝓧') (θ : Θ) (x' : 𝓧') : 0 ≤ encode Q θ x' :=
  ENNReal.toReal_nonneg

/-- The encoded rows of a Markov kernel sum to one, so its whole encoding sums to
`Fintype.card Θ`. -/
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
  simp only [stochasticMatrices, Set.mem_univ_pi, StdSimplex.range_toFun_comp_weights,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, encodeMatrix]
  refine fun x => ⟨fun x' => ENNReal.toReal_nonneg, ?_⟩
  rw [← ENNReal.toReal_sum fun x' _ => measure_ne_top _ _, sum_measure_singleton,
    Finset.coe_univ, measure_univ, ENNReal.toReal_one]

/-- A continuous linear functional on `Θ → 𝓧' → ℝ` is the coordinate-weighted sum of its values
on the standard basis `Pi.single θ (Pi.single x' 1)`. -/
private theorem clm_apply_eq_sum_single [Fintype Θ] [DecidableEq Θ] [DecidableEq 𝓧']
    (f : (Θ → 𝓧' → ℝ) →L[ℝ] ℝ) (v : Θ → 𝓧' → ℝ) :
    f v = ∑ θ, ∑ x', v θ x' * f (Pi.single θ (Pi.single x' (1 : ℝ))) := by
  have hv : (∑ θ, ∑ x', v θ x' • (Pi.single θ (Pi.single x' (1 : ℝ)) : Θ → 𝓧' → ℝ)) = v := by
    funext θ₀ x'₀
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply, Pi.zero_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
  calc f v
      = f (∑ θ, ∑ x', v θ x' • (Pi.single θ (Pi.single x' (1 : ℝ)) : Θ → 𝓧' → ℝ)) := by rw [hv]
    _ = ∑ θ, ∑ x', v θ x' * f (Pi.single θ (Pi.single x' (1 : ℝ))) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [map_sum]
        exact Finset.sum_congr rfl fun x' _ => by rw [map_smul, smul_eq_mul]

/-- Under the uniform prior on `Θ`, the average risk of the experiment `Q` at the identity
estimator with the nonnegative affine loss `(θ, x') ↦ a θ x' + C` is `ENNReal.ofReal` of a
nonnegative real double sum. -/
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

/-- If `P` has Bayes risk at most that of `P'` under the uniform prior for every everywhere-finite
loss, then `P'` is a garbling of `P`. -/
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
    -- The Bayes risk of `Q` at the identity estimator is `ofReal ((card Θ)⁻¹ · f (encode Q) + C)`.
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
      have := hκ
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

/-- On finite spaces with `Θ` nonempty, if `P` Blackwell-dominates `P'` and both are Markov
kernels, then `P'` is a garbling of `P`.

Each hypothesis is needed. With `Θ` empty every Bayes risk is `0`, yet no Markov kernel maps a
nonempty `𝓧` to an empty `𝓧'`. The zero kernel has Bayes risk `0` for every loss and so
dominates every `P'`, yet `η ∘ₖ 0 = 0`. Over a one-point sample space `P' = 2 • P` has twice the
Bayes risk of `P` for every loss, yet is no Markov garbling of `P`. Dominance in a single
decision problem does not force garbling either. -/
theorem isGarblingOf_of_blackwellDominates
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧'] [Nonempty Θ]
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} [IsMarkovKernel P] [IsMarkovKernel P']
    (h : P.BlackwellDominates P') :
    P'.IsGarblingOf P :=
  isGarblingOf_of_bayesRisk_uniform_le fun ℓ _ => h ℓ _

/-- On finite spaces with `Θ` nonempty and Markov `P` and `P'`, `P'` is a garbling of `P`
exactly when `P` Blackwell-dominates `P'`. -/
theorem isGarblingOf_iff_blackwellDominates
    [Fintype Θ] [Fintype 𝓧] [Fintype 𝓧'] [Nonempty Θ]
    [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓧']
    {P : Kernel Θ 𝓧} {P' : Kernel Θ 𝓧'} [IsMarkovKernel P] [IsMarkovKernel P'] :
    P'.IsGarblingOf P ↔ P.BlackwellDominates P' :=
  ⟨blackwellDominates_of_isGarblingOf, isGarblingOf_of_blackwellDominates⟩

/-! ### Deterministic experiments: partitions as kernels

A deterministic classifier `f : Θ → 𝓧` is the experiment `Kernel.deterministic f hf`, an
error-free observation of the cell of `θ` in the partition of `Θ` into the fibers of `f`.
Between deterministic experiments the garbling order is functional factoring, which
`Core.Probability.Decision.Duality` uses to read the converse as [van-rooy-2003]'s comparison
of partition questions. -/

/-- `deterministic g` is a garbling of `deterministic f` exactly when `g` factors through `f`;
randomized post-processing gains nothing between deterministic experiments. -/
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
      have he := congrArg (fun μ : Measure 𝓨 ↦ μ {g θ}) h12
      rw [Measure.dirac_apply' _ (measurableSet_singleton _),
        Measure.dirac_apply' _ (measurableSet_singleton _)] at he
      simp [Ne.symm hne] at he
    exact ⟨Function.extend f g (fun _ ↦ Classical.arbitrary 𝓨),
      (hft.extend_comp _).symm⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨Kernel.deterministic ψ (measurable_of_countable ψ), inferInstance,
      (Kernel.deterministic_comp_deterministic hf (measurable_of_countable ψ)).symm⟩

end ProbabilityTheory
