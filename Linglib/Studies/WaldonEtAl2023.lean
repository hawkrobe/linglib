import Linglib.Semantics.Degree.Aggregation
import Linglib.Data.Examples.WaldonEtAl2023
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Waldon, Condoravdi, Levin & Degen (2023): On the Context Dependence of Artifact Noun Interpretation

This file formalizes [waldon-etal-2023]'s account of how a policy goal shapes the boundary of an
artifact noun category, *no electronic devices are allowed in the theater* read with the goal of
limiting light or of limiting noise. Following [sassoon-fadlon-2017], an artifact noun denotes
an additive, weighted, multi-dimensional measure (2), whereas a natural kind composes its
dimensions multiplicatively (3), so that one failed dimension excludes an entity from the kind
but not from the artifact category. The proposal (8) makes the dimensions and their weights
contextual: an explicit goal weights the context-independent category measure by `γ` and the
goal-relevant feature by `1 − γ` (13), and with no goal stated the goal weight is split by the
goals' plausibility (14) (`Norming`, `measure`). The interpreter's posterior that an object is
prohibited (12), under the paper's simplifying assumptions of a uniform threshold on `[0, 1]`
and an even prior, is the measure itself (`prohibitionPosterior_eq`). The Goal Insensitive
hypothesis is `γ = 1`, under which no condition moves any object; under Goal Sensitivity an
object's prohibition orders across explicit goals by its goal-relevant features, and one goal
raises an object above the neutral baseline while lowering another, which no single shift of
the standard of comparison can do (`not_threshold_shift`). The experiment's Bayesian data
analysis estimates `γ` at about 0.76, with 1 outside the credible interval.

## Implementation notes

Objects and goals are types, and the category, feature and plausibility measures of the
norming studies are the fields of `Norming`, bounded as the slider scales are, in place of
values retyped from the paper; every prediction is stated over them and over `γ`. The
posterior is the Bayes ratio with the threshold marginalized by Lebesgue measure on `[0, m]`.
The paper's examples are the rows of `Data.Examples.WaldonEtAl2023`.

## References

* [waldon-etal-2023]
* [sassoon-fadlon-2017]
* [kennedy-2007]
* [lassiter-goodman-2017]
-/

open Degree.Aggregation MeasureTheory
open scoped ENNReal

namespace WaldonEtAl2023

variable {O G : Type*} [Fintype G]

/-! ### The norming data and the contextual measure -/

/-- The measures the norming studies supply (§3.1): the category-membership measure `cat`, the
goal-relevant feature measures, on the unit interval, and the plausibility of the goals, a
distribution. -/
structure Norming (O G : Type*) [Fintype G] where
  cat : O → ℝ
  feature : G → O → ℝ
  plausibility : G → ℝ
  cat_mem : ∀ o, cat o ∈ Set.Icc 0 1
  feature_mem : ∀ g o, feature g o ∈ Set.Icc 0 1
  plausibility_nonneg : ∀ g, 0 ≤ plausibility g
  plausibility_sum : ∑ g, plausibility g = 1

/-- An experimental condition: no goal stated, or an explicit policy goal. -/
inductive Condition (G : Type*)
  | neutral
  | explicit (g : G)

variable (N : Norming O G) (γ : ℝ)

/-- The goal-weighted measure of the artifact noun, (13) under an explicit goal and (14) with
the goal weight split by plausibility: a `weightedScore` over the category and the goal
dimensions. -/
noncomputable def measure : Condition G → O → ℝ
  | .explicit g => weightedScore [γ, 1 - γ] [N.cat, N.feature g]
  | .neutral => λ o => γ * N.cat o + (1 - γ) * ∑ g, N.plausibility g * N.feature g o

theorem measure_explicit (g : G) (o : O) :
    measure N γ (.explicit g) o = γ * N.cat o + (1 - γ) * N.feature g o := by
  simp [measure, weightedScore]

/-- The plausibility-weighted feature lies on the unit interval. -/
theorem mix_mem_Icc (o : O) : ∑ g, N.plausibility g * N.feature g o ∈ Set.Icc 0 1 :=
  ⟨Finset.sum_nonneg λ g _ => mul_nonneg (N.plausibility_nonneg g) (N.feature_mem g o).1,
    (Finset.sum_le_sum λ g _ => mul_le_of_le_one_right (N.plausibility_nonneg g)
      (N.feature_mem g o).2).trans_eq N.plausibility_sum⟩

/-- For `γ` on the unit interval the measure lies on the unit interval, as the threshold reads
it. -/
theorem measure_mem_Icc (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (c : Condition G) (o : O) :
    measure N γ c o ∈ Set.Icc 0 1 := by
  have hc := N.cat_mem o
  rcases c with _ | g
  · have hm := mix_mem_Icc N o
    simp only [measure, Set.mem_Icc] at *
    constructor <;> nlinarith
  · have hf := N.feature_mem g o
    rw [measure_explicit]
    simp only [Set.mem_Icc] at *
    constructor <;> nlinarith

/-! ### The interpretive model (12) -/

/-- The probability that a measure meets a standard uniform on the unit interval: the Lebesgue
mass of `[0, m]`. -/
noncomputable def meetsProb (m : ℝ) : ℝ≥0∞ := volume (Set.Icc (0 : ℝ) m)

theorem meetsProb_eq (m : ℝ) : meetsProb m = ENNReal.ofReal m := by
  rw [meetsProb, Real.volume_Icc, sub_zero]

/-- The posterior that an object of measure `m` is prohibited: the Bayes ratio of (12) with an
even prior and the threshold marginalized. -/
noncomputable def prohibitionPosterior (m : ℝ) : ℝ≥0∞ :=
  2⁻¹ * meetsProb m / (2⁻¹ * meetsProb m + 2⁻¹ * (1 - meetsProb m))

/-- The posterior is the measure. -/
theorem prohibitionPosterior_eq {m : ℝ} (hm1 : m ≤ 1) :
    prohibitionPosterior m = ENNReal.ofReal m := by
  have h1 : meetsProb m ≤ 1 := by
    rw [meetsProb_eq, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hm1
  rw [prohibitionPosterior, ← mul_add, add_tsub_cancel_of_le h1, mul_one, meetsProb_eq,
    ENNReal.mul_div_right_comm, ENNReal.div_self (by norm_num) (by norm_num), one_mul]

/-- Every prediction is a comparison of measures. -/
theorem prohibitionPosterior_lt_iff {m m' : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hm0' : 0 ≤ m')
    (hm1' : m' ≤ 1) : prohibitionPosterior m < prohibitionPosterior m' ↔ m < m' := by
  rw [prohibitionPosterior_eq hm1, prohibitionPosterior_eq hm1',
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hm0]

/-! ### Goal sensitivity (§4.3) -/

/-- The Goal Insensitive hypothesis, `γ = 1`: no condition moves any object. -/
theorem measure_one (c c' : Condition G) (o : O) : measure N 1 c o = measure N 1 c' o := by
  rcases c with _ | g <;> rcases c' with _ | g' <;> simp [measure, weightedScore]

/-- Under Goal Sensitivity, an object's measure across explicit goals orders by its
goal-relevant features. -/
theorem measure_explicit_lt (hγ : γ < 1) {g g' : G} {o : O}
    (h : N.feature g o < N.feature g' o) :
    measure N γ (.explicit g) o < measure N γ (.explicit g') o := by
  rw [measure_explicit, measure_explicit]
  nlinarith

/-- An explicit goal moves an object away from the neutral baseline by the goal weight times
the excess of the goal's feature over the plausibility-weighted mix. -/
theorem measure_explicit_sub_neutral (g : G) (o : O) :
    measure N γ (.explicit g) o - measure N γ .neutral o =
      (1 - γ) * (N.feature g o - ∑ g', N.plausibility g' * N.feature g' o) := by
  rw [measure_explicit]
  simp only [measure]
  ring

/-- Bidirectionality: under Goal Sensitivity one goal raises an object whose feature exceeds
the mix and lowers one whose feature falls short of it, the flashlight and the boombox under
the goal of limiting light. -/
theorem measure_bidirectional (hγ : γ < 1) {g : G} {o o' : O}
    (ho : ∑ g', N.plausibility g' * N.feature g' o < N.feature g o)
    (ho' : N.feature g o' < ∑ g', N.plausibility g' * N.feature g' o') :
    measure N γ .neutral o < measure N γ (.explicit g) o ∧
      measure N γ (.explicit g) o' < measure N γ .neutral o' := by
  constructor
  · have := measure_explicit_sub_neutral N γ g o
    nlinarith
  · have := measure_explicit_sub_neutral N γ g o'
    nlinarith

/-- No single shift of the standard of comparison is bidirectional: with one measure and two
thresholds, an object included under the second but not the first and another included under
the first but not the second cannot both exist. -/
theorem not_threshold_shift (m : O → ℝ) (θ θ' : ℝ) (o o' : O) :
    ¬ ((m o < θ ∧ θ' ≤ m o) ∧ (θ ≤ m o' ∧ m o' < θ')) :=
  λ ⟨⟨h1, h2⟩, h3, h4⟩ => by linarith

end WaldonEtAl2023
