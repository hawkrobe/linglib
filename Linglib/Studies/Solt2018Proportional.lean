import Linglib.Semantics.Degree.Aggregation
import Linglib.Semantics.Degree.Measure.Basic
import Linglib.Semantics.Genericity.SortedOntology
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum

/-!
# [solt-2018-proportional]: Proportional comparatives and relative scales

*More residents of Ithaca than New York City know their neighbors* has a
salient TRUE reading even though the absolute counts point the other way:
the salient interpretation compares **proportions**, which standard degree
analyses of the comparative ([von-stechow-1984] a.o.) do not deliver.
[solt-2018-proportional] compares two accounts:

1. **Ambiguity** ([partee-1989]; degree-based entries from [romero-2015],
   Solt's eq. 7): *many* and *few* are lexically ambiguous between a cardinal
   entry `λd λP λQ. |P ∩ Q| ≽ d` and a proportional entry
   `λd λP λQ. |P ∩ Q| / |P| ≽ d`.
2. **Measurement-based** (Solt's preferred analysis): *many*/*few* are
   unambiguous degree predicates; a null `Meas` head introduces a
   context-dependent measure function, which may be **domain-restricted**
   (eq. 20) or specifically **proportional** (eq. 21):
   `μ^c_{DIM-prop;x}(y) = μ^c_DIM(y) / μ^c_DIM(x)`, with range [0, 1].

The adjudicating evidence (Solt §4) is the distribution of readings: with an
individual-level predicate the *positive* form gets only the proportional
reading, while the *comparative* keeps both (`licensedReadings`,
`comparative_keeps_cardinal`) — an asymmetry the ambiguity account cannot
derive.

Solt's eq. (21) is an instance of `spatialNormalizedScore`
(`Semantics/Degree/Aggregation.lean`) with a single unit-weighted measure and
constant denominator `μ_DIM(totality)`; the monotonicity constraint on measure
functions (Solt's eq. 18, after [schwarzschild-2006]) is the substrate's
`Degree.admissibleMeasure`.

## Main declarations

- `proportionalMeasure`: Solt's eq. (21) proportional measure function
- `cardinal_proportional_divergence`: the headline example's two readings come
  apart — cardinal FALSE, proportional TRUE
- `licensedReadings`, `comparative_keeps_cardinal`: Solt §4's distribution of
  readings over predicate level × positive/comparative form
- `proportionalMeasure_monotonic`, `proportionalMeasure_mem_unit_interval`,
  `proportionalMeasure_scale_invariant`: eq. (21) is a normalized monotone
  measure — the discrete analogue of conditional measure

Solt's other 2018 paper, the multidimensionality chapter
[solt-2018-multidim], shares this paper's scale foundation; see
`Studies/Solt2018Multidim.lean`.
-/

namespace Solt2018Proportional

open Degree (admissibleMeasure)
open Degree.Aggregation (spatialNormalizedScore spatialNormalizedScore_zero
  spatialNormalizedScore_le_one spatialNormalizedScore_nonneg weightedScore)
open Semantics.Kinds.SortedOntology (PredicateLevel)

/-! ### The proportional measure function -/

variable {α : Type*} (μ : α → ℚ)

/-- Solt's eq. (21): the proportional measure function for a dimension
    measured by `μ`, relative to totality `tot`, applied to part `y`; returns
    `μ(y) / μ(tot)`, and 0 when the totality has zero measure (the
    `spatialNormalizedScore` zero-extent convention). -/
def proportionalMeasure (tot y : α) : ℚ :=
  spatialNormalizedScore [1] [μ] (λ _ => μ tot) y

/-- `proportionalMeasure` computed: `μ(y) / μ(tot)` when `μ(tot) ≠ 0`. -/
theorem proportionalMeasure_eq (tot y : α) (h : μ tot ≠ 0) :
    proportionalMeasure μ tot y = μ y / μ tot := by
  simp [proportionalMeasure, spatialNormalizedScore, weightedScore, h]

/-- A zero-measure totality (empty domain) yields proportion 0. -/
theorem proportionalMeasure_zero (tot y : α) (h : μ tot = 0) :
    proportionalMeasure μ tot y = 0 :=
  spatialNormalizedScore_zero _ _ _ _ h

/-! ### The proportional-comparative puzzle

Solt's example (1), *More residents of Ithaca than New York City know their
neighbors*: Ithaca's population is dwarfed by NYC's, so the absolute count of
Ithaca residents who know their neighbors is smaller, yet the sentence has a
salient TRUE reading comparing proportions. Counts below are illustrative —
the paper reports populations only in prose. -/

/-- A city with a total resident count and a count of residents who know
    their neighbors. -/
structure City where
  population : ℚ
  knowsNeighbors : ℚ
  popPos : 0 < population
  subBounded : knowsNeighbors ≤ population

/-- The two salient resident pluralities of a city: the residents who know
    their neighbors, and the totality. -/
inductive Residents | knowers | all

/-- The cardinality measure on a city's resident pluralities (Solt's `μ_#`). -/
def City.card (c : City) : Residents → ℚ
  | .knowers => c.knowsNeighbors
  | .all => c.population

/-- Ithaca: small population, high proportion know their neighbors. -/
def ithaca : City where
  population := 30000
  knowsNeighbors := 24000
  popPos := by norm_num
  subBounded := by norm_num

/-- New York City: huge population, low proportion know their neighbors. -/
def nyc : City where
  population := 8000000
  knowsNeighbors := 800000
  popPos := by norm_num
  subBounded := by norm_num

/-- Cardinal reading of (1): FALSE — in absolute terms more NYC residents
    know their neighbors. -/
theorem cardinal_reading_ithaca_lt_nyc :
    ithaca.card .knowers < nyc.card .knowers := by
  norm_num [City.card, ithaca, nyc]

/-- Proportional reading of (1): TRUE — the proportion of Ithaca residents
    who know their neighbors exceeds NYC's, via `proportionalMeasure` with
    the cardinality measure `City.card`. -/
theorem proportional_reading_ithaca_gt_nyc :
    proportionalMeasure nyc.card .all .knowers <
      proportionalMeasure ithaca.card .all .knowers := by
  rw [proportionalMeasure_eq nyc.card .all .knowers (by norm_num [City.card, nyc]),
      proportionalMeasure_eq ithaca.card .all .knowers (by norm_num [City.card, ithaca])]
  norm_num [City.card, ithaca, nyc]

/-- The two readings of (1) diverge: cardinal FALSE, proportional TRUE.
    Solt's measurement-based account derives both from one `Meas` head
    instantiated with different measure-function varieties. -/
theorem cardinal_proportional_divergence :
    ithaca.card .knowers < nyc.card .knowers ∧
      proportionalMeasure nyc.card .all .knowers <
        proportionalMeasure ithaca.card .all .knowers :=
  ⟨cardinal_reading_ithaca_lt_nyc, proportional_reading_ithaca_gt_nyc⟩

/-! ### Distribution of cardinal vs proportional readings

Solt §4 (pp. 1135–1136): with an individual-level predicate
([carlson-1977]; [milsark-1977], [partee-1989] for the *many*/*few*
observation), the `Meas` head is necessarily domain-restricted, and the
standard range introduced by POS sits inside the bounded segment
[0, μ(totality)] of the scale — so the *positive* form is necessarily
proportional (Solt's diagram 23). The *comparative* composes with `-er`
rather than POS, so an ordinary (non-proportional) domain-restricted measure
still yields its cardinal reading: both readings survive. Solt's examples
(35) vs (36) diagnose the positive restriction; her (1)–(2) — individual-level
comparatives with available false cardinal readings — witness the comparative's
freedom. The ambiguity account cannot derive this asymmetry: if only
proportional *many* combines with individual-level predicates, the comparative
should lose its cardinal reading too. -/

/-- Cardinal vs proportional reading of a quantity word. -/
inductive Reading | cardinal | proportional
  deriving DecidableEq

/-- Positive (bare, POS-bound) vs comparative (`-er`) form of *many*/*few*. -/
inductive QForm | positive | comparative

/-- Solt §4's distribution of readings by predicate level and form: the
    positive form loses its cardinal reading under an individual-level
    predicate; the comparative never does. -/
def licensedReadings : PredicateLevel → QForm → List Reading
  | .stageLevel, _ => [.cardinal, .proportional]
  | .individualLevel, .positive => [.proportional]
  | .individualLevel, .comparative => [.cardinal, .proportional]

/-- Stage-level predicates license both readings of both forms —
    Solt's (35), *few egg-laying mammals were found in our survey*. -/
theorem stage_level_both_readings (f : QForm) :
    Reading.cardinal ∈ licensedReadings .stageLevel f ∧
      Reading.proportional ∈ licensedReadings .stageLevel f := by
  cases f <;> exact ⟨by decide, by decide⟩

/-- The positive form is proportional-only under an individual-level
    predicate — Solt's (36), *#few egg-laying mammals suckle their young,
    perhaps because there are few*. -/
theorem positive_individual_only_proportional :
    licensedReadings .individualLevel .positive = [.proportional] := rfl

/-- The §4 asymmetry that adjudicates between the accounts: exactly where
    the positive form loses the cardinal reading, the comparative keeps it
    (Solt's (1)–(2) retain false cardinal readings). -/
theorem comparative_keeps_cardinal :
    Reading.cardinal ∈ licensedReadings .individualLevel .comparative ∧
      Reading.cardinal ∉ licensedReadings .individualLevel .positive := by
  exact ⟨by decide, by decide⟩

/-! ### Structural properties: a normalized monotone measure

With a monotonic measure (Solt's eq. 18 constraint = `admissibleMeasure`,
after [schwarzschild-2006]), `proportionalMeasure` is bounded in [0, 1],
saturates at the totality, preserves the part order, and is invariant under
rescaling of the underlying measure — a normalized monotone measure, the
discrete analogue of conditional measure. -/

/-- The proportion of the totality in itself is 1: saturation. -/
theorem proportionalMeasure_self_eq_one (tot : α) (htot : 0 < μ tot) :
    proportionalMeasure μ tot tot = 1 := by
  rw [proportionalMeasure_eq _ _ _ htot.ne']
  exact div_self htot.ne'

/-- Solt's eq. (18) monotonicity constraint is preserved by the eq. (21)
    construction: an `admissibleMeasure` yields a strictly monotone
    proportion whenever the totality has positive measure. -/
theorem proportionalMeasure_monotonic [Preorder α] (hμ : admissibleMeasure μ)
    (tot : α) {y z : α} (htot : 0 < μ tot) (hyz : y < z) :
    proportionalMeasure μ tot y < proportionalMeasure μ tot z := by
  rw [proportionalMeasure_eq _ _ _ htot.ne', proportionalMeasure_eq _ _ _ htot.ne']
  exact (div_lt_div_iff_of_pos_right htot).mpr (hμ hyz)

/-- The proportional measure is nonnegative when the underlying measure is. -/
theorem proportionalMeasure_nonneg (hnn : ∀ x, 0 ≤ μ x) (tot y : α) :
    0 ≤ proportionalMeasure μ tot y :=
  spatialNormalizedScore_nonneg _ _ _ _
    (by simpa [weightedScore] using hnn y) (hnn tot)

/-- The proportional measure of a part of the totality is at most 1. -/
theorem proportionalMeasure_le_one [Preorder α] (hμ : Monotone μ)
    (tot y : α) (hy : y ≤ tot) (htot : 0 < μ tot) :
    proportionalMeasure μ tot y ≤ 1 :=
  spatialNormalizedScore_le_one _ _ _ _
    (by simpa [weightedScore] using hμ hy) htot

/-- Probability-style range: for a monotone nonnegative measure and a part
    `y ≤ tot` with `0 < μ(tot)`, the proportion lies in the unit interval. -/
theorem proportionalMeasure_mem_unit_interval [Preorder α]
    (hnn : ∀ x, 0 ≤ μ x) (hμ : Monotone μ) (tot y : α) (hy : y ≤ tot)
    (htot : 0 < μ tot) :
    proportionalMeasure μ tot y ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨proportionalMeasure_nonneg μ hnn tot y,
   proportionalMeasure_le_one μ hμ tot y hy htot⟩

/-- Scale invariance: rescaling the measure by a nonzero constant leaves the
    proportion unchanged — the proportional reading of (1) does not depend on
    the unit of counting, only the cardinal reading does. -/
theorem proportionalMeasure_scale_invariant (k : ℚ) (hk : k ≠ 0)
    (tot y : α) (htot : μ tot ≠ 0) :
    proportionalMeasure (λ x => k * μ x) tot y = proportionalMeasure μ tot y := by
  rw [proportionalMeasure_eq _ tot y (mul_ne_zero hk htot),
      proportionalMeasure_eq _ tot y htot, mul_div_mul_left _ _ hk]

end Solt2018Proportional
