import Linglib.Semantics.Degree.Aggregation
import Linglib.Semantics.Degree.Discrete
import Linglib.Semantics.Kinds.SortedOntology
import Linglib.Core.Order.Boundedness
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Basic

/-!
# [solt-2018-proportional]

Stephanie Solt (2018). Proportional comparatives and relative scales.
*Proceedings of Sinn und Bedeutung 21*, 1123–1140.

## Puzzle (§1)

Sentences like (1) have a salient TRUE reading despite the absolute
counts pointing the other way:

> (1)  More residents of Ithaca than New York City know their neighbors.

Ithaca's population (~30,000) is dwarfed by NYC's (~8M), so the
absolute number of Ithaca residents who know their neighbors is
smaller. The salient interpretation compares **proportions**, not
absolute counts. The puzzle for degree semantics: standard `more`
analyses (Cresswell 1977, von Stechow 1984, Heim 1985, Kennedy 1997)
return the absolute reading.

## Two accounts (§2)

Solt compares two strategies:

1. **Ambiguity account** (Partee 1989, Romero 2015): *many*/*few* are
   lexically ambiguous between cardinal and proportional entries —
   `[[many_CARD]] = λdλPλQ.|P∩Q| ≽ d` vs
   `[[many_PROP]] = λdλPλQ.|P∩Q|/|P| ≽ d` (Solt eq. 7).

2. **Measurement-based** (Solt's preferred analysis): a single
   underspecified `Meas` head introduces a context-dependent measure
   function, which can be a **domain-restricted** measure function
   (eq. 20) or a **proportional** measure function (eq. 21):

       μ^c_{DIM-prop;x}(y) = μ^c_DIM(y) / μ^c_DIM(x)

The proportional measure function is the central new substrate. It maps
parts of an entity to values encoding the **proportion** they represent
of the totality.

## Relation to substrate

Solt's eq. (21) is exactly an instance of `spatialNormalizedScore` in
`Semantics/Degree/Aggregation.lean §2`: the numerator is a
weighted sum (with `weights = [1]` and one measure function) and the
denominator is `μ_DIM(totality)`. Solt 2018 (this paper) and
[tham-2025] are the two consumers of `spatialNormalizedScore` —
this file establishes the substrate's second-consumer status.

## Relation to [solt-2018] (the multidimensionality chapter)

Solt's other 2018 paper — the Springer chapter "Multidimensionality,
subjectivity and scales: experimental evidence" — develops the
**scale ⟨D, ≻, DIM⟩** triple (eq. 33) that this paper also uses
(eq. 15). Tham 2025 §5.2 builds on the multidim chapter for the
multidimensional adjective representation; this file builds on the SuB
paper for the proportional measurement substrate. Both papers share the
same scalar foundation.

## File organization

- §1 Background data: the proportional comparative puzzle
- §2 Two accounts of proportional comparatives
  - §2.1 Ambiguity account (Partee/Romero entries)
  - §2.2 Measurement-based account (Solt's `Meas` + measure functions)
- §3 The proportional measure function (eq. 21) — substrate consumer
- §4 Distribution of cardinal vs proportional readings
- §5 Cross-paper engagement (Tham 2025, multidim chapter)
- §6 Mathlib-style structural properties (proportional measure as a
     normalized monotone measure: bounded in `[0, 1]`, saturates at
     totality, scale-invariant under measure rescaling)
-/

namespace Solt2018Proportional

open Degree.Aggregation (spatialNormalizedScore
  spatialNormalizedScore_unit spatialNormalizedScore_le_one
  spatialNormalizedScore_nonneg weightedScore)
open Semantics.Kinds.SortedOntology (PredicateLevel)

-- ════════════════════════════════════════════════════
-- § 1. The proportional-comparative puzzle
-- ════════════════════════════════════════════════════

/-- A city with a total population and a count of residents satisfying
    the predicate (e.g. *know their neighbors*). -/
structure City where
  name : String
  population : ℚ
  knowsNeighbors : ℚ
  /-- Population must be positive for proportional measurement to be
      meaningful (denominator nonzero). -/
  popPos : 0 < population
  /-- The subset count is bounded by the total. -/
  subBounded : knowsNeighbors ≤ population
  deriving Repr

/-- Ithaca: small population, high proportion know their neighbors. -/
def ithaca : City where
  name := "Ithaca"
  population := 30000
  knowsNeighbors := 24000   -- 80%
  popPos := by norm_num
  subBounded := by norm_num

/-- New York City: huge population, low proportion know their neighbors. -/
def nyc : City where
  name := "NYC"
  population := 8000000
  knowsNeighbors := 800000  -- 10%
  popPos := by norm_num
  subBounded := by norm_num

/-- Cardinal comparison: NYC has more knowing-neighbors residents in
    absolute terms. The "obvious" reading of (1) is FALSE. -/
theorem cardinal_reading_ithaca_lt_nyc :
    ithaca.knowsNeighbors < nyc.knowsNeighbors := by
  show (24000 : ℚ) < 800000; norm_num

-- ════════════════════════════════════════════════════
-- § 2. Two accounts
-- ════════════════════════════════════════════════════

/-! ### §2.1 Ambiguity account ([partee-1989], [romero-2015])

  Solt eq. (7): *many* is two lexical entries.

  - `[[many_CARD]] = λdλPλQ.|P ∩ Q| ≽ d`
  - `[[many_PROP]] = λdλPλQ.|P ∩ Q| / |P| ≽ d`

  The proportional entry has the normalization built into the lexical
  semantics. Comparatives derive from `[[-er]] = λIλJ.max(J) ≻ max(I)`.

  Solt critiques this account on §4 grounds (distribution of cardinal
  vs proportional readings) and §3 grounds (*n percent* requires a
  separate proportional entry). -/

/-- Cardinal entry of *many* (Solt eq. 7a, simplified to a Bool
    threshold check on a pair of natural-number cardinalities). -/
def manyCard (threshold : ℚ) (pAndQ : ℚ) (_p : ℚ) : Bool :=
  decide (pAndQ ≥ threshold)

/-- Proportional entry of *many* (Solt eq. 7b). Returns false when the
    domain is empty (denominator zero) — convention matches
    `spatialNormalizedScore`. -/
def manyProp (threshold : ℚ) (pAndQ : ℚ) (p : ℚ) : Bool :=
  if p = 0 then false else decide (pAndQ / p ≥ threshold)

/-! ### §2.2 Measurement-based account

  Solt's preferred analysis: *many*/*few* have unambiguous degree-
  predicate semantics; a null `Meas` head introduces an underspecified
  measure function `μ^c_DIM`. The measure function can be:

  - **Unrestricted** (eq. 17, Fig. 1a): `μ_DIM : D_e → S_DIM`
  - **Domain-restricted** (eq. 20, Fig. 1b): `μ_DIM;x : {y | y ⊑ x} → S_DIM`
  - **Proportional** (eq. 21, Fig. 1c): `μ_DIM-prop;x(y) = μ_DIM(y) / μ_DIM(x)`,
    range [0, 1]

  All three satisfy the **monotonicity constraint** (eq. 18):
  `∀ x, y. x ⊑ y → μ_DIM(x) ≺ μ_DIM(y)` — measure functions are
  monotonic on the part-whole relation [schwarzschild-2006]. -/

/-- A scale [solt-2018-proportional] eq. (15) (= [solt-2018]
    eq. 33). Solt writes `S = ⟨D, ≻, DIM⟩` with `D` a set of degrees,
    `≻` an ordering on D, and `DIM` a dimension of measurement. The
    Lean structure is named `SoltScale` to avoid shadowing mathlib's
    `Scale`; for present purposes the dimension is just a string label
    and `D = ℚ`, `≻ = <` are monomorphized from the worked examples.

    TODO: when `Solt2018Multidim.lean` (the Springer chapter) lands
    or another consumer needs the multi-scale-per-dimension structure
    Solt motivates (inches vs cm for the height dimension), promote
    to `structure SoltScale (D : Type) [LinearOrder D]` carrying the
    `(D, <)` pair explicitly. -/
structure SoltScale where
  /-- Dimension label (e.g. "cardinality", "volume", "intelligence"). -/
  dimension : String
  deriving Repr, BEq

/-- Cardinality scale (the most common dimension for *many*-comparatives). -/
def cardinalityScale : SoltScale := { dimension := "cardinality" }

/-- A measure function for a given α maps individuals to ℚ degrees. -/
abbrev DimensionedMeasure (α : Type) := α → ℚ

/-- Solt eq. (18) Monotonicity constraint: if `x ⊑ y` then
    `μ(x) ≺ μ(y)`. Stated relative to a part-whole relation `subPart`. -/
def Monotonic {α : Type} (μ : DimensionedMeasure α) (subPart : α → α → Prop) : Prop :=
  ∀ x y, subPart x y → μ x < μ y

-- ════════════════════════════════════════════════════
-- § 3. The proportional measure function (eq. 21)
-- ════════════════════════════════════════════════════

/-! Solt's eq. (21) is the headline contribution: a measure function
    whose range is `[0, 1]` and whose value at `y ⊑ x` encodes the
    proportion `y` represents of the totality `x` along dimension DIM.

    This is exactly `spatialNormalizedScore [1] [μ_DIM]
    (fun _ => μ_DIM totality)`, which is why the Tham 2025 substrate
    earns its second consumer here. The single measure function in the
    weighted-sum slot recovers Solt's single-dimension proportional
    measure; Tham's eq. 47b uses the same substrate with a list of
    dimension measures and dimension-specific weights. -/

/-- Solt eq. (21): the proportional measure function for dimension DIM
    relative to totality `tot`, applied to part `y`. Returns
    `μ_DIM(y) / μ_DIM(tot)`. -/
def proportionalMeasure {α : Type} (μ_DIM : DimensionedMeasure α)
    (tot : α) (y : α) : ℚ :=
  spatialNormalizedScore [1] [μ_DIM] (fun _ => μ_DIM tot) y

/-- Solt eq. (21) computed: `μ_DIM(y) / μ_DIM(tot)` (when `μ_DIM(tot) ≠ 0`). -/
theorem proportionalMeasure_eq {α : Type} (μ_DIM : DimensionedMeasure α)
    (tot y : α) (h : μ_DIM tot ≠ 0) :
    proportionalMeasure μ_DIM tot y = μ_DIM y / μ_DIM tot := by
  show spatialNormalizedScore [1] [μ_DIM] (fun _ => μ_DIM tot) y =
    μ_DIM y / μ_DIM tot
  unfold spatialNormalizedScore
  show (if μ_DIM tot = 0 then 0 else weightedScore [1] [μ_DIM] y / μ_DIM tot) =
    μ_DIM y / μ_DIM tot
  rw [if_neg h]
  congr 1
  unfold weightedScore
  show ((0 : ℚ) + 1 * μ_DIM y) = μ_DIM y
  ring

/-- Edge case: when the totality has zero measure (empty domain), the
    proportional measure returns 0. Matches the
    `spatialNormalizedScore` zero-extent convention. -/
theorem proportionalMeasure_zero {α : Type} (μ_DIM : DimensionedMeasure α)
    (tot y : α) (h : μ_DIM tot = 0) :
    proportionalMeasure μ_DIM tot y = 0 := by
  show spatialNormalizedScore [1] [μ_DIM] (fun _ => μ_DIM tot) y = 0
  unfold spatialNormalizedScore
  show (if μ_DIM tot = 0 then 0 else weightedScore [1] [μ_DIM] y / μ_DIM tot) = 0
  rw [if_pos h]

/-- Cardinality measure function on cities: maps a city to its
    population (the totality measure). -/
def cityPop (c : City) : ℚ := c.population

/-- The "knows neighbors" subset measure function on cities. -/
def cityKnows (c : City) : ℚ := c.knowsNeighbors

/-- Sanity check: `cityKnows ithaca / cityKnows ithaca = 1` as a
    `proportionalMeasure` evaluation. -/
theorem ithaca_self_proportion_eq_one :
    proportionalMeasure cityKnows ithaca ithaca = 1 := by
  rw [proportionalMeasure_eq]
  · show (24000 : ℚ) / 24000 = 1; norm_num
  · show (24000 : ℚ) ≠ 0; norm_num

/-- The proportional reading of (1): proportion of Ithaca residents who
    know their neighbors EXCEEDS the proportion of NYC residents who do.
    This is the salient TRUE reading despite (cardinal_reading_ithaca_lt_nyc). -/
theorem proportional_reading_ithaca_gt_nyc :
    (ithaca.knowsNeighbors / ithaca.population) >
    (nyc.knowsNeighbors / nyc.population) := by
  show (24000 : ℚ) / 30000 > 800000 / 8000000
  norm_num

/-- Headline: cardinal and proportional readings DIVERGE for (1). The
    cardinal reading is false; the proportional reading is true. Solt's
    measurement-based account predicts both via the same `Meas` head
    instantiated with different measure-function types. -/
theorem cardinal_proportional_divergence :
    ithaca.knowsNeighbors < nyc.knowsNeighbors ∧
    (ithaca.knowsNeighbors / ithaca.population) >
      (nyc.knowsNeighbors / nyc.population) :=
  ⟨cardinal_reading_ithaca_lt_nyc, proportional_reading_ithaca_gt_nyc⟩

-- ════════════════════════════════════════════════════
-- § 4. Distribution of cardinal vs proportional
-- ════════════════════════════════════════════════════

/-! Solt §4 (p. 1135) argues that the AMBIGUITY account (entries
    `many_CARD` and `many_PROP` separately) overgenerates: in
    combination with individual-level predicates
    ([milsark-1977], [partee-1989], [carlson-1977]),
    *many*/*few* allow ONLY the proportional reading.

    Eqs. (35)–(36):
    - (35) "Few egg-laying mammals were found in our survey, perhaps
           because there *are* few." — FELICITOUS. *Found in our
           survey* is stage-level, so the cardinal reading is
           available; on the cardinal reading, *few Ns* can be all
           the Ns (there's a small total population), and the
           continuation *are few* is consistent with that.
    - (36) "#Few egg-laying mammals suckle their young, perhaps
           because there *are* few." — INFELICITOUS. *Suckle their
           young* is individual-level, so only the proportional
           reading is licensed. On the proportional reading, *few Ns*
           are a small fraction of the Ns, and the continuation
           *are few* (≈ "there are not many egg-laying mammals
           overall") is INCONSISTENT with the proportional claim
           (which presupposes a denominator population).

    The measurement-based account explains the contrast: in the
    presence of an individual-level predicate, the `Meas` head is
    necessarily restricted to a domain-restricted variety, blocking
    the cardinal reading.

    The substrate primitive `PredicateLevel`
    (`Semantics/Kinds/SortedOntology.lean §2`) is reused
    here directly rather than re-stipulated; the same enum is
    consumed by `Fragments/German/BarePluralWordOrder.lean` and
    `Studies/Magri2009.lean`. -/

/-- Solt's distribution claim: in the presence of an individual-level
    predicate, only the proportional reading is licensed. Encoded as a
    decidable function over Carlson's `PredicateLevel`. -/
def licensedReadings : PredicateLevel → List String
  | .stageLevel       => ["cardinal", "proportional"]
  | .individualLevel  => ["proportional"]

/-- Stage-level predicates license both cardinal and proportional. -/
theorem stage_level_both_readings :
    "cardinal" ∈ licensedReadings .stageLevel ∧
    "proportional" ∈ licensedReadings .stageLevel := by decide

/-- Individual-level predicates license ONLY proportional. -/
theorem individual_level_only_proportional :
    "cardinal" ∉ licensedReadings .individualLevel ∧
    "proportional" ∈ licensedReadings .individualLevel := by decide

/-- The Solt §4 distribution gap: stage-level licenses cardinal,
    individual-level does not. The ambiguity account does not predict
    this asymmetry without ad hoc stipulation. -/
theorem stage_individual_distribution_gap :
    "cardinal" ∈ licensedReadings .stageLevel ∧
    "cardinal" ∉ licensedReadings .individualLevel := by decide

-- ════════════════════════════════════════════════════
-- § 5. Cross-paper engagement
-- ════════════════════════════════════════════════════

/-! ### §5.1 Substrate sharing with [tham-2025]

  Tham 2025's eq. (47b) for *cracked* uses the same substrate
  (`spatialNormalizedScore`) with:
  - `weights : List ℚ` of length 3 (quantity, quality, positioning)
  - `measures : List (α → ℚ)` of length 3 (per-dimension extent)
  - `spatial : α → ℚ` = the host entity's spatial extent

  Solt's eq. (21) uses the substrate with:
  - `weights = [1]` (single dimension)
  - `measures = [μ_DIM]` (single measure function)
  - `spatial = fun _ => μ_DIM(totality)` (constant function returning
    the totality measure)

  The two papers are the substrate's two consumers. -/

/-- The substrate's two-consumer status: Solt's proportional measure
    is `spatialNormalizedScore` with a single weighted dimension and a
    constant denominator; Tham's eq. 47b uses multiple weighted
    dimensions with a per-host denominator. -/
theorem solt_proportional_is_single_dim_spatial_normalized
    {α : Type} (μ_DIM : DimensionedMeasure α) (tot y : α) :
    proportionalMeasure μ_DIM tot y =
      spatialNormalizedScore [1] [μ_DIM] (fun _ => μ_DIM tot) y := rfl

/-- Solt 2018 SuB eq. (18) Monotonicity Constraint, specialized to
    the proportional measure function: if `y ⊑ z ⊑ tot` then the
    proportion of `y` in `tot` is strictly less than the proportion of
    `z` in `tot`. The general eq. (18) constraint
    (`∀ x, y. x ⊑ y ⇒ μ^c_DIM(x) ≺ μ^c_DIM(y)`) is the
    [schwarzschild-2006] part-whole monotonicity condition; this
    theorem shows it is preserved by the eq. (21) proportional
    construction whenever `μ_DIM(tot) > 0`. -/
theorem proportionalMeasure_monotonic {α : Type}
    (μ_DIM : DimensionedMeasure α) (subPart : α → α → Prop)
    (μ_mono : Monotonic μ_DIM subPart) (tot y z : α)
    (htot : 0 < μ_DIM tot) (hyz : subPart y z) :
    proportionalMeasure μ_DIM tot y < proportionalMeasure μ_DIM tot z := by
  rw [proportionalMeasure_eq μ_DIM tot y htot.ne',
      proportionalMeasure_eq μ_DIM tot z htot.ne']
  exact (div_lt_div_iff_of_pos_right htot).mpr (μ_mono y z hyz)

-- ════════════════════════════════════════════════════
-- § 6. Mathlib-style structural properties of `proportionalMeasure`
-- ════════════════════════════════════════════════════

/-! The proportional measure function has the structural properties
    one expects of a *probability-style* fraction-of-totality. These
    theorems make Solt's eq. (21) into a recognizable mathematical
    object — a normalized monotone measure — rather than a stipulation. -/

/-- The proportion of the totality with itself is 1: `μ(tot)/μ(tot) = 1`.
    The "saturates at the totality" property. -/
@[simp]
theorem proportionalMeasure_self_eq_one {α : Type}
    (μ_DIM : DimensionedMeasure α) (tot : α) (htot : 0 < μ_DIM tot) :
    proportionalMeasure μ_DIM tot tot = 1 := by
  rw [proportionalMeasure_eq μ_DIM tot tot htot.ne']
  exact div_self htot.ne'

/-- Helper: weighted score of `[1] [μ_DIM]` at `y` is just `μ_DIM y`.
    Used to discharge the substrate-side hypothesis when consuming
    `spatialNormalizedScore_le_one` and `_nonneg` from `Aggregation.lean`. -/
private theorem weightedScore_singleton {α : Type}
    (μ_DIM : DimensionedMeasure α) (y : α) :
    weightedScore [1] [μ_DIM] y = μ_DIM y := by
  unfold weightedScore
  show ((0 : ℚ) + 1 * μ_DIM y) = μ_DIM y
  ring

/-- Solt's proportional measure is nonnegative when the underlying
    measure is. Consumes the substrate's `spatialNormalizedScore_nonneg`. -/
theorem proportionalMeasure_nonneg {α : Type}
    (μ_DIM : DimensionedMeasure α) (μ_nonneg : ∀ x, 0 ≤ μ_DIM x)
    (tot y : α) :
    0 ≤ proportionalMeasure μ_DIM tot y := by
  apply spatialNormalizedScore_nonneg
  · rw [weightedScore_singleton]; exact μ_nonneg y
  · exact μ_nonneg tot

/-- Solt's proportional measure is bounded above by 1 when the part is
    a subpart of the totality (under a monotonic measure). Consumes the
    substrate's `spatialNormalizedScore_le_one`. -/
theorem proportionalMeasure_le_one {α : Type}
    (μ_DIM : DimensionedMeasure α) (subPart : α → α → Prop)
    (μ_mono_le : ∀ x y, subPart x y → μ_DIM x ≤ μ_DIM y)
    (tot y : α) (hy : subPart y tot) (htot : 0 < μ_DIM tot) :
    proportionalMeasure μ_DIM tot y ≤ 1 := by
  apply spatialNormalizedScore_le_one
  · rw [weightedScore_singleton]; exact μ_mono_le y tot hy
  · exact htot

/-- **Probability-style range** (the deepest mathlib-style theorem in
    this file). When `μ` is monotonic on the part-whole relation,
    `μ ≥ 0`, and `y ⊑ tot` with `0 < μ(tot)`, the proportional measure
    `μ(y)/μ(tot)` lies in the unit interval `[0, 1]`.

    Bundles `proportionalMeasure_nonneg` + `proportionalMeasure_le_one`
    (mathlib idiom: separate primitives + bundled corollary). Combined
    with `proportionalMeasure_self_eq_one` (= 1 at the totality) and
    `proportionalMeasure_monotonic` (preserves order on subparts),
    Solt's proportional measure is a recognizable *normalized monotone
    measure* — the discrete-probability analogue of conditional measure
    `P(Y | X)` in measure theory. -/
theorem proportionalMeasure_mem_unit_interval {α : Type}
    (μ_DIM : DimensionedMeasure α)
    (μ_nonneg : ∀ x, 0 ≤ μ_DIM x)
    (subPart : α → α → Prop)
    (μ_mono_le : ∀ x y, subPart x y → μ_DIM x ≤ μ_DIM y)
    (tot y : α) (hy : subPart y tot) (htot : 0 < μ_DIM tot) :
    0 ≤ proportionalMeasure μ_DIM tot y ∧
      proportionalMeasure μ_DIM tot y ≤ 1 :=
  ⟨proportionalMeasure_nonneg μ_DIM μ_nonneg tot y,
   proportionalMeasure_le_one μ_DIM subPart μ_mono_le tot y hy htot⟩

/-- **Scale invariance**: scaling the measure by a nonzero constant
    leaves the proportion unchanged. The proportion of crackers in a
    barrel is the same whether we measure mass in grams or kilograms.

    For Solt's NYC/Ithaca example: the proportional reading is
    invariant under unit conversion (people-per-thousand vs people-per-
    million); only the cardinal reading depends on the absolute unit. -/
theorem proportionalMeasure_scale_invariant {α : Type}
    (k : ℚ) (hk : k ≠ 0) (μ_DIM : DimensionedMeasure α)
    (tot y : α) (htot : μ_DIM tot ≠ 0) :
    proportionalMeasure (fun x => k * μ_DIM x) tot y =
    proportionalMeasure μ_DIM tot y := by
  have hktot : k * μ_DIM tot ≠ 0 := mul_ne_zero hk htot
  rw [proportionalMeasure_eq _ tot y hktot,
      proportionalMeasure_eq _ tot y htot]
  rw [mul_div_mul_left _ _ hk]

/-! ### §5.2 Connection to [solt-2018] (the multidim chapter)

  Solt's other 2018 paper develops the experimental subjectivity
  typology (RelNum / AbsTot / AbsPart / RelNo / Eval; multidim chapter
  Figure 1, pp. 5–6) and the measure-function-formal-properties theory
  of subjective vs objective comparatives. The (D, ≻, DIM) tuple
  (multidim chapter eq. 33 = SuB paper eq. 15) is the shared scalar
  foundation. *clean*/*dirty* — the multidim chapter's mixed-class
  exemplar — is the closest sibling to *cracked* in Solt's typology
  (both AbsPart in the multidim chapter's classification). The
  substrate `spatialNormalizedScore` is general enough that a future
  formalization of the multidim chapter could use it for *clean*/*dirty*
  in the same way Tham 2025 uses it for *cracked*. -/

end Solt2018Proportional
