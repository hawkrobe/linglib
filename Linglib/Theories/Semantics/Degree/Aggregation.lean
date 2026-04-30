import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic

/-!
# Dimensional Aggregation for Multidimensional Predicates

General mechanisms for combining dimensional assessments into overall
predicate application. These apply to any multi-dimensional predicate —
gradable adjectives (@cite{dambrosio-hedden-2024}, @cite{sassoon-2013}),
artifact nouns (@cite{waldon-etal-2023}, @cite{sassoon-fadlon-2017}),
disturbance predicates (@cite{tham-2025}), and proportional measures
for vague quantity expressions (@cite{solt-2018-proportional}).

Aggregation is analogous to preference aggregation in social choice theory.
Arrow's impossibility theorem and its escape routes characterize the
available aggregation functions:

- **Counting** (§1): x is F iff ≥k dimensions are satisfied.
  Subsumes @cite{sassoon-2013}'s conjunctive (k=n) and disjunctive (k=1).
- **Majority** (§1): x is F iff a strict majority of dimensions are satisfied.
- **Weighted** (§2): x is F iff Σᵢ wᵢ·fᵢ(x) ≥ θ (utilitarian aggregation).
  Subsumes @cite{waldon-etal-2023}'s eq. 8.
- **Spatially-normalized weighted** (§2): x is F iff (Σᵢ wᵢ·fᵢ(x)) / s(x) ≥ θ,
  where s : α → ℚ is a host-extent measure. This is @cite{tham-2025}'s eq. 47b
  for physical disturbance adjectives — the numerator is a weighted sum of
  per-dimension EXTENT measures, and the denominator is the host's SPATIAL
  EXTENT, so the same physical disturbance counts as more severe on a smaller
  host. Reduces to plain weighted aggregation when s ≡ 1.
- **Multiplicative** (§4): x is F iff Πᵢ fᵢ(x) ≥ θ (Cobb-Douglas aggregation).
  @cite{sassoon-fadlon-2017} argue natural kinds compose multiplicatively:
  failure on ANY dimension kills membership.

The weighted score is unified over ℚ-valued measure functions. Bool-valued
dimension predicates are a special case via `boolMeasures`.
-/

namespace Semantics.Degree.Aggregation

variable {α : Type}

-- ════════════════════════════════════════════════════
-- § 1. Counting Aggregation
-- ════════════════════════════════════════════════════

/-- Counting aggregation: x satisfies the predicate iff at least `k` of
    the dimension predicates in `dims` return `true` for `x`.

    Generalizes @cite{sassoon-2013}'s binding types:
    - `k = dims.length` → conjunctive (∀ dims)
    - `k = 1` → disjunctive (∃ dim)
    - intermediate `k` → mixed / "dimension counting" -/
def countBinding (k : Nat) (dims : List (α → Bool)) (x : α) : Bool :=
  decide ((dims.filter (fun d => d x)).length ≥ k)

/-- Majority binding: x satisfies the predicate iff a strict majority
    of dimensions are satisfied. May's theorem (1952) characterizes this
    as the unique aggregation rule satisfying neutrality, anonymity, and
    positive responsiveness. -/
def majorityBinding (dims : List (α → Bool)) (x : α) : Bool :=
  decide (2 * (dims.filter (fun d => d x)).length > dims.length)

-- ════════════════════════════════════════════════════
-- § 2. Weighted Aggregation (Unified ℚ)
-- ════════════════════════════════════════════════════

/-- Lift Bool dimension predicates to ℚ-valued measure functions.
    Each `d : α → Bool` becomes `fun x => if d x then 1 else 0`. -/
def boolMeasures (dims : List (α → Bool)) : List (α → ℚ) :=
  dims.map (fun d x => if d x then 1 else 0)

/-- Weighted score: Σᵢ wᵢ · fᵢ(x), where each fᵢ : α → ℚ is a
    measure function along one dimension.

    This is the unified core: @cite{waldon-etal-2023}'s eq. (8) uses
    ℚ-valued measures directly; @cite{dambrosio-hedden-2024}'s Bool
    dimensions are the special case via `boolMeasures`. -/
def weightedScore (weights : List ℚ) (measures : List (α → ℚ)) (x : α) : ℚ :=
  (weights.zip measures).foldl (fun acc (w, f) => acc + w * f x) 0

/-- Weighted binding (Bool dimensions): x is F iff its weighted score
    over Bool-lifted measures exceeds threshold θ. -/
def weightedBinding (weights : List ℚ) (θ : ℚ)
    (dims : List (α → Bool)) (x : α) : Bool :=
  decide (weightedScore weights (boolMeasures dims) x ≥ θ)

/-- Weighted binding over continuous ℚ-valued measures. -/
def weightedBindingQ (weights : List ℚ) (θ : ℚ)
    (measures : List (α → ℚ)) (x : α) : Bool :=
  decide (weightedScore weights measures x ≥ θ)

/-- Spatially-normalized weighted score: (Σᵢ wᵢ·fᵢ(x)) / s(x).

    @cite{tham-2025} eq. 47b for physical disturbance adjectives. The
    `measures` track per-dimension EXTENT of disturbance (e.g., total
    crack length, depth-weighted area); the `spatial` measure tracks the
    host entity's SPATIAL EXTENT. A small disturbance on a small host can
    score the same as a large disturbance on a large host — boundedness
    of the scale comes from the denominator, not from any single
    dimension. Returns `0` when `spatial x = 0` (avoiding division by
    zero); callers should ensure `spatial x ≠ 0` for meaningful results. -/
def spatialNormalizedScore (weights : List ℚ) (measures : List (α → ℚ))
    (spatial : α → ℚ) (x : α) : ℚ :=
  if spatial x = 0 then 0 else weightedScore weights measures x / spatial x

/-- Spatially-normalized weighted binding (Bool dimensions): x is F iff
    its spatially-normalized weighted score over Bool-lifted measures
    exceeds threshold θ. -/
def spatialNormalizedBinding (weights : List ℚ) (θ : ℚ)
    (dims : List (α → Bool)) (spatial : α → ℚ) (x : α) : Bool :=
  decide (spatialNormalizedScore weights (boolMeasures dims) spatial x ≥ θ)

-- ════════════════════════════════════════════════════
-- § 3. Properties
-- ════════════════════════════════════════════════════

/-- Counting with threshold 0 is always satisfied (vacuously true). -/
theorem countBinding_zero (dims : List (α → Bool)) (x : α) :
    countBinding 0 dims x = true := by
  simp [countBinding]

/-- The spatial-normalization reduces to plain weighted score when
    `spatial x = 1` (constant unit host extent). -/
@[simp]
theorem spatialNormalizedScore_unit (weights : List ℚ) (measures : List (α → ℚ))
    (x : α) :
    spatialNormalizedScore weights measures (fun _ => 1) x =
      weightedScore weights measures x := by
  unfold spatialNormalizedScore
  split_ifs with h
  · exact absurd h one_ne_zero
  · exact div_one _

/-- Spatial normalization at a zero-extent host returns 0. Documents the
    edge-case convention: a host with no spatial extent cannot exhibit a
    physical disturbance, so the predicate is vacuously not satisfied. -/
@[simp]
theorem spatialNormalizedScore_zero (weights : List ℚ) (measures : List (α → ℚ))
    (spatial : α → ℚ) (x : α) (h : spatial x = 0) :
    spatialNormalizedScore weights measures spatial x = 0 := by
  simp [spatialNormalizedScore, h]

/-- **Bounded-by-one normalization** (mathlib-style structural property).
    When the weighted-score numerator is bounded by the spatial-extent
    denominator, the normalized score is at most 1. This makes Tham
    2025's "boundedness from spatial extent" claim (§3.4) into a
    structural theorem rather than a stipulation. -/
theorem spatialNormalizedScore_le_one
    (weights : List ℚ) (measures : List (α → ℚ))
    (spatial : α → ℚ) (x : α)
    (hsum : weightedScore weights measures x ≤ spatial x)
    (hpos : 0 < spatial x) :
    spatialNormalizedScore weights measures spatial x ≤ 1 := by
  unfold spatialNormalizedScore
  rw [if_neg hpos.ne']
  exact div_le_one_of_le₀ hsum hpos.le

/-- **Nonnegativity of normalized score**. When the weighted score is
    nonnegative and the spatial extent is nonnegative, the normalized
    score is nonnegative. Combined with `spatialNormalizedScore_le_one`,
    this places the score in `[0, 1]` — the "fraction of the totality"
    intuition Tham 2025 §3.4 and Solt 2018 eq. 21 both require. -/
theorem spatialNormalizedScore_nonneg
    (weights : List ℚ) (measures : List (α → ℚ))
    (spatial : α → ℚ) (x : α)
    (hnum : 0 ≤ weightedScore weights measures x)
    (hspatial : 0 ≤ spatial x) :
    0 ≤ spatialNormalizedScore weights measures spatial x := by
  unfold spatialNormalizedScore
  by_cases h : spatial x = 0
  · rw [if_pos h]
  · rw [if_neg h]; exact div_nonneg hnum hspatial

-- ════════════════════════════════════════════════════
-- § 4. Multiplicative Aggregation (Cobb-Douglas)
-- ════════════════════════════════════════════════════

/-- Multiplicative (Cobb-Douglas) score: Πᵢ fᵢ(x).
    @cite{sassoon-fadlon-2017} argue natural kind nouns compose
    multiplicatively: failure on ANY single dimension kills membership.
    Contrast with additive `weightedScore` for artifact nouns. -/
def multiplicativeScore (measures : List (α → ℚ)) (x : α) : ℚ :=
  measures.foldl (fun acc f => acc * f x) 1

-- ════════════════════════════════════════════════════
-- § 5. Classification
-- ════════════════════════════════════════════════════

/-- Classification of dimensional aggregation mechanisms.
    Each type corresponds to an escape route from Arrow's impossibility. -/
inductive AggregationType where
  /-- Threshold counting (rejects WO via non-transitivity or incompleteness). -/
  | counting
  /-- Weighted sum / utilitarian (rejects ONC, accepts interval scale IUC). -/
  | utilitarian
  /-- Weighted product / Cobb-Douglas (rejects ONC, accepts ratio scale RNC). -/
  | cobbDouglas
  deriving Repr, DecidableEq

end Semantics.Degree.Aggregation
