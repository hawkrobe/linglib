import Mathlib.Data.Rat.Defs

/-!
# Dimensional Aggregation for Multidimensional Predicates

General mechanisms for combining dimensional assessments into overall
predicate application. These apply to any multi-dimensional predicate —
gradable adjectives (@cite{dambrosio-hedden-2024}, @cite{sassoon-2013}),
artifact nouns (@cite{waldon-etal-2023}, @cite{sassoon-fadlon-2017}),
and disturbance predicates (@cite{tham-2025}).

Aggregation is analogous to preference aggregation in social choice theory.
Arrow's impossibility theorem and its escape routes characterize the
available aggregation functions:

- **Counting** (§1): x is F iff ≥k dimensions are satisfied.
  Subsumes @cite{sassoon-2013}'s conjunctive (k=n) and disjunctive (k=1).
- **Majority** (§1): x is F iff a strict majority of dimensions are satisfied.
- **Weighted** (§2): x is F iff Σᵢ wᵢ·fᵢ(x) ≥ θ (utilitarian aggregation).
  Subsumes @cite{tham-2025}'s eq. 47b and @cite{waldon-etal-2023}'s eq. 8.
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

-- ════════════════════════════════════════════════════
-- § 3. Properties
-- ════════════════════════════════════════════════════

/-- Counting with threshold 0 is always satisfied (vacuously true). -/
theorem countBinding_zero (dims : List (α → Bool)) (x : α) :
    countBinding 0 dims x = true := by
  simp [countBinding]

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
  deriving Repr, DecidableEq, BEq

end Semantics.Degree.Aggregation
