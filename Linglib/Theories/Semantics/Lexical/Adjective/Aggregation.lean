import Linglib.Theories.Semantics.Lexical.Adjective.Theory

/-!
# Dimensional Aggregation for Multidimensional Adjectives
@cite{dambrosio-hedden-2024}

D'Ambrosio, J. & Hedden, B. (2024). Multidimensional Adjectives.
*Australasian Journal of Philosophy* 102(2): 253–277.

The problem of **dimensional aggregation**: how do the dimensions of a
multidimensional adjective combine to determine whether it applies
(positive form) and how objects compare (comparative form)?

This is analogous to preference aggregation in social choice theory.
Arrow's impossibility theorem and its escape routes characterize what
aggregation functions are available:

- **Counting** (§4.2): x is F iff ≥k dimensions are satisfied.
  Subsumes @cite{sassoon-2013}'s conjunctive (k=n) and disjunctive (k=1).
- **Majority** (§4.2): x is F iff a strict majority of dimensions are satisfied.
- **Weighted** (§4.3): x is F iff Σᵢ wᵢ·dᵢ(x) ≥ θ (utilitarian aggregation).
  Subsumes @cite{tham-2025}'s eq. 47b weighted formula.
-/

namespace Semantics.Lexical.Adjective.Aggregation

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
-- § 2. Weighted Aggregation
-- ════════════════════════════════════════════════════

/-- Weighted score over Bool dimensions: Σᵢ wᵢ · [dᵢ(x)],
    where [b] = 1 if b, 0 otherwise. -/
def weightedScore (weights : List ℚ) (dims : List (α → Bool)) (x : α) : ℚ :=
  (weights.zip dims).foldl
    (fun acc (w, d) => acc + w * if d x then 1 else 0) 0

/-- Weighted binding: x is F iff its weighted score exceeds threshold θ. -/
def weightedBinding (weights : List ℚ) (θ : ℚ)
    (dims : List (α → Bool)) (x : α) : Bool :=
  decide (weightedScore weights dims x ≥ θ)

-- ════════════════════════════════════════════════════
-- § 3. Subsumption Theorems
-- ════════════════════════════════════════════════════

private theorem all_eq_decide_filter_ge_length :
    ∀ (dims : List (α → Bool)) (x : α),
      dims.all (· x) = decide ((dims.filter (fun d => d x)).length ≥ dims.length)
  | [], _ => rfl
  | d :: ds, x => by
    have ih := all_eq_decide_filter_ge_length ds x
    simp only [List.all_cons, List.length_cons]
    cases hd : d x
    · rw [@List.filter_cons_of_neg _ (· x) d ds (by simp [hd])]
      simp only [Bool.false_and]
      exact (decide_eq_false_iff_not.mpr (by
        have := List.length_filter_le (· x) ds; omega)).symm
    · rw [@List.filter_cons_of_pos _ (· x) d ds hd]
      simp only [Bool.true_and, List.length_cons, ih]
      exact decide_eq_decide.mpr (by omega)

private theorem any_eq_decide_filter_ge_one :
    ∀ (dims : List (α → Bool)) (x : α),
      dims.any (· x) = decide ((dims.filter (fun d => d x)).length ≥ 1)
  | [], _ => rfl
  | d :: ds, x => by
    simp only [List.any_cons]
    cases hd : d x
    · rw [@List.filter_cons_of_neg _ (· x) d ds (by simp [hd])]
      simp only [Bool.false_or]
      exact any_eq_decide_filter_ge_one ds x
    · rw [@List.filter_cons_of_pos _ (· x) d ds hd]
      simp only [Bool.true_or, List.length_cons]
      exact (decide_eq_true_iff.mpr (by omega)).symm

/-- Conjunctive binding = counting with threshold k = dims.length.
    @cite{sassoon-2013}'s ∀-binding is a special case of counting. -/
theorem conjunctive_is_countAll (dims : List (α → Bool)) (x : α) :
    conjunctiveBinding dims x = countBinding dims.length dims x :=
  all_eq_decide_filter_ge_length dims x

/-- Disjunctive binding = counting with threshold k = 1.
    @cite{sassoon-2013}'s ∃-binding is a special case of counting. -/
theorem disjunctive_is_countOne (dims : List (α → Bool)) (x : α) :
    disjunctiveBinding dims x = countBinding 1 dims x :=
  any_eq_decide_filter_ge_one dims x

/-- Counting with threshold 0 is always satisfied (vacuously true). -/
theorem countBinding_zero (dims : List (α → Bool)) (x : α) :
    countBinding 0 dims x = true := by
  simp [countBinding]

-- ════════════════════════════════════════════════════
-- § 4. Classification
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

/-- @cite{sassoon-2013}'s binding types all map to counting aggregation.
    The key gap: Sassoon has no utilitarian or Cobb-Douglas mechanism. -/
def toAggregationType : DimensionBindingType → AggregationType
  | .conjunctive => .counting
  | .disjunctive => .counting
  | .mixed => .counting

/-- All of Sassoon 2013's binding types are counting aggregation. -/
theorem sassoon_all_counting :
    ∀ b : DimensionBindingType, toAggregationType b = AggregationType.counting := by
  intro b; cases b <;> rfl

end Semantics.Lexical.Adjective.Aggregation
