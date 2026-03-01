import Linglib.Core.Agent.RationalAction

/-!
# Rank Orderings @cite{luce-1959}

Luce (1959, §2.F, pp. 66–72): the probability of observing a complete rank
ordering under the Luce choice rule. The key insight is that ranking
probability decomposes into a product of successive top-choices from
shrinking alternative sets — a direct consequence of IIA.

## Main results

- `rankProb`: probability of a ranking (as a `List`) under the Luce model,
  defined as the product of successive `pChoice` values from shrinking tails.
- `rankProb_eq_score_prod`: express ranking probability in terms of score
  ratios `v(aᵢ) / ∑ⱼ≥ᵢ v(aⱼ)` (Theorem 9).
- `rankProb_sum_eq_one`: ranking probabilities over all permutations sum to 1.
- `rankProb_marginal_first`: marginalizing rankings over the first choice
  recovers `pChoice`.

## References

- Luce, R. D. (1959). Individual Choice Behavior, §2.F (pp. 66–72).
-/

namespace Core

open BigOperators Finset Real

variable {S A : Type*} [Fintype A] [DecidableEq A]

-- ============================================================================
-- §2.F Rank Orderings (Luce 1959, pp. 66–72)
-- ============================================================================

/-- The tail suffix of a list starting at position `i` (0-indexed).
    Used to represent the shrinking alternative set at each step of ranking. -/
def tailSuffix (ranking : List A) (i : Nat) : Finset A :=
  (ranking.drop i).toFinset

/-- Probability of a single step in the ranking: choosing `ranking[i]` from
    the remaining alternatives `{ranking[i], ranking[i+1], ...}`. -/
noncomputable def rankStepProb (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) : ℝ :=
  match ranking[i]? with
  | none => 1
  | some a => ra.pChoice s (tailSuffix ranking i) a

/-- **Ranking probability** (Luce 1959, Theorem 9):
    The probability of observing the complete rank ordering `a₁ > a₂ > ... > aₙ`
    is the product of successive top-choices from shrinking sets:

    `P(a₁ > a₂ > ... > aₙ) = P(a₁ | {a₁,...,aₙ}) · P(a₂ | {a₂,...,aₙ}) · ... · P(aₙ₋₁ | {aₙ₋₁, aₙ})`

    Under the Luce model with ratio scale `v`, this becomes:
    `P(a₁ > ... > aₙ) = ∏ᵢ v(aᵢ) / ∑ⱼ≥ᵢ v(aⱼ)` -/
noncomputable def rankProb (ra : RationalAction S A) (s : S) (ranking : List A) : ℝ :=
  (List.range ranking.length).foldl (λ acc i => acc * rankStepProb ra s ranking i) 1

/-- Recursive characterization of ranking probability: the first-choice probability
    times the ranking probability of the remaining alternatives. -/
noncomputable def rankProbRec (ra : RationalAction S A) (s : S) : List A → ℝ
  | [] => 1
  | a :: rest => ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest

/-- `rankProbRec` agrees with the explicit `rankProb` definition. -/
theorem rankProbRec_eq_rankProb (ra : RationalAction S A) (s : S) (ranking : List A) :
    rankProbRec ra s ranking = rankProb ra s ranking := by
  -- TODO: induction on ranking, unfolding foldl at each step
  sorry

/-- Ranking probability is non-negative: each factor is a `pChoice` value,
    hence non-negative. -/
theorem rankProb_nonneg (ra : RationalAction S A) (s : S) (ranking : List A) :
    0 ≤ rankProb ra s ranking := by
  -- TODO: induction via rankProbRec; each factor is pChoice ≥ 0
  sorry

-- ============================================================================
-- Score-ratio form (Theorem 9, second part)
-- ============================================================================

/-- The score-ratio factor at position `i`: `v(aᵢ) / ∑ⱼ≥ᵢ v(aⱼ)`.
    This is the `i`-th factor in the score-product form of ranking probability. -/
noncomputable def scoreRatio (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) : ℝ :=
  match ranking[i]? with
  | none => 1
  | some a =>
    let tailSum := ∑ b ∈ tailSuffix ranking i, ra.score s b
    if tailSum = 0 then 0 else ra.score s a / tailSum

/-- The score-product form of ranking probability:
    `∏ᵢ v(aᵢ) / ∑ⱼ≥ᵢ v(aⱼ)`. -/
noncomputable def rankProbScoreProd (ra : RationalAction S A) (s : S)
    (ranking : List A) : ℝ :=
  (List.range ranking.length).foldl (λ acc i => acc * scoreRatio ra s ranking i) 1

/-- **Theorem 9 (score form)**: ranking probability equals the product of score ratios.

    Each `pChoice` factor equals the corresponding score ratio by definition of
    the Luce choice rule, so the two products are term-by-term equal. -/
theorem rankProb_eq_score_prod (ra : RationalAction S A) (s : S) (ranking : List A)
    (hnd : ranking.Nodup) :
    rankProb ra s ranking = rankProbScoreProd ra s ranking := by
  -- TODO: suffices to show rankStepProb = scoreRatio at each position,
  -- which follows from pChoice_mem when the element is in the tail finset
  sorry

-- ============================================================================
-- Summation over permutations (Theorem 9, completeness)
-- ============================================================================

/-- All permutations of a finset, as lists. -/
noncomputable def allRankings (T : Finset A) : Finset (List A) :=
  T.val.toList.permutations.toFinset

/-- Every ranking in `allRankings T` is a permutation of `T`. -/
theorem mem_allRankings_iff (T : Finset A) (ranking : List A) :
    ranking ∈ allRankings T ↔ ranking.toFinset = T ∧ ranking.Nodup := by
  -- TODO: follows from Multiset.mem_permutations and List.toFinset properties
  sorry

/-- **Ranking probabilities sum to 1** (Luce 1959, Theorem 9 completeness):
    Over all `n!` permutations of the alternative set, ranking probabilities
    form a proper distribution.

    The proof proceeds by induction on `|T|`:
    - Base: single element, ranking probability is 1.
    - Step: factor out the first-choice probability (which sums to 1 over
      first choices by `pChoice_sum_eq_one`), then apply the inductive
      hypothesis to each `(n-1)`-element ranking. -/
theorem rankProb_sum_eq_one (ra : RationalAction S A) (s : S)
    (T : Finset A) (hT : T.Nonempty)
    (hpos : ∑ b ∈ T, ra.score s b ≠ 0) :
    ∑ r ∈ allRankings T, rankProb ra s r = 1 := by
  -- TODO: induction on T.card, using pChoice_sum_eq_one and
  -- the recursive decomposition rankProbRec
  sorry

-- ============================================================================
-- Marginalization (recovering pChoice)
-- ============================================================================

/-- Rankings starting with a given element `a`. -/
noncomputable def rankingsStartingWith (T : Finset A) (a : A) : Finset (List A) :=
  (allRankings T).filter (λ r => r.head? = some a)

/-- **Marginal first-choice** (Luce 1959, Theorem 9 corollary):
    Summing the ranking probability over all rankings that start with `a`
    recovers the choice probability `pChoice(a, T)`.

    This is because `P(a first) = P(a | T) · ∑_σ P(σ | T \ {a}) = P(a | T) · 1`,
    where the inner sum equals 1 by `rankProb_sum_eq_one` on the remaining
    alternatives. -/
theorem rankProb_marginal_first (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∑ b ∈ T, ra.score s b ≠ 0) :
    ∑ r ∈ rankingsStartingWith T a, rankProb ra s r = ra.pChoice s T a := by
  -- TODO: decompose each ranking as a :: rest, factor out pChoice,
  -- apply rankProb_sum_eq_one to the (T \ {a}) rankings
  sorry

-- ============================================================================
-- Expected rank (Theorem 10)
-- ============================================================================

/-- The rank of element `a` in a ranking (1-indexed, so rank 1 = best).
    Returns 0 if `a` is not in the ranking. -/
def rankOf (ranking : List A) (a : A) : Nat :=
  if a ∈ ranking then ranking.findIdx (· == a) + 1 else 0

/-- Expected rank of alternative `a` under the ranking distribution.

    `E[rank(a)] = ∑_σ P(σ) · rank(a, σ)`

    Luce (1959, Theorem 10) shows this relates to the ratio scale value:
    alternatives with higher `v(a)` have lower (better) expected rank. -/
noncomputable def expectedRank (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) : ℝ :=
  ∑ r ∈ allRankings T, rankProb ra s r * (rankOf r a : ℝ)

/-- **Theorem 10 (monotonicity)**: higher score implies lower expected rank.

    If `v(a₁) > v(a₂)` then `E[rank(a₁)] < E[rank(a₂)]`: the alternative
    with higher ratio-scale value is expected to be ranked higher (closer to 1).

    The proof uses the marginal decomposition: for each position `k`,
    the probability that `a₁` lands at position `k` exceeds the probability
    that `a₂` lands there (by IIA and the score ordering), which makes
    `a₁`'s expected rank stochastically dominated by `a₂`'s. -/
theorem expectedRank_lt_of_score_gt (ra : RationalAction S A) (s : S)
    (T : Finset A) (a₁ a₂ : A) (ha₁ : a₁ ∈ T) (ha₂ : a₂ ∈ T)
    (hne : a₁ ≠ a₂)
    (hpos : ∑ b ∈ T, ra.score s b ≠ 0)
    (hgt : ra.score s a₁ > ra.score s a₂) :
    expectedRank ra s T a₁ < expectedRank ra s T a₂ := by
  -- TODO: decompose by position, use pChoice monotonicity at each position
  sorry

end Core
