import Linglib.Core.Agent.ChoiceApproximations
import Linglib.Core.Agent.RankOrderings

/-!
# Semiorder–Ranking Bridge @cite{luce-1959}

Connects the two halves of Luce (1959) that are formalized independently in
`ChoiceApproximations.lean` (§1.G) and `RankOrderings.lean` (§2.F):

- **§1.G** defines pairwise choice probabilities `P(x,y) = v(x)/(v(x)+v(y))`,
  JND thresholds, the semiorder `(L(π), I(π))`, and the trace ordering.
- **§2.F** defines ranking probabilities as products of successive `pChoice`
  values from shrinking alternative sets.

The bridge connects them via five results:

1. **`fromScale`**: Construct a `RationalAction` from a raw scale `v : A → ℝ`.
2. **`pairwiseProb_eq_pChoice`**: Binary choice probability equals `pChoice`
   restricted to the pair `{x, y}`.
3. **`rankProbRec_swap_ratio`**: Swapping two adjacent elements in a ranking
   changes the probability by the ratio `(v(x) + S_rest) / (v(y) + S_rest)`.
4. **JND effects on rankings**: Indistinguishable items have bounded swap
   ratio; discriminable items have ordered ranking probability.
5. **Trace–expected rank**: The trace ordering matches expected rank ordering.
-/

namespace Core

open Real BigOperators Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

-- ============================================================================
-- §1. RationalAction from a ratio scale
-- ============================================================================

/-- Construct a `RationalAction` from a raw positive scale `v : A → ℝ`,
    the type used throughout ChoiceApproximations (§1.G).

    This lets us apply the RankOrderings (§2.F) machinery — `rankProbRec`,
    `expectedRank` — to the same scales that define `pairwiseProb`, `jndL`,
    `jndI`, and the trace. -/
noncomputable def RationalAction.fromScale (v : A → ℝ) (hv : ∀ a, 0 ≤ v a) :
    RationalAction Unit A where
  score _ a := v a
  score_nonneg _ a := hv a

-- ============================================================================
-- §2. pairwiseProb = pChoice on pairs
-- ============================================================================

/-- The fundamental connection between §1.G and §2.F: binary choice
    probability `P(x, y) = v(x)/(v(x)+v(y))` from ChoiceApproximations
    equals `pChoice` from RationalAction on the two-element set `{x, y}`.

    Proof: unfold both sides. `pairwiseProb v x y = v x / (v x + v y)`.
    `pChoice () {x,y} x = v x / (∑ b ∈ {x,y}, v b) = v x / (v x + v y)`
    when `x ≠ y` (so `{x,y}` has two elements). -/
theorem pairwiseProb_eq_pChoice (v : A → ℝ) (hv : ∀ a, 0 < v a)
    (x y : A) (hne : x ≠ y) :
    pairwiseProb v x y =
    (RationalAction.fromScale v (λ a => le_of_lt (hv a))).pChoice () {x, y} x := by
  simp only [pairwiseProb, RationalAction.pChoice, RationalAction.fromScale]
  have hx_mem : x ∈ ({x, y} : Finset A) := mem_insert_self x {y}
  simp only [hx_mem, ↓reduceIte]
  have hx_notin_y : x ∉ ({y} : Finset A) := by simp [hne]
  have hsum_eq : ∑ b ∈ ({x, y} : Finset A), v b = v x + v y :=
    by rw [Finset.sum_insert hx_notin_y, Finset.sum_singleton]
  have hsum_ne : ∑ b ∈ ({x, y} : Finset A), v b ≠ 0 := by
    rw [hsum_eq]; linarith [hv x, hv y]
  simp only [hsum_ne, ↓reduceIte]
  rw [hsum_eq]

-- ============================================================================
-- §3. Adjacent-swap ranking ratio
-- ============================================================================

/-- Swapping two adjacent elements in a ranking changes the probability by
    the ratio `(v(x) + S_rest) / (v(y) + S_rest)` where `S_rest = ∑ b ∈ rest, v b`.

    This corrects the naive intuition that the ratio should be `v(x)/v(y)`.
    The difference arises because the *second* step of each ranking draws from
    a different set: `{y} ∪ rest` vs `{x} ∪ rest`. Expanding:

    `rankProbRec(x::y::rest) / rankProbRec(y::x::rest)`
    `= [pChoice(T, x) · pChoice({y}∪R, y)] / [pChoice(T, y) · pChoice({x}∪R, x)]`
    `= [v(x)/S_T · v(y)/(v(y)+S_R)] / [v(y)/S_T · v(x)/(v(x)+S_R)]`
    `= (v(x)+S_R) / (v(y)+S_R)`

    where `T = {x,y} ∪ R` and `S_R = ∑ b ∈ R, v b`. -/
theorem rankProbRec_swap_ratio (ra : RationalAction Unit A) (s : Unit)
    (x y : A) (rest : List A) (hne : x ≠ y)
    (hx : x ∉ rest) (hy : y ∉ rest)
    (hnd : rest.Nodup)
    (hpos_tail : 0 < rankProbRec ra s rest)
    (hpos_sum : ∑ b ∈ (x :: y :: rest).toFinset, ra.score s b ≠ 0) :
    rankProbRec ra s (x :: y :: rest) / rankProbRec ra s (y :: x :: rest) =
    (ra.score s x + ∑ b ∈ rest.toFinset, ra.score s b) /
    (ra.score s y + ∑ b ∈ rest.toFinset, ra.score s b) := by
  -- TODO: unfold rankProbRec twice on each side, cancel the common
  -- rankProbRec(rest) factor, then simplify the pChoice quotients.
  -- The key step is showing (x::y::rest).toFinset = (y::x::rest).toFinset
  -- and that the pChoice ratio simplifies to the score ratio.
  sorry

-- ============================================================================
-- §4. JND effects on ranking probability
-- ============================================================================

/-- If `x` is discriminably preferred to `y` at threshold `π` (i.e., `xL(π)y`),
    then the ranking with `x` before `y` is strictly more probable than
    the ranking with `y` before `x`.

    From `jndL`, `P(x,y) > π > 1/2`, so `v(x) > v(y)`, hence
    `v(x) + S_R > v(y) + S_R`, making the ranking `x::y::rest` more probable.

    This is the ranking-probability counterpart of Theorem 5's L-transitivity:
    discriminable preference in pairwise choice implies discriminable
    preference in ranking probability. -/
theorem jndL_swap_ordered (v : A → ℝ) (hv : ∀ a, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (x y : A) (rest : List A)
    (hL : jndL v thr x y)
    (hx : x ∉ rest) (hy : y ∉ rest) (hnd : rest.Nodup) :
    rankProbRec (RationalAction.fromScale v (λ a => le_of_lt (hv a))) ()
      (y :: x :: rest) <
    rankProbRec (RationalAction.fromScale v (λ a => le_of_lt (hv a))) ()
      (x :: y :: rest) := by
  -- From jndL, v(x) > v(y). The ratio (v(x)+S_R)/(v(y)+S_R) > 1.
  -- So rankProbRec(x::y::rest) > rankProbRec(y::x::rest).
  sorry

/-- If `x` and `y` are indistinguishable at threshold `π` (i.e., `xI(π)y`),
    then swapping them in a ranking changes the probability by at most
    a factor of `thr / (1 - thr)`.

    From `jndI`, `P(x,y) ≤ thr`, so `v(x)/(v(x)+v(y)) ≤ thr`, giving
    `v(x)/v(y) ≤ thr/(1-thr)`. Since `(v(x)+S_R)/(v(y)+S_R) ≤ v(x)/v(y)`
    when `v(x) ≥ v(y)` (adding a constant to both sides shrinks the ratio),
    the swap ratio is bounded by `thr/(1-thr)`.

    When `v(x) ≤ v(y)`, the ratio is ≤ 1 < thr/(1-thr) (since thr > 1/2). -/
theorem jndI_swap_bounded (v : A → ℝ) (hv : ∀ a, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y : A) (rest : List A)
    (hI : jndI v thr x y)
    (hx : x ∉ rest) (hy : y ∉ rest) (hnd : rest.Nodup) :
    rankProbRec (RationalAction.fromScale v (λ a => le_of_lt (hv a))) ()
      (x :: y :: rest) /
    rankProbRec (RationalAction.fromScale v (λ a => le_of_lt (hv a))) ()
      (y :: x :: rest) ≤ thr / (1 - thr) := by
  -- From jndI, 1-thr ≤ P(x,y) ≤ thr. The upper bound gives
  -- v(x)/v(y) ≤ thr/(1-thr). The swap ratio (v(x)+S_R)/(v(y)+S_R)
  -- is ≤ v(x)/v(y) ≤ thr/(1-thr) when v(x) ≥ v(y),
  -- and ≤ 1 < thr/(1-thr) when v(x) < v(y).
  sorry

-- ============================================================================
-- §5. Trace ordering matches expected rank ordering
-- ============================================================================

/-- The trace ordering from §1.G (Definition 4) matches the expected rank
    ordering from §2.F: `x ≥_T y` iff `E[rank(x)] ≤ E[rank(y)]`.

    By Theorem 6 (trace_iff_scale_ge), `x ≥_T y ↔ v(x) ≥ v(y)`.
    By Theorem 10 (expectedRank_lt_of_score_gt), `v(x) > v(y)` implies
    `E[rank(x)] < E[rank(y)]`. So the two orderings agree on strict preference.

    The `≤` case (when `v(x) = v(y)`) follows from the fact that both
    `traceGe` and `expectedRank` are symmetric in that case.

    NOTE: depends on `expectedRank_lt_of_score_gt`, which is sorry'd
    in RankOrderings.lean. -/
theorem traceGe_iff_expectedRank_le (v : A → ℝ) (hv : ∀ a, 0 < v a)
    (T : Finset A) (x y : A) (hx : x ∈ T) (hy : y ∈ T) (hne : x ≠ y)
    (hpos : ∑ b ∈ T, v b ≠ 0) :
    traceGe v x y ↔
    expectedRank (RationalAction.fromScale v (λ a => le_of_lt (hv a))) () T x ≤
    expectedRank (RationalAction.fromScale v (λ a => le_of_lt (hv a))) () T y := by
  -- Forward: traceGe → v(x) ≥ v(y) (by trace_iff_scale_ge) →
  --   E[rank(x)] ≤ E[rank(y)] (by expectedRank_lt_of_score_gt or equality)
  -- Backward: E[rank(x)] ≤ E[rank(y)] → v(x) ≥ v(y) (contrapositive of
  --   expectedRank_lt_of_score_gt) → traceGe (by trace_iff_scale_ge)
  sorry

end Core
