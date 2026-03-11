import Linglib.Core.Agent.ChoiceApproximations
import Linglib.Core.Agent.RankOrderings

/-!
# Semiorder–Ranking Bridge @cite{luce-1959}

Connects the two halves of @cite{luce-1959} that are formalized independently in
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
    `pChoice {x,y} x = v x / (∑ b ∈ {x,y}, v b) = v x / (v x + v y)`
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

-- Private helpers for swap ratio proof

private theorem pChoice_pos_of_score_pos (ra : RationalAction Unit A) (s : Unit)
    (T : Finset A) (a : A) (ha : a ∈ T) (hpos : ∀ b, 0 < ra.score s b) :
    0 < ra.pChoice s T a := by
  have hsum_pos : 0 < ∑ b ∈ T, ra.score s b :=
    Finset.sum_pos (fun b _ => hpos b) ⟨a, ha⟩
  simp only [RationalAction.pChoice, ha, ne_of_gt hsum_pos, ↓reduceIte]
  exact div_pos (hpos a) hsum_pos

private theorem rankProbRec_pos_of_score_pos (ra : RationalAction Unit A) (s : Unit)
    (ranking : List A) (hpos : ∀ b, 0 < ra.score s b) :
    0 < rankProbRec ra s ranking := by
  induction ranking with
  | nil => simp [rankProbRec]
  | cons a rest ih =>
    show 0 < ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest
    exact mul_pos
      (pChoice_pos_of_score_pos ra s _ a (by simp [List.toFinset_cons]) hpos) ih

private theorem pChoice_eq_score_div_sum (ra : RationalAction Unit A) (s : Unit)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hne : ∑ b ∈ T, ra.score s b ≠ 0) :
    ra.pChoice s T a = ra.score s a / ∑ b ∈ T, ra.score s b := by
  simp [RationalAction.pChoice, ha, hne]

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
    (x y : A) (rest : List A) (_hne : x ≠ y)
    (hx : x ∉ rest) (hy : y ∉ rest)
    (_hnd : rest.Nodup)
    (hpos : ∀ b, 0 < ra.score s b) :
    rankProbRec ra s (x :: y :: rest) / rankProbRec ra s (y :: x :: rest) =
    (ra.score s x + ∑ b ∈ rest.toFinset, ra.score s b) /
    (ra.score s y + ∑ b ∈ rest.toFinset, ra.score s b) := by
  set vx := ra.score s x; set vy := ra.score s y
  set S_R := ∑ b ∈ rest.toFinset, ra.score s b
  set tail := rankProbRec ra s rest
  have hvx := hpos x; have hvy := hpos y
  have hS_nn : 0 ≤ S_R := Finset.sum_nonneg fun b _ => le_of_lt (hpos b)
  have htail_pos := rankProbRec_pos_of_score_pos ra s rest hpos
  have hx_notin : x ∉ rest.toFinset := by rwa [List.mem_toFinset]
  have hy_notin : y ∉ rest.toFinset := by rwa [List.mem_toFinset]
  have hT_eq : (x :: y :: rest).toFinset = (y :: x :: rest).toFinset := by
    simp only [List.toFinset_cons]; ext a; simp [Finset.mem_insert]; tauto
  show ra.pChoice s (x :: y :: rest).toFinset x *
       (ra.pChoice s (y :: rest).toFinset y * tail) /
      (ra.pChoice s (y :: x :: rest).toFinset y *
       (ra.pChoice s (x :: rest).toFinset x * tail)) =
      (vx + S_R) / (vy + S_R)
  rw [hT_eq]
  set T := (y :: x :: rest).toFinset
  have hS_T_ne : ∑ b ∈ T, ra.score s b ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun b _ => hpos b)
      ⟨y, by simp [T, List.toFinset_cons]⟩)
  have hS_yR_ne : vy + S_R ≠ 0 := ne_of_gt (by linarith)
  have hS_xR_ne : vx + S_R ≠ 0 := ne_of_gt (by linarith)
  rw [pChoice_eq_score_div_sum ra s T x (by simp [T, List.toFinset_cons]) hS_T_ne,
      pChoice_eq_score_div_sum ra s T y (by simp [T, List.toFinset_cons]) hS_T_ne,
      pChoice_eq_score_div_sum ra s (y :: rest).toFinset y (by simp [List.toFinset_cons])
        (by rw [List.toFinset_cons, Finset.sum_insert hy_notin]; exact hS_yR_ne),
      pChoice_eq_score_div_sum ra s (x :: rest).toFinset x (by simp [List.toFinset_cons])
        (by rw [List.toFinset_cons, Finset.sum_insert hx_notin]; exact hS_xR_ne)]
  rw [show ∑ b ∈ (y :: rest).toFinset, ra.score s b = vy + S_R from
        by rw [List.toFinset_cons, Finset.sum_insert hy_notin],
      show ∑ b ∈ (x :: rest).toFinset, ra.score s b = vx + S_R from
        by rw [List.toFinset_cons, Finset.sum_insert hx_notin]]
  have hne_tail : (tail : ℝ) ≠ 0 := ne_of_gt htail_pos
  field_simp

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
  set ra := RationalAction.fromScale v (λ a => le_of_lt (hv a))
  have hpos : ∀ b, 0 < ra.score () b := fun b => hv b
  have hne : x ≠ y := by
    intro heq; subst heq
    simp [jndL, pairwiseProb_self v hv] at hL; linarith
  have hvxy : v y < v x :=
    (pairwiseProb_gt_half_iff v hv x y).mp (lt_trans hthr_lower hL)
  have hden_pos := rankProbRec_pos_of_score_pos ra () (y :: x :: rest) hpos
  have hratio := rankProbRec_swap_ratio ra () x y rest hne hx hy hnd hpos
  have hvy_S_pos : (0 : ℝ) < ra.score () y + ∑ b ∈ rest.toFinset, ra.score () b :=
    add_pos_of_pos_of_nonneg (hpos y) (Finset.sum_nonneg fun b _ => le_of_lt (hpos b))
  have h1 : 1 < rankProbRec ra () (x :: y :: rest) / rankProbRec ra () (y :: x :: rest) := by
    rw [hratio, one_lt_div hvy_S_pos]
    -- ra.score () x = v x and ra.score () y = v y
    have : ra.score () y < ra.score () x := hvxy
    linarith
  exact (one_lt_div hden_pos).mp h1

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
  set ra := RationalAction.fromScale v (λ a => le_of_lt (hv a))
  have hpos : ∀ b, 0 < ra.score () b := fun b => hv b
  by_cases heq : x = y
  · -- x = y: ratio is 1, and thr/(1-thr) ≥ 1 since thr > 1/2
    subst heq
    rw [div_self (ne_of_gt (rankProbRec_pos_of_score_pos ra () (x :: x :: rest) hpos))]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - thr)]
    linarith
  · -- x ≠ y: use swap ratio
    have hratio := rankProbRec_swap_ratio ra () x y rest heq hx hy hnd hpos
    rw [hratio]
    -- Convert ra.score to v for arithmetic
    have hv_eq : ∀ b, ra.score () b = v b := fun _ => by
      simp only [ra, RationalAction.fromScale]
    simp_rw [hv_eq]
    set S_R := ∑ b ∈ rest.toFinset, v b
    have hS_nn : 0 ≤ S_R := Finset.sum_nonneg fun b _ => le_of_lt (hv b)
    have h1thr : 0 < 1 - thr := by linarith
    have hvy_S : 0 < v y + S_R := by linarith [hv y]
    obtain ⟨_, hhi⟩ := hI
    simp only [pairwiseProb] at hhi
    have hvx_bound : v x * (1 - thr) ≤ thr * v y := by
      have : v x ≤ thr * (v x + v y) := by
        rwa [div_le_iff₀ (by linarith [hv x, hv y] : (0:ℝ) < v x + v y)] at hhi
      nlinarith
    suffices h : (v x + S_R) * (1 - thr) ≤ thr * (v y + S_R) from
      (div_le_div_iff₀ hvy_S h1thr).mpr h
    nlinarith [mul_nonneg hS_nn (show 0 ≤ 2 * thr - 1 from by linarith)]

-- ============================================================================
-- §5. Trace ordering matches expected rank ordering
-- ============================================================================

/-- The trace ordering from §1.G (Definition 4) matches the expected rank
    ordering from §2.F: `x ≥_T y` iff `E[rank(x)] ≤ E[rank(y)]`.

    By `trace_iff_scale_ge`, `x ≥_T y ↔ v(x) ≥ v(y)`.
    By `expectedRank_lt_of_score_gt`, `v(x) > v(y)` implies
    `E[rank(x)] < E[rank(y)]`. So the two orderings agree on strict preference.

    The `≤` case (when `v(x) = v(y)`) follows from `expectedRank_eq_of_score_eq`. -/
theorem traceGe_iff_expectedRank_le (v : A → ℝ) (hv : ∀ a, 0 < v a)
    (T : Finset A) (x y : A) (hx : x ∈ T) (hy : y ∈ T) (hne : x ≠ y) :
    traceGe v x y ↔
    expectedRank (RationalAction.fromScale v (λ a => le_of_lt (hv a))) () T x ≤
    expectedRank (RationalAction.fromScale v (λ a => le_of_lt (hv a))) () T y := by
  set ra := RationalAction.fromScale v (λ a => le_of_lt (hv a))
  have hpos' : ∀ a ∈ T, 0 < ra.score () a := fun a _ => hv a
  constructor
  · -- Forward: traceGe → v(y) ≤ v(x) → E[rank(x)] ≤ E[rank(y)]
    intro h
    rw [trace_iff_scale_ge v hv x y] at h
    rcases eq_or_lt_of_le h with heq | hlt
    · -- v(y) = v(x): equal scores → equal expected ranks
      exact le_of_eq (expectedRank_eq_of_score_eq ra () T x y hx hy hne hpos' heq.symm)
    · -- v(y) < v(x): strict monotonicity
      exact le_of_lt (expectedRank_lt_of_score_gt ra () T x y hx hy hne hpos' hlt)
  · -- Backward: E[rank(x)] ≤ E[rank(y)] → traceGe (contrapositive)
    intro hle
    rw [trace_iff_scale_ge v hv x y]
    by_contra h_not
    push_neg at h_not
    -- h_not : v x < v y, i.e., ra.score () y > ra.score () x
    have hgt : ra.score () y > ra.score () x := h_not
    have := expectedRank_lt_of_score_gt ra () T y x hy hx hne.symm hpos' hgt
    linarith

end Core
