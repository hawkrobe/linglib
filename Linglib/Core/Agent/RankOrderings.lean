import Linglib.Core.Agent.RationalAction

/-!
# Rank Orderings @cite{luce-1959}

@cite{luce-1959}: the probability of observing a complete rank
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

-/

namespace Core

open BigOperators Finset Real

variable {S A : Type*} [Fintype A] [DecidableEq A]

-- ============================================================================
-- §2.F Rank Orderings (@cite{luce-1959}, pp. 66–72)
-- ============================================================================

/-- The tail suffix of a list starting at position `i` (0-indexed).
    Used to represent the shrinking alternative set at each step of ranking. -/
def tailSuffix (ranking : List A) (i : Nat) : Finset A :=
  (ranking.drop i).toFinset

/-- Probability of a single step in the ranking: choosing `ranking[i]` from
    the remaining alternatives `{ranking[i], ranking[i+1],...}`. -/
noncomputable def rankStepProb (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) : ℝ :=
  match ranking[i]? with
  | none => 1
  | some a => ra.pChoice s (tailSuffix ranking i) a

/-- **Ranking probability** (@cite{luce-1959}, Theorem 9):
    The probability of observing the complete rank ordering `a₁ > a₂ >... > aₙ`
    is the product of successive top-choices from shrinking sets:

    `P(a₁ > a₂ >... > aₙ) = P(a₁ | {a₁,...,aₙ}) · P(a₂ | {a₂,...,aₙ}) ·... · P(aₙ₋₁ | {aₙ₋₁, aₙ})`

    Under the Luce model with ratio scale `v`, this becomes:
    `P(a₁ >... > aₙ) = ∏ᵢ v(aᵢ) / ∑ⱼ≥ᵢ v(aⱼ)` -/
noncomputable def rankProb (ra : RationalAction S A) (s : S) (ranking : List A) : ℝ :=
  (List.range ranking.length).foldl (λ acc i => acc * rankStepProb ra s ranking i) 1

/-- Recursive characterization of ranking probability: the first-choice probability
    times the ranking probability of the remaining alternatives. -/
noncomputable def rankProbRec (ra : RationalAction S A) (s : S) : List A → ℝ
  | [] => 1
  | a :: rest => ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest

/-- Foldl with multiplication factors out the initial value:
    `foldl (· * f ·) c xs = c * foldl (· * f ·) 1 xs`. -/
private theorem foldl_mul_comm_init (f : Nat → ℝ) (c : ℝ) :
    ∀ xs : List Nat, xs.foldl (fun acc i => acc * f i) c =
      c * xs.foldl (fun acc i => acc * f i) 1
  | [] => by simp
  | x :: xs => by
    simp only [List.foldl]
    rw [foldl_mul_comm_init f (c * f x) xs, foldl_mul_comm_init f (1 * f x) xs]
    ring

/-- Decompose foldl on range(n+1): peel off index 0 and shift the rest.
    Uses `List.range_succ_eq_map` and `List.foldl_map` from mathlib. -/
private theorem foldl_range_succ (f : Nat → ℝ) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc i => acc * f i) 1 =
    f 0 * (List.range n).foldl (fun acc i => acc * f (i + 1)) 1 := by
  rw [List.range_succ_eq_map]
  show (List.map Nat.succ (List.range n)).foldl (fun acc i => acc * f i) (1 * f 0) =
    f 0 * (List.range n).foldl (fun acc i => acc * f (i + 1)) 1
  rw [one_mul, List.foldl_map, foldl_mul_comm_init]

/-- `rankProbRec` agrees with the explicit `rankProb` definition.

    Proof by list induction. The key steps use:
    - `List.range_succ_eq_map` to decompose `range(n+1) = 0 :: map succ (range n)`
    - `List.foldl_map` to shift indices through the map
    - `foldl_mul_comm_init` to factor out the first-choice probability
    - Definitional equalities: `rankStepProb (a::rest) 0 = pChoice` and
      `rankStepProb (a::rest) (i+1) = rankStepProb rest i` -/
theorem rankProbRec_eq_rankProb (ra : RationalAction S A) (s : S) (ranking : List A) :
    rankProbRec ra s ranking = rankProb ra s ranking := by
  induction ranking with
  | nil => rfl
  | cons a rest ih =>
    show ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest =
      (List.range (rest.length + 1)).foldl
        (fun acc i => acc * rankStepProb ra s (a :: rest) i) 1
    rw [ih, rankProb, foldl_range_succ]
    -- Both sides now match by definitional equalities:
    -- rankStepProb (a::rest) 0 = pChoice (since (a::rest)[0]? = some a
    --   and tailSuffix (a::rest) 0 = (a::rest).toFinset)
    -- rankStepProb (a::rest) (i+1) = rankStepProb rest i (since
    --   (a::rest)[i+1]? = rest[i]? and tailSuffix (a::rest) (i+1) = tailSuffix rest i)
    congr 1

/-- Each `rankStepProb` is non-negative: either 1 (out of range) or `pChoice`. -/
private theorem rankStepProb_nonneg (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) :
    0 ≤ rankStepProb ra s ranking i := by
  simp only [rankStepProb]
  cases ranking[i]? with
  | none => linarith
  | some a => exact ra.pChoice_nonneg s _ a

private theorem foldl_mul_nonneg {f : Nat → ℝ} {init : ℝ}
    (hinit : 0 ≤ init) (hf : ∀ i, 0 ≤ f i) :
    ∀ l : List Nat, 0 ≤ l.foldl (fun acc i => acc * f i) init
  | [] => by simpa using hinit
  | x :: xs => foldl_mul_nonneg (mul_nonneg hinit (hf x)) hf xs

/-- Ranking probability is non-negative: each factor is a `pChoice` value,
    hence non-negative. -/
theorem rankProb_nonneg (ra : RationalAction S A) (s : S) (ranking : List A) :
    0 ≤ rankProb ra s ranking :=
  foldl_mul_nonneg one_pos.le (rankStepProb_nonneg ra s ranking) _

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

omit [Fintype A] in
/-- If `ranking[i]? = some a`, then `a` is in the tail suffix at position `i`.
    This is because `a = ranking[i]` is the head of `ranking.drop i`. -/
private theorem mem_tailSuffix_of_getElem?
    {ranking : List A} {i : Nat} {a : A}
    (h : ranking[i]? = some a) :
    a ∈ tailSuffix ranking i := by
  simp only [tailSuffix, List.mem_toFinset]
  have hi : i < ranking.length := by
    by_contra hc; push_neg at hc
    simp [List.getElem?_eq_none hc] at h
  rw [List.drop_eq_getElem_cons hi]
  have hval : ranking[i] = a := by
    have := List.getElem?_eq_getElem hi
    rw [h] at this; exact Option.some.inj this.symm
  rw [hval]; exact List.Mem.head _

/-- `rankStepProb` equals `scoreRatio` at every position: the `pChoice`
    formulation and the explicit score/sum formulation agree because
    `ranking[i]` is always in the tail suffix at position `i`. -/
private theorem rankStepProb_eq_scoreRatio (ra : RationalAction S A) (s : S)
    (ranking : List A) (i : Nat) :
    rankStepProb ra s ranking i = scoreRatio ra s ranking i := by
  simp only [rankStepProb, scoreRatio]
  cases h : ranking[i]? with
  | none => rfl
  | some a =>
    have hmem : a ∈ tailSuffix ranking i := mem_tailSuffix_of_getElem? h
    simp only [RationalAction.pChoice, hmem, ↓reduceIte]

/-- **Theorem 9 (score form)**: ranking probability equals the product of score ratios.

    Each `pChoice` factor equals the corresponding score ratio by definition of
    the Luce choice rule, so the two products are term-by-term equal. -/
theorem rankProb_eq_score_prod (ra : RationalAction S A) (s : S) (ranking : List A)
    (_hnd : ranking.Nodup) :
    rankProb ra s ranking = rankProbScoreProd ra s ranking := by
  simp only [rankProb, rankProbScoreProd]
  congr 1
  ext acc i
  exact congrArg (acc * ·) (rankStepProb_eq_scoreRatio ra s ranking i)

-- ============================================================================
-- Summation over permutations (Theorem 9, completeness)
-- ============================================================================

/-- All permutations of a finset, as lists. -/
noncomputable def allRankings (T : Finset A) : Finset (List A) :=
  T.val.toList.permutations.toFinset

omit [Fintype A] in
/-- Every ranking in `allRankings T` is a permutation of `T`.

    Uses `List.mem_permutations`, `List.perm_ext_iff_of_nodup`, and
    `Multiset.mem_toList` from mathlib to connect the List-level
    permutation API with Finset membership. -/
theorem mem_allRankings_iff (T : Finset A) (ranking : List A) :
    ranking ∈ allRankings T ↔ ranking.toFinset = T ∧ ranking.Nodup := by
  simp only [allRankings, List.mem_toFinset, List.mem_permutations]
  have hT_nodup : T.val.toList.Nodup := by
    rw [← Multiset.coe_nodup, Multiset.coe_toList]; exact T.nodup
  constructor
  · intro hperm
    constructor
    · ext x
      simp only [List.mem_toFinset]
      rw [hperm.mem_iff, Multiset.mem_toList]; exact Iff.rfl
    · exact hperm.nodup_iff.mpr hT_nodup
  · intro ⟨hfs, hnd⟩
    rw [List.perm_ext_iff_of_nodup hnd hT_nodup]
    intro x
    rw [← List.mem_toFinset (l := ranking), hfs,
        Multiset.mem_toList, Finset.mem_val]

-- ============================================================================
-- Decomposition of allRankings by first element
-- ============================================================================

/-- Cons into allRankings: if `rest ∈ allRankings (T.erase a)` and `a ∈ T`,
    then `a :: rest ∈ allRankings T`. -/
private theorem cons_mem_allRankings {T : Finset A} {a : A} {rest : List A}
    (ha : a ∈ T) (hrest : rest ∈ allRankings (T.erase a)) :
    a :: rest ∈ allRankings T := by
  rw [mem_allRankings_iff] at hrest ⊢
  obtain ⟨hfs, hnd⟩ := hrest
  constructor
  · simp only [List.toFinset_cons, hfs, Finset.insert_erase ha]
  · rw [List.nodup_cons]
    refine ⟨fun h => ?_, hnd⟩
    exact (Finset.mem_erase.mp (hfs ▸ List.mem_toFinset.mpr h)).1 rfl

/-- Extract first element: if `a :: rest ∈ allRankings T`,
    then `a ∈ T` and `rest ∈ allRankings (T.erase a)`. -/
private theorem of_cons_mem_allRankings {T : Finset A} {a : A} {rest : List A}
    (h : a :: rest ∈ allRankings T) :
    a ∈ T ∧ rest ∈ allRankings (T.erase a) := by
  rw [mem_allRankings_iff] at h
  obtain ⟨hfs, hnd⟩ := h
  rw [List.nodup_cons] at hnd
  constructor
  · have : a ∈ (a :: rest).toFinset := by simp
    rw [hfs] at this; exact this
  · rw [mem_allRankings_iff]
    constructor
    · rw [List.toFinset_cons] at hfs
      have ha_nin : a ∉ rest.toFinset := by rw [List.mem_toFinset]; exact hnd.1
      rw [← hfs, Finset.erase_insert ha_nin]
    · exact hnd.2

omit [Fintype A] in
/-- Rankings of a nonempty set are nonempty lists. -/
private theorem allRankings_ne_nil {T : Finset A} (hT : T.Nonempty)
    {r : List A} (hr : r ∈ allRankings T) : r ≠ [] := by
  intro heq; subst heq
  rw [mem_allRankings_iff] at hr
  simp at hr
  exact Finset.Nonempty.ne_empty hT hr.symm

/-- `allRankings T = ⋃_{a ∈ T} image (cons a) (allRankings (T.erase a))`. -/
private theorem allRankings_eq_biUnion (T : Finset A) (hT : T.Nonempty) :
    allRankings T = T.biUnion (fun a => (allRankings (T.erase a)).image (List.cons a)) := by
  ext r
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro hr
    have hne := allRankings_ne_nil hT hr
    obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨ha, hrest⟩ := of_cons_mem_allRankings hr
    exact ⟨a, ha, rest, hrest, rfl⟩
  · rintro ⟨a, ha, rest, hrest, rfl⟩
    exact cons_mem_allRankings ha hrest

/-- Cons-images for distinct first elements are disjoint. -/
private theorem cons_image_pairwise_disjoint (T : Finset A) :
    (T : Set A).PairwiseDisjoint
      (fun a => (allRankings (T.erase a)).image (List.cons a)) := by
  intro a _ b _ hab
  simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
  rintro r ⟨_, _, rfl⟩ ⟨_, _, h⟩
  exact hab (List.cons.inj h).1.symm

/-- Decompose a sum over `allRankings T` by first element. -/
private theorem sum_allRankings_by_first (T : Finset A) (hT : T.Nonempty)
    (f : List A → ℝ) :
    ∑ r ∈ allRankings T, f r =
    ∑ a ∈ T, ∑ rest ∈ allRankings (T.erase a), f (a :: rest) := by
  rw [allRankings_eq_biUnion T hT, Finset.sum_biUnion (cons_image_pairwise_disjoint T)]
  congr 1; ext a
  rw [Finset.sum_image]
  intro r₁ _ r₂ _ h
  exact List.cons.inj h |>.2

/-- `rankProb (a :: rest)` factors as `pChoice s T a * rankProb rest`
    when `(a :: rest).toFinset = T`. -/
private theorem rankProb_cons_eq (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (rest : List A)
    (hfs : (a :: rest).toFinset = T) :
    rankProb ra s (a :: rest) = ra.pChoice s T a * rankProb ra s rest := by
  rw [← rankProbRec_eq_rankProb, ← rankProbRec_eq_rankProb]
  show ra.pChoice s (a :: rest).toFinset a * rankProbRec ra s rest =
    ra.pChoice s T a * rankProbRec ra s rest
  rw [hfs]

-- ============================================================================
-- Theorem 9 completeness: ranking probabilities sum to 1
-- ============================================================================

/-- Score positivity propagates to erased subsets. -/
private theorem score_pos_erase {ra : RationalAction S A} {s : S}
    {T : Finset A} (hpos : ∀ a ∈ T, 0 < ra.score s a)
    (a : A) : ∀ b ∈ T.erase a, 0 < ra.score s b :=
  fun b hb => hpos b (Finset.mem_of_mem_erase hb)

/-- Score positivity implies nonzero sum over nonempty sets. -/
private theorem score_sum_ne_zero {ra : RationalAction S A} {s : S}
    {T : Finset A} (hT : T.Nonempty) (hpos : ∀ a ∈ T, 0 < ra.score s a) :
    ∑ b ∈ T, ra.score s b ≠ 0 := by
  obtain ⟨a, ha⟩ := hT
  exact ne_of_gt (Finset.sum_pos (fun b hb => hpos b hb) ⟨a, ha⟩)

/-- Core induction: ranking probabilities sum to 1 for any finset
    with strictly positive scores. -/
private theorem rankProb_sum_eq_one_aux (ra : RationalAction S A) (s : S) :
    ∀ (n : ℕ) (T : Finset A), T.card = n → (∀ a ∈ T, 0 < ra.score s a) →
    ∑ r ∈ allRankings T, rankProb ra s r = 1 := by
  intro n
  induction n with
  | zero =>
    intro T hcard _
    have hT_empty : T = ∅ := Finset.card_eq_zero.mp hcard
    subst hT_empty
    simp only [allRankings, Finset.empty_val, Multiset.toList_zero, List.permutations_nil,
               List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    simp [rankProb]
  | succ n ih =>
    intro T hcard hpos
    have hT : T.Nonempty := Finset.card_pos.mp (by omega)
    rw [sum_allRankings_by_first T hT]
    have step : ∀ a ∈ T,
        ∑ rest ∈ allRankings (T.erase a), rankProb ra s (a :: rest) =
        ra.pChoice s T a := by
      intro a ha
      have hcard_erase : (T.erase a).card = n := by
        rw [Finset.card_erase_of_mem ha, hcard]; omega
      have hpos_erase := score_pos_erase hpos a
      have : ∀ rest ∈ allRankings (T.erase a),
          rankProb ra s (a :: rest) = ra.pChoice s T a * rankProb ra s rest := by
        intro rest hrest
        apply rankProb_cons_eq
        rw [mem_allRankings_iff] at hrest
        simp [List.toFinset_cons, hrest.1, Finset.insert_erase ha]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
      rw [ih (T.erase a) hcard_erase hpos_erase, mul_one]
    rw [Finset.sum_congr rfl step]
    exact ra.pChoice_sum_eq_one s T (score_sum_ne_zero hT hpos)

/-- **Ranking probabilities sum to 1** (@cite{luce-1959}, Theorem 9 completeness):
    Over all `n!` permutations of the alternative set, ranking probabilities
    form a proper distribution.

    The proof proceeds by induction on `|T|`:
    - Base (`T = ∅`): `allRankings ∅ = {[]}`, `rankProb [] = 1`.
    - Step: decompose `allRankings T` by first element, factor out `pChoice`
      (which sums to 1 by `pChoice_sum_eq_one`), and apply the inductive
      hypothesis to each `(n-1)`-element ranking.

    Requires strictly positive scores (Luce's ratio scale assumption). -/
theorem rankProb_sum_eq_one (ra : RationalAction S A) (s : S)
    (T : Finset A) (hT : T.Nonempty)
    (hpos : ∀ a ∈ T, 0 < ra.score s a) :
    ∑ r ∈ allRankings T, rankProb ra s r = 1 :=
  rankProb_sum_eq_one_aux ra s T.card T rfl hpos

-- ============================================================================
-- Marginalization (recovering pChoice)
-- ============================================================================

/-- Rankings starting with a given element `a`. -/
noncomputable def rankingsStartingWith (T : Finset A) (a : A) : Finset (List A) :=
  (allRankings T).filter (λ r => r.head? = some a)

/-- Rankings starting with `a` biject with `allRankings (T.erase a)` via cons. -/
private theorem rankingsStartingWith_eq (T : Finset A) (a : A) (ha : a ∈ T) :
    rankingsStartingWith T a = (allRankings (T.erase a)).image (List.cons a) := by
  ext r
  simp only [rankingsStartingWith, Finset.mem_filter, Finset.mem_image]
  constructor
  · intro ⟨hr, hhead⟩
    obtain ⟨a', rest, rfl⟩ : ∃ a' rest, r = a' :: rest := by
      cases r with
      | nil => simp at hhead
      | cons a' rest => exact ⟨a', rest, rfl⟩
    simp at hhead; subst hhead
    obtain ⟨_, hrest⟩ := of_cons_mem_allRankings hr
    exact ⟨rest, hrest, rfl⟩
  · rintro ⟨rest, hrest, rfl⟩
    exact ⟨cons_mem_allRankings ha hrest, by simp⟩

/-- **Marginal first-choice** (@cite{luce-1959}, Theorem 9 corollary):
    Summing the ranking probability over all rankings that start with `a`
    recovers the choice probability `pChoice(a, T)`.

    This is because `P(a first) = P(a | T) · ∑_σ P(σ | T \ {a}) = P(a | T) · 1`,
    where the inner sum equals 1 by `rankProb_sum_eq_one` on the remaining
    alternatives. -/
theorem rankProb_marginal_first (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    ∑ r ∈ rankingsStartingWith T a, rankProb ra s r = ra.pChoice s T a := by
  rw [rankingsStartingWith_eq T a ha]
  rw [Finset.sum_image (fun r₁ _ r₂ _ h => (List.cons.inj h).2)]
  have hrw : ∀ rest ∈ allRankings (T.erase a),
      rankProb ra s (a :: rest) = ra.pChoice s T a * rankProb ra s rest := by
    intro rest hrest
    apply rankProb_cons_eq
    rw [mem_allRankings_iff] at hrest
    simp [List.toFinset_cons, hrest.1, Finset.insert_erase ha]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have hcard_pos : 0 < (T.erase a).card ∨ (T.erase a).card = 0 := by omega
  rcases hcard_pos with hcp | hcp
  · rw [rankProb_sum_eq_one_aux ra s (T.erase a).card (T.erase a) rfl
          (score_pos_erase hpos a), mul_one]
  · have : T.erase a = ∅ := Finset.card_eq_zero.mp hcp
    simp only [this, allRankings, Finset.empty_val, Multiset.toList_zero,
               List.permutations_nil, List.toFinset_cons, List.toFinset_nil,
               Finset.insert_empty, Finset.sum_singleton, rankProb]
    simp [mul_one]

-- ============================================================================
-- Expected rank monotonicity
-- ============================================================================

/-- The rank of element `a` in a ranking (1-indexed, so rank 1 = best).
    Returns 0 if `a` is not in the ranking. -/
def rankOf (ranking : List A) (a : A) : Nat :=
  if a ∈ ranking then ranking.findIdx (· == a) + 1 else 0

/-- Expected rank of alternative `a` under the ranking distribution.

    `E[rank(a)] = ∑_σ P(σ) · rank(a, σ)`

    The monotonicity theorem `expectedRank_lt_of_score_gt` shows that
    alternatives with higher `v(a)` have lower (better) expected rank. -/
noncomputable def expectedRank (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) : ℝ :=
  ∑ r ∈ allRankings T, rankProb ra s r * (rankOf r a : ℝ)

-- ============================================================================
-- Expected rank monotonicity: infrastructure
-- ============================================================================

/-- `rankOf (a :: rest) a = 1`: the first element has rank 1. -/
private theorem rankOf_cons_self (a : A) (rest : List A) :
    rankOf (a :: rest) a = 1 := by
  simp [rankOf, List.findIdx_cons]

/-- `rankOf (b :: rest) a = rankOf rest a + 1` when `b ≠ a` and `a ∈ rest`. -/
private theorem rankOf_cons_ne {b a : A} {rest : List A}
    (hne : b ≠ a) (ha : a ∈ rest) :
    rankOf (b :: rest) a = rankOf rest a + 1 := by
  have hmem : a ∈ b :: rest := List.mem_cons_of_mem b ha
  simp only [rankOf, hmem, ha, ↓reduceIte, List.findIdx_cons]
  simp [show (b == a) = false from by simp [hne]]

/-- Positive scores imply strictly positive `pChoice`. -/
private theorem pChoice_pos {ra : RationalAction S A} {s : S}
    {T : Finset A} {a : A} (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    0 < ra.pChoice s T a := by
  have hsum_pos : 0 < ∑ b ∈ T, ra.score s b :=
    Finset.sum_pos (fun b hb => hpos b hb) ⟨a, ha⟩
  simp only [RationalAction.pChoice, ha, ne_of_gt hsum_pos, ↓reduceIte]
  exact div_pos (hpos a ha) hsum_pos

/-- Higher score implies higher `pChoice` in the same set. -/
private theorem pChoice_gt_of_score_gt {ra : RationalAction S A} {s : S}
    {T : Finset A} {a₁ a₂ : A} (ha₁ : a₁ ∈ T) (ha₂ : a₂ ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b)
    (hgt : ra.score s a₁ > ra.score s a₂) :
    ra.pChoice s T a₁ > ra.pChoice s T a₂ := by
  have hratio := ra.pChoice_ratio s T a₁ a₂ ha₁ ha₂
  have hp₂ := pChoice_pos ha₂ hpos
  have hv₂ := hpos a₂ ha₂
  -- From ratio: pChoice(a₁) * v(a₂) = pChoice(a₂) * v(a₁) > pChoice(a₂) * v(a₂)
  have h : ra.pChoice s T a₂ * ra.score s a₂ < ra.pChoice s T a₁ * ra.score s a₂ := by
    rw [show ra.pChoice s T a₁ * ra.score s a₂ =
      ra.pChoice s T a₂ * ra.score s a₁ from hratio]
    exact mul_lt_mul_of_pos_left hgt hp₂
  -- Divide both sides by v(a₂) > 0
  exact lt_of_mul_lt_mul_right h (le_of_lt hv₂)

-- ============================================================================
-- Expected rank decomposition: E[rank(a,T)] = 1 + ∑_{b≠a} pChoice(b) · E[rank(a,T\{b})]
-- ============================================================================

/-- Inner sum when the first element equals `a`: contributes `pChoice(a, T)`. -/
private theorem expectedRank_first_self (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    ∑ rest ∈ allRankings (T.erase a),
      rankProb ra s (a :: rest) * (rankOf (a :: rest) a : ℝ) =
    ra.pChoice s T a := by
  have hsub : ∀ rest ∈ allRankings (T.erase a),
      rankProb ra s (a :: rest) * (rankOf (a :: rest) a : ℝ) =
      ra.pChoice s T a * rankProb ra s rest := by
    intro rest hrest
    rw [show (rankOf (a :: rest) a : ℝ) = 1 from by simp [rankOf_cons_self]]
    rw [mul_one]
    apply rankProb_cons_eq
    rw [mem_allRankings_iff] at hrest
    simp [List.toFinset_cons, hrest.1, Finset.insert_erase ha]
  rw [Finset.sum_congr rfl hsub, ← Finset.mul_sum,
      rankProb_sum_eq_one_aux ra s _ _ rfl (score_pos_erase hpos a), mul_one]

/-- Inner sum when first element is `b ≠ a`:
    contributes `pChoice(b, T) · (1 + E[rank(a, T\{b})])`. -/
private theorem expectedRank_first_ne (ra : RationalAction S A) (s : S)
    (T : Finset A) (a b : A) (ha : a ∈ T) (hb : b ∈ T) (hne : b ≠ a)
    (hpos : ∀ c ∈ T, 0 < ra.score s c) :
    ∑ rest ∈ allRankings (T.erase b),
      rankProb ra s (b :: rest) * (rankOf (b :: rest) a : ℝ) =
    ra.pChoice s T b * (1 + expectedRank ra s (T.erase b) a) := by
  have ha_erase : a ∈ T.erase b := Finset.mem_erase.mpr ⟨hne.symm, ha⟩
  have ha_rest : ∀ rest ∈ allRankings (T.erase b), a ∈ rest := by
    intro rest hrest
    rw [mem_allRankings_iff] at hrest
    exact List.mem_toFinset.mp (hrest.1 ▸ ha_erase)
  have hsub : ∀ rest ∈ allRankings (T.erase b),
      rankProb ra s (b :: rest) * (rankOf (b :: rest) a : ℝ) =
      ra.pChoice s T b * (rankProb ra s rest * (rankOf rest a : ℝ) +
        rankProb ra s rest) := by
    intro rest hrest
    have hfact : rankProb ra s (b :: rest) = ra.pChoice s T b * rankProb ra s rest := by
      apply rankProb_cons_eq
      rw [mem_allRankings_iff] at hrest
      simp [List.toFinset_cons, hrest.1, Finset.insert_erase hb]
    have hrk : (rankOf (b :: rest) a : ℝ) = (rankOf rest a : ℝ) + 1 := by
      rw [rankOf_cons_ne hne (ha_rest rest hrest)]; push_cast; ring
    rw [hfact, hrk]; ring
  rw [Finset.sum_congr rfl hsub, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [rankProb_sum_eq_one_aux ra s _ _ rfl (score_pos_erase hpos b)]
  unfold expectedRank; congr 1; ring

/-- **Expected rank decomposition**: conditioning on the first element.
    `E[rank(a, T)] = 1 + ∑_{b ∈ T\{a}} pChoice(b, T) · E[rank(a, T\{b})]` -/
private theorem expectedRank_decomp (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    expectedRank ra s T a =
    1 + ∑ b ∈ T.erase a, ra.pChoice s T b * expectedRank ra s (T.erase b) a := by
  have hT : T.Nonempty := ⟨a, ha⟩
  show ∑ r ∈ allRankings T, rankProb ra s r * (rankOf r a : ℝ) =
    1 + ∑ b ∈ T.erase a, ra.pChoice s T b * expectedRank ra s (T.erase b) a
  rw [sum_allRankings_by_first T hT]
  -- Split: ∑_{b ∈ T} = f(a) + ∑_{b ∈ T.erase a}
  rw [← Finset.add_sum_erase T _ ha]
  rw [expectedRank_first_self ra s T a ha hpos]
  -- Rewrite each b ≠ a term
  have h_ne : ∀ b ∈ T.erase a,
      (∑ rest ∈ allRankings (T.erase b),
        rankProb ra s (b :: rest) * (rankOf (b :: rest) a : ℝ)) =
      ra.pChoice s T b * (1 + expectedRank ra s (T.erase b) a) := by
    intro b hb
    exact expectedRank_first_ne ra s T a b ha (Finset.mem_of_mem_erase hb)
      (ne_of_mem_erase hb) hpos
  rw [Finset.sum_congr rfl h_ne]
  -- pChoice(a) + ∑ pChoice(b) * (1 + E[...]) = 1 + ∑ pChoice(b) * E[...]
  have hexpand : ∀ b ∈ T.erase a,
      ra.pChoice s T b * (1 + expectedRank ra s (T.erase b) a) =
      ra.pChoice s T b + ra.pChoice s T b * expectedRank ra s (T.erase b) a :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib]
  have h1 : ra.pChoice s T a + ∑ b ∈ T.erase a, ra.pChoice s T b = 1 := by
    rw [Finset.add_sum_erase T _ ha]
    exact ra.pChoice_sum_eq_one s T (score_sum_ne_zero hT hpos)
  linarith

/-- For `a ∈ T`, `rankOf r a ≥ 1` for any ranking `r ∈ allRankings T`. -/
private theorem rankOf_ge_one_of_mem {T : Finset A} {a : A} (ha : a ∈ T)
    {r : List A} (hr : r ∈ allRankings T) : 1 ≤ rankOf r a := by
  rw [mem_allRankings_iff] at hr
  have : a ∈ r := List.mem_toFinset.mp (hr.1 ▸ ha)
  simp [rankOf, this]

/-- Expected rank is at least 1 for any element in the set. -/
private theorem expectedRank_ge_one (ra : RationalAction S A) (s : S)
    (T : Finset A) (a : A) (ha : a ∈ T)
    (hpos : ∀ b ∈ T, 0 < ra.score s b) :
    1 ≤ expectedRank ra s T a := by
  have hT : T.Nonempty := ⟨a, ha⟩
  -- E[rank(a)] = ∑ P(r) * rank(r,a) ≥ ∑ P(r) * 1 = 1
  calc expectedRank ra s T a
      = ∑ r ∈ allRankings T, rankProb ra s r * (rankOf r a : ℝ) := rfl
    _ ≥ ∑ r ∈ allRankings T, rankProb ra s r * 1 := by
        apply Finset.sum_le_sum; intro r hr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast rankOf_ge_one_of_mem ha hr)
          (rankProb_nonneg ra s r)
    _ = 1 := by simp [rankProb_sum_eq_one ra s T hT hpos]

-- ============================================================================
-- Cross-set monotonicity
-- ============================================================================

/-- Singleton expected rank: `E[rank(a, {a})] = 1`. -/
private theorem expectedRank_singleton (ra : RationalAction S A) (s : S) (a : A)
    (hpos : 0 < ra.score s a) :
    expectedRank ra s {a} a = 1 := by
  have hpos' : ∀ b ∈ ({a} : Finset A), 0 < ra.score s b := by simp; exact hpos
  rw [expectedRank_decomp ra s {a} a (Finset.mem_singleton_self a) hpos']
  simp [Finset.erase_singleton]

/-- `pChoice(c, S₁) ≤ pChoice(c, S₂)` when `S₁` has a higher-scored element than `S₂`.
    `S₁ = insert a₁ C`, `S₂ = insert a₂ C`, `v(a₁) ≥ v(a₂)`, `c ∈ C`. -/
private theorem pChoice_cross_le {ra : RationalAction S A} {s : S}
    {S₁ S₂ : Finset A} {c : A} (hc₁ : c ∈ S₁) (hc₂ : c ∈ S₂)
    (hpos₁ : ∀ b ∈ S₁, 0 < ra.score s b)
    (hpos₂ : ∀ b ∈ S₂, 0 < ra.score s b)
    (hsum_le : ∑ b ∈ S₂, ra.score s b ≤ ∑ b ∈ S₁, ra.score s b) :
    ra.pChoice s S₁ c ≤ ra.pChoice s S₂ c := by
  have hsum₁_pos : 0 < ∑ b ∈ S₁, ra.score s b :=
    Finset.sum_pos (fun b hb => hpos₁ b hb) ⟨c, hc₁⟩
  have hsum₂_pos : 0 < ∑ b ∈ S₂, ra.score s b :=
    Finset.sum_pos (fun b hb => hpos₂ b hb) ⟨c, hc₂⟩
  simp only [RationalAction.pChoice, hc₁, hc₂, ne_of_gt hsum₁_pos, ne_of_gt hsum₂_pos, ↓reduceIte]
  exact div_le_div_of_nonneg_left (le_of_lt (hpos₁ c hc₁)) hsum₂_pos hsum_le

/-- **Cross-set monotonicity**: a higher-scored element gets a better expected rank
    when competing against the same field.

    If `S₁ = insert a₁ C` and `S₂ = insert a₂ C` with `v(a₁) ≥ v(a₂)`, then
    `E[rank(a₁, S₁)] ≤ E[rank(a₂, S₂)]`.

    Proof by induction on `|C|`. The decomposition
    `E[rank(aᵢ, Sᵢ)] = 1 + ∑_{c∈C} pChoice(c, Sᵢ) · E[rank(aᵢ, Sᵢ\{c})]`
    gives a term-by-term comparison: `pChoice(c, S₂) ≥ pChoice(c, S₁)` (larger
    denominator for S₁) and `E[rank(a₂, S₂\{c})] ≥ E[rank(a₁, S₁\{c})]` (by IH). -/
private theorem expectedRank_cross_le_aux (ra : RationalAction S A) (s : S) :
    ∀ (n : ℕ) (C : Finset A) (a₁ a₂ : A),
    C.card = n → (ha₁ : a₁ ∉ C) → (ha₂ : a₂ ∉ C) →
    (∀ b ∈ insert a₁ C, 0 < ra.score s b) →
    (∀ b ∈ insert a₂ C, 0 < ra.score s b) →
    ra.score s a₁ ≥ ra.score s a₂ →
    expectedRank ra s (insert a₁ C) a₁ ≤
    expectedRank ra s (insert a₂ C) a₂ := by
  intro n
  induction n with
  | zero =>
    intro C a₁ a₂ hcard ha₁ ha₂ hpos₁ hpos₂ _
    have hC : C = ∅ := Finset.card_eq_zero.mp hcard
    subst hC
    simp only [Finset.insert_empty]
    have h₁ := expectedRank_singleton ra s a₁ (hpos₁ a₁ (Finset.mem_singleton_self a₁))
    have h₂ := expectedRank_singleton ra s a₂ (hpos₂ a₂ (Finset.mem_singleton_self a₂))
    linarith
  | succ n ih =>
    intro C a₁ a₂ hcard ha₁ ha₂ hpos₁ hpos₂ hge
    -- Decompose: E[rank(aᵢ, Sᵢ)] = 1 + ∑_{c ∈ C} pChoice(c, Sᵢ) * E[rank(aᵢ, Sᵢ\{c})]
    -- where Sᵢ = insert aᵢ C, Sᵢ.erase aᵢ = C
    rw [expectedRank_decomp ra s _ a₁ (Finset.mem_insert_self a₁ C) hpos₁,
        expectedRank_decomp ra s _ a₂ (Finset.mem_insert_self a₂ C) hpos₂,
        Finset.erase_insert ha₁, Finset.erase_insert ha₂]
    -- Goal: 1 + ∑_{c∈C} p(c,S₁)·E₁(c) ≤ 1 + ∑_{c∈C} p(c,S₂)·E₂(c)
    suffices h : ∑ c ∈ C, ra.pChoice s (insert a₁ C) c *
          expectedRank ra s ((insert a₁ C).erase c) a₁ ≤
        ∑ c ∈ C, ra.pChoice s (insert a₂ C) c *
          expectedRank ra s ((insert a₂ C).erase c) a₂ by linarith
    -- Two-step inequality: ∑ p₁·E₁ ≤ ∑ p₁·E₂ ≤ ∑ p₂·E₂
    -- where E_i(c) = expectedRank(aᵢ, Sᵢ\{c}) and Sᵢ\{c} = insert aᵢ (C\{c})
    have hS₁_erase : ∀ c ∈ C, (insert a₁ C).erase c = insert a₁ (C.erase c) :=
      fun c hc => Finset.erase_insert_of_ne (fun h => ha₁ (h ▸ hc))
    have hS₂_erase : ∀ c ∈ C, (insert a₂ C).erase c = insert a₂ (C.erase c) :=
      fun c hc => Finset.erase_insert_of_ne (fun h => ha₂ (h ▸ hc))
    -- Sum over S₂ ≤ sum over S₁ (for pChoice_cross_le)
    have hsum_le : ∑ b ∈ insert a₂ C, ra.score s b ≤ ∑ b ∈ insert a₁ C, ra.score s b := by
      rw [Finset.sum_insert ha₁, Finset.sum_insert ha₂]; linarith
    calc ∑ c ∈ C, ra.pChoice s (insert a₁ C) c *
              expectedRank ra s ((insert a₁ C).erase c) a₁
        ≤ ∑ c ∈ C, ra.pChoice s (insert a₁ C) c *
              expectedRank ra s ((insert a₂ C).erase c) a₂ := by
          apply Finset.sum_le_sum; intro c hc
          apply mul_le_mul_of_nonneg_left _ (ra.pChoice_nonneg s _ c)
          rw [hS₁_erase c hc, hS₂_erase c hc]
          have hcard_c : (C.erase c).card = n := by
            rw [Finset.card_erase_of_mem hc, hcard]; omega
          have hsub₁ : insert a₁ (C.erase c) ⊆ insert a₁ C :=
            Finset.insert_subset_insert a₁ (Finset.erase_subset c C)
          have hsub₂ : insert a₂ (C.erase c) ⊆ insert a₂ C :=
            Finset.insert_subset_insert a₂ (Finset.erase_subset c C)
          exact ih (C.erase c) a₁ a₂ hcard_c
            (fun h => ha₁ (Finset.mem_of_mem_erase h))
            (fun h => ha₂ (Finset.mem_of_mem_erase h))
            (fun b hb => hpos₁ b (hsub₁ hb))
            (fun b hb => hpos₂ b (hsub₂ hb))
            hge
      _ ≤ ∑ c ∈ C, ra.pChoice s (insert a₂ C) c *
              expectedRank ra s ((insert a₂ C).erase c) a₂ := by
          apply Finset.sum_le_sum; intro c hc
          apply mul_le_mul_of_nonneg_right
          · exact pChoice_cross_le (Finset.mem_insert_of_mem hc) (Finset.mem_insert_of_mem hc)
              hpos₁ hpos₂ hsum_le
          · have hc_ne₂ : c ≠ a₂ := fun h => ha₂ (h ▸ hc)
            have ha₂_mem_erase : a₂ ∈ (insert a₂ C).erase c :=
              Finset.mem_erase.mpr ⟨hc_ne₂.symm, Finset.mem_insert_self a₂ C⟩
            linarith [expectedRank_ge_one ra s ((insert a₂ C).erase c) a₂ ha₂_mem_erase
              (fun b hb => hpos₂ b (Finset.mem_of_mem_erase hb))]

/-- **Theorem 10 (monotonicity)**: higher score implies lower expected rank.

    If `v(a₁) > v(a₂)` then `E[rank(a₁)] < E[rank(a₂)]`: the alternative
    with higher ratio-scale value is expected to be ranked higher (closer to 1).

    The proof uses conditional expectation decomposition:
    `E[rank(a, T)] = 1 + ∑_{b≠a} pChoice(b,T) · E[rank(a, T\{b})]`
    and combines within-set induction with cross-set monotonicity
    (a higher-scored element gets better expected rank against the same field). -/
theorem expectedRank_lt_of_score_gt (ra : RationalAction S A) (s : S)
    (T : Finset A) (a₁ a₂ : A) (ha₁ : a₁ ∈ T) (ha₂ : a₂ ∈ T)
    (hne : a₁ ≠ a₂)
    (hpos : ∀ a ∈ T, 0 < ra.score s a)
    (hgt : ra.score s a₁ > ra.score s a₂) :
    expectedRank ra s T a₁ < expectedRank ra s T a₂ := by
  -- Induction on |T|
  suffices h : ∀ (n : ℕ) (T : Finset A), T.card = n → a₁ ∈ T → a₂ ∈ T →
      (∀ a ∈ T, 0 < ra.score s a) →
      expectedRank ra s T a₁ < expectedRank ra s T a₂ from
    h T.card T rfl ha₁ ha₂ hpos
  intro n; induction n with
  | zero => intro T hcard h₁; simp [Finset.card_eq_zero.mp hcard] at h₁
  | succ m ih =>
    intro T hcard ha₁' ha₂' hpos'
    -- Decompose both expected ranks
    rw [expectedRank_decomp ra s T a₁ ha₁' hpos',
        expectedRank_decomp ra s T a₂ ha₂' hpos']
    -- Split off the special terms: a₂ from T\{a₁}, a₁ from T\{a₂}
    have ha₂_e₁ : a₂ ∈ T.erase a₁ := Finset.mem_erase.mpr ⟨hne.symm, ha₂'⟩
    have ha₁_e₂ : a₁ ∈ T.erase a₂ := Finset.mem_erase.mpr ⟨hne, ha₁'⟩
    rw [← Finset.add_sum_erase _ _ ha₂_e₁, ← Finset.add_sum_erase _ _ ha₁_e₂]
    -- Unify the common field: (T\{a₁})\{a₂} = (T\{a₂})\{a₁}
    rw [show (T.erase a₂).erase a₁ = (T.erase a₁).erase a₂ from Finset.erase_right_comm]
    -- Goal: 1 + (p₂*E₁' + Σ₁) < 1 + (p₁*E₂' + Σ₂) where both sums are over R
    -- Fact 1: common terms satisfy Σ₁ ≤ Σ₂ (by IH giving < hence ≤)
    have h_sums : ∀ c ∈ (T.erase a₁).erase a₂,
        ra.pChoice s T c * expectedRank ra s (T.erase c) a₁ ≤
        ra.pChoice s T c * expectedRank ra s (T.erase c) a₂ := by
      intro c hc
      apply mul_le_mul_of_nonneg_left _ (ra.pChoice_nonneg s T c)
      have hc_mem : c ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
      have ha₁_ec : a₁ ∈ T.erase c :=
        Finset.mem_erase.mpr ⟨((Finset.mem_erase.mp (Finset.mem_of_mem_erase hc)).1).symm, ha₁'⟩
      have ha₂_ec : a₂ ∈ T.erase c :=
        Finset.mem_erase.mpr ⟨((Finset.mem_erase.mp hc).1).symm, ha₂'⟩
      have hcard_ec : (T.erase c).card = m := by
        rw [Finset.card_erase_of_mem hc_mem, hcard]; omega
      exact le_of_lt (ih (T.erase c) hcard_ec ha₁_ec ha₂_ec (score_pos_erase hpos' c))
    -- Fact 2: cross term satisfies p₂*E₁' < p₁*E₂'
    have h_cross : ra.pChoice s T a₂ * expectedRank ra s (T.erase a₂) a₁ <
        ra.pChoice s T a₁ * expectedRank ra s (T.erase a₁) a₂ := by
      have hp_gt := pChoice_gt_of_score_gt ha₁' ha₂' hpos' hgt
      have hE₁'_ge := expectedRank_ge_one ra s (T.erase a₂) a₁ ha₁_e₂ (score_pos_erase hpos' a₂)
      -- Cross-set comparison: E₁' ≤ E₂'
      have hE_cross : expectedRank ra s (T.erase a₂) a₁ ≤
          expectedRank ra s (T.erase a₁) a₂ := by
        conv_lhs => rw [show T.erase a₂ = insert a₁ ((T.erase a₁).erase a₂) from by
          rw [← Finset.erase_right_comm]; exact (Finset.insert_erase ha₁_e₂).symm]
        conv_rhs => rw [show T.erase a₁ = insert a₂ ((T.erase a₁).erase a₂) from
          (Finset.insert_erase ha₂_e₁).symm]
        exact expectedRank_cross_le_aux ra s _ _ a₁ a₂ rfl
          (mt Finset.mem_of_mem_erase (Finset.notMem_erase a₁ T))
          (Finset.notMem_erase a₂ _)
          (fun b hb => hpos' b (by
            rcases Finset.mem_insert.mp hb with rfl | hb'
            · assumption
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb')))
          (fun b hb => hpos' b (by
            rcases Finset.mem_insert.mp hb with rfl | hb'
            · assumption
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb')))
          (le_of_lt hgt)
      -- p₁*E₂' ≥ p₁*E₁' > p₂*E₁'
      calc ra.pChoice s T a₂ * expectedRank ra s (T.erase a₂) a₁
          < ra.pChoice s T a₁ * expectedRank ra s (T.erase a₂) a₁ :=
            mul_lt_mul_of_pos_right hp_gt (by linarith)
        _ ≤ ra.pChoice s T a₁ * expectedRank ra s (T.erase a₁) a₂ :=
            mul_le_mul_of_nonneg_left hE_cross (le_of_lt (pChoice_pos ha₁' hpos'))
    -- Combine: 1 + p₂*E₁' + Σ₁ < 1 + p₁*E₂' + Σ₂
    linarith [Finset.sum_le_sum h_sums]

end Core
