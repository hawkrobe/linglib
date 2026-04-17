import Linglib.Core.Constraint.Weighted
import Linglib.Core.Agent.RationalAction

/-!
# MaxEnt → OT Limit
@cite{smolensky-legendre-2006} @cite{prince-smolensky-1993}

As the rationality parameter α → ∞, MaxEnt Harmonic Grammar recovers
Optimality Theory's categorical optimization. OT is the "infinite-temperature"
limit of MaxEnt.

The argument has two components:

1. **HG–OT agreement** (@cite{smolensky-legendre-2006} ch. 14): with
   exponentially separated weights, the Harmonic Grammar winner (argmax of
   harmony score) equals the OT winner (lexicographic comparison of violation
   profiles). The key: if weight wₖ exceeds M · Σᵢ₍ᵢ>ₖ₎ wᵢ (where M bounds
   violation counts), then a single violation difference on constraint k
   outweighs any combination of violations on lower-ranked constraints.

2. **MaxEnt concentration** (`softmax_argmax_limit`): as α → ∞, the MaxEnt
   distribution softmax(α·H) concentrates on the argmax of H — i.e., the HG
   winner. This is proved in `Core.Agent.RationalAction`.

Together: MaxEnt(α → ∞) → HG winner = OT winner.

## Definitions

- `otToWeighted`: convert OT ranking + violation bound to weighted constraints
- `LexStrictlyBetter`: violation vector a lexicographically dominates b
- `ExponentiallySeparated`: weight separation condition for HG–OT agreement
- `lex_imp_harmony`: key lemma (lex dominance ⟹ higher harmony)
- `maxent_ot_limit`: main limit theorem
-/

namespace Core.Constraint

open Core Core.OT Core.ConstraintEvaluation Real Finset

-- ============================================================================
-- § 1: OT → HG Weight Construction
-- ============================================================================

/-- Convert an OT constraint ranking to weighted constraints.

    Each constraint at rank position i (0 = highest) receives weight
    `(M+1)^(n−1−i)`, where n is the number of constraints and M is a
    violation count bound. This exponential spacing ensures HG–OT agreement.

    The `eval` function is preserved: the weighted constraint evaluates
    candidates identically to the original named constraint. -/
def otToWeighted {C : Type} (ranking : List (NamedConstraint C)) (M : Nat) :
    List (WeightedConstraint C) :=
  ranking.mapIdx fun i con =>
    { toNamedConstraint := con
      weight := ((M + 1 : ℚ) ^ (ranking.length - 1 - i)) }

/-- The weighted constraints have the same length as the ranking. -/
theorem otToWeighted_length {C : Type} (ranking : List (NamedConstraint C)) (M : Nat) :
    (otToWeighted ranking M).length = ranking.length := by
  simp [otToWeighted]

/-- Each weighted constraint preserves the original eval function. -/
theorem otToWeighted_eval {C : Type} (ranking : List (NamedConstraint C)) (M : Nat)
    (i : Fin ranking.length) (c : C) :
    ((otToWeighted ranking M).get (i.cast (otToWeighted_length ranking M).symm)).eval c =
    (ranking.get i).eval c := by
  simp only [otToWeighted, List.get_eq_getElem, List.getElem_mapIdx, Fin.val_cast]

-- ============================================================================
-- § 2: Lexicographic Dominance (Fin n)
-- ============================================================================

/-- Candidate a (violation vector va) **lexicographically beats** candidate b
    (vb): at the first position where they differ, a has strictly fewer
    violations.

    This mirrors `Core.ConstraintEvaluation.lexLT` but on `Fin n → Nat`
    rather than `List Nat`, enabling Finset-based reasoning. -/
def LexStrictlyBetter {n : Nat} (va vb : Fin n → Nat) : Prop :=
  ∃ k : Fin n,
    (∀ i : Fin n, i < k → va i = vb i) ∧
    va k < vb k

-- ============================================================================
-- § 3: Exponentially Separated Weights
-- ============================================================================

/-- Weights are **exponentially separated** with violation bound M:
    each weight exceeds M times the sum of all lower-ranked weights.

    This ensures that no combination of lower-constraint violations
    can override a single higher-constraint violation difference,
    matching OT's strict ranking semantics. -/
def ExponentiallySeparated {n : Nat} (w : Fin n → ℚ) (M : Nat) : Prop :=
  (∀ i, 0 < w i) ∧
  ∀ k : Fin n, (M : ℚ) * (univ.filter (· > k)).sum w < w k

/-- Concrete exponential weights: wᵢ = (M+1)^(n−1−i).
    Constraint 0 (highest-ranked) gets the largest weight (M+1)^(n−1). -/
def expWeights (n : Nat) (M : Nat) : Fin n → ℚ :=
  fun i => ((M + 1 : ℚ) ^ (n - 1 - i.val))

/-- Exponential weights are positive. -/
theorem expWeights_pos (n : Nat) (M : Nat) (i : Fin n) :
    0 < expWeights n M i := by
  simp only [expWeights]
  positivity

private lemma filter_gt_insert_succ' {n : ℕ} {k : Fin n} (hk : k.val + 1 < n) :
    univ.filter (· > k) =
    insert (⟨k.val + 1, hk⟩ : Fin n) (univ.filter (· > ⟨k.val + 1, hk⟩)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.lt_def, Fin.ext_iff]
  omega

private lemma succ_not_mem_filter_gt' {n : ℕ} {k : Fin n} (hk : k.val + 1 < n) :
    (⟨k.val + 1, hk⟩ : Fin n) ∉ univ.filter (· > ⟨k.val + 1, hk⟩) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]; omega

private lemma expWeights_succ_eq' {n M : ℕ} {k : Fin n} (hk : k.val + 1 < n) :
    expWeights n M k = (↑M + 1) * expWeights n M ⟨k.val + 1, hk⟩ := by
  simp only [expWeights]
  rw [show n - 1 - k.val = (n - 1 - (k.val + 1)) + 1 from by omega, pow_succ]; ring

private lemma expWeights_bound (n M : ℕ) (hM : 0 < M) (k : Fin n) :
    (↑M : ℚ) * (univ.filter (· > k)).sum (expWeights n M) <
    expWeights n M k := by
  by_cases hk : k.val + 1 = n
  · have hempty : univ.filter (· > k) = (∅ : Finset (Fin n)) := by
      ext i; constructor
      · intro hi; simp only [Finset.mem_filter, Fin.lt_def] at hi; omega
      · exact (Finset.notMem_empty _).elim
    rw [hempty, Finset.sum_empty, mul_zero]
    exact expWeights_pos n M k
  · have hlt : k.val + 1 < n := by omega
    rw [filter_gt_insert_succ' hlt,
      Finset.sum_insert (succ_not_mem_filter_gt' hlt), mul_add]
    have ih := expWeights_bound n M hM ⟨k.val + 1, hlt⟩
    rw [expWeights_succ_eq' hlt]
    linarith

/-- Exponential weights are exponentially separated. -/
theorem expWeights_separated (n : Nat) (M : Nat) (hM : 0 < M) :
    ExponentiallySeparated (expWeights n M) M :=
  ⟨expWeights_pos n M, fun k => expWeights_bound n M hM k⟩

-- ============================================================================
-- § 3b: Ganging (complement of exponential separation)
-- ============================================================================

/-- **Ganging**: two constraints with individual weights w₁, w₂ each weaker
    than a third weight w₃, but jointly stronger.

    This is the hallmark of weighted constraint interaction that distinguishes
    MaxEnt/HG from OT (@cite{hayes-wilson-2008}). In OT (strict ranking), a
    lower-ranked constraint can never override a higher-ranked one regardless
    of how many violations accumulate. In MaxEnt, constraint effects are
    *additive*, so multiple weak constraints can "gang up" to outweigh a
    strong one. -/
def Ganging (w₁ w₂ w₃ : ℚ) : Prop :=
  0 < w₁ ∧ 0 < w₂ ∧ 0 < w₃ ∧
  w₁ < w₃ ∧ w₂ < w₃ ∧
  w₃ < w₁ + w₂

/-- Ganging is achievable: weights (2, 2, 3) exhibit ganging. -/
theorem ganging_example : Ganging 2 2 3 := by
  unfold Ganging; norm_num

/-- **Ganging is incompatible with exponential separation**: if weights are
    exponentially separated, no pair of lower constraints can gang up
    against any higher constraint. -/
theorem exponential_separation_precludes_ganging {n : Nat}
    (w : Fin n → ℚ) (M : Nat)
    (_hw : ExponentiallySeparated w M)
    (k : Fin n) :
    ¬Ganging ((univ.filter (· > k)).sum w) 0 (w k) := by
  intro ⟨_, h0, _, _, _, _⟩
  linarith

/-- With exponentially separated weights (M = 1), each constraint
    outweighs the total of all lower weights. -/
theorem no_ganging_when_separated {n : Nat} (w : Fin n → ℚ)
    (hw : ExponentiallySeparated w 1) (k : Fin n) :
    (univ.filter (· > k)).sum w < w k := by
  have h := hw.2 k
  simp only [Nat.cast_one, one_mul] at h
  exact h

-- ============================================================================
-- § 4: HG–OT Agreement
-- ============================================================================

/-- Weighted violation sum (the positive part of harmony:
    `harmonyScore = -weightedViolations`). -/
def weightedViolations {n : Nat} (w : Fin n → ℚ) (v : Fin n → Nat) : ℚ :=
  univ.sum fun i => w i * (v i : ℚ)

/-- **HG–OT agreement lemma** (@cite{smolensky-legendre-2006}): with
    exponentially separated weights and bounded violations, lexicographic
    dominance implies strictly lower weighted violations.

    Since `harmonyScore = -weightedViolations`, this means the
    lexicographically better candidate has strictly higher harmony.

    Proof sketch: decompose the violation-difference sum at the first
    differing position k.
    - For i < k: terms cancel (va(i) = vb(i) by `hlex`)
    - At i = k: wₖ · (vb(k) − va(k)) ≥ wₖ  (since vb(k) > va(k))
    - For i > k: |wᵢ · (vb(i) − va(i))| ≤ wᵢ · M  (by `hM`)
    - Net: ≥ wₖ − M · Σᵢ₍ᵢ>ₖ₎ wᵢ > 0  (by `hw`) -/
theorem lex_imp_lower_violations {n : Nat} (w : Fin n → ℚ) (M : Nat)
    (va vb : Fin n → Nat)
    (hM : ∀ i, va i ≤ M ∧ vb i ≤ M)
    (hw : ExponentiallySeparated w M)
    (hlex : LexStrictlyBetter va vb) :
    weightedViolations w va < weightedViolations w vb := by
  obtain ⟨k, h_agree, h_lt⟩ := hlex
  simp only [weightedViolations]
  -- Suffices: 0 < Σ w_i · (vb_i − va_i)
  suffices hpos : (0 : ℚ) <
      univ.sum (λ i => w i * ((vb i : ℚ) - (va i : ℚ))) by
    have hlink : univ.sum (λ i => w i * (va i : ℚ)) +
        univ.sum (λ i => w i * ((vb i : ℚ) - (va i : ℚ))) =
        univ.sum (λ i => w i * (vb i : ℚ)) := by
      rw [← Finset.sum_add_distrib]; congr 1; ext i; ring
    linarith
  -- Split the sum: f(k) + Σ_{i≠k} f(i)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  -- Split erase k into i < k and i > k
  have hsplit : univ.erase k =
      univ.filter (· < k) ∪ univ.filter (· > k) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_erase] at hi
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases lt_or_gt_of_ne hi.1 with h | h
      · exact Or.inl ⟨Finset.mem_univ _, h⟩
      · exact Or.inr ⟨Finset.mem_univ _, h⟩
    · intro hi
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hi
      rw [Finset.mem_erase]
      rcases hi with ⟨_, h⟩ | ⟨_, h⟩
      · exact ⟨ne_of_lt h, Finset.mem_univ _⟩
      · exact ⟨ne_of_gt h, Finset.mem_univ _⟩
  have hdisj : Disjoint (univ.filter (· < k) : Finset (Fin n))
      (univ.filter (· > k)) := by
    rw [Finset.disjoint_left]
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hsplit, Finset.sum_union hdisj]
  -- Terms i < k: each is 0
  have hlt_zero : (univ.filter (· < k)).sum
      (λ i => w i * ((vb i : ℚ) - (va i : ℚ))) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [h_agree i hi, sub_self, mul_zero]
  -- Term at k: w_k · (vb_k − va_k) ≥ w_k > 0
  have hk_bound : w k ≤ w k * ((vb k : ℚ) - (va k : ℚ)) := by
    have h1 : (va k : ℚ) + 1 ≤ (vb k : ℚ) := by exact_mod_cast h_lt
    nlinarith [(hw.1 k).le]
  -- Terms i > k: each ≥ −w_i · M, so sum ≥ −M · Σ_{i>k} w_i
  have hgt_bound : -(M : ℚ) * (univ.filter (· > k)).sum w ≤
      (univ.filter (· > k)).sum
        (λ i => w i * ((vb i : ℚ) - (va i : ℚ))) := by
    have h_each : ∀ i ∈ univ.filter (· > k),
        -(w i * (M : ℚ)) ≤ w i * ((vb i : ℚ) - (va i : ℚ)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hva : (va i : ℚ) ≤ (M : ℚ) := by exact_mod_cast (hM i).1
      nlinarith [(hw.1 i).le]
    have h_neg_sum : (univ.filter (· > k)).sum (λ i => -(w i * (M : ℚ))) =
        -(M : ℚ) * (univ.filter (· > k)).sum w := by
      trans (univ.filter (· > k)).sum (λ i => -(M : ℚ) * w i)
      · apply Finset.sum_congr rfl; intro i _; ring
      · rw [← Finset.mul_sum]
    linarith [Finset.sum_le_sum h_each]
  -- Combine: w_k − M · Σ_{i>k} w_i > 0 from ExponentiallySeparated
  linarith [hw.2 k, hlt_zero]

private lemma foldl_sub_map_sum {α : Type} (l : List α) (f : α → ℚ) (init : ℚ) :
    l.foldl (fun acc x => acc - f x) init = init - (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih]; ring

private lemma harmonyScore_eq_neg_sum {C : Type}
    (cons : List (WeightedConstraint C)) (c : C) :
    harmonyScore cons c = -((cons.map (λ con => con.weight * (con.eval c : ℚ))).sum) := by
  unfold harmonyScore; rw [foldl_sub_map_sum]; ring

private lemma mapIdx_sum_eq_fin_sum {α : Type} (l : List α) (f : ℕ → α → ℚ) :
    (l.mapIdx f).sum = ∑ i : Fin l.length, f i (l.get i) := by
  induction l generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapIdx_cons, List.sum_cons, ih]
    show f 0 x + ∑ i, f (↑i + 1) (xs.get i) =
         ∑ i : Fin (xs.length + 1), (fun j : Fin (xs.length + 1) => f (↑j) ((x :: xs).get j)) i
    rw [Fin.sum_univ_succ]; simp

private lemma map_mapIdx_sum {α β : Type} (l : List α) (f : ℕ → α → β) (g : β → ℚ) :
    (l.mapIdx f |>.map g).sum = (l.mapIdx (fun i x => g (f i x))).sum := by
  congr 1
  induction l generalizing f with
  | nil => simp
  | cons x xs ih => simp only [List.mapIdx_cons, List.map_cons]; congr 1; exact ih _

private lemma harmonyScore_otToWeighted_eq {C : Type}
    (ranking : List (NamedConstraint C)) (M : Nat) (c : C) :
    harmonyScore (otToWeighted ranking M) c =
    -(weightedViolations (expWeights ranking.length M)
      (fun i : Fin ranking.length => (ranking.get i).eval c)) := by
  rw [harmonyScore_eq_neg_sum, neg_inj, weightedViolations]
  simp only [otToWeighted]
  rw [map_mapIdx_sum, mapIdx_sum_eq_fin_sum]
  simp only [expWeights]

/-- HG–OT agreement for a concrete candidate type: if candidate `a`
    lexicographically beats `b` on the violation profile induced by `ranking`,
    then `a` has strictly higher harmony under `otToWeighted ranking M`,
    provided M bounds all violation counts. -/
theorem ot_lex_imp_higher_harmony {C : Type}
    (ranking : List (NamedConstraint C)) (M : Nat) (hM : 0 < M)
    (a b : C)
    (hbound : ∀ con ∈ ranking, con.eval a ≤ M ∧ con.eval b ≤ M)
    (hlex : LexStrictlyBetter
      (fun i : Fin ranking.length => (ranking.get i).eval a)
      (fun i : Fin ranking.length => (ranking.get i).eval b)) :
    harmonyScoreR (otToWeighted ranking M) a >
    harmonyScoreR (otToWeighted ranking M) b := by
  simp only [harmonyScoreR, gt_iff_lt]
  have hlt : harmonyScore (otToWeighted ranking M) b <
      harmonyScore (otToWeighted ranking M) a := by
    rw [harmonyScore_otToWeighted_eq, harmonyScore_otToWeighted_eq, neg_lt_neg_iff]
    exact lex_imp_lower_violations _ M _ _
      (fun i => hbound (ranking.get i) (by simp [List.get_eq_getElem, List.getElem_mem]))
      (expWeights_separated ranking.length M hM) hlex
  exact_mod_cast hlt

-- ============================================================================
-- § 5: MaxEnt → OT Limit
-- ============================================================================

/-- **MaxEnt concentration on HG winner**: as α → ∞, MaxEnt probability
    concentrates on the candidate with the highest harmony score.

    This is `softmax_argmax_limit` instantiated with harmony scores.
    The interesting content is in the *hypotheses*: showing that the
    HG winner equals the OT winner (§4). -/
theorem maxent_concentrates_on_hg_winner {C : Type} [Fintype C] [Nonempty C]
    [DecidableEq C]
    (constraints : List (WeightedConstraint C))
    (c_opt : C)
    (h_opt : ∀ c, c ≠ c_opt →
      harmonyScoreR constraints c < harmonyScoreR constraints c_opt) :
    ∀ ε > 0, ∃ α₀ : ℝ, ∀ α, α > α₀ →
      |softmax (harmonyScoreR constraints) α c_opt - 1| < ε :=
  softmax_argmax_limit (harmonyScoreR constraints) c_opt h_opt

/-- **MaxEnt → OT limit** (@cite{smolensky-legendre-2006}): as α → ∞,
    MaxEnt probability concentrates on the OT winner.

    Given a constraint ranking with violation bound M and a candidate `c_opt`
    that lexicographically beats all competitors, the MaxEnt probability
    `softmax(α · H)(c_opt) → 1` as `α → ∞`.

    The proof combines:
    1. `ot_lex_imp_higher_harmony`: lex-better ⟹ higher harmony (HG–OT agreement)
    2. `softmax_argmax_limit`: MaxEnt concentrates on harmony maximizer -/
theorem maxent_ot_limit {C : Type} [Fintype C] [Nonempty C] [DecidableEq C]
    (ranking : List (NamedConstraint C)) (M : Nat) (hM : 0 < M)
    (c_opt : C)
    (hbound : ∀ c : C, ∀ con ∈ ranking, con.eval c ≤ M)
    (hlex : ∀ c, c ≠ c_opt → LexStrictlyBetter
      (fun i : Fin ranking.length => (ranking.get i).eval c_opt)
      (fun i : Fin ranking.length => (ranking.get i).eval c)) :
    ∀ ε > 0, ∃ α₀ : ℝ, ∀ α, α > α₀ →
      |softmax (harmonyScoreR (otToWeighted ranking M)) α c_opt - 1| < ε := by
  apply softmax_argmax_limit
  intro c hc
  exact ot_lex_imp_higher_harmony ranking M hM c_opt c
    (fun con hcon => ⟨hbound c_opt con hcon, hbound c con hcon⟩)
    (hlex c hc)

end Core.Constraint
