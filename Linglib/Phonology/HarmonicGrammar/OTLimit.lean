import Linglib.Phonology.Constraints.Defs
import Linglib.Core.Optimization.Evaluation
import Linglib.Core.Probability.SoftmaxTheory

/-!
# MaxEnt → OT Limit
[smolensky-legendre-2006] [prince-smolensky-1993]

As the rationality parameter α → ∞, MaxEnt Harmonic Grammar recovers
Optimality Theory's categorical optimization. OT is the "infinite-temperature"
limit of MaxEnt.

The argument has two components:

1. **HG–OT agreement** ([smolensky-legendre-2006] ch. 14): with
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
- `ExponentiallySeparated`: weight separation condition for HG–OT agreement
- `ot_lex_imp_higher_harmony`: key lemma (lex dominance ⟹ higher harmony)
- `maxent_ot_limit`: main limit theorem
-/

namespace HarmonicGrammar
open Constraints


open Core Constraints Core.Optimization.Evaluation Real Finset

/-! ### OT → HG weight construction -/

/-- Convert an OT constraint ranking to weighted constraints.

    Each constraint at rank position i (0 = highest) receives weight
    `(M+1)^(n−1−i)`, where n is the number of constraints and M is a
    violation count bound. This exponential spacing ensures HG–OT agreement.

    The `eval` function is preserved: the weighted constraint evaluates
    candidates identically to the original named constraint. -/
def otToWeighted {C : Type*} (ranking : List (Constraint C)) (M : Nat) :
    List (Constraint.Weighted C) :=
  ranking.mapIdx fun i con =>
    { con := con
      weight := ((M + 1 : ℝ) ^ (ranking.length - 1 - i)) }

/-- The weighted constraints have the same length as the ranking. -/
theorem otToWeighted_length {C : Type*} (ranking : List (Constraint C)) (M : Nat) :
    (otToWeighted ranking M).length = ranking.length := by
  simp [otToWeighted]

/-- Each weighted constraint preserves the original eval function. -/
theorem otToWeighted_eval {C : Type*} (ranking : List (Constraint C)) (M : Nat)
    (i : Fin ranking.length) (c : C) :
    ((otToWeighted ranking M).get (i.cast (otToWeighted_length ranking M).symm)).con c =
    (ranking.get i) c := by
  simp only [otToWeighted, List.get_eq_getElem, List.getElem_mapIdx, Fin.val_cast]

/-! ### Exponentially separated weights -/

/-- Weights are **exponentially separated** with violation bound M:
    each weight exceeds M times the sum of all lower-ranked weights.

    This ensures that no combination of lower-constraint violations
    can override a single higher-constraint violation difference,
    matching OT's strict ranking semantics. -/
def ExponentiallySeparated {n : Nat} (w : Fin n → ℝ) (M : Nat) : Prop :=
  (∀ i, 0 < w i) ∧
  ∀ k : Fin n, (M : ℝ) * (univ.filter (· > k)).sum w < w k

/-- Concrete exponential weights: wᵢ = (M+1)^(n−1−i).
    Constraint 0 (highest-ranked) gets the largest weight (M+1)^(n−1). -/
def expWeights (n : Nat) (M : Nat) : Fin n → ℝ :=
  fun i => ((M + 1 : ℝ) ^ (n - 1 - i.val))

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
    (↑M : ℝ) * (univ.filter (· > k)).sum (expWeights n M) <
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

/-! ### Ganging (complement of exponential separation) -/

/-- **Ganging**: two constraints with individual weights w₁, w₂ each weaker
    than a third weight w₃, but jointly stronger.

    This is the hallmark of weighted constraint interaction that distinguishes
    MaxEnt/HG from OT ([hayes-wilson-2008]). In OT (strict ranking), a
    lower-ranked constraint can never override a higher-ranked one regardless
    of how many violations accumulate. In MaxEnt, constraint effects are
    *additive*, so multiple weak constraints can "gang up" to outweigh a
    strong one. -/
def Ganging (w₁ w₂ w₃ : ℝ) : Prop :=
  0 < w₁ ∧ 0 < w₂ ∧ 0 < w₃ ∧
  w₁ < w₃ ∧ w₂ < w₃ ∧
  w₃ < w₁ + w₂

/-- Ganging is achievable: weights (2, 2, 3) exhibit ganging. -/
theorem ganging_example : Ganging 2 2 3 := by
  unfold Ganging; norm_num

/-- With exponentially separated weights (M = 1), each constraint
    outweighs the total of all lower weights. -/
theorem no_ganging_when_separated {n : Nat} (w : Fin n → ℝ)
    (hw : ExponentiallySeparated w 1) (k : Fin n) :
    (univ.filter (· > k)).sum w < w k := by
  have h := hw.2 k
  simp only [Nat.cast_one, one_mul] at h
  exact h

/-- **Ganging is precluded by exponential separation**: with exponentially
    separated weights (M = 1), no two distinct lower-ranked constraints `i`,
    `j` can gang up against a higher-ranked `k`. Their combined weight is at
    most the total lower weight, which `no_ganging_when_separated` bounds
    strictly below `w k` — contradicting ganging's `w k < w i + w j`. -/
theorem exponential_separation_precludes_ganging {n : Nat} (w : Fin n → ℝ)
    (hw : ExponentiallySeparated w 1) (k i j : Fin n)
    (hi : k < i) (hj : k < j) (hij : i ≠ j) :
    ¬ Ganging (w i) (w j) (w k) := by
  rintro ⟨_, _, _, _, _, hgang⟩
  have hsum : (univ.filter (· > k)).sum w < w k := no_ganging_when_separated w hw k
  have hsub : ({i, j} : Finset (Fin n)) ⊆ univ.filter (· > k) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, gt_iff_lt]
    rcases hx with rfl | rfl <;> assumption
  have hpair : w i + w j ≤ (univ.filter (· > k)).sum w := by
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => (hw.1 l).le)
  linarith

/-! ### HG–OT agreement -/

/-- Weighted violation sum (the positive part of harmony:
    `harmonyScore = -weightedViolations`). -/
def weightedViolations {n : Nat} (w : Fin n → ℝ) (v : Fin n → Nat) : ℝ :=
  univ.sum fun i => w i * (v i : ℝ)

/-- **HG–OT agreement lemma** ([smolensky-legendre-2006]): with
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
theorem lex_imp_lower_violations {n : Nat} (w : Fin n → ℝ) (M : Nat)
    (va vb : Fin n → Nat)
    (hM : ∀ i, va i ≤ M ∧ vb i ≤ M)
    (hw : ExponentiallySeparated w M)
    (hlex : toLex va < toLex vb) :
    weightedViolations w va < weightedViolations w vb := by
  obtain ⟨k, h_agree, h_lt⟩ :
      ∃ k : Fin n, (∀ i, i < k → va i = vb i) ∧ va k < vb k := hlex
  simp only [weightedViolations]
  -- Suffices: 0 < Σ w_i · (vb_i − va_i)
  suffices hpos : (0 : ℝ) <
      univ.sum (λ i => w i * ((vb i : ℝ) - (va i : ℝ))) by
    have hlink : univ.sum (λ i => w i * (va i : ℝ)) +
        univ.sum (λ i => w i * ((vb i : ℝ) - (va i : ℝ))) =
        univ.sum (λ i => w i * (vb i : ℝ)) := by
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
      (λ i => w i * ((vb i : ℝ) - (va i : ℝ))) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [h_agree i hi, sub_self, mul_zero]
  -- Term at k: w_k · (vb_k − va_k) ≥ w_k > 0
  have hk_bound : w k ≤ w k * ((vb k : ℝ) - (va k : ℝ)) := by
    have h1 : (va k : ℝ) + 1 ≤ (vb k : ℝ) := by exact_mod_cast h_lt
    nlinarith [(hw.1 k).le]
  -- Terms i > k: each ≥ −w_i · M, so sum ≥ −M · Σ_{i>k} w_i
  have hgt_bound : -(M : ℝ) * (univ.filter (· > k)).sum w ≤
      (univ.filter (· > k)).sum
        (λ i => w i * ((vb i : ℝ) - (va i : ℝ))) := by
    have h_each : ∀ i ∈ univ.filter (· > k),
        -(w i * (M : ℝ)) ≤ w i * ((vb i : ℝ) - (va i : ℝ)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hva : (va i : ℝ) ≤ (M : ℝ) := by exact_mod_cast (hM i).1
      nlinarith [(hw.1 i).le]
    have h_neg_sum : (univ.filter (· > k)).sum (λ i => -(w i * (M : ℝ))) =
        -(M : ℝ) * (univ.filter (· > k)).sum w := by
      trans (univ.filter (· > k)).sum (λ i => -(M : ℝ) * w i)
      · apply Finset.sum_congr rfl; intro i _; ring
      · rw [← Finset.mul_sum]
    linarith [Finset.sum_le_sum h_each]
  -- Combine: w_k − M · Σ_{i>k} w_i > 0 from ExponentiallySeparated
  linarith [hw.2 k, hlt_zero]

private lemma mapIdx_sum_eq_fin_sum {α : Type*} (l : List α) (f : ℕ → α → ℝ) :
    (l.mapIdx f).sum = ∑ i : Fin l.length, f i (l.get i) := by
  induction l generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapIdx_cons, List.sum_cons, ih]
    show f 0 x + ∑ i, f (↑i + 1) (xs.get i) =
         ∑ i : Fin (xs.length + 1), (fun j : Fin (xs.length + 1) => f (↑j) ((x :: xs).get j)) i
    rw [Fin.sum_univ_succ]; simp

private lemma map_mapIdx_sum {α β : Type*} (l : List α) (f : ℕ → α → β) (g : β → ℝ) :
    (l.mapIdx f |>.map g).sum = (l.mapIdx (fun i x => g (f i x))).sum := by
  congr 1
  induction l generalizing f with
  | nil => simp
  | cons x xs ih => simp only [List.mapIdx_cons, List.map_cons]; congr 1; exact ih _

private lemma harmonyScore_otToWeighted_eq {C : Type*}
    (ranking : List (Constraint C)) (M : Nat) (c : C) :
    harmonyScore (otToWeighted ranking M) c =
    -(weightedViolations (expWeights ranking.length M)
      (fun i : Fin ranking.length => (ranking.get i) c)) := by
  rw [harmonyScore_eq_neg_sum, neg_inj, weightedViolations]
  simp only [otToWeighted]
  rw [map_mapIdx_sum, mapIdx_sum_eq_fin_sum]
  simp only [expWeights]

/-- HG–OT agreement for a concrete candidate type: if candidate `a`
    lexicographically beats `b` on the violation profile induced by `ranking`,
    then `a` has strictly higher harmony under `otToWeighted ranking M`,
    provided M bounds all violation counts. -/
theorem ot_lex_imp_higher_harmony {C : Type*}
    (ranking : List (Constraint C)) (M : Nat) (hM : 0 < M)
    (a b : C)
    (hbound : ∀ con ∈ ranking, con a ≤ M ∧ con b ≤ M)
    (hlex : toLex (fun i : Fin ranking.length => (ranking.get i) a) <
            toLex (fun i : Fin ranking.length => (ranking.get i) b)) :
    harmonyScore (otToWeighted ranking M) a >
    harmonyScore (otToWeighted ranking M) b := by
  rw [gt_iff_lt, harmonyScore_otToWeighted_eq, harmonyScore_otToWeighted_eq, neg_lt_neg_iff]
  exact lex_imp_lower_violations _ M _ _
    (fun i => hbound (ranking.get i) (by simp [List.get_eq_getElem, List.getElem_mem]))
    (expWeights_separated ranking.length M hM) hlex

/-! ### MaxEnt → OT limit -/

/-- **MaxEnt concentration on HG winner**: as α → ∞, MaxEnt probability
    concentrates on the candidate with the highest harmony score.

    This is `softmax_argmax_limit` instantiated with harmony scores.
    The interesting content is in the *hypotheses*: showing that the
    HG winner equals the OT winner (§4). -/
theorem maxent_concentrates_on_hg_winner {C : Type*} [Fintype C] [Nonempty C]
    [DecidableEq C]
    (constraints : List (Constraint.Weighted C))
    (c_opt : C)
    (h_opt : ∀ c, c ≠ c_opt →
      harmonyScore constraints c < harmonyScore constraints c_opt) :
    ∀ ε > 0, ∃ α₀ : ℝ, ∀ α, α > α₀ →
      |softmax (α • harmonyScore constraints) c_opt - 1| < ε :=
  softmax_argmax_limit (harmonyScore constraints) c_opt h_opt

/-- **MaxEnt → OT limit** ([smolensky-legendre-2006]): as α → ∞,
    MaxEnt probability concentrates on the OT winner.

    Given a constraint ranking with violation bound M and a candidate `c_opt`
    that lexicographically beats all competitors, the MaxEnt probability
    `softmax(α · H)(c_opt) → 1` as `α → ∞`.

    The proof combines:
    1. `ot_lex_imp_higher_harmony`: lex-better ⟹ higher harmony (HG–OT agreement)
    2. `softmax_argmax_limit`: MaxEnt concentrates on harmony maximizer -/
theorem maxent_ot_limit {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (ranking : List (Constraint C)) (M : Nat) (hM : 0 < M)
    (c_opt : C)
    (hbound : ∀ c : C, ∀ con ∈ ranking, con c ≤ M)
    (hlex : ∀ c, c ≠ c_opt →
      toLex (fun i : Fin ranking.length => (ranking.get i) c_opt) <
      toLex (fun i : Fin ranking.length => (ranking.get i) c)) :
    ∀ ε > 0, ∃ α₀ : ℝ, ∀ α, α > α₀ →
      |softmax (α • harmonyScore (otToWeighted ranking M)) c_opt - 1| < ε := by
  apply softmax_argmax_limit
  intro c hc
  exact ot_lex_imp_higher_harmony ranking M hM c_opt c
    (fun con hcon => ⟨hbound c_opt con hcon, hbound c con hcon⟩)
    (hlex c hc)

end HarmonicGrammar
