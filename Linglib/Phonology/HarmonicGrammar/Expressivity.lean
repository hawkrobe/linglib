import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Core.Optimization.Evaluation
import Linglib.Core.Probability.SoftmaxTheory
import Linglib.Core.Optimization.Semiring
import Linglib.Core.Optimization.Dequantization.LogSumExp.Softmax

/-!
# Expressivity: OT, Harmonic Grammar, and MaxEnt

How the frameworks' expressive powers relate ([prince-smolensky-1993];
[smolensky-legendre-2006] ch. 14; [pater-2009]; [coetzee-pater-2011]):
with exponentially separated weights HG's argmax agrees with OT's
lexicographic comparison, so OT ⊆ HG; as the rationality parameter α → ∞,
MaxEnt recovers categorical OT; and the containment is strict —
*cumulativity*, summed low-weight violations overpowering a single
high-weight one, is HG-expressible but not OT-expressible.

## Main definitions

- `expWeights`, `ExponentiallySeparated`: the HG reading of an OT ranking.
- `RealizationProblem`: inputs, per-input candidates, violation profiles,
  and the target mapping a grammar must realize; `IsHGRealizable`,
  `IsOTRealizable` — realizability by a non-negative weighting / a ranking.
- `RealizationProblem.ercs`: the problem's winner–loser ERCs
  ([prince-2002]).

## Main results

- `ot_lex_imp_higher_harmony`: lex dominance gives higher harmony under
  exponentially separated weights.
- `maxent_ot_limit`: as α → ∞, MaxEnt concentrates on the OT winner.
- `RealizationProblem.realizedByRanking_iff_satisfiedBy`: OT-realization is
  ERC satisfaction, so OT-realizability is consistency of the problem's ERC
  set (`isOTRealizable_iff_linearExtensions_nonempty`; [prince-2002]).
- `RealizationProblem.IsOTRealizable.isHGRealizable` and
  `hg_strictly_contains_ot`: OT ⊆ HG, strictly — the witness is
  [coetzee-pater-2011]'s abstract Lyman's Law instance (eq 18-19, after
  [ito-mester-1986]).
-/

namespace HarmonicGrammar

open Core Constraints Core.Optimization.Evaluation Real Finset Filter Topology
open OptimalityTheory

/-! ### OT → HG weights

An OT ranking is a `List (Constraint C)`; as a `CON C ranking.length` it is just
`ranking.get`. The Harmonic-Grammar reading of that ranking with violation bound
`M` weights coordinate `i` (0 = highest) by `(M+1)^(n−1−i)` — the `expWeights`
vector below. So the HG harmony of an OT ranking is
`harmonyScore ranking.get (expWeights ranking.length M)`, with no separate
weighted-constraint object. -/

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

/-- HG–OT agreement for a concrete candidate type: if candidate `a`
    lexicographically beats `b` on the violation profile induced by `ranking`,
    then `a` has strictly higher harmony than `b` under the ranking's exponential
    weights `expWeights ranking.length M`, provided `M` bounds all violations.
    With `harmonyScore con w c = -weightedViolations w (· c)`, the bridge to
    `lex_imp_lower_violations` is definitional. -/
theorem ot_lex_imp_higher_harmony {C : Type*}
    (ranking : List (Constraint C)) (M : Nat) (hM : 0 < M)
    (a b : C)
    (hbound : ∀ con ∈ ranking, con a ≤ M ∧ con b ≤ M)
    (hlex : toLex (fun i : Fin ranking.length => (ranking.get i) a) <
            toLex (fun i : Fin ranking.length => (ranking.get i) b)) :
    harmonyScore ranking.get (expWeights ranking.length M) a >
    harmonyScore ranking.get (expWeights ranking.length M) b := by
  show -weightedViolations (expWeights ranking.length M) (fun i => ranking.get i b) <
       -weightedViolations (expWeights ranking.length M) (fun i => ranking.get i a)
  rw [neg_lt_neg_iff]
  exact lex_imp_lower_violations (expWeights ranking.length M) M
    (fun i => ranking.get i a) (fun i => ranking.get i b)
    (fun i => hbound (ranking.get i) (by simp [List.get_eq_getElem, List.getElem_mem]))
    (expWeights_separated ranking.length M hM) hlex

/-! ### MaxEnt → OT limit -/

/-- **MaxEnt concentration on HG winner**: as α → ∞, MaxEnt probability
    concentrates on the candidate with the highest harmony score.

    This is `softmax_argmax_limit` instantiated with harmony scores.
    The interesting content is in the *hypotheses*: showing that the
    HG winner equals the OT winner (§4). -/
theorem maxent_concentrates_on_hg_winner {C : Type*} [Fintype C] [Nonempty C]
    [DecidableEq C] {n : Nat} (con : CON C n) (w : Fin n → ℝ)
    (c_opt : C)
    (h_opt : ∀ c, c ≠ c_opt →
      harmonyScore con w c < harmonyScore con w c_opt) :
    Tendsto (fun α : ℝ => softmax (α • harmonyScore con w) c_opt) atTop (𝓝 1) :=
  softmax_argmax_limit (harmonyScore con w) c_opt h_opt

/-- **MaxEnt → OT limit** ([smolensky-legendre-2006]): as α → ∞,
    MaxEnt probability concentrates on the OT winner.

    Given a constraint ranking with violation bound M and a candidate `c_opt`
    that lexicographically beats all competitors,
    `Tendsto (softmax (α • H) c_opt) atTop (𝓝 1)`.

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
    Tendsto (fun α : ℝ =>
      softmax (α • harmonyScore ranking.get (expWeights ranking.length M)) c_opt)
      atTop (𝓝 1) := by
  apply softmax_argmax_limit
  intro c hc
  exact ot_lex_imp_higher_harmony ranking M hM c_opt c
    (fun con hcon => ⟨hbound c_opt con hcon, hbound c con hcon⟩)
    (hlex c hc)

/-! ### The warped-semiring view of the limit -/

open Core.Optimization in
/-- The `lseFinset α` aggregator on harmony scores converges to the OT
    winner's harmony as `α → ∞` — the warped-semiring restatement of
    `maxent_ot_limit` ([litvinov-2005]'s Maslov dequantization applied to
    the constraint-framework family): where `maxent_ot_limit` concentrates
    the softmax *probability* on the OT winner, this realises the winner's
    harmony as the dequantized limit of the warped semiring's additive
    operator. Composes `ot_lex_imp_higher_harmony` with
    `argmax_winner_iff_lse_max_limit`. -/
theorem lse_aggregator_tendsto_winner_harmony {C : Type*} [DecidableEq C]
    (ranking : List (Constraint C)) (M : Nat) (hM : 0 < M)
    (cands : Finset C) (c_opt : C) (hc_opt : c_opt ∈ cands)
    (hbound : ∀ c ∈ cands, ∀ con ∈ ranking, con c ≤ M)
    (hlex : ∀ c ∈ cands, c ≠ c_opt →
      toLex (fun i : Fin ranking.length => (ranking.get i) c_opt) <
      toLex (fun i : Fin ranking.length => (ranking.get i) c)) :
    Tendsto (fun α : ℝ =>
        lseFinset α cands (harmonyScore ranking.get (expWeights ranking.length M))) atTop
      (𝓝 (harmonyScore ranking.get (expWeights ranking.length M) c_opt)) := by
  have hne : cands.Nonempty := ⟨c_opt, hc_opt⟩
  apply (argmax_winner_iff_lse_max_limit hne hc_opt).mp
  intro c' hc'
  by_cases h : c' = c_opt
  · subst h; exact le_refl _
  · exact le_of_lt (ot_lex_imp_higher_harmony ranking M hM c_opt c'
      (fun con hcon => ⟨hbound c_opt hc_opt con hcon, hbound c' hc' con hcon⟩)
      (hlex c' hc' h))

/-! ## Realizability

Which target mappings each framework realizes. -/

variable {Input Output : Type*} {n : ℕ}

/-! ### Realization problems -/

/-- A multi-input optimization problem: a target mapping that a single
    grammar must realize for every input simultaneously (for OT, the data of
    [tesar-smolensky-1995]'s ranking problem). -/
structure RealizationProblem (Input : Type*) (Output : Type*) (n : ℕ) where
  /-- The set of inputs the grammar handles. -/
  inputs : Finset Input
  /-- Candidate set for each input. -/
  cands : Input → Finset Output
  /-- Violation profile: `vp i o k` is the count of constraint `k` violations
      incurred by output `o` from input `i`. -/
  vp : Input → Output → Fin n → ℕ
  /-- The output the grammar must select for each input. -/
  target : Input → Output
  /-- Each target output is in its input's candidate set. -/
  target_mem : ∀ i ∈ inputs, target i ∈ cands i

namespace RealizationProblem

/-- `w` *HG-realizes* the target: for every input, the target strictly
    minimizes the weighted violation sum among candidates. -/
def realizedByWeighting (P : RealizationProblem Input Output n) (w : Fin n → ℝ) : Prop :=
  ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
    weightedViolations w (P.vp i (P.target i)) <
    weightedViolations w (P.vp i o)

/-- Some non-negative weighting realizes the target. Non-negativity is
    [pater-2009]'s standard HG; [coetzee-pater-2011] §4.4 discusses negative
    weights. -/
def IsHGRealizable (P : RealizationProblem Input Output n) : Prop :=
  ∃ w : Fin n → ℝ, (∀ k, 0 ≤ w k) ∧ P.realizedByWeighting w

/-- `σ` *OT-realizes* the target: for every input, the target strictly
    lex-dominates every alternative under the ranking `σ`. -/
def realizedByRanking (P : RealizationProblem Input Output n) (σ : Ranking n) : Prop :=
  ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
    toLex (fun k : Fin n => P.vp i (P.target i) (σ k)) <
    toLex (fun k : Fin n => P.vp i o (σ k))

/-- Some constraint ranking realizes the target. -/
def IsOTRealizable (P : RealizationProblem Input Output n) : Prop :=
  ∃ σ : Ranking n, P.realizedByRanking σ

instance [DecidableEq Output] (P : RealizationProblem Input Output n) (σ : Ranking n) :
    Decidable (P.realizedByRanking σ) := by
  unfold realizedByRanking; infer_instance

instance [DecidableEq Output] (P : RealizationProblem Input Output n) :
    Decidable P.IsOTRealizable := by
  unfold IsOTRealizable; infer_instance

/-- `σ` OT-realizes `P` iff for every input the target is the unique
    `Tableau.optimal` of the σ-permuted tableau. -/
theorem realizedByRanking_iff_optimal [DecidableEq Output]
    (P : RealizationProblem Input Output n) (σ : Ranking n) :
    P.realizedByRanking σ ↔ ∀ i (hi : i ∈ P.inputs),
      Tableau.optimal ⟨P.cands i, fun o => toLex (fun k => P.vp i o (σ k)),
        ⟨P.target i, P.target_mem i hi⟩⟩ = {P.target i} := by
  refine ⟨fun h i hi => ?_, fun h i hi o ho hne => ?_⟩
  · exact (Tableau.optimal_eq_singleton_iff (P.target_mem i hi)).mpr
      fun o ho hne => h i hi o ho hne
  · exact (Tableau.optimal_eq_singleton_iff (P.target_mem i hi)).mp (h i hi) o ho hne

/-! ### OT-realization is ERC satisfaction -/

/-- The winner–loser ERCs of a systemic problem: one comparative row per input
    and non-target candidate ([prince-2002]). -/
def ercs [DecidableEq Output] (P : RealizationProblem Input Output n) : Finset (ERC n) :=
  P.inputs.biUnion fun i => ((P.cands i).erase (P.target i)).image fun o =>
    ercOfProfiles (P.vp i (P.target i)) (P.vp i o)

theorem mem_ercs [DecidableEq Output] {P : RealizationProblem Input Output n} {α : ERC n} :
    α ∈ P.ercs ↔ ∃ i ∈ P.inputs, ∃ o ∈ P.cands i, o ≠ P.target i ∧
      ercOfProfiles (P.vp i (P.target i)) (P.vp i o) = α := by
  simp only [ercs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_erase]
  tauto

/-- OT-realization is ERC satisfaction ([prince-2002]): provided no
    competitor ties the target's violation profile, `σ` realizes the target
    iff `σ` satisfies every winner–loser ERC. -/
theorem realizedByRanking_iff_satisfiedBy [DecidableEq Output]
    {P : RealizationProblem Input Output n} {σ : Ranking n}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
      P.vp i (P.target i) ≠ P.vp i o) :
    P.realizedByRanking σ ↔ ∀ α ∈ P.ercs, α.SatisfiedBy σ := by
  constructor
  · intro h α hα
    obtain ⟨i, hi, o, ho, hone, rfl⟩ := mem_ercs.mp hα
    exact (satisfiedBy_ercOfProfiles_iff_le σ _ _).mpr (h i hi o ho hone).le
  · intro h i hi o ho hone
    refine lt_of_le_of_ne ((satisfiedBy_ercOfProfiles_iff_le σ _ _).mp
      (h _ (mem_ercs.mpr ⟨i, hi, o, ho, hone, rfl⟩))) fun heq => hvp i hi o ho hone ?_
    exact funext fun c => by simpa using congrFun (toLex_inj.mp heq) (σ.symm c)

/-- OT-realizability is consistency of the problem's ERC set
    ([prince-2002]). -/
theorem isOTRealizable_iff_linearExtensions_nonempty [DecidableEq Output]
    {P : RealizationProblem Input Output n}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
      P.vp i (P.target i) ≠ P.vp i o) :
    P.IsOTRealizable ↔ (ERC.linearExtensions P.ercs).Nonempty :=
  exists_congr fun _ => (realizedByRanking_iff_satisfiedBy hvp).trans
    ERC.mem_linearExtensions.symm

end RealizationProblem

/-! ### Forward containment — OT ⊆ HG -/

/-- Permuting weights is dual to permuting constraints. -/
private theorem weightedViolations_perm_reindex
    (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (v : Fin n → ℕ) :
    weightedViolations (fun j => w (σ.symm j)) v =
    weightedViolations w (v ∘ σ) := by
  simp only [weightedViolations, Function.comp_apply]
  rw [← Equiv.sum_comp σ (fun j => w (σ.symm j) * (v j : ℝ))]
  apply Finset.sum_congr rfl
  intro k _
  simp [Equiv.symm_apply_apply]

/-- Forward containment: an OT-realizable problem is HG-realizable, via
    exponentially separated weights permuted by the ranking
    (`lex_imp_lower_violations`, with separation bound the supremum of the
    finitely many violation counts). -/
theorem RealizationProblem.IsOTRealizable.isHGRealizable
    {P : RealizationProblem Input Output n} (h : P.IsOTRealizable) : P.IsHGRealizable := by
  obtain ⟨σ, hσ⟩ := h
  set M := (P.inputs.sup fun i => (P.cands i).sup fun o => Finset.univ.sup (P.vp i o)) + 1
  have hbound : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, ∀ k, P.vp i o k ≤ M := fun i hi o ho k =>
    ((Finset.le_sup (Finset.mem_univ k)).trans
      ((Finset.le_sup (f := fun o => Finset.univ.sup (P.vp i o)) ho).trans
        (Finset.le_sup (f := fun i => (P.cands i).sup fun o => Finset.univ.sup (P.vp i o))
          hi))).trans (Nat.le_succ _)
  refine ⟨fun j => expWeights n M (σ.symm j), fun k => (expWeights_pos n M (σ.symm k)).le, ?_⟩
  intro i hi o ho hne
  rw [weightedViolations_perm_reindex σ, weightedViolations_perm_reindex σ]
  apply lex_imp_lower_violations _ M
  · intro k
    exact ⟨hbound i hi (P.target i) (P.target_mem i hi) (σ k), hbound i hi o ho (σ k)⟩
  · exact expWeights_separated n M (Nat.succ_pos _)
  · exact hσ i hi o ho hne

/-! ### Strict containment — the cumulativity gap -/

/-- The cumulativity gap: HG with non-negative weights strictly contains OT.
    The inline witness is [coetzee-pater-2011]'s abstract Lyman's Law
    instance (eq 18-19, after [ito-mester-1986]): faithful candidates
    violating `{M1}`, `{M2}`, `{M1, M2}` against an unfaithful `{F}`, with
    the third input alone targeted unfaithful. Weights `[3, 2, 2]` realize
    this (`2 + 2 > 3` on the third input only), while the winner–loser ERCs
    `F ≫ M1`, `F ≫ M2`, and "some markedness constraint above `F`" are
    inconsistent. -/
theorem hg_strictly_contains_ot :
    ∃ (Input Output : Type) (n : ℕ) (P : RealizationProblem Input Output n),
      P.IsHGRealizable ∧ ¬ P.IsOTRealizable := by
  refine ⟨Fin 3, Bool, 3,
    { inputs := Finset.univ
      cands := fun _ => Finset.univ
      vp := fun i b => if b then ![![0, 1, 0], ![0, 0, 1], ![0, 1, 1]] i else ![1, 0, 0]
      target := ![true, true, false]
      target_mem := fun _ _ => Finset.mem_univ _ },
    ⟨![3, 2, 2], fun k => by fin_cases k <;> norm_num, ?_⟩, ?_⟩
  · intro i _ o _ hne
    simp only [weightedViolations, Fin.sum_univ_three]
    fin_cases i <;> cases o <;>
      first
      | (exfalso; exact hne rfl)
      | norm_num [Matrix.cons_val_two, Matrix.tail_cons]
  · rintro ⟨σ, hσ⟩
    rw [RealizationProblem.realizedByRanking_iff_satisfiedBy (by decide)] at hσ
    have h₁ : σ.toRel 0 1 := (simpleERC_satisfiedBy_toRel_iff 0 1 σ).mp
      (hσ _ (RealizationProblem.mem_ercs.mpr
        ⟨0, Finset.mem_univ _, false, Finset.mem_univ _, by decide, by decide⟩))
    have h₂ : σ.toRel 0 2 := (simpleERC_satisfiedBy_toRel_iff 0 2 σ).mp
      (hσ _ (RealizationProblem.mem_ercs.mpr
        ⟨1, Finset.mem_univ _, false, Finset.mem_univ _, by decide, by decide⟩))
    have h₃ := hσ _ (RealizationProblem.mem_ercs.mpr
      ⟨2, Finset.mem_univ _, true, Finset.mem_univ _, by decide, rfl⟩)
    obtain ⟨w, hwW, hdom⟩ := (ERC.satisfiedBy_iff_dominance σ _).mp h₃ 0 (by decide)
    fin_cases w
    · exact absurd hwW (by decide)
    · exact absurd h₁ (not_le.mpr hdom)
    · exact absurd h₂ (not_le.mpr hdom)

end HarmonicGrammar
