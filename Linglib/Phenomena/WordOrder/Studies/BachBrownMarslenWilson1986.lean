import Linglib.Phenomena.WordOrder.CrossSerial
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bach, Brown & Marslen-Wilson (1986)
@cite{bach-brown-marslen-wilson-1986}

Crossed and Nested Dependencies in German and Dutch: A Psycholinguistic Study.
*Language and Cognitive Processes*, 1(4), 249–262.

## Core Finding

Dutch crossed verb-cluster dependencies (NP₁ NP₂ NP₃ V₁ V₂ V₃) are easier to
process than German nested dependencies (NP₁ NP₂ NP₃ V₃ V₂ V₁) at two or more
levels of embedding, in both comprehensibility ratings and comprehension accuracy.
At one level of embedding (Level 2), German/Participle does not differ from Dutch,
though German/Infinitive shows a significant baseline disadvantage across all
levels. This confirms @cite{evers-1975}'s
intuition that crossed dependencies are easier, with the first controlled
experimental evidence.

## Incremental Integration Model

The paper argues qualitatively that crossed dependencies allow incremental
top-down integration while nested dependencies force bottom-up accumulation of
floating propositions. We formalize this via `totalIntegrationCost`: the
cumulative count of NPs awaiting matrix-connected integration during verb-cluster
processing. This metric is our formalization, not the paper's — they argue
informally about when partial interpretations become available.

The integration model is derived from the `VerbClusterBinding` permutation:
NP_i is matrix-integrated after k verbs iff `max(σ(0), σ(i)) < k` — all
verbs in the control chain from the bound verb to the matrix verb have been
heard. For identity (crossed), σ(0) = 0 so integration is min(k, n). For
reverse (nested), σ(0) = n−1 so nothing integrates until all verbs are heard.

The cost ratio nested/crossed is exactly 2 for all n, but the absolute difference
n(n−1)/2 grows quadratically — consistent with the finding that the processing
difference is undetectable at n=2 (gap = 1) but large at n=3 (gap = 3).

## Dependency Length Invariance

Crossed and nested patterns have identical total NP-verb dependency length (n²).
This means the Bach et al. finding cannot be explained by dependency length
minimization alone — the advantage of crossed dependencies is about *when*
information becomes available for matrix integration, not about dependency
distance.

## Formal–Processing Dissociation

Crossed dependencies require mildly context-sensitive power
(@cite{shieber-1985}, @cite{bresnan-etal-1982}) while nested dependencies are
context-free, yet crossed is psycholinguistically easier. This refutes models
where parsing difficulty tracks the Chomsky hierarchy and provides evidence
against push-down-store models of human parsing (@cite{evers-1975}).
-/

namespace Phenomena.WordOrder.Studies.BachBrownMarslenWilson1986

open Core (VerbClusterBinding)
open Core.VerbClusterBinding (identity reverse unintegratedCount npVerbDist
  identity_unintegratedCount reverse_unintegratedCount)
open Phenomena.WordOrder.CrossSerial (crossSerialRequires nestedRequires)

-- ============================================================================
-- §1: Incremental Integration Model
-- ============================================================================

/-- Cumulative unintegrated NPs across verb positions 1..n.

    Crossed: (n−1) + (n−2) + ··· + 0 = n(n−1)/2
    Nested:  n + n + ··· + n + 0      = n(n−1) -/
def totalIntegrationCost {n : Nat} (σ : VerbClusterBinding n) : Nat :=
  ∑ k ∈ Finset.range n, σ.unintegratedCount (k + 1)

-- ============================================================================
-- §2: Model Predictions
-- ============================================================================

/-- Level 2 (n=2): minimal gap (1 vs 2). -/
theorem level2_costs :
    totalIntegrationCost (identity 2) = 1 ∧
    totalIntegrationCost (reverse 2) = 2 := by decide

/-- Level 3 (n=3): gap widens (3 vs 6). -/
theorem level3_costs :
    totalIntegrationCost (identity 3) = 3 ∧
    totalIntegrationCost (reverse 3) = 6 := by decide

/-- Level 4 (n=4): gap widens further (6 vs 12). -/
theorem level4_costs :
    totalIntegrationCost (identity 4) = 6 ∧
    totalIntegrationCost (reverse 4) = 12 := by decide

/-- The absolute cost gap grows with embedding depth. -/
theorem gap_grows :
    totalIntegrationCost (reverse 3) - totalIntegrationCost (identity 3) >
    totalIntegrationCost (reverse 2) - totalIntegrationCost (identity 2) := by
  decide

/-- Crossed is strictly cheaper for n ≥ 2.

    Proof by element-wise comparison via `Finset.sum_lt_sum`: at each verb
    position k ∈ {1,…,n}, unintegratedCount (identity n) ≤ unintegratedCount
    (reverse n), with strict inequality at k = 1 (the first verb heard). -/
theorem crossed_lt_nested (n : Nat) (h : n ≥ 2) :
    totalIntegrationCost (identity n) < totalIntegrationCost (reverse n) := by
  unfold totalIntegrationCost
  apply Finset.sum_lt_sum
  · intro i hi
    have him := Finset.mem_range.mp hi
    rw [identity_unintegratedCount, reverse_unintegratedCount]
    rw [Nat.min_eq_left (by omega)]
    split <;> omega
  · exact ⟨0, Finset.mem_range.mpr (by omega), by
      rw [identity_unintegratedCount, reverse_unintegratedCount,
          Nat.min_eq_left (by omega), if_neg (show ¬(0 + 1 ≥ n) from by omega)]
      omega⟩

-- ============================================================================
-- §3: Dependency Length Invariance
-- ============================================================================

/-- Total NP-verb dependency length across all n pairs. -/
def totalNPVerbDist {n : Nat} (σ : VerbClusterBinding n) : Nat :=
  ∑ i ∈ Finset.range n, if hi : i < n then npVerbDist n σ ⟨i, hi⟩ else 0

/-- Cross-serial total distance = n². -/
private theorem crossSerial_dist_sq (n : Nat) :
    totalNPVerbDist (identity n) = n * n := by
  simp only [totalNPVerbDist]
  have : ∀ i ∈ Finset.range n,
      (if hi : i < n then npVerbDist n (identity n) ⟨i, hi⟩ else 0) = n := by
    intro i hi; have him := Finset.mem_range.mp hi
    simp only [show i < n from him, dite_true, npVerbDist, identity, Equiv.refl_apply]; omega
  rw [Finset.sum_congr rfl this]
  simp [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

/-- Nested total distance = n² (sum of first n odd numbers). -/
private theorem nested_dist_sq (n : Nat) :
    totalNPVerbDist (reverse n) = n * n := by
  unfold totalNPVerbDist
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hLast : (if hi : m < m + 1 then npVerbDist (m + 1) (reverse (m + 1)) ⟨m, hi⟩ else 0) = 1 := by
      simp only [show m < m + 1 from by omega, dite_true, npVerbDist, reverse, Equiv.coe_fn_mk]; omega
    rw [hLast]
    have hStep : ∀ i ∈ Finset.range m,
        (if hi : i < m + 1 then npVerbDist (m + 1) (reverse (m + 1)) ⟨i, hi⟩ else 0) =
        (if hi : i < m then npVerbDist m (reverse m) ⟨i, hi⟩ else 0) + 2 := by
      intro i hi; have him := Finset.mem_range.mp hi
      simp only [show i < m + 1 from by omega, show i < m from him, dite_true,
                  npVerbDist, reverse, Equiv.coe_fn_mk]; omega
    rw [Finset.sum_congr rfl hStep, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, ih]
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

/-- General case: both patterns yield total distance n². -/
theorem dep_length_equal (n : Nat) :
    totalNPVerbDist (identity n) = totalNPVerbDist (reverse n) := by
  rw [crossSerial_dist_sq, nested_dist_sq]

-- ============================================================================
-- §4: Formal–Processing Dissociation
-- ============================================================================

/-- Crossed dependencies are formally harder (mildly context-sensitive) but
    psycholinguistically easier — formal complexity ≠ processing complexity.

    Two independent arguments against PDA parsing:
    1. Dutch is comprehensible at Level 2 despite requiring MCS power
       (a PDA cannot handle crossed deps at any depth)
    2. Dutch is *easier* than German at Level 3+
       (a PDA predicts nested should be easier or equal) -/
theorem formal_processing_dissociation :
    crossSerialRequires = .mildlyContextSensitive ∧
    nestedRequires = .contextFree ∧
    totalIntegrationCost (identity 3) < totalIntegrationCost (reverse 3) :=
  ⟨rfl, rfl, by decide⟩

/-- Integration cost difference is NOT explained by dependency length. -/
theorem cost_differs_despite_equal_dep_length :
    totalIntegrationCost (identity 3) < totalIntegrationCost (reverse 3) ∧
    totalNPVerbDist (identity 3) = totalNPVerbDist (reverse 3) :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- §5: Experimental Data
-- ============================================================================

/-- Language group. German was tested with two verb-form versions (infinitive
    and past participle) due to normative disagreement among informants. -/
inductive LangGroup where
  | dutch | germanInf | germanPart
  deriving DecidableEq, Repr

/-- Test sentence comprehensibility ratings × 100 (Table 1).
    Original scale: 1 = easy, 9 = hard. Levels 1–4 indexed 0–3. -/
def testRating : LangGroup → Fin 4 → Nat
  | .dutch,      0 => 114 | .dutch,      1 => 234
  | .dutch,      2 => 542 | .dutch,      3 => 766
  | .germanInf,  0 => 109 | .germanInf,  1 => 277
  | .germanInf,  2 => 616 | .germanInf,  3 => 826
  | .germanPart, 0 => 124 | .germanPart, 1 => 263
  | .germanPart, 2 => 581 | .germanPart, 3 => 766

/-- Paraphrase sentence ratings × 100 (Table 1, Levels 2–4 indexed 0–2).
    Paraphrases express the same propositions using right-branching structure,
    controlling for propositional complexity. -/
def paraRating : LangGroup → Fin 3 → Nat
  | .dutch,      0 => 211 | .dutch,      1 => 406 | .dutch,      2 => 594
  | .germanInf,  0 => 202 | .germanInf,  1 => 413 | .germanInf,  2 => 589
  | .germanPart, 0 => 236 | .germanPart, 1 => 385 | .germanPart, 2 => 562

/-- Comprehension accuracy × 100 for Test sentences (Table 3).
    Questions tested whether each subject NP was correctly associated with
    its predicate verb phrase. Levels 2–3 indexed 0–1. -/
def testComprehension : LangGroup → Fin 2 → Nat
  | .dutch,      0 => 168 | .dutch,      1 => 117
  | .germanInf,  0 => 173 | .germanInf,  1 =>  89
  | .germanPart, 0 => 158 | .germanPart, 1 =>  79

/-- Comprehension accuracy × 100 by NP position at Level 3, Test (Table 4).
    NP1 = matrix subject (highest clause), NP3 = most deeply embedded. -/
def comprehensionByNP : LangGroup → Fin 3 → Nat
  | .dutch,      0 => 117 | .dutch,      1 =>  83 | .dutch,      2 => 150
  | .germanInf,  0 =>  88 | .germanInf,  1 =>  67 | .germanInf,  2 => 112
  | .germanPart, 0 => 102 | .germanPart, 1 =>  38 | .germanPart, 2 =>  97

/-- Test−Paraphrase error rate difference × 100 by NP at Level 3 (Table 5).
    Higher = more syntactic disruption (Test harder relative to Paraphrase). -/
def errorDiffByNP : LangGroup → Fin 3 → Nat
  | .dutch,      0 => 11 | .dutch,      1 => 59 | .dutch,      2 =>  0
  | .germanInf,  0 => 32 | .germanInf,  1 => 91 | .germanInf,  2 => 41
  | .germanPart, 0 => 31 | .germanPart, 1 => 67 | .germanPart, 2 => 36

-- ============================================================================
-- §6: Data Confirms Model
-- ============================================================================

/-- At Level 2, German/Participle does not differ from Dutch (spread = 29).
    German/Infinitive is slightly worse throughout (spread = 43). The paper
    reports a significant overall Ger/Inf disadvantage but no difference
    for Ger/Part vs Dutch at Level 2. -/
theorem level2_german_part_similar :
    testRating .germanPart 1 - testRating .dutch 1 ≤ 30 := by decide

/-- At Level 3, Dutch rates Test sentences as easier than both German groups. -/
theorem level3_dutch_easier_rating :
    testRating .dutch 2 < testRating .germanInf 2 ∧
    testRating .dutch 2 < testRating .germanPart 2 := by decide

/-- At Level 3, Dutch comprehension accuracy exceeds both German groups. -/
theorem level3_dutch_better_comprehension :
    testComprehension .dutch 1 > testComprehension .germanInf 1 ∧
    testComprehension .dutch 1 > testComprehension .germanPart 1 := by decide

/-- The syntactic complexity effect (Test − Paraphrase) grows faster for
    both German groups than Dutch from Level 2 to Level 3, paralleling the
    model's prediction that the integration cost gap grows with depth. -/
theorem syntactic_effect_grows_faster_for_german :
    let dutch_l2 := testRating .dutch 1 - paraRating .dutch 0
    let dutch_l3 := testRating .dutch 2 - paraRating .dutch 1
    let gerInf_l2 := testRating .germanInf 1 - paraRating .germanInf 0
    let gerInf_l3 := testRating .germanInf 2 - paraRating .germanInf 1
    let gerPart_l2 := testRating .germanPart 1 - paraRating .germanPart 0
    let gerPart_l3 := testRating .germanPart 2 - paraRating .germanPart 1
    (gerInf_l3 - dutch_l3) > (gerInf_l2 - dutch_l2) ∧
    (gerPart_l3 - dutch_l3) > (gerPart_l2 - dutch_l2) := by decide

-- ============================================================================
-- §7: NP-by-NP Analysis (Tables 4–5)
-- ============================================================================

/-- NP2 (middle NP) is hardest for all three groups (Table 4, Test).
    This is an interference effect: NP2 is distinguished by neither primacy
    (NP1) nor recency (NP3), making it hardest to retrieve regardless of
    the dependency pattern. -/
theorem np2_hardest :
    comprehensionByNP .dutch 1 < comprehensionByNP .dutch 0 ∧
    comprehensionByNP .dutch 1 < comprehensionByNP .dutch 2 ∧
    comprehensionByNP .germanInf 1 < comprehensionByNP .germanInf 0 ∧
    comprehensionByNP .germanInf 1 < comprehensionByNP .germanInf 2 ∧
    comprehensionByNP .germanPart 1 < comprehensionByNP .germanPart 0 ∧
    comprehensionByNP .germanPart 1 < comprehensionByNP .germanPart 2 := by
  decide

/-- Dutch advantage is largest for NP3 (most deeply embedded clause).

    Dutch shows ZERO Test−Para error for NP3 (errorDiffByNP .dutch 2 = 0),
    while both German groups show substantial error (41, 36). The paper
    explains: in Dutch, NP3's verb (V₃) arrives last and integrates into
    an already-built matrix structure. In German, NP3's verb (V₃) arrives
    first — the proposition is immediately parseable but floats without
    a matrix root, so the information decays before it can be used. -/
theorem dutch_np3_advantage :
    errorDiffByNP .dutch 2 = 0 ∧
    errorDiffByNP .germanInf 2 > 0 ∧
    errorDiffByNP .germanPart 2 > 0 := by decide

-- ============================================================================
-- §8: PDA Counter-Model
-- ============================================================================

/-- A push-down automaton (PDA) parsing model predicts that difficulty
    should track the Chomsky hierarchy: context-free patterns (nested) should
    be easier than mildly-context-sensitive patterns (crossed), because PDAs
    can parse the former but not the latter (@cite{evers-1975}).

    The data refutes this: crossed is empirically easier at n ≥ 3.
    This is the paper's central argument against stack-based parsing. -/
theorem pda_refuted :
    -- PDA prediction: nested should be easier (CF-parsable by a PDA)
    nestedRequires < crossSerialRequires ∧
    -- Empirical reality: crossed is easier (lower integration cost)
    totalIntegrationCost (identity 3) < totalIntegrationCost (reverse 3) ∧
    -- Confirmed by comprehensibility ratings
    testRating .dutch 2 < testRating .germanInf 2 ∧
    -- Confirmed by comprehension accuracy
    testComprehension .dutch 1 > testComprehension .germanInf 1 :=
  ⟨by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- §9: Summary
-- ============================================================================

/-- The model predicts crossed < nested, the data confirms it, and
    dependency length cannot explain the difference. -/
theorem model_matches_data :
    totalIntegrationCost (identity 3) < totalIntegrationCost (reverse 3) ∧
    testRating .dutch 2 < testRating .germanInf 2 ∧
    testComprehension .dutch 1 > testComprehension .germanInf 1 ∧
    totalNPVerbDist (identity 3) = totalNPVerbDist (reverse 3) :=
  ⟨by decide, by decide, by decide, by decide⟩

end Phenomena.WordOrder.Studies.BachBrownMarslenWilson1986
