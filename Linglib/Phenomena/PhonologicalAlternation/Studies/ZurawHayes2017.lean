import Linglib.Fragments.Tagalog.Phonology

/-!
# @cite{zuraw-hayes-2017}: Intersecting Constraint Families
@cite{zuraw-hayes-2017}

@cite{zuraw-hayes-2017} "Intersecting Constraint Families: An Argument
for Harmonic Grammar" (Language 93(3): 497–546).

## Main claims

1. When phonological variation is governed by two independent families
   of constraints, the data exhibits **across-the-board effects** with
   **floor and ceiling compression** — a family of sigmoid curves.

2. This pattern is naturally predicted by Harmonic Grammar (MaxEnt and
   Noisy HG) because constraint effects are *additive*.

3. **Decision-tree models** fail because their *multiplicative*
   decomposition produces "claws" (monotonically increasing
   differentiation), not sigmoid families (§2.6, §3.10).

4. **Stochastic OT** fails because ranking paradoxes prevent fitting
   structured constraint sets to the observed pattern (§2.6, §3.8).

## Formalization

This file proves the decision-tree failure theorem and connects the
empirical Tagalog data to the MaxEnt prediction via the constraint
independence machinery from `Separability.lean`. The deeper proof
that MaxEnt's success follows from harmony separability is developed
by @cite{magri-2025} — see `Magri2025.lean`.

The formalization uses the 2×2 sub-case of the Tagalog data
(maŋ-other/paŋ-res × /b//k/) from `Fragments.Tagalog.Phonology`,
which suffices for the mathematical theorem. The full paper uses a
6×6 grid (6 prefixes × 6 consonants).

## Case studies

- **Tagalog nasal substitution** (§2): nearly synergistic families
  (both markedness and prefix UNIFORMITY constraints mostly penalize
  substitution; only \*NC̥ favors it on the consonant side)
- **French liaison/elision** (§3): synergistic families
  (word2 ALIGN + word1 USE both favor non-alignment)
- **Hungarian vowel harmony** (§4): mixed families
  (stem vowel AGREE + final consonant BILABIAL/SIBILANT/etc.)
-/

namespace Phenomena.PhonologicalAlternation.Studies.ZurawHayes2017

open Theories.Phonology.HarmonicGrammar
open Fragments.Tagalog.Phonology

-- ============================================================================
-- § 1: Across-the-Board Consistency
-- ============================================================================

/-- **Across-the-board consistency**: one dimension's effect has the same
    sign regardless of the other dimension's value. Formally: the product
    of row-wise rate differences across columns is positive (same sign). -/
def ConsistentOrdering (r : Square ℚ) : Prop :=
  (r.tl - r.bl) * (r.tr - r.br) > 0

/-- Tagalog nasal substitution rates exhibit across-the-board consistency:
    maŋ- prefixes have higher substitution than paŋ- prefixes for both
    voiced (/b/) and voiceless (/k/) stem-initial consonants. -/
theorem tagalog_consistent_ordering :
    ConsistentOrdering
      { tl := nasalSubRate .mang_b   -- 0.916
        tr := nasalSubRate .mang_k   -- 0.993
        bl := nasalSubRate .pang_b   -- 0.434
        br := nasalSubRate .pang_k } -- 0.909
    := by
  simp only [ConsistentOrdering, nasalSubRate]; norm_num

-- ============================================================================
-- § 2: Decision-Tree Models Fail (§2.6, §3.10)
-- ============================================================================

/-- **Decision-tree models predict monotonic differentiation** (§2.6):
    In a multiplicative model `P(x,y) = g(x) · h(y)`, the difference
    between two h-values is *proportional* to g:

      `g(x) · h(y₂) - g(x) · h(y₁) = g(x) · (h(y₂) - h(y₁))`

    So at the floor (g → 0), all h-differences vanish, and at the
    ceiling (g → 1), h-differences are maximal. Differences grow
    **monotonically** from floor to ceiling.

    This is the "claws" pattern: pinching at one end
    only. In contrast, MaxEnt predicts humped differentiation: sigmoid
    families compressed at *both* extremes — the observed pattern. -/
theorem decision_tree_monotonic_diff (g₁ g₂ h₁ h₂ : ℚ)
    (hg : g₁ < g₂)
    (hh : h₁ < h₂) :
    g₁ * h₂ - g₁ * h₁ < g₂ * h₂ - g₂ * h₁ := by
  have key : g₁ * (h₂ - h₁) < g₂ * (h₂ - h₁) :=
    mul_lt_mul_of_pos_right hg (by linarith)
  linarith [mul_sub g₁ h₂ h₁, mul_sub g₂ h₂ h₁]

/-- In a multiplicative model, the ratio of differences across two
    g-values exactly equals the ratio of those g-values.
    Cross-multiplied form (avoids division): -/
theorem decision_tree_diff_proportional (g₁ g₂ h₁ h₂ : ℚ) :
    (g₂ * h₂ - g₂ * h₁) * g₁ = (g₁ * h₂ - g₁ * h₁) * g₂ := by ring

/-- **Decision-tree ceiling bound**: in a multiplicative model with both
    factors in [0,1], the product is bounded above by both factors.

    This is the mathematical core of why decision trees produce "claws"
    instead of sigmoid families: probabilities can never exceed either
    component probability. At the floor (g → 0), all products vanish
    regardless of h — explaining the pinch at one end. But at the
    ceiling (g → 1), differences are preserved — so there is NO
    compression at the top. MaxEnt, by contrast, compresses at BOTH
    extremes via the sigmoid function `1/(1 + eⁿ)`. -/
theorem decision_tree_product_bound (g h : ℚ)
    (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    g * h ≤ g ∧ g * h ≤ h :=
  ⟨mul_le_of_le_one_right hg hh1, mul_le_of_le_one_left hh hg1⟩

-- ============================================================================
-- § 3: Model Comparison (Table 7, Table 17)
-- ============================================================================

-- Log likelihoods from Z&H Table 7 (Tagalog) and Table 17 (French).
-- Closer to 0 is better. The paper's central empirical argument is
-- that BOTH harmonic grammar variants succeed (MaxEnt AND Noisy HG)
-- while ALL ranking-based models fail.

/-- MaxEnt achieves the best fit for Tagalog (Table 7). -/
theorem tagalog_maxent_best :
    (-28482 : ℚ) / 100 > -29231 / 100 ∧   -- ME > Decision tree
    (-28482 : ℚ) / 100 > -29448 / 100 ∧   -- ME > Noisy HG
    (-28482 : ℚ) / 100 > -31464 / 100 ∧   -- ME > Stochastic OT
    (-28482 : ℚ) / 100 > -64572 / 100     -- ME > Stratified OT
    := by constructor <;> norm_num

/-- Both HG variants beat both ranking models for Tagalog (Table 7).
    This is the paper's core claim: constraint weighting consistently
    outperforms constraint ranking. -/
theorem tagalog_hg_beats_ranking :
    (-29448 : ℚ) / 100 > -31464 / 100 ∧   -- NHG > Stochastic OT
    (-29448 : ℚ) / 100 > -64572 / 100     -- NHG > Stratified OT
    := by constructor <;> norm_num

/-- MaxEnt and Noisy HG achieve the best fits for French (Table 17). -/
theorem french_maxent_best :
    (-19771 : ℚ) / 100 > -19880 / 100 ∧   -- ME > Noisy HG
    (-19771 : ℚ) / 100 > -20795 / 100 ∧   -- ME > Decision tree
    (-19771 : ℚ) / 100 > -23361 / 100 ∧   -- ME > Stochastic OT
    (-19771 : ℚ) / 100 > -41064 / 100     -- ME > Stratified OT
    := by constructor <;> norm_num

/-- Both HG variants beat both ranking models for French (Table 17). -/
theorem french_hg_beats_ranking :
    (-19880 : ℚ) / 100 > -23361 / 100 ∧   -- NHG > Stochastic OT
    (-19880 : ℚ) / 100 > -41064 / 100     -- NHG > Stratified OT
    := by constructor <;> norm_num

-- ============================================================================
-- § 4: MaxEnt Predicts the Sigmoid Family Pattern
-- ============================================================================

/-- **MaxEnt predicts HZ's generalization for Tagalog nasal substitution**:
    for *any* weight assignment `w : Fin 6 → ℝ`, the MaxEnt logit rates
    satisfy the constant-difference identity.

    `LR(/maŋb/) − LR(/maŋk/) = LR(/paŋb/) − LR(/paŋk/)`

    The proof instantiates `me_predicts_hz` (Separability.lean) with the
    Tagalog violation differences and their independence (from the
    Tagalog fragment). -/
theorem maxent_predicts_hz_tagalog (w : Fin 6 → ℝ) :
    ConstantLogitDiff
      (fun x => ∑ k : Fin 6, w k * deltaR k x)
      nasalSubSquare :=
  me_predicts_hz w deltaR nasalSubSquare violDiff_independence

-- ============================================================================
-- § 5: Closed-Form Logit-Rate Difference
-- ============================================================================

/-- The constant logit-rate difference equals `−w₂ + w₃ + w₄`
    for both rows, regardless of weights. This follows from the
    insensitivity structure of the six constraints: markedness
    constraints (C₁–C₄) are insensitive to prefix, so their
    contributions cancel in the row difference, while faithfulness
    constraints (C₅–C₆) are insensitive to stem consonant, so they
    cancel in the column difference. -/
theorem hz_constant_value_tagalog (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    -w 1 + w 2 + w 3 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

theorem hz_constant_value_tagalog' (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) =
    -w 1 + w 2 + w 3 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- The HZ identity verified concretely: both row-differences are equal. -/
theorem hz_identity_concrete (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) := by
  rw [hz_constant_value_tagalog, hz_constant_value_tagalog']

-- ============================================================================
-- § 6: NHG Produces Consistent Ordering (§2.5, Figure 8)
-- ============================================================================

/-- **NHG produces consistent ordering** (@cite{zuraw-hayes-2017} §2.5,
    Figure 8): when the harmony scores satisfy `ConstantLogitDiff`, NHG
    probabilities `Φ(d(x)/σ)` exhibit across-the-board consistency.

    Composes `constantLogitDiff_mono_consistent` (CLD + strict monotonicity
    ⟹ consistent ordering) with `normalCDF_strictMono`. Since
    `x ↦ Φ(x/σ)` is strictly monotone for `σ > 0`, the result follows.
    This is the formal version of Z&H's argument that NHG produces sigmoid
    families (not claws) because the normal CDF compresses at both
    extremes. -/
theorem nhg_consistent_ordering {X : Type} (d : X → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (sq : Square X)
    (hcld : ConstantLogitDiff d sq)
    (hne : d sq.tl ≠ d sq.bl) :
    (Core.normalCDF (d sq.tl / σ) - Core.normalCDF (d sq.bl / σ)) *
    (Core.normalCDF (d sq.tr / σ) - Core.normalCDF (d sq.br / σ)) > 0 :=
  constantLogitDiff_mono_consistent d (fun x => Core.normalCDF (x / σ))
    (Core.normalCDF_strictMono.comp (fun _ _ h => (div_lt_div_iff_of_pos_right hσ).mpr h))
    sq hcld hne

/-- **NHG predicts consistent ordering for Tagalog nasal substitution**:
    for any weight assignment and noise level, the NHG probabilities of
    nasal substitution exhibit across-the-board consistency whenever the
    mang- and pang- prefixes have different logit rates for b-initial stems.

    End-to-end chain: Tagalog violation differences (fragment) →
    `violDiff_independence` → `maxent_predicts_hz_tagalog` (CLD) →
    `nhg_consistent_ordering` (CDF monotonicity) → consistent ordering. -/
theorem nhg_tagalog_consistent (w : Fin 6 → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hne : (∑ k : Fin 6, w k * deltaR k .mang_b) ≠
           (∑ k : Fin 6, w k * deltaR k .pang_b)) :
    (Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .mang_b) / σ) -
     Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .pang_b) / σ)) *
    (Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .mang_k) / σ) -
     Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .pang_k) / σ)) > 0 :=
  nhg_consistent_ordering (fun x => ∑ k : Fin 6, w k * deltaR k x)
    σ hσ nasalSubSquare (maxent_predicts_hz_tagalog w) hne

end Phenomena.PhonologicalAlternation.Studies.ZurawHayes2017
