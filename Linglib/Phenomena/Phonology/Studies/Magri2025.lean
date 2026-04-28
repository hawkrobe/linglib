import Linglib.Phenomena.Phonology.Studies.ZurawHayes2017

/-!
# @cite{magri-2025}: Constraint Interaction in Probabilistic Phonology
@cite{magri-2025}

Replication of @cite{magri-2025} "Constraint Interaction in Probabilistic
Phonology: Deducing Maximum Entropy Grammars from Hayes and Zuraw's Shifted
Sigmoids Generalization" (Linguistic Inquiry, Early Access).

## Main result

Within harmony-based probabilistic phonology, an n-ary harmony function
predicts the shifted-sigmoids generalization of Hayes and Zuraw
(@cite{zuraw-hayes-2017}; @cite{hayes-2022}) **if and only
if** the harmony is *separable* — it decomposes as `∏ₖ hₖ(Cₖ)^{wₖ}`.
Since MaxEnt harmony is separable (each `hₖ = exp(−·)`), ME predicts HZ
as a corollary. And since any separable harmony can be construed as ME
through constraint rescaling `Ĉₖ = −log hₖ(Cₖ)`, the characterization
is complete.

## Formalization

This study file instantiates @cite{magri-2025}'s theory with the Tagalog
nasal substitution case study from the paper, verifying:

1. The six constraints satisfy `ConstraintIndependence`
2. The violation differences inherit independence (`ViolDiffIndependence`)
3. ME predicts HZ's constant logit-rate difference identity
4. The identity holds for *any* weight assignment (not just specific values)

The 2×2 square data and constraint inventory come from
`Phenomena/Phonology/Studies/ZurawHayes2017.lean` (Magri 2025 inherits
the sub-square setup from Z&H 2017).
-/

namespace Magri2025

open Core.Constraint
open ZurawHayes2017

/-! ## § 1: Constraint Independence

The constraint violation profiles viewed as functions on underlying
forms (ignoring the candidate dimension, since we work with violation
*differences* Δₖ). For the independence check, we verify that each
raw constraint is insensitive to at least one dimension.
-/

/-- C₁ = DEP-C is insensitive to the prefix (row dimension):
    the violation is 1 for NO and 0 for YES regardless of prefix.
    DEP-C as the constraint violated by non-substitution follows
    @cite{zuraw-2010}'s discussion in §4.2. -/
theorem depC_insensitive_to_row (o : NasalSubOutput) :
    depC (.mang_b, o) = depC (.pang_b, o) ∧
    depC (.mang_k, o) = depC (.pang_k, o) := by
  cases o <;> decide

/-- C₂ = \*NC is insensitive to the prefix. Per @cite{zuraw-2010} ex. (17):
    "\*NC: A [+nasal] segment must not be immediately followed by a
    [-voice, -sonorant] segment". -/
theorem starNC_insensitive_to_row (o : NasalSubOutput) :
    starNC (.mang_b, o) = starNC (.pang_b, o) ∧
    starNC (.mang_k, o) = starNC (.pang_k, o) := by
  cases o <;> decide

/-- C₃ = \*\[stem\] is insensitive to the prefix. -/
theorem starStemVelar_insensitive_to_row (o : NasalSubOutput) :
    starStemVelar (.mang_b, o) = starStemVelar (.pang_b, o) ∧
    starStemVelar (.mang_k, o) = starStemVelar (.pang_k, o) := by
  cases o <;> decide

/-- C₄ = \*\[stem\]/n is insensitive to the prefix. -/
theorem starStemVelarCoronal_insensitive_to_row (o : NasalSubOutput) :
    starStemVelarCoronal (.mang_b, o) = starStemVelarCoronal (.pang_b, o) ∧
    starStemVelarCoronal (.mang_k, o) = starStemVelarCoronal (.pang_k, o) := by
  cases o <;> decide

/-- C₅ = UNIF(maŋ) is insensitive to the stem-initial obstruent (column). -/
theorem unifMang_insensitive_to_col (o : NasalSubOutput) :
    unifMang (.mang_b, o) = unifMang (.mang_k, o) ∧
    unifMang (.pang_b, o) = unifMang (.pang_k, o) := by
  cases o <;> decide

/-- C₆ = UNIF(paŋ) is insensitive to the stem-initial obstruent. -/
theorem unifPang_insensitive_to_col (o : NasalSubOutput) :
    unifPang (.mang_b, o) = unifPang (.mang_k, o) ∧
    unifPang (.pang_b, o) = unifPang (.pang_k, o) := by
  cases o <;> decide

/-- **Constraint independence**: for each fixed output, the six
    constraints satisfy `ConstraintIndependence` on the nasal substitution
    square.

    C₁–C₄ (markedness) are insensitive to row (prefix);
    C₅–C₆ (faithfulness) are insensitive to column (stem obstruent). -/
theorem constraint_independence (o : NasalSubOutput) :
    ConstraintIndependence (fun k x => constraints k (x, o)) nasalSubSquare := by
  intro k; fin_cases k <;> cases o <;>
    simp only [constraints, depC, starNC, starStemVelar,
      starStemVelarCoronal, unifMang, unifPang, nasalSubSquare,
      InsensitiveToRow, InsensitiveToCol] <;>
    decide

/-! ## § 2: Violation Difference Consistency -/

/-- The violation differences are consistent with the raw constraint
    profiles: `Δₖ(x) = Cₖ(x, NO) − Cₖ(x, YES)`. -/
theorem violDiff_consistent (k : Fin 6) (x : NasalSubInput) :
    violDiffProfile k x =
    (constraints k (x, .no) : ℤ) - (constraints k (x, .yes) : ℤ) := by
  fin_cases k <;> cases x <;> decide

/-! ## § 3: ME Predicts HZ -/

/-- **ME predicts HZ for Tagalog nasal substitution**:
    for *any* weight assignment `w : Fin 6 → ℝ`, the MaxEnt logit rates
    of nasal substitution satisfy the constant-difference identity.

    `LR(/maŋb/) − LR(/maŋk/) = LR(/paŋb/) − LR(/paŋk/)`

    This is a direct instantiation of `me_predicts_hz` with the
    Tagalog violation differences and their verified independence. -/
theorem me_predicts_hz_tagalog (w : Fin 6 → ℝ) :
    ConstantLogitDiff
      (fun x => ∑ k : Fin 6, w k * deltaR k x)
      nasalSubSquare :=
  me_predicts_hz w deltaR nasalSubSquare violDiff_independence

/-! ## § 4: Concrete Logit-Rate Computations

The logit rate is `LR(x) = Σₖ wₖ · Δₖ(x)`. We verify the
symbolic expressions for each cell.
-/

/-- `LR(maŋb) = w₁ − w₅` -/
theorem logitRate_mang_b (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) =
    w 0 - w 4 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- `LR(/maŋk/) = w₁ + w₂ − w₃ − w₄ − w₅` -/
theorem logitRate_mang_k (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    w 0 + w 1 - w 2 - w 3 - w 4 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- `LR(/paŋb/) = w₁ − w₆` -/
theorem logitRate_pang_b (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) =
    w 0 - w 5 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- `LR(/paŋk/) = w₁ + w₂ − w₃ − w₄ − w₆` -/
theorem logitRate_pang_k (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) =
    w 0 + w 1 - w 2 - w 3 - w 5 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- The constant logit-rate difference equals `−w₂ + w₃ + w₄`
    for both rows, regardless of weights. This follows from the
    insensitivity structure of the six constraints (§ 1).

    Note that `w 2` and `w 3` are not separately identifiable from the
    b-vs-k square data — only the sum `w 2 + w 3` matters here, since
    `*[stemŋ]` and `*[stemŋ]/n` coincide on the b/k restriction. -/
theorem hz_constant_value (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    -w 1 + w 2 + w 3 := by
  rw [logitRate_mang_b, logitRate_mang_k]; ring

theorem hz_constant_value' (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) =
    -w 1 + w 2 + w 3 := by
  rw [logitRate_pang_b, logitRate_pang_k]; ring

/-- The HZ identity verified concretely: both row-differences are equal. -/
theorem hz_identity_concrete (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) := by
  rw [hz_constant_value, hz_constant_value']

/-! ## § 5: Empirical Rate Verification

The empirical rates satisfy HZ's identity to good approximation.
The exact identity is `logit(R(tl)) − logit(R(tr)) = logit(R(bl)) − logit(R(br))`.
We verify the approximate version on the rational rates.
-/

/-- Rates are in (0, 1). -/
theorem rate_pos (x : NasalSubInput) : 0 < nasalSubRate x := by
  cases x <;> norm_num [nasalSubRate]

theorem rate_lt_one (x : NasalSubInput) : nasalSubRate x < 1 := by
  cases x <;> norm_num [nasalSubRate]

-- The logit-rate differences are approximately equal:
-- `logit(0.916) − logit(0.993) ≈ logit(0.434) − logit(0.909)`.
--
-- We verify the exact rational version. The logit of `p` is
-- `log(p/(1−p))`, and the *difference* of logits is
-- `log(p₁(1−p₂) / (p₂(1−p₁)))`. We check that the ratios
-- `p₁(1−p₂) / (p₂(1−p₁))` are approximately equal across rows,
-- verifying HZ's empirical observation.

/-- Logit-odds ratio for top row: (916/1000)·(7/1000) / ((993/1000)·(84/1000))
    = 916·7 / (993·84) = 6412 / 83412. -/
theorem top_row_odds_ratio :
    nasalSubRate .mang_b * (1 - nasalSubRate .mang_k) /
    (nasalSubRate .mang_k * (1 - nasalSubRate .mang_b)) =
    6412 / 83412 := by
  simp only [nasalSubRate]; norm_num

/-- Logit-odds ratio for bottom row: (434/1000)·(91/1000) / ((909/1000)·(566/1000))
    = 434·91 / (909·566) = 39494 / 514494. -/
theorem bottom_row_odds_ratio :
    nasalSubRate .pang_b * (1 - nasalSubRate .pang_k) /
    (nasalSubRate .pang_k * (1 - nasalSubRate .pang_b)) =
    39494 / 514494 := by
  simp only [nasalSubRate]; norm_num

/-- The two odds ratios are close: 6412/83412 ≈ 0.0769 and
    39494/514494 ≈ 0.0768 — a remarkable match confirming HZ's
    empirical observation. Equality of these ratios would mean
    `logit(R(tl)) − logit(R(tr)) = logit(R(bl)) − logit(R(br))`
    exactly. -/
theorem odds_ratios_close :
    -- Cross-multiply to avoid division: a/b ≈ c/d iff ad ≈ bc
    -- 6412 · 514494 = 3,298,935,528
    -- 39494 · 83412 = 3,294,273,528
    -- Difference: 4,662,000 (≈ 0.14% of either product)
    6412 * 514494 = 3298935528 ∧
    39494 * 83412 = 3294273528 := by
  constructor <;> norm_num

/-! ## § 6: Separable Forward Direction -/

/-- **ME predicts HZ at the probability level**: the log-probability-ratio
    `log(P(YES|x)/P(NO|x))` under ME satisfies HZ's constant-difference
    identity for Tagalog nasal substitution, for *any* weight assignment.

    This instantiates `separable_predicts_hz` with `meSeparable` and the
    Tagalog constraints. Since ME rescaling is the identity
    (`meSeparable_rescale`), the rescaled violation differences reduce to
    the raw violation differences, and `violDiff_independence` provides
    the independence hypothesis. -/
theorem me_separable_predicts_hz_tagalog (w : Fin 6 → ℝ) :
    ConstantLogitDiff
      (fun x => Real.log (
        (meSeparable 6 w).eval (fun k => constraints k (x, .yes)) /
        (meSeparable 6 w).eval (fun k => constraints k (x, .no))))
      nasalSubSquare := by
  apply separable_predicts_hz
  intro k
  simp only [SeparableHarmony.rescale, meSeparable, Real.log_exp, nasalSubSquare]
  fin_cases k <;>
    simp only [constraints, depC, starNC, starStemVelar,
      starStemVelarCoronal, unifMang, unifPang] <;>
    simp

end Magri2025
