import Linglib.Pragmatics.DecisionTheoretic.Basic

/-!
# Decision-Theoretic Semantics: "But" ([merin-1999-relevance] §4)
[merin-1999-relevance]

Merin's DTS account of adversative conjunction. The felicity of "A but B"
requires that A and B have opposite relevance signs, and that the conjunction
A∧B is negatively relevant (the "but"-clause wins). The default interpretation
sets H = B, yielding unexpected-B-given-A.

## Key Definitions

- `butFelicitous` (Hypothesis 4): felicity conditions for "A but B"
- `NNIR` (Def. 10): Non-Negative Instantial Relevance
- `defaultButCtx`: the default interpretation where H = B

## Main Results

- **Theorem 8**: CIP + contrariness → unexpectedness (P(B∣A) < P(B))
- **Theorem 9**: When H = B, CIP holds automatically
- **Theorem 10**: Negative relevance implies unexpectedness in default-but
- **Corollary 11** (Harris universal): NNIR prevents "Qa but Qb"
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DTS.But

open DTS

variable {W : Type*} [MeasurableSpace W]

/-! ### Felicity conditions for "but" -/

/-- **Hypothesis 4**: Felicity conditions for "A but B".

"A but B" is felicitous iff:
(i) A is positively relevant to H,
(ii) B is negatively relevant to H,
(iii) A∧B is negatively relevant to H (B "wins"). -/
def butFelicitous (ctx : Context W) (a b : Set W) : Prop :=
  posRelevant ctx a ∧ negRelevant ctx b ∧ negRelevant ctx (a ∩ b)

/-! ### Non-Negative Instantial Relevance (NNIR) -/

/-- **Definition 10**: Non-Negative Instantial Relevance (NNIR).

For a predicate Q over entities, observing Q(a) never makes Q(b) less
probable: P(Q(b)∣Q(a)) ≥ P(Q(b)) for all a, b.

This captures a cross-linguistic universal: properties are positively
correlated across instances (knowing one dog is friendly makes it more
likely another is). -/
def NNIR (E : Type*) (μ : Measure W) (Q : E → Set W) : Prop :=
  ∀ a b : E, μ (Q b) ≤ μ[|Q a] (Q b)

/-! ### Default but (H = B) -/

/-- Default "but" context: the issue is identified with the but-clause
itself (H = B).

Merin argues this is the preferred interpretation when no explicit issue is
provided. -/
abbrev defaultButCtx (μ : Measure W) (b : Set W) (hb : MeasurableSet b) : Context W :=
  ⟨b, hb, μ⟩

/-- Cross-product factorization identity (with normalization). -/
private lemma cross_product_factorization (aH anH bH bnH pH pnH : ℝ)
    (hsum : pH + pnH = 1) :
    (aH + anH) * (bH + bnH) * (pH * pnH) - (aH * bH * pnH + anH * bnH * pH) =
    (pnH * aH - pH * anH) * (pH * bnH - pnH * bH) := by
  have : pnH = 1 - pH := by linarith
  subst this; ring

/-! ### Theorems -/

/-- **Theorem 8**: CIP + contrariness implies unexpectedness.

If A and B are conditionally independent given H and ¬H, and have opposite
relevance signs, then P(B∣A) < P(B) — B is unexpected given A.

CIP turns the total-probability decompositions of P(A∧B), P(A), and P(B)
into a factorized cross-product whose factors contrariness makes jointly
positive. -/
theorem cip_contrariness_implies_unexpectedness (ctx : Context W)
    [IsProbabilityMeasure ctx.prior] [ctx.Nondegenerate] {a b : Set W}
    (ham : MeasurableSet a)
    (hcip : CondIndepIssue ctx a b) (hcontr : hContrary ctx a b)
    (ha0 : ctx.prior a ≠ 0) (hb0 : ctx.prior b ≠ 0) :
    ctx.prior[|a] b < ctx.prior b := by
  have hH : ctx.prior ctx.topic ≠ 0 := Context.Nondegenerate.topic_ne_zero
  have hNH : ctx.prior ctx.topicᶜ ≠ 0 := Context.Nondegenerate.compl_ne_zero
  set μ := ctx.prior
  set H := ctx.topic
  have hHm : MeasurableSet H := ctx.topicMeasurable
  -- Raw real forms of the CIP equations (before the shadows fold them).
  have hcipH' := congrArg ENNReal.toReal
    (show μ[|H] (a ∩ b) = μ[|H] a * μ[|H] b from (hcip true).measure_inter_eq_mul)
  rw [ENNReal.toReal_mul, cond_real_apply μ hHm, cond_real_apply μ hHm,
    cond_real_apply μ hHm] at hcipH'
  have hcipNH' := congrArg ENNReal.toReal
    (show μ[|Hᶜ] (a ∩ b) = μ[|Hᶜ] a * μ[|Hᶜ] b from (hcip false).measure_inter_eq_mul)
  rw [ENNReal.toReal_mul, cond_real_apply μ hHm.compl, cond_real_apply μ hHm.compl,
    cond_real_apply μ hHm.compl] at hcipNH'
  -- ℝ shadows, conditioning-set first.
  set pH := (μ H).toReal with hpH_def
  set pnH := (μ Hᶜ).toReal with hpnH_def
  set aH := (μ (H ∩ a)).toReal with haH_def
  set anH := (μ (Hᶜ ∩ a)).toReal with hanH_def
  set bH := (μ (H ∩ b)).toReal with hbH_def
  set bnH := (μ (Hᶜ ∩ b)).toReal with hbnH_def
  set abH := (μ (H ∩ (a ∩ b))).toReal with habH_def
  set abnH := (μ (Hᶜ ∩ (a ∩ b))).toReal with habnH_def
  have hpH_pos : 0 < pH := ENNReal.toReal_pos hH (measure_ne_top μ _)
  have hpnH_pos : 0 < pnH := ENNReal.toReal_pos hNH (measure_ne_top μ _)
  have hNormHP : pH + pnH = 1 := by
    have h := congrArg ENNReal.toReal (prob_add_prob_compl (μ := μ) hHm)
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_one] at h
  have htotA : aH + anH = (μ a).toReal := real_total μ hHm a
  have htotB : bH + bnH = (μ b).toReal := real_total μ hHm b
  have htotAB : abH + abnH = (μ (a ∩ b)).toReal := real_total μ hHm (a ∩ b)
  have haH_nn : 0 ≤ aH := ENNReal.toReal_nonneg
  have hanH_nn : 0 ≤ anH := ENNReal.toReal_nonneg
  have hbH_nn : 0 ≤ bH := ENNReal.toReal_nonneg
  have hbnH_nn : 0 ≤ bnH := ENNReal.toReal_nonneg
  -- CIP in mass form: abH·pH = aH·bH and abnH·pnH = anH·bnH.
  have hcipH : abH * pH = aH * bH := by
    rw [div_mul_div_comm,
      div_eq_div_iff hpH_pos.ne' (mul_pos hpH_pos hpH_pos).ne'] at hcipH'
    exact mul_right_cancel₀ hpH_pos.ne' (by linear_combination hcipH')
  have hcipNH : abnH * pnH = anH * bnH := by
    rw [div_mul_div_comm,
      div_eq_div_iff hpnH_pos.ne' (mul_pos hpnH_pos hpnH_pos).ne'] at hcipNH'
    exact mul_right_cancel₀ hpnH_pos.ne' (by linear_combination hcipNH')
  clear hcipH' hcipNH'
  -- Contrariness gives the sign of the factorized cross-product.
  have hSign : 0 < (pnH * aH - pH * anH) * (pH * bnH - pnH * bH) := by
    rcases hcontr with ⟨hposA, hnegB⟩ | ⟨hnegA, hposB⟩
    · have hA := (posRelevant_iff_real_cross ctx).mp hposA
      have hB := (negRelevant_iff_real_cross ctx hb0).mp hnegB
      nlinarith
    · have hA := (negRelevant_iff_real_cross ctx ha0).mp hnegA
      have hB := (posRelevant_iff_real_cross ctx).mp hposB
      nlinarith
  have hFact := cross_product_factorization aH anH bH bnH pH pnH hNormHP
  -- From CIP: P(A∧B)·pH·pnH = aH·bH·pnH + anH·bnH·pH.
  have h_cip_sum : (μ (a ∩ b)).toReal * (pH * pnH) =
      aH * bH * pnH + anH * bnH * pH := by
    rw [← htotAB]; nlinarith
  -- Hence P(A∧B) < P(A)·P(B).
  have hProd_pos : 0 < pH * pnH := mul_pos hpH_pos hpnH_pos
  have hKey : (μ (a ∩ b)).toReal < (μ a).toReal * (μ b).toReal := by
    have h1 : 0 < (μ a).toReal * (μ b).toReal * (pH * pnH) -
        (aH * bH * pnH + anH * bnH * pH) := by
      rw [← htotA, ← htotB]; linarith [hFact, hSign]
    nlinarith
  -- Conclude at the conditional.
  refine (ENNReal.toReal_lt_toReal (cond_apply_ne_top μ ham b)
    (measure_ne_top μ b)).mp ?_
  rw [cond_real_apply μ ham b, div_lt_iff₀ (ENNReal.toReal_pos ha0 (measure_ne_top μ a))]
  linarith [hKey, mul_comm (μ a).toReal (μ b).toReal]

/-- **Theorem 9**: When H = B, issue-conditional independence holds
automatically for any A.

P(A∧B∣B) = P(A∣B)·P(B∣B) because B∧(A∧B) = B∧A and P(B∣B) = 1, and
P(A∧B∣¬B) = P(A∣¬B)·P(B∣¬B) because both sides vanish on ¬B. -/
theorem condIndepIssue_defaultButCtx (μ : Measure W) [IsFiniteMeasure μ]
    (a b : Set W) (ham : MeasurableSet a) (hbm : MeasurableSet b) :
    CondIndepIssue (defaultButCtx μ b hbm) a b := by
  refine (condIndepIssue_iff _ ham hbm).mpr ⟨?_, ?_⟩
  · show μ[|b] (a ∩ b) = μ[|b] a * μ[|b] b
    rcases eq_or_ne (μ b) 0 with h0 | h0
    · simp [ProbabilityTheory.cond, Measure.restrict_eq_zero.mpr h0]
    · rw [cond_eq_one_of_subset μ hbm subset_rfl h0, mul_one, cond_apply hbm,
        cond_apply hbm, Set.inter_comm a b, ← Set.inter_assoc, Set.inter_self]
  · show μ[|bᶜ] (a ∩ b) = μ[|bᶜ] a * μ[|bᶜ] b
    have hzb : μ[|bᶜ] b = 0 := by
      rw [cond_apply hbm.compl, Set.compl_inter_self, measure_empty, mul_zero]
    have hzab : μ[|bᶜ] (a ∩ b) = 0 := by
      rw [cond_apply hbm.compl,
        show bᶜ ∩ (a ∩ b) = ∅ by
          rw [Set.inter_comm a b, ← Set.inter_assoc, Set.compl_inter_self,
            Set.empty_inter],
        measure_empty, mul_zero]
    rw [hzab, hzb, mul_zero]

/-- **Theorem 10**: Negative relevance implies unexpectedness in default-but.

When the issue is B itself and A is negatively relevant to H = B, then
P(B∣A) < P(B) — B is unexpected given A. -/
theorem default_but_properties (μ : Measure W) [IsProbabilityMeasure μ]
    {a b : Set W} (ham : MeasurableSet a) (hbm : MeasurableSet b)
    (hNegA : negRelevant (defaultButCtx μ b hbm) a)
    (ha0 : μ a ≠ 0) (hB : μ b ≠ 0) (hNB : μ bᶜ ≠ 0) :
    μ[|a] b < μ b := by
  haveI : (defaultButCtx μ b hbm).Nondegenerate := ⟨hB, hNB⟩
  have hcross := (negRelevant_iff_real_cross (defaultButCtx μ b hbm) ha0).mp hNegA
  set pB := (μ b).toReal with hpB_def
  set pnB := (μ bᶜ).toReal with hpnB_def
  set xa := (μ (b ∩ a)).toReal with hxa_def
  set ya := (μ (bᶜ ∩ a)).toReal with hya_def
  have htot : xa + ya = (μ a).toReal := real_total μ hbm a
  have hnorm : pB + pnB = 1 := by
    have h := congrArg ENNReal.toReal (prob_add_prob_compl (μ := μ) hbm)
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_one] at h
  have hxa_nn : 0 ≤ xa := ENNReal.toReal_nonneg
  have hkey : xa < pB * (μ a).toReal := by
    rw [← htot]
    have hx : xa * (pB + pnB) = xa * 1 := by rw [hnorm]
    nlinarith [hcross, hx]
  refine (ENNReal.toReal_lt_toReal (cond_apply_ne_top μ ham b)
    (measure_ne_top μ b)).mp ?_
  rw [cond_real_apply μ ham b, div_lt_iff₀ (ENNReal.toReal_pos ha0 (measure_ne_top μ a)),
    Set.inter_comm a b]
  exact hkey

/-- **Corollary 11** (Harris universal): NNIR prevents "Qa but Qb".

In the default-but interpretation with a live antecedent Q(b), the issue is
Q(b) itself: P(Q(b)∣Q(b)) = 1 while P(Q(b)∣¬Q(b)) = 0, so the Bayes factor
is genuinely infinite — Q(b) cannot be negatively relevant to itself,
violating `butFelicitous`. -/
theorem harris_universal {E : Type*} (μ : Measure W) [IsFiniteMeasure μ]
    (Q : E → Set W) (a b : E) (hQb : MeasurableSet (Q b)) (hb : μ (Q b) ≠ 0)
    (_hnnir : NNIR E μ Q) :
    ¬ butFelicitous (defaultButCtx μ (Q b) hQb) (Q a) (Q b) := by
  rintro ⟨_, hNeg, _⟩
  simp only [negRelevant, bayesFactor_def] at hNeg
  rw [cond_eq_one_of_subset μ hQb subset_rfl hb,
    show μ[|(Q b)ᶜ] (Q b) = 0 from by
      rw [cond_apply hQb.compl, Set.compl_inter_self, measure_empty, mul_zero],
    ENNReal.div_zero one_ne_zero] at hNeg
  exact absurd hNeg (by simp)

/-! **Theorem 13** (not formalized): Savage-Kemeny-Gaifman-Humburg theorem.

Symmetric probability on finite models extends to infinite models only if
NNIR holds, providing a foundational justification for NNIR as a
rationality constraint. Requires de Finetti-style exchangeability
arguments.

Reference: Gaifman, H. & Snir, M. (1982). Probabilities over rich languages. -/

end DTS.But
