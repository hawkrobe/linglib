import Linglib.Pragmatics.DecisionTheoretic.Basic
import Linglib.Pragmatics.DecisionTheoretic.ScalarImplicature
import Linglib.Semantics.Presupposition.Basic

/-!
# Decision-Theoretic Semantics: "Also" ([merin-1999-relevance] §5.2–5.4)
[merin-1999-relevance]

Merin's DTS account of additive particles. Presupposition is modeled as
*i-irrelevance*: a presupposed proposition is one whose conditional is the
prior itself — conditioning on it changes nothing. "Also" requires
topic-anaphoric salience: the antecedent D must have been relevant before
becoming presupposed.

## Key Definitions

- `presupposedIrrelevant` (Def. 12): presupposition as informational
  inertness, `μ[|a] = μ`
- `TopicAnaphoricSalience` (Def. 13): conditions for anaphoric antecedent
- `AlsoFelicitous` (Hypothesis 8): felicity conditions for "and also"
- `properlyAccommodable` (partial Def. 14): accommodable propositions

## Main Results

- **Corollary 15** (`also_nonidentity`): "also" requires non-identity (a ≠ b)
- **Fact 17** (`presuppositional_independence_additivity`): presupposition
  implies multiplicativity of the Bayes factor without CIP
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DTS.Also

open Semantics.Presupposition
open DTS
open DTS.ScalarImplicature (sgnRelevance RelevanceSign)

variable {W : Type*} [MeasurableSpace W]

/-! ### Presupposition as irrelevance (Def. 12) -/

/-- **Definition 12**: A proposition A is i-presupposed iff conditioning on
it changes nothing: the conditional measure is the prior itself.

This is stronger than P(A) = 1 in spirit: A is informationally *inert* —
P(X∣A) = P(X) for every X at once. -/
def presupposedIrrelevant (μ : Measure W) (a : Set W) : Prop :=
  μ[|a] = μ

/-! ### Topic-anaphoric salience (Def. 13) -/

/-- **Definition 13**: Topic-anaphoric salience.

D is topic-anaphorically salient for E in context iff:
(i) E is relevant to the current issue H,
(ii) D is presupposed (informationally inert),
(iii) D was recently relevant — before becoming presupposed, D bore on the
issue. -/
structure TopicAnaphoricSalience (ctx : Context W) (d e : Set W) where
  /-- E is relevant to the current issue. -/
  eRelevant : posRelevant ctx e ∨ negRelevant ctx e
  /-- D is currently presupposed (informationally inert). -/
  dPresupposed : presupposedIrrelevant ctx.prior d
  /-- D was previously relevant (before becoming presupposed). -/
  dWasRelevant : RelevanceSign

/-! ### "Also" felicity (Hypothesis 8) -/

/-- **Hypothesis 8**: Felicity conditions for "and also(b, B)".

For "Q(a) and also Q(b)": Q(a) and Q(b) have the *same* relevance sign
(both support or both oppose H). This distinguishes "and also" from
"but also" (opposite signs).

The `sameSign` field records the relevance sign of Q(a) before it was
presupposed; `signMatches` requires Q(b) to bear it now. -/
structure AlsoFelicitous (ctx : Context W) (qa qb : Set W) where
  /-- Q(a) is presupposed. -/
  qaPresupposed : presupposedIrrelevant ctx.prior qa
  /-- Q(b) is relevant. -/
  qbRelevant : posRelevant ctx qb ∨ negRelevant ctx qb
  /-- Same relevance sign: Q(a) had the same sign as Q(b) before
      presupposition. -/
  sameSign : RelevanceSign
  /-- The sign matches Q(b)'s current relevance direction. -/
  signMatches : sgnRelevance ctx qb = sameSign

/-- "But also" variant: opposite relevance signs.

"Q(a) but also Q(b)": Q(a) had the opposite relevance sign from Q(b). This
combines adversativity ("but") with additivity ("also"). -/
structure ButAlsoFelicitous (ctx : Context W) (qa qb : Set W) where
  /-- Q(a) is presupposed. -/
  qaPresupposed : presupposedIrrelevant ctx.prior qa
  /-- Q(b) is relevant. -/
  qbRelevant : posRelevant ctx qb ∨ negRelevant ctx qb
  /-- Previous sign of Q(a). -/
  previousSign : RelevanceSign
  /-- Current sign of Q(b). -/
  currentSign : RelevanceSign
  /-- Signs are opposite. -/
  oppositeSigns : (previousSign = .pos ∧ currentSign = .neg) ∨
                  (previousSign = .neg ∧ currentSign = .pos)

/-! ### Accommodation (partial Def. 14) -/

/-- **Partial Definition 14**: Properly accommodable propositions.

A proposition φ is properly accommodable iff:
(i) 0 < P(φ) (non-trivially satisfiable),
(ii) P(φ) < 1 (not already known),
(iii) φ is irrelevant to the current issue. -/
def properlyAccommodable (ctx : Context W) (φ : Set W) : Prop :=
  0 < ctx.prior φ ∧ ctx.prior φ < 1 ∧ irrelevant ctx φ

/-! ### Theorems -/

section Theorems

/-- A presupposed proposition has nonzero mass (else conditioning on it
would collapse the prior to the zero measure). -/
private lemma presup_ne_zero (μ : Measure W) [IsProbabilityMeasure μ] {a : Set W}
    (hp : presupposedIrrelevant μ a) : μ a ≠ 0 := by
  intro h0
  have h1 : μ[|a] = 0 := by
    rw [ProbabilityTheory.cond, Measure.restrict_eq_zero.mpr h0, smul_zero]
  have h2 := congrArg (fun m : Measure W => m Set.univ) (hp.symm.trans h1)
  simp [measure_univ] at h2

/-- Presupposition factorizes every joint: P(A ∩ X) = P(A)·P(X). -/
private lemma presup_joint (μ : Measure W) [IsProbabilityMeasure μ] {a : Set W}
    (ha : MeasurableSet a) (hp : presupposedIrrelevant μ a) (x : Set W) :
    μ (a ∩ x) = μ a * μ x := by
  have hA := presup_ne_zero μ hp
  have hx : μ[|a] x = μ x := congrArg (fun m : Measure W => m x) hp
  rw [cond_apply ha μ x] at hx
  calc μ (a ∩ x) = μ a * ((μ a)⁻¹ * μ (a ∩ x)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hA (measure_ne_top μ a), one_mul]
  _ = μ a * μ x := by rw [hx]

/-- Presupposition implies the Bayes factor equals 1: an informationally
inert proposition is equally likely under either side of any issue. -/
private lemma presup_implies_bf_one (ctx : Context W)
    [IsProbabilityMeasure ctx.prior] {a : Set W} (ha : MeasurableSet a)
    (hp : presupposedIrrelevant ctx.prior a)
    (hH : ctx.prior ctx.topic ≠ 0) (hNH : ctx.prior ctx.topicᶜ ≠ 0) :
    bayesFactor ctx a = 1 := by
  have hA := presup_ne_zero ctx.prior hp
  have h1 : ctx.prior[|ctx.topic] a = ctx.prior a := by
    rw [cond_apply ctx.topicMeasurable, Set.inter_comm,
      presup_joint ctx.prior ha hp, mul_comm, mul_assoc,
      ENNReal.mul_inv_cancel hH (measure_ne_top _ _), mul_one]
  have h2 : ctx.prior[|ctx.topicᶜ] a = ctx.prior a := by
    rw [cond_apply ctx.topicMeasurable.compl, Set.inter_comm,
      presup_joint ctx.prior ha hp, mul_comm, mul_assoc,
      ENNReal.mul_inv_cancel hNH (measure_ne_top _ _), mul_one]
  rw [bayesFactor_def, h1, h2, ENNReal.div_self hA (measure_ne_top _ _)]

/-- **Corollary 15**: "Also" requires non-identity.

If Q(a) is presupposed and "Q(a) and also Q(b)" is felicitous, then a ≠ b:
a presupposed proposition has Bayes factor 1, but felicity requires Q(b)
to be relevant. -/
theorem also_nonidentity {E : Type*} (ctx : Context W)
    [IsProbabilityMeasure ctx.prior] (Q : E → Set W) (a b : E)
    (hQa : MeasurableSet (Q a))
    (hAlso : AlsoFelicitous ctx (Q a) (Q b))
    (hH : ctx.prior ctx.topic ≠ 0) (hNH : ctx.prior ctx.topicᶜ ≠ 0) :
    a ≠ b := by
  intro hab
  subst hab
  have hBF := presup_implies_bf_one ctx hQa hAlso.qaPresupposed hH hNH
  rcases hAlso.qbRelevant with hPos | hNeg
  · exact absurd hBF.symm (ne_of_lt hPos)
  · exact absurd hBF (ne_of_lt hNeg)

/-- Presupposition implies CIP: an informationally inert proposition is
conditionally independent of any other proposition given both H and ¬H. -/
private lemma presup_implies_cip (ctx : Context W)
    [IsProbabilityMeasure ctx.prior] {a b : Set W} (ha : MeasurableSet a)
    (hbm : MeasurableSet b)
    (hp : presupposedIrrelevant ctx.prior a) : CondIndepIssue ctx a b := by
  have hA := presup_ne_zero ctx.prior hp
  refine (condIndepIssue_iff _ ha hbm).mpr ⟨?_, ?_⟩
  · rcases eq_or_ne (ctx.prior ctx.topic) 0 with h0 | h0
    · simp [ProbabilityTheory.cond, Measure.restrict_eq_zero.mpr h0]
    · rw [cond_apply ctx.topicMeasurable, cond_apply ctx.topicMeasurable,
        cond_apply ctx.topicMeasurable,
        show ctx.topic ∩ (a ∩ b) = a ∩ (ctx.topic ∩ b) by
          ext w; simp [Set.mem_inter_iff]; tauto,
        presup_joint ctx.prior ha hp,
        show ctx.topic ∩ a = a ∩ ctx.topic from Set.inter_comm _ _,
        presup_joint ctx.prior ha hp,
        show (ctx.prior ctx.topic)⁻¹ * (ctx.prior a * ctx.prior ctx.topic) *
            ((ctx.prior ctx.topic)⁻¹ * ctx.prior (ctx.topic ∩ b)) =
          (ctx.prior ctx.topic)⁻¹ * ctx.prior ctx.topic *
            ((ctx.prior ctx.topic)⁻¹ * (ctx.prior a * ctx.prior (ctx.topic ∩ b)))
          from by ring,
        ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), one_mul]
  · rcases eq_or_ne (ctx.prior ctx.topicᶜ) 0 with h0 | h0
    · simp [ProbabilityTheory.cond, Measure.restrict_eq_zero.mpr h0]
    · rw [cond_apply ctx.topicMeasurable.compl, cond_apply ctx.topicMeasurable.compl,
        cond_apply ctx.topicMeasurable.compl,
        show ctx.topicᶜ ∩ (a ∩ b) = a ∩ (ctx.topicᶜ ∩ b) by
          ext w; simp [Set.mem_inter_iff]; tauto,
        presup_joint ctx.prior ha hp,
        show ctx.topicᶜ ∩ a = a ∩ ctx.topicᶜ from Set.inter_comm _ _,
        presup_joint ctx.prior ha hp,
        show (ctx.prior ctx.topicᶜ)⁻¹ * (ctx.prior a * ctx.prior ctx.topicᶜ) *
            ((ctx.prior ctx.topicᶜ)⁻¹ * ctx.prior (ctx.topicᶜ ∩ b)) =
          (ctx.prior ctx.topicᶜ)⁻¹ * ctx.prior ctx.topicᶜ *
            ((ctx.prior ctx.topicᶜ)⁻¹ * (ctx.prior a * ctx.prior (ctx.topicᶜ ∩ b)))
          from by ring,
        ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), one_mul]

/-- **Fact 17**: Presupposition implies multiplicativity without CIP.

If A is presupposed, then BF(A∧B) = BF(A)·BF(B) with no independence
assumption: inertness supplies the factorization. -/
theorem presuppositional_independence_additivity (ctx : Context W)
    [IsProbabilityMeasure ctx.prior] {a b : Set W} (ha : MeasurableSet a)
    (hbm : MeasurableSet b)
    (hp : presupposedIrrelevant ctx.prior a)
    (hNotH' : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    bayesFactor ctx (a ∩ b) = bayesFactor ctx a * bayesFactor ctx b :=
  (presup_implies_cip ctx ha hbm hp).bayesFactor_inter hNotH'

/-! **Prediction 4** (not formalized): "Also" removes causal implicature.

In "Kim fell and she also broke her arm", the additive particle "also"
enforces presuppositional independence of the antecedent ("Kim fell"),
removing the default causal reading that plain "and" would carry ("Kim
fell and [as a result] broke her arm").

This connects to `Causation` — the causal reading arises from
non-independence of the conjuncts, and "also" explicitly marks the
antecedent as presupposed (hence independent). -/

end Theorems

end DTS.Also
