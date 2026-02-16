import Linglib.Theories.DTS.Core

/-!
# Decision-Theoretic Semantics: Scalar Implicature (Merin 1999 §3)

Merin's DTS account of scalar implicature via *protentive speaker meaning*
and relevance-ordered alternatives. The key insight: scalar implicature
arises because conjunction is more relevant than disjunction (Theorem 6a),
so a speaker who says "A or B" implicates ¬(A ∧ B).

## Key Definitions

- `PSM` — Protentive Speaker Meaning (Def. 7): the hypothesis supported
  by an utterance's relevance sign
- `upwardCone` / `downwardCone` — alternatives ordered by Bayes factor
- `Hypothesis1` — claim/counterclaim structure for scalar alternatives

## Main Results

- **Prediction 1**: A disjunct does not always dominate its disjunction
- **Prediction 2**: Under CIP, conjunction dominates both conjuncts and
  disjunction

## References

- Merin, A. (1999). Information, relevance, and social decisionmaking.
  §3: Scalar implicature.
-/

namespace Theories.DTS.ScalarImplicature

open Core.Proposition
open Theories.DTS

-- ============================================================
-- Section 1: Protentive Speaker Meaning (Def. 7)
-- ============================================================

/-- Sign of relevance: positive, negative, or neutral. -/
inductive RelevanceSign where
  | pos   -- supports H
  | neg   -- supports ¬H
  | neutral
  deriving DecidableEq, Repr

/-- Protentive Speaker Meaning (Def. 7): the hypothesis supported by
an utterance's relevance sign.

If E is positively relevant, PSM = H.
If E is negatively relevant, PSM = ¬H.
Otherwise neutral. -/
def sgnRelevance {W : Type*} [Fintype W] (ctx : DTSContext W) (e : BProp W) : RelevanceSign :=
  let bf := bayesFactor ctx e
  if bf > 1 then .pos
  else if bf < 1 then .neg
  else .neutral

-- ============================================================
-- Section 2: Relevance-Ordered Alternatives (Def. 8)
-- ============================================================

/-- Upward cone: alternatives at least as relevant as σ.

Given a list of alternatives ordered by Bayes factor, the upward cone of σ
contains all alternatives with BF ≥ BF(σ). -/
def upwardCone {W : Type*} [Fintype W] (ctx : DTSContext W)
    (alts : List (BProp W)) (σ : BProp W) : List (BProp W) :=
  alts.filter λ a => bayesFactor ctx a ≥ bayesFactor ctx σ

/-- Downward cone: alternatives at most as relevant as σ. -/
def downwardCone {W : Type*} [Fintype W] (ctx : DTSContext W)
    (alts : List (BProp W)) (σ : BProp W) : List (BProp W) :=
  alts.filter λ a => bayesFactor ctx a ≤ bayesFactor ctx σ

/-- Hypothesis 1: Claim/counterclaim structure for scalar alternatives.

The *claim* is the disjunction of upward-cone members (what the speaker
means to convey). The *counterclaim* is the disjunction of downward-cone
members (what the speaker implicates is false). -/
structure ScalarInterpretation (W : Type*) where
  /-- The scalar alternative uttered. -/
  uttered : BProp W
  /-- The claim: disjunction of upward cone members. -/
  claim : BProp W
  /-- The counterclaim: disjunction of downward cone members. -/
  counterclaim : BProp W

-- ============================================================
-- Section 3: Predictions
-- ============================================================

section Predictions

variable {W : Type*} [Fintype W]

/-- **Prediction 1**: It is NOT the case that a disjunct always dominates
its disjunction in Bayes factor.

This follows from Theorem 6b direction: XOR (and hence plain disjunction)
need not track the relevance of individual disjuncts. -/
theorem not_if_not_indeed_disjunct :
    ¬ (∀ (ctx : DTSContext World4) (a b : BProp World4),
      posRelevant ctx a → posRelevant ctx b →
      bayesFactor ctx a > bayesFactor ctx (Decidable.por World4 a b)) := by
  -- Counterexample: a = b, so a∨b = a and BF(a) = BF(a∨b), not strict >.
  intro h
  have := h ⟨⟨λ w => match w with | .w0 => true | _ => false⟩, λ _ => 1/4⟩
            (λ w => match w with | .w0 | .w1 => true | _ => false)
            (λ w => match w with | .w0 | .w1 => true | _ => false)
            (by native_decide) (by native_decide)
  simp only [bayesFactor, condProb, probSum, Decidable.pand, Decidable.pnot, Decidable.por] at this
  norm_num at this

/-- **Prediction 2**: Under CIP with both A,B positively relevant,
conjunction dominates both conjuncts and disjunction.

This is the core of Merin's scalar implicature account: "A and B" is
strictly more relevant than "A or B", explaining why "or" implicates ¬∧. -/
theorem if_not_indeed_conjunction (ctx : DTSContext W) (a b : BProp W)
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNonzero : condProb ctx.prior a (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hNonzero' : condProb ctx.prior b (Decidable.pnot W ctx.issue.topic) ≠ 0)
    (hABNonzero : condProb ctx.prior (Decidable.pand W a b)
      (Decidable.pnot W ctx.issue.topic) ≠ 0) :
    bayesFactor ctx (Decidable.pand W a b) > bayesFactor ctx a ∧
    bayesFactor ctx (Decidable.pand W a b) >
      bayesFactor ctx (Decidable.por W a b) := by
  have hConj := conjunction_dominates_conjuncts ctx a b hcip hPosA hPosB
    hNonzero hNonzero' hABNonzero
  constructor
  · exact lt_of_le_of_lt (le_max_left _ _) hConj
  -- TODO: Disjunction ordering requires inclusion-exclusion on condProb.
  · sorry

end Predictions

end Theories.DTS.ScalarImplicature
