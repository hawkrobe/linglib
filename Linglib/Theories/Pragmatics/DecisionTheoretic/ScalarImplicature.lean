import Linglib.Theories.Pragmatics.DecisionTheoretic.Core

/-!
# Decision-Theoretic Semantics: Scalar Implicature (@cite{merin-1999} §3)
@cite{merin-1999}

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

-/

namespace DTS.ScalarImplicature

open DTS

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
def sgnRelevance {W : Type*} [Fintype W] (ctx : DTSContext W) (e : Set W)
    [DecidablePred (· ∈ e)] : RelevanceSign :=
  let bf := bayesFactor ctx e
  if bf > 1 then .pos
  else if bf < 1 then .neg
  else .neutral

-- ============================================================
-- Section 2: Relevance-Ordered Alternatives (Def. 8)
-- ============================================================

/-- Upward cone: alternatives at least as relevant as σ.

Given a list of alternatives ordered by Bayes factor, the upward cone of σ
contains all alternatives with BF ≥ BF(σ).

Each alternative is bundled with its decidability instance so that
`bayesFactor` (which requires `[DecidablePred]`) can be evaluated. -/
def upwardCone {W : Type*} [Fintype W] (ctx : DTSContext W)
    (alts : List (Σ p : Set W, DecidablePred (· ∈ p))) (σ : Set W)
    [DecidablePred (· ∈ σ)] : List (Σ p : Set W, DecidablePred (· ∈ p)) :=
  alts.filter (fun a => letI := a.2; bayesFactor ctx a.1 ≥ bayesFactor ctx σ)

/-- Downward cone: alternatives at most as relevant as σ. -/
def downwardCone {W : Type*} [Fintype W] (ctx : DTSContext W)
    (alts : List (Σ p : Set W, DecidablePred (· ∈ p))) (σ : Set W)
    [DecidablePred (· ∈ σ)] : List (Σ p : Set W, DecidablePred (· ∈ p)) :=
  alts.filter (fun a => letI := a.2; bayesFactor ctx a.1 ≤ bayesFactor ctx σ)

/-- Hypothesis 1: Claim/counterclaim structure for scalar alternatives.

The *claim* is the disjunction of upward-cone members (what the speaker
means to convey). The *counterclaim* is the disjunction of downward-cone
members (what the speaker implicates is false). -/
structure ScalarInterpretation (W : Type*) where
  /-- The scalar alternative uttered. -/
  uttered : Set W
  /-- The claim: disjunction of upward cone members. -/
  claim : Set W
  /-- The counterclaim: disjunction of downward cone members. -/
  counterclaim : Set W

-- ============================================================
-- Section 3: Predictions
-- ============================================================

section Predictions

variable {W : Type*} [Fintype W]

/-- **Prediction 1**: It is NOT the case that a disjunct always dominates
its disjunction in Bayes factor.

This follows from Theorem 6b direction: XOR (and hence plain disjunction)
need not track the relevance of individual disjuncts.

TODO: Construct a concrete counterexample over `World4` with appropriate
prior, decidable predicates, and the witnesses showing
`bayesFactor ctx a = bayesFactor ctx (a ∪ b)` (so the
strict `>` inequality fails). The original Bool proof relied on
`native_decide` over a 4-world enumeration; a Prop-level counterexample
needs explicit decidability for the chosen predicates. -/
theorem not_if_not_indeed_disjunct :
    ¬ (∀ (ctx : DTSContext World4) (a b : Set World4)
       [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)],
      posRelevant ctx a → posRelevant ctx b →
      bayesFactor ctx a > bayesFactor ctx (a ∪ b)) := by
  sorry

/-- **Prediction 2**: Under CIP with both A,B positively relevant,
conjunction dominates both conjuncts and disjunction.

This is the core of Merin's scalar implicature account: "A and B" is
strictly more relevant than "A or B", explaining why "or" implicates ¬∧. -/
theorem if_not_indeed_conjunction (ctx : DTSContext W) (a b : Set W)
    [DecidablePred (· ∈ a)] [DecidablePred (· ∈ b)]
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNonzero : condProb ctx.prior a (ctx.topicᶜ) ≠ 0)
    (hNonzero' : condProb ctx.prior b (ctx.topicᶜ) ≠ 0)
    (hABNonzero : condProb ctx.prior (a ∩ b)
      (ctx.topicᶜ) ≠ 0)
    (hPrior : ∀ w, ctx.prior w ≥ 0) :
    bayesFactor ctx (a ∩ b) > bayesFactor ctx a ∧
    bayesFactor ctx (a ∩ b) >
      bayesFactor ctx (a ∪ b) := by
  have hFull := conjunction_dominates_disjunction ctx a b hcip hPosA hPosB
    hNonzero hNonzero' hABNonzero hPrior
  constructor
  · exact lt_of_le_of_lt (le_max_left _ _) hFull.1
  · exact lt_trans hFull.2.1 hFull.1

end Predictions

end DTS.ScalarImplicature
