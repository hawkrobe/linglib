import Linglib.Pragmatics.DecisionTheoretic.Basic

/-!
# Decision-Theoretic Semantics: Scalar Implicature ([merin-1999-relevance] §3)
[merin-1999-relevance]

Merin's DTS account of scalar implicature via *protentive speaker meaning*
and relevance-ordered alternatives. The key insight: scalar implicature
arises because conjunction is more relevant than disjunction (Theorem 6a),
so a speaker who says "A or B" implicates ¬(A ∧ B).

## Key Definitions

- `sgnRelevance` — Protentive Speaker Meaning (Def. 7): the hypothesis
  supported by an utterance's relevance sign
- `upwardCone` / `downwardCone` — alternatives ordered by Bayes factor
- `ScalarInterpretation` — claim/counterclaim structure for scalar
  alternatives (Hypothesis 1)

## Main Results

- **Prediction 1** (`not_if_not_indeed_disjunct`): a disjunct does not
  always dominate its disjunction
- **Prediction 2** (`if_not_indeed_conjunction`): under CIP, conjunction
  dominates both conjuncts and disjunction
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DTS.ScalarImplicature

open DTS

variable {W : Type*} [MeasurableSpace W]

/-! ### Protentive Speaker Meaning (Def. 7) -/

/-- Sign of relevance: positive (supports H), negative (supports ¬H), or
neutral. -/
inductive RelevanceSign where
  | pos | neg | neutral
  deriving DecidableEq, Repr

open Classical in
/-- Protentive Speaker Meaning (Def. 7): the hypothesis supported by an
utterance's relevance sign. -/
noncomputable def sgnRelevance (ctx : Context W) (e : Set W) : RelevanceSign :=
  if 1 < bayesFactor ctx e then .pos
  else if bayesFactor ctx e < 1 then .neg
  else .neutral

/-! ### Relevance-ordered alternatives (Def. 8) -/

/-- Upward cone: alternatives at least as relevant as σ. -/
def upwardCone (ctx : Context W) (alts : Set (Set W)) (σ : Set W) : Set (Set W) :=
  {a ∈ alts | bayesFactor ctx σ ≤ bayesFactor ctx a}

/-- Downward cone: alternatives at most as relevant as σ. -/
def downwardCone (ctx : Context W) (alts : Set (Set W)) (σ : Set W) : Set (Set W) :=
  {a ∈ alts | bayesFactor ctx a ≤ bayesFactor ctx σ}

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

/-! ### Predictions -/

/-- **Prediction 1**: It is NOT the case that a disjunct always strictly
dominates its disjunction in Bayes factor: a disjunction with an absorbed
disjunct is exactly as relevant as the dominant disjunct. -/
theorem not_if_not_indeed_disjunct :
    ¬ (∀ (ctx : Context World4) (a b : Set World4),
      posRelevant ctx a → posRelevant ctx b →
      bayesFactor ctx (a ∪ b) < bayesFactor ctx a) := by
  intro h
  have hsub : (↑({World4.w0} : Finset World4) : Set World4) ⊆
      ↑({World4.w0, World4.w1} : Finset World4) :=
    Finset.coe_subset.mpr (by decide)
  have := h ⟨(↑({World4.w0} : Finset World4) : Set World4), .of_discrete, .count⟩
    ↑({World4.w0, World4.w1} : Finset World4) ↑({World4.w0} : Finset World4) ?_ ?_
  · rw [Set.union_eq_self_of_subset_right hsub] at this
    exact lt_irrefl _ this
  · -- BF({w0, w1}) = 3 > 1
    simp only [posRelevant, bayesFactor, cond_apply MeasurableSet.of_discrete,
      ← Finset.coe_compl, ← Finset.coe_inter, Measure.count_apply_finset]
    rw [show ({World4.w0} : Finset World4).card = 1 by decide,
      show ({World4.w0} ∩ {World4.w0, World4.w1} : Finset World4).card = 1 by decide,
      show ({World4.w0}ᶜ : Finset World4).card = 3 by decide,
      show ({World4.w0}ᶜ ∩ {World4.w0, World4.w1} : Finset World4).card = 1 by decide]
    simp only [Nat.cast_one, Nat.cast_ofNat, inv_one]
    norm_num
  · -- BF({w0}) = ∞ > 1: the issue itself is infinitely relevant
    simp only [posRelevant, bayesFactor, cond_apply MeasurableSet.of_discrete,
      ← Finset.coe_compl, ← Finset.coe_inter, Measure.count_apply_finset]
    rw [show ({World4.w0} : Finset World4).card = 1 by decide,
      show ({World4.w0} ∩ {World4.w0} : Finset World4).card = 1 by decide,
      show ({World4.w0}ᶜ : Finset World4).card = 3 by decide,
      show ({World4.w0}ᶜ ∩ {World4.w0} : Finset World4).card = 0 by decide]
    simp

/-- **Prediction 2**: Under CIP with both A, B positively relevant,
conjunction dominates both conjuncts and disjunction.

This is the core of Merin's scalar implicature account: "A and B" is
strictly more relevant than "A or B", explaining why "or" implicates ¬∧. -/
theorem if_not_indeed_conjunction (ctx : Context W) [IsFiniteMeasure ctx.prior]
    (a b : Set W) (hbm : MeasurableSet b)
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNotH : ctx.prior[|ctx.topicᶜ] a ≠ 0)
    (hNotH' : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    bayesFactor ctx a < bayesFactor ctx (a ∩ b) ∧
    bayesFactor ctx (a ∪ b) < bayesFactor ctx (a ∩ b) := by
  have hFull := conjunction_dominates_disjunction ctx a b hbm hcip hPosA hPosB
    hNotH hNotH'
  exact ⟨lt_of_le_of_lt (le_max_left _ _) hFull.1, hFull.2.1.trans hFull.1⟩

end DTS.ScalarImplicature
