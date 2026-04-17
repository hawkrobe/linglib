import Linglib.Core.Agent.Emotion
import Linglib.Core.Agent.BToM
import Linglib.Core.GameTheory
import Linglib.Core.Agent.DecisionTheory
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Linglib.Theories.Semantics.Gradability.Classification

/-!
# @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023} — Emotion Prediction as
  Computation over a Generative Theory of Mind

Houlihan, Kleiman-Weiner, Hewitt, Tenenbaum & Saxe. *Phil. Trans. R. Soc. A* 381: 20220047.

## Overview

Emotion prediction = inverse planning + computed appraisals + emotion concepts.

**Module 1** (Inverse Planning): Observers infer a player's social preferences
(ω_Money, ω_AIA, ω_DIA) and beliefs (π_{a₂}) from their action in a Split-or-Steal
game, using Bayesian inversion of a forward planning model with Fehr-Schmidt
social utility.

**Module 2** (Computed Appraisals): Four appraisal types (AU, PE, CFa₁, CFa₂)
computed over three utility domains (monetary, AIA, DIA) × two perspectives
(base, reputational), yielding a 19-dimensional appraisal space.

**Module 3** (Emotion Concepts): Each of 20 emotions is a specific sparse
readout (β weights) over the shared appraisal space. The learned readout
structure (Fig. 4) is unique for each emotion — a reverse-engineered
computational appraisal theory.

## Key Results

1. Social preferences (not just monetary) are necessary: the SOCIALLESION
   model (ccc = 0.663) is much worse than COMPUTEDAPPRAISALS (ccc = 0.854).
2. Inverse planning is necessary: the INVERSEPLANNINGLESION model
   (ccc = 0.762) can't predict *why*-dependent emotions (envy, gratitude).
3. Different emotions load on different utility domains: envy is specifically
   about DIA, guilt about reputational AIA.

## File Structure

- §1. Domain-refined emotion profiles (19-dimensional, from Fig. 4)
- §2. PublicGame BToM instantiation
- §3. Structural theorems connecting emotion profiles to game features
- §4. Evaluative adjective semantics via inferred preference weights
- §5. Lesion model structure
-/

set_option autoImplicit false

namespace HoulihanEtAl2023

open Core.Agent.Emotion Core.GameTheory Core.Agent.SocialUtility
     Core.DecisionTheory

-- ════════════════════════════════════════════════════════════════
-- §1. Domain-Refined Emotion Profiles
-- ════════════════════════════════════════════════════════════════

/-! Domain-refined profiles abstracted from Fig. 4 of
@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}.
Each profile specifies signs for monetary (M), affiliation/AIA (A),
and social equity/DIA (E) base domains, plus reputational (R).

Convention: `.positive` = β > 0, `.negative` = β < 0, `.irrelevant` = β ≈ 0.

These refine the qualitative profiles in `Core.Agent.Emotion` by
decomposing the collapsed `base` sign into three domain-specific signs. -/

/-- Helper: all-irrelevant domain weights. -/
private abbrev D0 : DomainWeights := ⟨.irrelevant, .irrelevant, .irrelevant⟩
/-- Helper: all-irrelevant refined perspective. -/
private abbrev R0 : RefinedPerspectiveWeights := ⟨D0, .irrelevant⟩

/-! ### Positive Emotions -/

/-- Joy: positive AU and PE on monetary. -/
def joyR : RefinedEmotionProfile :=
  ⟨"joy",
   ⟨⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,  -- AU: money +
    ⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,  -- PE: money +
    R0, R0⟩, .retrospective⟩

/-- Surprise: loads on |PEπ_{a₂}| — the absolute prediction error about
the opponent's action. This is the paper's 19th appraisal dimension,
distinct from the per-domain base PE dimensions (PE_base_{Money,AIA,DIA}).
Placed in PE.reputational as the best available slot, since it concerns
the social dimension (how unexpected was the opponent's choice?). -/
def surpriseR : RefinedEmotionProfile :=
  ⟨"surprise",
   ⟨R0,
    ⟨D0, .positive⟩,   -- PE reputational: |PEπ_{a₂}| (opponent acted unexpectedly)
    R0, R0⟩, .retrospective⟩

/-- Pride: positive AU on monetary + reputational, positive CFa reputational. -/
def prideR : RefinedEmotionProfile :=
  ⟨"pride",
   ⟨⟨⟨.positive, .irrelevant, .irrelevant⟩, .positive⟩,   -- AU: money+ repu+
    R0,
    ⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,  -- CFa: money+
    R0⟩, .retrospective⟩

/-- Gratitude: positive AU/PE on monetary, negative CFo (opponent's
alternative would have been worse — opponent was kind). -/
def gratitudeR : RefinedEmotionProfile :=
  ⟨"gratitude",
   ⟨⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,  -- AU: money+
    ⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,  -- PE: money+
    R0,
    ⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩⟩, -- CFo: money−
   .retrospective⟩

/-- Relief: positive AU/PE, negative CFa (own alternative was worse). -/
def reliefR : RefinedEmotionProfile :=
  ⟨"relief",
   ⟨⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    ⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    ⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    R0⟩, .retrospective⟩

/-- Amusement: positive AU/PE/CFo on monetary. -/
def amusementR : RefinedEmotionProfile :=
  ⟨"amusement",
   ⟨⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    ⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    R0,
    ⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩⟩,
   .retrospective⟩

/-- Excitement: positive AU monetary, positive PE monetary + reputational. -/
def excitementR : RefinedEmotionProfile :=
  ⟨"excitement",
   ⟨⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    ⟨⟨.positive, .irrelevant, .irrelevant⟩, .positive⟩,
    R0, R0⟩, .retrospective⟩

/-- Respect: positive AU reputational only. -/
def respectR : RefinedEmotionProfile :=
  ⟨"respect",
   ⟨⟨D0, .positive⟩, R0, R0, R0⟩, .retrospective⟩

/-! ### Negative Emotions -/

/-- Disappointment: negative AU/PE monetary, positive CFa (agent's
alternative would have been better). -/
def disappointmentR : RefinedEmotionProfile :=
  ⟨"disappointment",
   ⟨⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    ⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    ⟨⟨.positive, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    R0⟩, .retrospective⟩

/-- Annoyance: negative AU/PE monetary. -/
def annoyanceR : RefinedEmotionProfile :=
  ⟨"annoyance",
   ⟨⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    ⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    R0, R0⟩, .retrospective⟩

/-- Fury: negative AU monetary + reputational, negative PE. -/
def furyR : RefinedEmotionProfile :=
  ⟨"fury",
   ⟨⟨⟨.negative, .irrelevant, .irrelevant⟩, .negative⟩,
    ⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    R0, R0⟩, .retrospective⟩

/-- Devastation: negative AU/PE monetary, negative CFo. -/
def devastationR : RefinedEmotionProfile :=
  ⟨"devastation",
   ⟨⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    ⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    R0,
    ⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩⟩,
   .retrospective⟩

/-- Disgust: negative AU monetary + reputational. -/
def disgustR : RefinedEmotionProfile :=
  ⟨"disgust",
   ⟨⟨⟨.negative, .irrelevant, .irrelevant⟩, .negative⟩, R0, R0, R0⟩,
   .retrospective⟩

/-! ### Social Emotions (domain-specific) -/

/-- Envy: negative AU monetary, positive CFo on DIA (social equity).
The key domain-specific finding: envy is about *disadvantageous inequality*
specifically — the opponent got more than the agent, and the opponent
could have acted differently. -/
def envyR : RefinedEmotionProfile :=
  ⟨"envy",
   ⟨⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,  -- AU: money−
    R0,
    R0,
    ⟨⟨.irrelevant, .irrelevant, .positive⟩, .irrelevant⟩⟩, -- CFo: DIA+
   .retrospective⟩

/-- Guilt: negative AU/CFa reputational. Purely about how the agent's
choice appears to others — a reputational emotion grounded in
AIA (the agent took advantage). -/
def guiltR : RefinedEmotionProfile :=
  ⟨"guilt",
   ⟨⟨D0, .negative⟩, R0, ⟨D0, .negative⟩, R0⟩, .retrospective⟩

/-- Embarrassment: negative PE/CFa reputational across all dimensions.
Purely reputational — no base loadings. -/
def embarrassmentR : RefinedEmotionProfile :=
  ⟨"embarrassment",
   ⟨⟨D0, .negative⟩, ⟨D0, .negative⟩, ⟨D0, .negative⟩, R0⟩,
   .retrospective⟩

/-- Regret: negative AU monetary, negative CFa monetary (own alternative
was better). -/
def regretR : RefinedEmotionProfile :=
  ⟨"regret",
   ⟨⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    R0,
    ⟨⟨.negative, .irrelevant, .irrelevant⟩, .irrelevant⟩,
    R0⟩, .retrospective⟩

/-- Contempt: negative AU reputational only. -/
def contemptR : RefinedEmotionProfile :=
  ⟨"contempt",
   ⟨⟨D0, .negative⟩, R0, R0, R0⟩, .retrospective⟩

/-- Sympathy: negative PE/CFo reputational. -/
def sympathyR : RefinedEmotionProfile :=
  ⟨"sympathy",
   ⟨R0, ⟨D0, .negative⟩, R0, ⟨D0, .negative⟩⟩, .retrospective⟩

/-- Confusion: positive PE monetary + reputational. -/
def confusionR : RefinedEmotionProfile :=
  ⟨"confusion",
   ⟨R0, ⟨⟨.positive, .irrelevant, .irrelevant⟩, .positive⟩, R0, R0⟩,
   .retrospective⟩

/-- All 20 domain-refined emotion profiles. -/
def allRefinedEmotions : List RefinedEmotionProfile :=
  [joyR, surpriseR, prideR, gratitudeR, reliefR, amusementR,
   disappointmentR, annoyanceR, furyR, embarrassmentR,
   regretR, guiltR, disgustR, devastationR,
   contemptR, respectR, envyR, sympathyR, confusionR, excitementR]

-- ════════════════════════════════════════════════════════════════
-- §2. Structural Theorems
-- ════════════════════════════════════════════════════════════════

theorem twenty_refined_emotions : allRefinedEmotions.length = 20 := by native_decide

/-- All 20 refined profiles have distinct weight matrices. -/
theorem refined_profiles_distinguishable :
    (allRefinedEmotions.map (·.weights)).Pairwise (· ≠ ·) := by native_decide

/-- All 20 refined profiles collapse to the corresponding qualitative
profiles in `Core.Agent.Emotion`. This is the single source of truth:
the qualitative profiles ARE the refined profiles with domain information
collapsed via `DomainWeights.collapse`. -/
theorem all_refined_collapse :
    allRefinedEmotions.map (·.toEmotionProfile) = allEmotions := by native_decide

-- ════════════════════════════════════════════════════════════════
-- §3. Split-or-Steal Domain: Emotion ↔ Game Feature Connections
-- ════════════════════════════════════════════════════════════════

/-! These theorems connect emotion profile structure to game-theoretic
features, showing that the appraisal patterns are *explained* by
the underlying social-cognitive computations. -/

/-- Envy's domain specificity: loads on DIA, not AIA or monetary for CFo.
This distinguishes envy from disappointment (which is monetary). -/
theorem envy_is_dia_specific :
    envyR.weights.cfo.base.socialEquity = .positive ∧
    envyR.weights.cfo.base.monetary = .irrelevant ∧
    envyR.weights.cfo.base.affiliation = .irrelevant := ⟨rfl, rfl, rfl⟩

/-- Guilt's reputational character: all base dimensions irrelevant.
Guilt is about how the agent's choice *appears*, not its material effect. -/
theorem guilt_is_purely_reputational :
    guiltR.weights.au.base = D0 ∧
    guiltR.weights.cfa.base = D0 := ⟨rfl, rfl⟩

/-- Gratitude requires opponent's counterfactual: the opponent
*could have* acted differently (CFo negative on monetary). -/
theorem gratitude_requires_opponent_counterfactual :
    gratitudeR.weights.cfo.base.monetary = .negative := rfl

/-- In Split-or-Steal, cooperating when opponent defects (CD) produces
maximum disadvantageous inequality — the structural condition for envy. -/
theorem cd_produces_di_for_envy (pot : ℚ) (hpot : 0 < pot) :
    (splitOrSteal pot).di .cooperate .defect = pot :=
  splitOrSteal_cd_di pot hpot

/-- In Split-or-Steal, defecting when opponent cooperates (DC) produces
maximum advantageous inequality — the structural condition for guilt. -/
theorem dc_produces_ai_for_guilt (pot : ℚ) (hpot : 0 < pot) :
    (splitOrSteal pot).ai .defect .cooperate = pot :=
  splitOrSteal_dc_ai pot hpot

-- (§4 Evaluative Adjective Semantics moved to §8 with proper
-- adjective infrastructure grounding via Adjective.Classification)

-- ════════════════════════════════════════════════════════════════
-- §5. Lesion Model Structure
-- ════════════════════════════════════════════════════════════════

/-! @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023} validate
the model via systematic lesion experiments:

1. **SOCIALLESION**: Remove social preferences (ω_AIA = ω_DIA = 0).
   Predictions degrade for social emotions (envy, guilt, gratitude, respect).
   ccc = 0.663 vs. full model 0.854.

2. **INVERSEPLANNINGLESION**: Remove inverse planning (use prior instead of
   posterior). Predictions degrade for intention-dependent emotions
   (envy, surprise, gratitude, pride, joy). ccc = 0.762.

These lesions are formalized as restrictions on the appraisal computation. -/

/-- A lesion zeroes out specific appraisal dimensions. -/
inductive Lesion where
  | social          -- Zero all AIA and DIA base dimensions
  | inversePlanning -- Use prior instead of posterior (no action-conditioning)
  | noCounterfactual -- Zero all CFa and CFo dimensions
  deriving DecidableEq, Repr

/-- Apply a social lesion: zero out affiliation and socialEquity base signs. -/
def domainSocialLesion (d : DomainWeights) : DomainWeights :=
  { d with affiliation := .irrelevant, socialEquity := .irrelevant }

/-- Apply social lesion to a refined perspective. -/
def perspectiveSocialLesion
    (r : RefinedPerspectiveWeights) : RefinedPerspectiveWeights :=
  { r with base := domainSocialLesion r.base }

/-- Apply social lesion to full refined weights. -/
def socialLesion
    (r : RefinedAppraisalWeights) : RefinedAppraisalWeights :=
  ⟨perspectiveSocialLesion r.au, perspectiveSocialLesion r.pe,
   perspectiveSocialLesion r.cfa, perspectiveSocialLesion r.cfo⟩

/-- Under social lesion, envy's CFo becomes all-irrelevant — envy is
indistinguishable from simple negative AU (≈ annoyance). -/
theorem envy_lesioned_loses_specificity :
    (socialLesion envyR.weights).cfo = R0 := by native_decide

/-- Under social lesion, guilt retains its reputational CFa loading
(distinguishing it from contempt), but loses all domain-specific
base information — the lesion degrades but doesn't eliminate guilt's
distinctive profile. -/
theorem guilt_lesioned_retains_reputational :
    (socialLesion guiltR.weights).cfa.reputational = .negative ∧
    (socialLesion contemptR.weights).cfa.reputational = .irrelevant := by native_decide

-- ════════════════════════════════════════════════════════════════
-- §6. Social Value Profiles and Game Bridge
-- ════════════════════════════════════════════════════════════════

/-- Social value profile: the three Fehr-Schmidt preference weights
inferred from an agent's action via BToM inverse planning.

This IS the `Desire` type for the Split-or-Steal BToM instantiation:
the latent variable the observer infers in Module 1. -/
structure SocialValueProfile where
  ωMoney : ℚ
  ωAIA   : ℚ
  ωDIA   : ℚ

/-- A player with `SocialValueProfile` evaluates a game outcome using
Fehr-Schmidt social utility. This is the paper's Eq. 3.1 for a single
outcome (before expectation over opponent beliefs). -/
def SocialValueProfile.evaluate (p : SocialValueProfile)
    (g : SymmetricGame) (a₁ a₂ : Action2) : ℚ :=
  g.socialUtility a₁ a₂ p.ωMoney p.ωAIA p.ωDIA

end HoulihanEtAl2023

/-! Game→DecisionProblem bridges are defined in the `SymmetricGame`
namespace for dot notation. -/

namespace Core.GameTheory.SymmetricGame

open Core.DecisionTheory

/-- A symmetric game with beliefs about the opponent's action yields
a material-payoff decision problem.

"Worlds" = opponent's possible actions. "Actions" = my possible actions. -/
def toDecisionProblem (g : SymmetricGame)
    (opponentBelief : Action2 → ℚ) : DecisionProblem Action2 Action2 where
  utility a₂ a₁ := g.payoff a₁ a₂
  prior := opponentBelief

/-- A symmetric game with Fehr-Schmidt social utility yields a
social decision problem — the paper's Eq. 3.1 before expectation.

The preference weights (ωMoney, ωAIA, ωDIA) are the BToM `Desire` type
for this domain: the latent variables the observer infers via inverse
planning (Module 1). -/
def toSocialDecisionProblem (g : SymmetricGame)
    (opponentBelief : Action2 → ℚ) (ωMoney ωAIA ωDIA : ℚ) :
    DecisionProblem Action2 Action2 where
  utility a₂ a₁ := g.socialUtility a₁ a₂ ωMoney ωAIA ωDIA
  prior := opponentBelief

end Core.GameTheory.SymmetricGame

namespace HoulihanEtAl2023

open Core.Agent.Emotion Core.GameTheory Core.Agent.SocialUtility
     Core.DecisionTheory

/-- The social decision problem uses SocialValueProfile.evaluate as
its utility function. -/
theorem social_dp_uses_evaluate (g : SymmetricGame) (π : Action2 → ℚ)
    (p : SocialValueProfile) :
    (g.toSocialDecisionProblem π p.ωMoney p.ωAIA p.ωDIA).utility =
    fun a₂ a₁ => p.evaluate g a₁ a₂ := rfl

-- ════════════════════════════════════════════════════════════════
-- §7. Fehr-Schmidt = combined3 Bridge
-- ════════════════════════════════════════════════════════════════

/-- Fehr-Schmidt utility is a 3-component weighted sum — a special case
of `RSA.CombinedUtility.combined3` with negative social weights:

    U_FS = 1·vSelf + (−α)·DI + (−β)·AI

This connects the social cognition infrastructure (`Core.Agent.SocialUtility`)
to the RSA combined utility framework (`Pragmatics.RSA.Core`). -/
theorem fehrSchmidt_eq_combined3 (vSelf vOther α β : ℚ) :
    fehrSchmidt vSelf vOther α β =
    RSA.CombinedUtility.combined3 1 (-α) (-β)
      vSelf (disadvantageousInequality vSelf vOther)
      (advantageousInequality vSelf vOther) := by
  unfold fehrSchmidt disadvantageousInequality advantageousInequality
    RSA.CombinedUtility.combined3
  ring

-- ════════════════════════════════════════════════════════════════
-- §8. Evaluative Adjective Semantics (Grounded)
-- ════════════════════════════════════════════════════════════════

/-! @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023} show that
observers infer agents' social value weights from actions. These inferred
weights ground evaluative adjectives as intersective modifiers in the sense
of @cite{kamp-1975}:

    ⟦generous person⟧ = ⟦person⟧ ∩ {x | ω_AIA(x) > θ}

The threshold θ makes them gradable (@cite{kennedy-2007}): "more generous"
= higher inferred ω_AIA. -/

/-- "Generous" as an intersective adjective meaning:
⟦generous N⟧(p) = N(p) ∧ ω_AIA(p) > θ. -/
def generousAdj (θ : ℚ) :
    Semantics.Gradability.Classification.AdjMeaning Unit SocialValueProfile :=
  fun N _ p => decide (p.ωAIA > θ) && N () p

/-- "Fair-minded" as an intersective adjective meaning:
⟦fair-minded N⟧(p) = N(p) ∧ ω_DIA(p) > θ. -/
def fairMindedAdj (θ : ℚ) :
    Semantics.Gradability.Classification.AdjMeaning Unit SocialValueProfile :=
  fun N _ p => decide (p.ωDIA > θ) && N () p

open Semantics.Gradability.Classification in
/-- Evaluative adjectives grounded in BToM-inferred preferences are
intersective: ⟦generous N⟧ = ⟦N⟧ ∩ {x | ω_AIA(x) > θ}. -/
theorem generous_is_intersective (θ : ℚ) :
    isIntersective (generousAdj θ) :=
  ⟨fun _ p => decide (p.ωAIA > θ), fun _ _ _ => rfl⟩

open Semantics.Gradability.Classification in
/-- Fair-minded is intersective. -/
theorem fairMinded_is_intersective (θ : ℚ) :
    isIntersective (fairMindedAdj θ) :=
  ⟨fun _ p => decide (p.ωDIA > θ), fun _ _ _ => rfl⟩

/-- Generous and selfish are contradictory at any threshold:
generous requires ω_AIA > θ, selfish requires ω_AIA < θ. -/
theorem generous_selfish_exclusive (θ : ℚ) (p : SocialValueProfile)
    (hg : p.ωAIA > θ) (hs : p.ωMoney > θ ∧ p.ωAIA < θ ∧ p.ωDIA < θ) :
    False := by linarith [hg, hs.2.1]

end HoulihanEtAl2023
