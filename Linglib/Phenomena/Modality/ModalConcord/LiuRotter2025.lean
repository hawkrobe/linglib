import Linglib.Phenomena.Modality.ModalConcord.Data
import Linglib.Core.ModalLogic

/-!
# Modal Concord: Commitment and Social Meaning — Liu & Rotter (2025)

Empirical data from "Non-redundant modal concord: Evidence from speaker
commitment and social meaning."

## Key finding

Modal concord (MC) is **not semantically vacuous**: necessity MC (*must
certainly*) strengthens speaker commitment, while possibility MC (*may
possibly*) weakens it. This FORCE × NUMBER interaction is not predicted by
syntactic agreement (Zeijlstra 2007), semantic identity (Geurts & Huitink
2006), or the register approach (Dieuleveut et al. 2025).

MC also carries social meaning: necessity MC signals competence (higher SES,
education, formality, confidence), while possibility MC signals warmth (higher
friendliness, warmth). The social meaning mirrors the commitment direction.

## Experiments

* **Experiment 1** (n=160): 2 (FORCE: necessity/possibility) × 2 (NUMBER:
  single/concord) between-subjects. DV: speaker commitment (7-point Likert).
* **Experiment 2** (n=160): Same design. DVs: 7 social meaning dimensions.

## Stimuli

* Necessity SM: *must/should/have to VP*
* Necessity MC: *must certainly/should definitely/have to necessarily VP*
* Possibility SM: *may/might/could VP*
* Possibility MC: *may possibly/might perhaps/could potentially VP*

## Reference

Liu, M. & Rotter, C. (2025). Non-redundant modal concord: Evidence from
speaker commitment and social meaning.
-/

namespace Phenomena.Modality.ModalConcord.LiuRotter2025

open Phenomena.Modality.ModalConcord (LikertRating)
open Core.ModalLogic (ModalForce)

/-! ## Experimental design -/

/-- NUMBER factor: single modal vs modal concord (doubled). -/
inductive Doubling where
  | single   -- bare modal auxiliary
  | concord  -- modal auxiliary + modal adverb
  deriving DecidableEq, BEq, Repr

/-- Experimental condition: FORCE × NUMBER. -/
structure Condition where
  force : ModalForce
  doubling : Doubling
  deriving DecidableEq, BEq, Repr

def necSM : Condition := ⟨.necessity, .single⟩
def necMC : Condition := ⟨.necessity, .concord⟩
def posSM : Condition := ⟨.possibility, .single⟩
def posMC : Condition := ⟨.possibility, .concord⟩

/-! ## Experiment 1: Speaker commitment

160 participants (40 per condition) rated speaker commitment on a
7-point Likert scale ("How certain is the speaker that...").

FORCE × NUMBER interaction: β = 0.56, SE = 0.17, t = 3.31, p = .001. -/

/-- Speaker commitment ratings (7-point Likert, 1=not at all certain,
    7=completely certain). -/
def commitmentRating : Condition → LikertRating
  | ⟨.necessity, .single⟩   => ⟨449/100, 131/100⟩  -- M=4.49, SD=1.31
  | ⟨.necessity, .concord⟩  => ⟨499/100, 121/100⟩  -- M=4.99, SD=1.21
  | ⟨.possibility, .single⟩  => ⟨384/100, 138/100⟩  -- M=3.84, SD=1.38
  | ⟨.possibility, .concord⟩ => ⟨337/100, 149/100⟩  -- M=3.37, SD=1.49

/-! ### Key Experiment 1 empirical generalizations -/

/-- **Necessity MC strengthens commitment**: *must certainly* is rated
    higher in speaker commitment than bare *must* (p = .03). -/
theorem necessity_mc_strengthens :
    (commitmentRating necMC).mean > (commitmentRating necSM).mean := by
  native_decide

/-- **Possibility MC weakens commitment**: *may possibly* is rated
    lower in speaker commitment than bare *may* (p = .04). -/
theorem possibility_mc_weakens :
    (commitmentRating posMC).mean < (commitmentRating posSM).mean := by
  native_decide

/-- **FORCE × NUMBER interaction**: The direction of the concord effect
    reverses with force. Necessity MC strengthens, possibility MC weakens.
    This is the paper's central finding (β = 0.56, p = .001). -/
theorem force_number_interaction :
    (commitmentRating necMC).mean > (commitmentRating necSM).mean ∧
    (commitmentRating posMC).mean < (commitmentRating posSM).mean := by
  constructor <;> native_decide

/-- **MC is semantically non-vacuous**: Both necessity and possibility
    MC differ from their single-modal counterparts. The syntactic
    agreement approach (Zeijlstra 2007), which treats one modal as
    semantically vacuous, incorrectly predicts MC = SM. -/
theorem mc_not_vacuous :
    (commitmentRating necMC).mean ≠ (commitmentRating necSM).mean ∧
    (commitmentRating posMC).mean ≠ (commitmentRating posSM).mean := by
  constructor <;> native_decide

/-- **Necessity above possibility**: Both SM and MC show higher
    commitment for necessity than possibility. -/
theorem necessity_above_possibility :
    (commitmentRating necSM).mean > (commitmentRating posSM).mean ∧
    (commitmentRating necMC).mean > (commitmentRating posMC).mean := by
  constructor <;> native_decide

/-- **No main effect of NUMBER**: Grand means of SM and MC are close
    (within 0.1 points). The concord effect appears only as an
    interaction with FORCE (β = −0.03, p = .86). -/
theorem no_main_effect_of_number :
    let smMean := ((commitmentRating necSM).mean + (commitmentRating posSM).mean) / 2
    let mcMean := ((commitmentRating necMC).mean + (commitmentRating posMC).mean) / 2
    smMean - mcMean > -1/10 ∧ smMean - mcMean < 1/10 := by
  constructor <;> native_decide

/-! ## Experiment 2: Social meaning

160 participants (40 per condition) rated speakers on 7 social
dimensions (7-point Likert scale) after hearing sentences. -/

/-- Social meaning dimensions (Experiment 2). -/
inductive SocialDimension where
  | ses          -- Socio-economic status
  | education    -- Education level
  | formality    -- Formality
  | confidence   -- Confidence
  | friendliness -- Friendliness
  | warmth       -- Warmth
  | coolness     -- Coolness
  deriving DecidableEq, BEq, Repr

/-- Competence/warmth classification (Fiske, Cuddy, Glick & Xu 2002).
    Necessity MC increases competence dimensions, decreases warmth.
    Possibility MC does the reverse. -/
inductive DimensionClass where
  | competence  -- Status, ability, expertise
  | warmth      -- Sociability, friendliness
  deriving DecidableEq, BEq, Repr

/-- Classify each social dimension as competence or warmth. -/
def SocialDimension.dimClass : SocialDimension → DimensionClass
  | .ses          => .competence
  | .education    => .competence
  | .formality    => .competence
  | .confidence   => .competence
  | .friendliness => .warmth
  | .warmth       => .warmth
  | .coolness     => .competence  -- patterns with competence in the data

def SocialDimension.all : List SocialDimension :=
  [.ses, .education, .formality, .confidence, .friendliness, .warmth, .coolness]

/-- FORCE × NUMBER interaction on a social dimension.
    Positive β: necessity MC scores higher (competence pattern).
    Negative β: necessity MC scores lower (warmth pattern). -/
structure InteractionEffect where
  beta : ℚ       -- Regression coefficient
  se : ℚ         -- Standard error
  significant : Bool  -- p < .05
  deriving Repr, BEq

/-- FORCE × NUMBER interaction results per social dimension.
    All 7 dimensions show significant interactions (p < .05). -/
def socialInteraction : SocialDimension → InteractionEffect
  | .ses          => ⟨41/100,  16/100, true⟩   -- β=0.41, p=.01
  | .education    => ⟨36/100,  15/100, true⟩   -- β=0.36, p=.02
  | .formality    => ⟨51/100,  16/100, true⟩   -- β=0.51, p=.002
  | .confidence   => ⟨43/100,  16/100, true⟩   -- β=0.43, p=.002
  | .friendliness => ⟨-41/100, 16/100, true⟩   -- β=−0.41, p=.002
  | .warmth       => ⟨-30/100, 15/100, true⟩   -- β=−0.30, p=.02
  | .coolness     => ⟨33/100,  16/100, true⟩   -- β=0.33, p=.02

/-! ### Key Experiment 2 empirical generalizations -/

/-- **All social dimensions show significant interaction**. -/
theorem all_interactions_significant :
    (socialInteraction .ses).significant = true ∧
    (socialInteraction .education).significant = true ∧
    (socialInteraction .formality).significant = true ∧
    (socialInteraction .confidence).significant = true ∧
    (socialInteraction .friendliness).significant = true ∧
    (socialInteraction .warmth).significant = true ∧
    (socialInteraction .coolness).significant = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Competence dimensions have positive interaction**: Necessity MC
    increases perceived competence (SES, education, formality,
    confidence, coolness). -/
theorem competence_positive :
    (socialInteraction .ses).beta > 0 ∧
    (socialInteraction .education).beta > 0 ∧
    (socialInteraction .formality).beta > 0 ∧
    (socialInteraction .confidence).beta > 0 ∧
    (socialInteraction .coolness).beta > 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Warmth dimensions have negative interaction**: Necessity MC
    decreases perceived warmth (friendliness, warmth). -/
theorem warmth_negative :
    (socialInteraction .friendliness).beta < 0 ∧
    (socialInteraction .warmth).beta < 0 := by
  constructor <;> native_decide

/-- **Social meaning mirrors commitment**: Competence dimensions
    have positive β (matching necessity strengthening), warmth
    dimensions have negative β (matching possibility weakening).
    This parallel suggests the social meaning *drives* the
    commitment effect. -/
theorem social_mirrors_commitment :
    -- Competence: positive β
    (socialInteraction .ses).beta > 0 ∧
    (socialInteraction .education).beta > 0 ∧
    (socialInteraction .formality).beta > 0 ∧
    (socialInteraction .confidence).beta > 0 ∧
    -- Warmth: negative β
    (socialInteraction .friendliness).beta < 0 ∧
    (socialInteraction .warmth).beta < 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Formality shows the strongest interaction** among all
    social dimensions (β = 0.51), consistent with the register
    approach to modal concord. -/
theorem formality_largest_competence :
    (socialInteraction .formality).beta > (socialInteraction .ses).beta ∧
    (socialInteraction .formality).beta > (socialInteraction .education).beta ∧
    (socialInteraction .formality).beta > (socialInteraction .confidence).beta ∧
    (socialInteraction .formality).beta > (socialInteraction .coolness).beta := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end Phenomena.Modality.ModalConcord.LiuRotter2025
