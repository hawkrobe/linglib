import Linglib.Semantics.Modality.ModalTypes
import Linglib.Studies.RotterLiu2025Concord
import Linglib.Fragments.English.Auxiliaries

/-!
# Modal Concord: Commitment and Social Meaning — [liu-rotter-2025]
[liu-rotter-2025] [rotter-liu-2025] [zeijlstra-2007]

Experimental data and analysis from "Non-redundant modal concord: Evidence
from speaker commitment and social meaning" [liu-rotter-2025].

Modal concord (MC) is **not semantically vacuous**: necessity MC (*must
certainly*) strengthens speaker commitment, while possibility MC (*may
possibly*) weakens it. This FORCE × NUMBER interaction is not predicted by
syntactic agreement, semantic identity, or the register approach. MC also
carries social meaning mirroring the commitment direction: necessity MC
signals competence, possibility MC signals warmth.

* **Experiment 1** (n=160): 2 (FORCE: necessity/possibility) × 2 (NUMBER:
  single/concord) between-subjects. DV: speaker commitment (7-point Likert).
  Stimuli: *must/should/have to VP* vs *must certainly/should definitely/
  have to necessarily VP*; *may/might/could VP* vs *may possibly/might
  perhaps/could potentially VP*.
* **Experiment 2** (n=160): same design. DVs: 7 social meaning dimensions.
* **Section A**: each aux-adverb stimulus pair shares modal force when
  projected to `ModalItem` — the structural precondition for concord.
* **Section B**: modal force predicts the commitment direction.
* **Section C**: connection to [rotter-liu-2025] — both studies find that
  MC preserves modal force (single reading, not double).
* **Section D**: modal concord as an instance of the general concord
  pattern; possibility MC patterns with negative concord (solidarity),
  necessity MC contrasts (competence).
-/

namespace LiuRotter2025

open RotterLiu2025Concord (LikertRating)
open English.Auxiliaries
open Semantics.Modality (ModalForce ModalItem ConcordType ConcordType.fromModalForce)
open Features.Register (SocialIndex)

/-! ## Experimental design -/

/-- NUMBER factor: single modal vs modal concord (doubled). -/
inductive Doubling where
  | single   -- bare modal auxiliary
  | concord  -- modal auxiliary + modal adverb
  deriving DecidableEq, Repr

/-- Experimental condition: FORCE × NUMBER. -/
structure Condition where
  force : ModalForce
  doubling : Doubling
  deriving DecidableEq, Repr

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
  | ⟨.necessity, .single⟩      => ⟨449/100, 131/100⟩  -- M=4.49, SD=1.31
  | ⟨.necessity, .concord⟩     => ⟨499/100, 121/100⟩  -- M=4.99, SD=1.21
  | ⟨.weakNecessity, .single⟩  => ⟨449/100, 131/100⟩  -- not tested separately
  | ⟨.weakNecessity, .concord⟩ => ⟨499/100, 121/100⟩  -- not tested separately
  | ⟨.possibility, .single⟩    => ⟨384/100, 138/100⟩  -- M=3.84, SD=1.38
  | ⟨.possibility, .concord⟩   => ⟨337/100, 149/100⟩  -- M=3.37, SD=1.49

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
    agreement approach, which treats one modal as
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
  deriving DecidableEq, Repr

/-- Competence/warmth classification.
    Necessity MC increases competence dimensions, decreases warmth.
    Possibility MC does the reverse. -/
inductive DimensionClass where
  | competence  -- Status, ability, expertise
  | warmth      -- Sociability, friendliness
  deriving DecidableEq, Repr

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

/-! ## Section A: Semantic overlap via ModalItem

Each aux-adverb pair from the stimuli shares concord-compatible force when
projected to `ModalItem`. Both necessity and weak necessity map to the same
concord class (necessity-type), so *should* (weak necessity) concords with
*definitely* (necessity). -/

-- Necessity pairs

/-- *must* + *certainly* share necessity-type concord force. -/
theorem must_certainly_share :
    must.toModalItem.sharesConcordForce certainly.toModalItem = true := by native_decide

/-- *should* + *definitely* share necessity-type concord force.
    *should* is weak necessity, *definitely* is strong necessity — both are
    necessity-type for concord purposes. -/
theorem should_definitely_share :
    should.toModalItem.sharesConcordForce definitely.toModalItem = true := by native_decide

/-- *have to* + *necessarily* share necessity-type concord force. -/
theorem haveTo_necessarily_share :
    haveTo.toModalItem.sharesConcordForce necessarily.toModalItem = true := by native_decide

-- Possibility pairs

/-- *may* + *possibly* share possibility force. -/
theorem may_possibly_share :
    may.toModalItem.sharesConcordForce possibly.toModalItem = true := by native_decide

/-- *might* + *perhaps* share possibility force. -/
theorem might_perhaps_share :
    might.toModalItem.sharesConcordForce perhaps.toModalItem = true := by native_decide

/-- *could* + *potentially* share possibility force. -/
theorem could_potentially_share :
    could.toModalItem.sharesConcordForce potentially.toModalItem = true := by native_decide

/-- **All six stimulus pairs share concord-compatible force**. -/
theorem all_pairs_share_force :
    must.toModalItem.sharesConcordForce certainly.toModalItem = true ∧
    should.toModalItem.sharesConcordForce definitely.toModalItem = true ∧
    haveTo.toModalItem.sharesConcordForce necessarily.toModalItem = true ∧
    may.toModalItem.sharesConcordForce possibly.toModalItem = true ∧
    might.toModalItem.sharesConcordForce perhaps.toModalItem = true ∧
    could.toModalItem.sharesConcordForce potentially.toModalItem = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- Register variants

/-- *must* (formal) and *certainly* (formal) are NOT register variants —
    they share the same register level. Concord here is not register mixing
    but force agreement between syntactically distinct categories. -/
theorem must_certainly_same_register :
    ¬ must.toModalItem.areRegisterVariants certainly.toModalItem := by decide

/-- *may* (neutral) and *possibly* (neutral) are also not register variants. -/
theorem may_possibly_same_register :
    ¬ may.toModalItem.areRegisterVariants possibly.toModalItem := by decide

/-! ## Section B: Force determines commitment direction

The paper's central finding — that necessity MC strengthens while
possibility MC weakens — can be encoded as a function from modal
force to predicted direction. -/

/-- Predicted commitment effect of concord given modal force.
    `true` = strengthening (MC > SM), `false` = weakening (MC < SM).
    Both necessity and weak necessity concord strengthen. -/
def concordStrengthens : ModalForce → Bool
  | .necessity     => true
  | .weakNecessity => true
  | .possibility   => false

/-- The data matches the force-based prediction for necessity. -/
theorem necessity_matches_prediction :
    concordStrengthens .necessity = true ∧
    (commitmentRating necMC).mean > (commitmentRating necSM).mean :=
  ⟨rfl, necessity_mc_strengthens⟩

/-- The data matches the force-based prediction for possibility. -/
theorem possibility_matches_prediction :
    concordStrengthens .possibility = false ∧
    (commitmentRating posMC).mean < (commitmentRating posSM).mean :=
  ⟨rfl, possibility_mc_weakens⟩

/-! ## Section C: Connection to [rotter-liu-2025]

Both studies agree that MC preserves modal force (single reading). -/

/-- Both studies: necessity MC yields single necessity. -/
theorem both_studies_single_necessity :
    (RotterLiu2025Concord.meaningRating .must).mean -
    (RotterLiu2025Concord.meaningRating .mustHaveTo).mean < 1/2 ∧
    (commitmentRating necMC).mean > 4 := by
  constructor <;> native_decide

/-- Register and commitment are complementary diagnostics. -/
theorem complementary_diagnostics :
    (RotterLiu2025Concord.formalityRating .haveTo).mean <
    (RotterLiu2025Concord.formalityRating .mustHaveTo).mean ∧
    (commitmentRating necMC).mean ≠ (commitmentRating necSM).mean := by
  constructor <;> native_decide

/-! ## Section D: Cross-phenomenon concord

Modal concord is an instance of the general `ConcordType` from
`Core/ModalLogic.lean`. The social indexation of MC depends on force:
necessity MC → competence, possibility MC → solidarity. This connects
to negative concord, which also indexes solidarity.

The `socialIndex` mapping is defined here (not in Core) because it
encodes an empirical claim from [rotter-liu-2025] §4. -/

/-- Social indexation of each concord type.
    NC and MC possibility both index solidarity;
    MC necessity indexes competence ([rotter-liu-2025] §4). -/
def socialIndex : ConcordType → SocialIndex
  | .negation         => .solidarity
  | .modalNecessity   => .competence
  | .modalPossibility => .solidarity

/-- Necessity MC is a competence-indexing concord phenomenon. -/
theorem necessity_mc_competence :
    socialIndex (ConcordType.fromModalForce .necessity) = .competence := rfl

/-- Possibility MC is a solidarity-indexing concord phenomenon. -/
theorem possibility_mc_solidarity :
    socialIndex (ConcordType.fromModalForce .possibility) = .solidarity := rfl

/-- **Possibility MC patterns with negative concord**: Both are
    solidarity-indexing concord phenomena. This is the cross-phenomenon
    generalization from [rotter-liu-2025] §4. -/
theorem possibility_mc_like_nc :
    socialIndex (ConcordType.fromModalForce .possibility) =
    socialIndex .negation := rfl

/-- **Necessity MC contrasts with negative concord**. -/
theorem necessity_mc_unlike_nc :
    socialIndex (ConcordType.fromModalForce .necessity) ≠
    socialIndex .negation := by decide

/-- **Force determines social meaning**: Necessity and possibility
    modal concord receive opposite social indexation. -/
theorem force_determines_social_index :
    socialIndex .modalNecessity ≠
    socialIndex .modalPossibility := by decide

/-- **Social meaning mirrors commitment direction**: The concord type's
    social index aligns with the commitment data — competence-indexing
    necessity MC strengthens commitment, solidarity-indexing possibility
    MC weakens it. -/
theorem social_index_aligns_with_commitment :
    -- Necessity: competence index + strengthening
    socialIndex (ConcordType.fromModalForce .necessity) = .competence ∧
    (commitmentRating necMC).mean > (commitmentRating necSM).mean ∧
    -- Possibility: solidarity index + weakening
    socialIndex (ConcordType.fromModalForce .possibility) = .solidarity ∧
    (commitmentRating posMC).mean < (commitmentRating posSM).mean := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;> native_decide

end LiuRotter2025
