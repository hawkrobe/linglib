import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Causation.PsychCausalLink
import Linglib.Core.Agent.BToM
import Linglib.Core.StructuralEquationModel
import Linglib.Theories.Semantics.Intensional.Situations.Elbourne
import Linglib.Phenomena.PsychVerbs.Studies.HartshorneEtAl2016.Bridge

/-!
# Psych Verb Denotation via Cognitive Situation Models

@cite{kim-2024} @cite{baker-saxe-tenenbaum-2017}
@cite{nadathur-lauer-2020} @cite{elbourne-2005}
@cite{hartshorne-odonnell-tenenbaum-2016}

Nobody has given psych verbs a compositional denotation grounded in a cognitive
situation model. The ingredients exist across Pesetsky (1995, causal heads),
Landau (2010, locative experiencers), Bott & Solstad (2014/2022, propositional
slots), Hacquard & Lidz (2022, ToM bootstrapping), and Hartshorne et al. (2016,
attitude/episode distinction) — but nobody has unified them through an explicit
cognitive architecture that serves as the model-theoretic backbone.

## Core idea

A psych verb denotes a relation evaluated over a **cognitive situation** — a
model of the experiencer's mind. The `CausalPathway` (perceptual vs
representational) determines which layer of the cognitive architecture the
stimulus connects through:

- **Perceptual** (frighten): stimulus evaluated via perception (extensional)
- **Representational** (concern): stimulus evaluated via belief (intensional)

From this single denotation, properties are **derived**, not stipulated:
- Opacity: perceptual = extensional; representational = can be intensional
- Temporal: perceptual = cause precedes effect; representational = overlap
- UPH: both pathways share the same type signature

## Connections to existing formalizations

| Section | Connects to | In Linglib |
|---------|-------------|------------|
| §8 BToM bridge | Baker et al. 2017 | `Core.BToM.BToMModel` |
| §9 CausalFrame | Nadathur & Lauer 2020 | `Core.StructuralEquationModel` |
| §10 Situations | Elbourne 2005/2013 | `Situations.Elbourne.SitVarStatus` |
| §11 Hartshorne | Hartshorne et al. 2016 | `HartshorneEtAl2016.Bridge` |
-/

namespace PsychVerbs

open Semantics.Causation.PsychCausation (CausalSource)
open Semantics.Causation.PsychCausalLink (PsychCausalLink eventiveLink maintenanceLink)

-- ════════════════════════════════════════════════════════════════
-- § 1. ExperiencerState — Cognitive Situation Model
-- ════════════════════════════════════════════════════════════════

/-- The evaluation domain for psych verb denotations.

    Models the experiencer's cognitive state decomposed into BToM layers.
    This is the **cognitive situation** over which psych verbs are evaluated.

    | Field | BToM layer |
    |-------|------------|
    | `perceives` | `perceptModel : World → Percept → F` |
    | `represents` | `beliefModel : Percept → Belief → F` |
    | `perceptCauses` | World → Percept → MentalState chain |
    | `beliefMaintains` | Belief → MentalState maintenance | -/
structure ExperiencerState (Stimulus MState : Type*) where
  /-- Perceptual layer: world-driven, extensional. -/
  perceives : Stimulus → Bool
  /-- Belief layer: mind-internal, potentially intensional. -/
  represents : Stimulus → Bool
  /-- Mental state layer: what psychological states are active. -/
  inMentalState : MState → Bool
  /-- Perceptual causation: perceiving s triggers mental state m. -/
  perceptCauses : Stimulus → MState → Bool
  /-- Representational maintenance: representing s maintains mental state m.
      Kim's (2024) maintenance relation at the belief layer. -/
  beliefMaintains : Stimulus → MState → Bool

-- ════════════════════════════════════════════════════════════════
-- § 2. CausalPathway
-- ════════════════════════════════════════════════════════════════

/-- The causal pathway through which a stimulus affects the experiencer.

    - **Perceptual**: World → Percept → MentalState (external causation)
    - **Representational**: Belief → MentalState (maintenance causation) -/
inductive CausalPathway where
  | perceptual       -- World → Percept → MentalState (external causation)
  | representational -- Belief → MentalState (maintenance causation)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 3. The Denotation
-- ════════════════════════════════════════════════════════════════

/-- The unified psych verb denotation.

    Both pathways take `(stimulus, experiencer-state)` in the same argument
    positions — the UPH is a **type-level guarantee**, not a theorem.

    `psychVerbSem pathway root stimulus es` = true iff:
    - The experiencer is in mental state `root`, AND
    - The stimulus is connected to `root` through the given `pathway`. -/
def psychVerbSem {Stimulus MState : Type*}
    (pathway : CausalPathway) (root : MState)
    (stimulus : Stimulus) (es : ExperiencerState Stimulus MState) : Bool :=
  es.inMentalState root &&
  match pathway with
  | .perceptual => es.perceives stimulus && es.perceptCauses stimulus root
  | .representational => es.represents stimulus && es.beliefMaintains stimulus root

-- ════════════════════════════════════════════════════════════════
-- § 4. Coreference and Extensionality
-- ════════════════════════════════════════════════════════════════

/-- Perceptual extensionality: co-referential stimuli have the same perceptual
    status and causal effects. -/
def ExperiencerState.perceptuallyExtensional
    {Stimulus MState : Type*}
    (es : ExperiencerState Stimulus MState)
    (coref : Stimulus → Stimulus → Bool) : Prop :=
  ∀ a b, coref a b = true →
    es.perceives a = es.perceives b ∧
    ∀ m, es.perceptCauses a m = es.perceptCauses b m

/-- Representational intensionality: co-referential stimuli CAN have
    different belief status. -/
def ExperiencerState.representationallyIntensional
    {Stimulus MState : Type*}
    (es : ExperiencerState Stimulus MState)
    (coref : Stimulus → Stimulus → Bool) : Prop :=
  ∃ a b, coref a b = true ∧ es.represents a ≠ es.represents b

-- ════════════════════════════════════════════════════════════════
-- § 5. Opacity Derivation
-- ════════════════════════════════════════════════════════════════

/-- The perceptual pathway is invariant under coreference. -/
theorem perceptual_extensional {Stimulus MState : Type*}
    {es : ExperiencerState Stimulus MState}
    {coref : Stimulus → Stimulus → Bool}
    {a b : Stimulus} {root : MState}
    (hExt : es.perceptuallyExtensional coref)
    (hCoref : coref a b = true) :
    psychVerbSem .perceptual root a es = psychVerbSem .perceptual root b es := by
  unfold psychVerbSem
  obtain ⟨hPerc, hCause⟩ := hExt a b hCoref
  rw [hPerc, hCause root]

section CiceroTully
/-- Stimuli for the Cicero/Tully opacity test. -/
inductive CiceroStimulus where
  | cicero | tully
  deriving DecidableEq, BEq, Repr

/-- Mental states for the opacity test. -/
inductive ConcernState where
  | concerned
  deriving DecidableEq, BEq, Repr

/-- Cognitive state: both Cicero and Tully are perceived (same person),
    but only Cicero is represented (the agent knows "Cicero" not "Tully"). -/
def ciceroTullyState : ExperiencerState CiceroStimulus ConcernState :=
  { perceives := fun _ => true
    represents := fun | .cicero => true | .tully => false
    inMentalState := fun _ => true
    perceptCauses := fun _ _ => true
    beliefMaintains := fun | .cicero, _ => true | .tully, _ => false }

-- Perceptual: extensional — both frighten (same person in the world)
theorem cicero_frightens :
    psychVerbSem .perceptual .concerned .cicero ciceroTullyState = true := rfl
theorem tully_frightens :
    psychVerbSem .perceptual .concerned .tully ciceroTullyState = true := rfl

-- Representational: intensional — Cicero concerns but Tully does not
theorem cicero_concerns :
    psychVerbSem .representational .concerned .cicero ciceroTullyState = true := rfl
theorem tully_not_concerns :
    psychVerbSem .representational .concerned .tully ciceroTullyState = false := rfl

/-- The representational pathway CAN be intensional. -/
theorem representational_can_be_intensional :
    ∃ (s₁ s₂ : CiceroStimulus) (m : ConcernState),
      psychVerbSem .representational m s₁ ciceroTullyState ≠
      psychVerbSem .representational m s₂ ciceroTullyState :=
  ⟨.cicero, .tully, .concerned, by decide⟩

end CiceroTully

-- ════════════════════════════════════════════════════════════════
-- § 6. CausalSource ↔ CausalPathway Isomorphism
-- ════════════════════════════════════════════════════════════════

def CausalPathway.toCausalSource : CausalPathway → CausalSource
  | .perceptual => .external
  | .representational => .internal

def causalSourceToPathway : CausalSource → CausalPathway
  | .external => .perceptual
  | .internal => .representational

theorem pathway_source_roundtrip (p : CausalPathway) :
    causalSourceToPathway p.toCausalSource = p := by cases p <;> rfl

theorem source_pathway_roundtrip (s : CausalSource) :
    (causalSourceToPathway s).toCausalSource = s := by cases s <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 7. Temporal Connection via PsychCausalLink
-- ════════════════════════════════════════════════════════════════

def CausalPathway.toLink (Time : Type*) [LinearOrder Time] :
    CausalPathway → PsychCausalLink Time
  | .perceptual => eventiveLink Time
  | .representational => maintenanceLink Time

theorem perceptual_has_transition (Time : Type*) [LinearOrder Time] :
    (CausalPathway.toLink Time .perceptual).involvesTransition = true := rfl

theorem representational_no_transition (Time : Type*) [LinearOrder Time] :
    (CausalPathway.toLink Time .representational).involvesTransition = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § 8. BToM Bridge (Baker et al. 2017)
-- ════════════════════════════════════════════════════════════════

section BToM
open Core.BToM (BToMModel)

/-- Construct an `ExperiencerState` from a `BToMModel` at a specific world. -/
def ExperiencerState.fromBToM
    {F : Type*} [CommSemiring F] [DecidableEq F]
    {Action Percept Belief Desire Shared Medium World : Type*}
    {Stimulus MState : Type*}
    (_model : BToMModel F Action Percept Belief Desire Shared Medium World)
    (w : World)
    (stimToPercept : Stimulus → Percept)
    (stimToBelief : Stimulus → Belief)
    (mentalStateActive : World → MState → Bool)
    (perceptTriggers : Percept → MState → Bool)
    (beliefMaintains' : Belief → MState → Bool)
    (threshold : F)
    : ExperiencerState Stimulus MState :=
  { perceives := fun s => _model.perceptModel w (stimToPercept s) != threshold
    represents := fun s =>
      _model.beliefModel (stimToPercept s) (stimToBelief s) != threshold
    inMentalState := mentalStateActive w
    perceptCauses := fun s m => perceptTriggers (stimToPercept s) m
    beliefMaintains := fun s m => beliefMaintains' (stimToBelief s) m }

/-- Same percept → same perceptual status. -/
theorem fromBToM_perceives_extensional
    {F : Type*} [CommSemiring F] [DecidableEq F]
    {Action Percept Belief Desire Shared Medium World : Type*}
    {Stimulus MState : Type*}
    (model : BToMModel F Action Percept Belief Desire Shared Medium World)
    (w : World) (stimToPercept : Stimulus → Percept)
    (stimToBelief : Stimulus → Belief)
    (mentalStateActive : World → MState → Bool)
    (perceptTriggers : Percept → MState → Bool)
    (beliefMaintains' : Belief → MState → Bool)
    (threshold : F) (a b : Stimulus)
    (hSamePercept : stimToPercept a = stimToPercept b) :
    (ExperiencerState.fromBToM model w stimToPercept stimToBelief
      mentalStateActive perceptTriggers beliefMaintains' threshold).perceives a =
    (ExperiencerState.fromBToM model w stimToPercept stimToBelief
      mentalStateActive perceptTriggers beliefMaintains' threshold).perceives b := by
  simp only [ExperiencerState.fromBToM, hSamePercept]

/-- Same percept → same denotation through the perceptual pathway. -/
theorem fromBToM_perceptual_extensional
    {F : Type*} [CommSemiring F] [DecidableEq F]
    {Action Percept Belief Desire Shared Medium World : Type*}
    {Stimulus MState : Type*}
    (model : BToMModel F Action Percept Belief Desire Shared Medium World)
    (w : World) (stimToPercept : Stimulus → Percept)
    (stimToBelief : Stimulus → Belief)
    (mentalStateActive : World → MState → Bool)
    (perceptTriggers : Percept → MState → Bool)
    (beliefMaintains' : Belief → MState → Bool)
    (threshold : F) (a b : Stimulus) (root : MState)
    (hSamePercept : stimToPercept a = stimToPercept b) :
    psychVerbSem .perceptual root a
      (ExperiencerState.fromBToM model w stimToPercept stimToBelief
        mentalStateActive perceptTriggers beliefMaintains' threshold) =
    psychVerbSem .perceptual root b
      (ExperiencerState.fromBToM model w stimToPercept stimToBelief
        mentalStateActive perceptTriggers beliefMaintains' threshold) := by
  simp only [psychVerbSem, ExperiencerState.fromBToM, hSamePercept]

end BToM

-- ════════════════════════════════════════════════════════════════
-- § 9. CausalFrame Integration (Nadathur & Lauer 2020)
-- ════════════════════════════════════════════════════════════════

section CausalFrame
open Core.StructuralEquationModel

private def stimPresent : Variable := mkVar "stimPresent"
private def perceivesStim : Variable := mkVar "perceivesStim"
private def representsStim : Variable := mkVar "representsStim"
private def inMentalStateVar : Variable := mkVar "inMentalState"

/-- Perceptual pathway: causal chain stimPresent → perceivesStim → inMentalState. -/
def perceptualDynamics : CausalDynamics :=
  CausalDynamics.causalChain stimPresent perceivesStim inMentalStateVar

/-- Representational pathway: single law representsStim → inMentalState. -/
def representationalDynamics : CausalDynamics :=
  CausalDynamics.ofList [CausalLaw.simple representsStim inMentalStateVar]

/-- Perceptual: stimulus is causally sufficient for mental state. -/
theorem perceptual_stimulus_sufficient :
    causallySufficient perceptualDynamics Situation.empty
      stimPresent inMentalStateVar = true := by native_decide

/-- Representational: representation is causally sufficient. -/
theorem representational_sufficient :
    causallySufficient representationalDynamics Situation.empty
      representsStim inMentalStateVar = true := by native_decide

/-- Representational: representation is causally necessary. -/
theorem representational_necessary :
    causallyNecessary representationalDynamics Situation.empty
      representsStim inMentalStateVar = true := by native_decide

/-- Intervening on perception blocks the mental state change. -/
theorem perception_intervention_blocks :
    let ⟨dynAfter, bgAfter⟩ :=
      intervene perceptualDynamics (Situation.empty.extend stimPresent true) perceivesStim false
    normalDevelopment dynAfter bgAfter 10 |>.get inMentalStateVar = none := by
  native_decide

end CausalFrame

-- ════════════════════════════════════════════════════════════════
-- § 10. Situation Semantics Bridge (Elbourne 2005/2013)
-- ════════════════════════════════════════════════════════════════

section Situations
open Semantics.Intensional.Situations.Elbourne (SitVarStatus)

/-- Cognitive refinement: `es₁` is a cognitive part of `es₂` if every
    positive fact in `es₁` is also in `es₂`. -/
def cognitiveLE {Stimulus MState : Type*}
    [DecidableEq Stimulus] [DecidableEq MState]
    (stimuli : List Stimulus) (states : List MState)
    (es₁ es₂ : ExperiencerState Stimulus MState) : Prop :=
  (∀ s ∈ stimuli, es₁.perceives s = true → es₂.perceives s = true) ∧
  (∀ s ∈ stimuli, es₁.represents s = true → es₂.represents s = true) ∧
  (∀ m ∈ states, es₁.inMentalState m = true → es₂.inMentalState m = true) ∧
  (∀ s ∈ stimuli, ∀ m ∈ states,
    es₁.perceptCauses s m = true → es₂.perceptCauses s m = true) ∧
  (∀ s ∈ stimuli, ∀ m ∈ states,
    es₁.beliefMaintains s m = true → es₂.beliefMaintains s m = true)

theorem cognitiveLE_refl {Stimulus MState : Type*}
    [DecidableEq Stimulus] [DecidableEq MState]
    (stimuli : List Stimulus) (states : List MState)
    (es : ExperiencerState Stimulus MState) :
    cognitiveLE stimuli states es es :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
   fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

theorem cognitiveLE_trans {Stimulus MState : Type*}
    [DecidableEq Stimulus] [DecidableEq MState]
    (stimuli : List Stimulus) (states : List MState)
    (es₁ es₂ es₃ : ExperiencerState Stimulus MState)
    (h₁₂ : cognitiveLE stimuli states es₁ es₂)
    (h₂₃ : cognitiveLE stimuli states es₂ es₃) :
    cognitiveLE stimuli states es₁ es₃ :=
  ⟨fun s hs h => h₂₃.1 s hs (h₁₂.1 s hs h),
   fun s hs h => h₂₃.2.1 s hs (h₁₂.2.1 s hs h),
   fun m hm h => h₂₃.2.2.1 m hm (h₁₂.2.2.1 m hm h),
   fun s hs m hm h => h₂₃.2.2.2.1 s hs m hm (h₁₂.2.2.2.1 s hs m hm h),
   fun s hs m hm h => h₂₃.2.2.2.2 s hs m hm (h₁₂.2.2.2.2 s hs m hm h)⟩

/-- `psychVerbSem` is persistent under cognitive refinement. -/
theorem psychVerbSem_monotone {Stimulus MState : Type*}
    [DecidableEq Stimulus] [DecidableEq MState]
    (stimuli : List Stimulus) (states : List MState)
    (pathway : CausalPathway) (root : MState)
    (stimulus : Stimulus)
    (es₁ es₂ : ExperiencerState Stimulus MState)
    (hLE : cognitiveLE stimuli states es₁ es₂)
    (hStim : stimulus ∈ stimuli) (hRoot : root ∈ states)
    (hTrue : psychVerbSem pathway root stimulus es₁ = true) :
    psychVerbSem pathway root stimulus es₂ = true := by
  unfold psychVerbSem at hTrue ⊢
  simp only [Bool.and_eq_true] at hTrue ⊢
  obtain ⟨hMS, hPath⟩ := hTrue
  have hMS₂ := hLE.2.2.1 root hRoot hMS
  refine ⟨hMS₂, ?_⟩
  match pathway with
  | .perceptual =>
    simp only [Bool.and_eq_true] at hPath ⊢
    exact ⟨hLE.1 stimulus hStim hPath.1, hLE.2.2.2.1 stimulus hStim root hRoot hPath.2⟩
  | .representational =>
    simp only [Bool.and_eq_true] at hPath ⊢
    exact ⟨hLE.2.1 stimulus hStim hPath.1, hLE.2.2.2.2 stimulus hStim root hRoot hPath.2⟩

/-- Map CausalPathway to Elbourne's SitVarStatus.
    Perceptual → free (de re); representational → bound (de dicto). -/
def pathwayToSitVarStatus : CausalPathway → SitVarStatus
  | .perceptual => .free
  | .representational => .bound

theorem perceptual_is_de_re :
    pathwayToSitVarStatus .perceptual = .free := rfl

theorem representational_is_de_dicto :
    pathwayToSitVarStatus .representational = .bound := rfl

end Situations

-- ════════════════════════════════════════════════════════════════
-- § 11. Hartshorne et al. (2016) Connection
-- ════════════════════════════════════════════════════════════════

section Hartshorne
open Phenomena.PsychVerbs.Studies.HartshorneEtAl2016 (SemanticType)
open Phenomena.PsychVerbs.Studies.HartshorneEtAl2016.Bridge (semanticTypeToCausalSource)

/-- Map Hartshorne et al.'s semantic type to CausalPathway. -/
def semanticTypeToPathway : SemanticType → CausalPathway
  | .habitualAttitude => .representational
  | .causedEpisode => .perceptual

/-- Map CausalPathway back to semantic type. -/
def pathwayToSemanticType : CausalPathway → SemanticType
  | .representational => .habitualAttitude
  | .perceptual => .causedEpisode

theorem semanticType_pathway_roundtrip (t : SemanticType) :
    pathwayToSemanticType (semanticTypeToPathway t) = t := by cases t <;> rfl

theorem pathway_semanticType_roundtrip (p : CausalPathway) :
    semanticTypeToPathway (pathwayToSemanticType p) = p := by cases p <;> rfl

/-- Three-way agreement: SemanticType → CausalSource → CausalPathway
    agrees with SemanticType → CausalPathway (direct). -/
theorem three_way_agreement (t : SemanticType) :
    causalSourceToPathway (semanticTypeToCausalSource t) =
      semanticTypeToPathway t := by cases t <;> rfl

end Hartshorne

end PsychVerbs
