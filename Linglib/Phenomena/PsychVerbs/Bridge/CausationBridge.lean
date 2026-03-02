import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Causation.PsychCausalLink
import Linglib.Theories.Semantics.Events.ProtoRoles
import Linglib.Phenomena.PsychVerbs.Data
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge.ProtoRoleBridge

/-!
# Psych Verb Causation Bridge (B&R 1988, Kim 2024 UPH)

@cite{belletti-rizzi-1988} @cite{kim-2024}

Bridge theorems connecting fragment entries to the B&R (1988) classification
and @cite{kim-2024}'s Uniform Projection Hypothesis for Class II psych verbs.

## Architecture

The fragment entries in `Verbal.lean` set four fields independently:
- `causalSource` (external vs internal)
- `subjectTheta` (stimulus vs experiencer)
- `objectTheta` (experiencer vs stimulus)
- `opaqueContext` (true vs false)

@cite{kim-2024}'s theory predicts these fields must covary:
- All Class II verbs share the same theta grid (UPH)
- `opaqueContext` is determined by `subjectIntensional` applied to `causalSource`
- `causalSource` determines temporal and event-structural behavior

These predictions are captured by the `classII_consistent` predicate (§ 1),
verified per-verb (§ 2), and then used to DERIVE consequences (§ 3–7).

## Key results

1. **Consistency**: each Class II entry satisfies `classII_consistent`,
   connecting 4 independently-set fields through Kim's theory
2. **UPH derivation**: theta-grid uniformity FOLLOWS from consistency
3. **Opacity derivation**: `opaqueContext` FOLLOWS from `causalSource`
4. **Temporal prediction**: temporal behavior FOLLOWS from `causalSource`
5. **T/SM restriction**: derived from the Onset Condition on causal chains
6. **Class I/II theta reversal**: derived from the consistency predicates
7. **Proto-role bridge**: theta roles map to canonical Dowty profiles
-/

namespace Phenomena.PsychVerbs.Bridge

open Semantics.Causation.PsychCausation
open Semantics.Causation.PsychCausalLink
open Core.Time (Interval)
open Fragments.English.Predicates.Verbal
open Phenomena.PsychVerbs.Data
open Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge
  (stimExpSubjectProfile stimExpObjectProfile expStimSubjectProfile)
open Semantics.Events.ProtoRoles

-- ════════════════════════════════════════════════════
-- § 1. Consistency Predicates
-- ════════════════════════════════════════════════════

/-- A Class II (object-experiencer) psych verb entry is internally consistent
    when its four independently-set fields agree with @cite{kim-2024}'s predictions:

    (a) It has a causal source (external or internal)
    (b) UPH theta grid: stimulus subject, experiencer object
    (c) Opacity agrees with `subjectIntensional` applied to the causal source

    The existential over `CausalSource` ties the causal source to the opacity
    prediction: changing the causal source field MUST change the opacity field
    to maintain consistency. -/
def classII_consistent (v : VerbEntry) : Prop :=
  ∃ cs : CausalSource,
    v.causalSource = some cs ∧
    v.subjectTheta = some .stimulus ∧
    v.objectTheta = some .experiencer ∧
    v.opaqueContext = subjectIntensional cs

/-- A Class I (experiencer-subject) psych verb entry is consistent with
    @cite{belletti-rizzi-1988}'s *temere* pattern: experiencer subject, stimulus object,
    no causal source (the internal/external distinction is Class-II-specific). -/
def classI_consistent (v : VerbEntry) : Prop :=
  v.causalSource = none ∧
  v.subjectTheta = some .experiencer ∧
  v.objectTheta = some .stimulus

-- ════════════════════════════════════════════════════
-- § 2. Per-Verb Consistency Verification
-- ════════════════════════════════════════════════════

/-! Each theorem below connects 4 independently-set fragment fields through
    Kim's theory. If ANY field on the fragment entry changes (causalSource,
    subjectTheta, objectTheta, or opaqueContext), the corresponding theorem
    breaks — ensuring the fields stay in theoretical agreement. -/

-- Eventive Class II (external causal source, transparent subjects)

theorem frighten_consistent : classII_consistent frighten :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem amuse_consistent : classII_consistent amuse :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem fascinate_consistent : classII_consistent fascinate :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem irritate_consistent : classII_consistent irritate :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem annoy_consistent : classII_consistent annoy :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem bore_consistent : classII_consistent bore :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem charm_consistent : classII_consistent charm :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem impress_consistent : classII_consistent impress :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem surprise_consistent : classII_consistent surprise :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem scare_consistent : classII_consistent scare :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem delight_consistent : classII_consistent delight :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem embarrass_consistent : classII_consistent embarrass :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem upset_psych_consistent : classII_consistent upset_psych :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem disgust_consistent : classII_consistent disgust :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem shock_consistent : classII_consistent shock :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem confuse_consistent : classII_consistent confuse :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem disappoint_consistent : classII_consistent disappoint :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

theorem worry_eventive_consistent : classII_consistent worry_eventive :=
  ⟨.external, rfl, rfl, rfl, rfl⟩

-- Stative Class II (internal causal source, opaque subjects)

theorem concern_consistent : classII_consistent concern :=
  ⟨.internal, rfl, rfl, rfl, rfl⟩

theorem interest_consistent : classII_consistent interest :=
  ⟨.internal, rfl, rfl, rfl, rfl⟩

theorem worry_stative_consistent : classII_consistent worry_stative :=
  ⟨.internal, rfl, rfl, rfl, rfl⟩

theorem please_psych_consistent : classII_consistent please_psych :=
  ⟨.internal, rfl, rfl, rfl, rfl⟩

theorem trouble_consistent : classII_consistent trouble :=
  ⟨.internal, rfl, rfl, rfl, rfl⟩

theorem puzzle_consistent : classII_consistent puzzle :=
  ⟨.internal, rfl, rfl, rfl, rfl⟩

-- Class I (experiencer-subject, no causal source)

theorem enjoy_consistent : classI_consistent enjoy :=
  ⟨rfl, rfl, rfl⟩

theorem like_consistent : classI_consistent like :=
  ⟨rfl, rfl, rfl⟩

theorem love_consistent : classI_consistent love :=
  ⟨rfl, rfl, rfl⟩

theorem hate_consistent : classI_consistent hate :=
  ⟨rfl, rfl, rfl⟩

theorem fear_np_consistent : classI_consistent fear_np :=
  ⟨rfl, rfl, rfl⟩

theorem dread_np_consistent : classI_consistent dread_np :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Derivations from Consistency
-- ════════════════════════════════════════════════════

/-- **UPH (derived)**: any two consistent Class II verbs share the same
    theta grid, regardless of their causal source. This is Kim's central
    claim — the eventive/stative split is orthogonal to argument structure.

    The proof extracts the theta-grid equalities from consistency and
    chains them. No enumeration of verbs needed. -/
theorem uph_from_consistency (v₁ v₂ : VerbEntry)
    (h₁ : classII_consistent v₁) (h₂ : classII_consistent v₂) :
    v₁.subjectTheta = v₂.subjectTheta ∧
    v₁.objectTheta = v₂.objectTheta := by
  obtain ⟨_, _, hs₁, ho₁, _⟩ := h₁
  obtain ⟨_, _, hs₂, ho₂, _⟩ := h₂
  exact ⟨hs₁.trans hs₂.symm, ho₁.trans ho₂.symm⟩

/-- **Opacity derivation**: any consistent Class II verb with internal
    causal source has an opaque subject position.

    This connects two independently-set fields (causalSource, opaqueContext)
    through Kim's theory: the opacity ISN'T stipulated — it FOLLOWS from
    the causal source being internal (maintenance relation). -/
theorem internal_implies_opaque (v : VerbEntry)
    (h : classII_consistent v) (hs : v.causalSource = some .internal) :
    v.opaqueContext = true := by
  obtain ⟨cs, hcs, _, _, ho⟩ := h
  cases hcs ▸ hs; exact ho

/-- **Transparency derivation**: any consistent Class II verb with external
    causal source has a transparent subject position. -/
theorem external_implies_transparent (v : VerbEntry)
    (h : classII_consistent v) (hs : v.causalSource = some .external) :
    v.opaqueContext = false := by
  obtain ⟨cs, hcs, _, _, ho⟩ := h
  cases hcs ▸ hs; exact ho

/-- **Theta reversal (derived)**: consistent Class I and Class II verbs
    swap subject and object theta roles. -/
theorem theta_reversal_from_consistency (vI vII : VerbEntry)
    (hI : classI_consistent vI) (hII : classII_consistent vII) :
    vI.subjectTheta = vII.objectTheta ∧
    vI.objectTheta = vII.subjectTheta := by
  obtain ⟨_, hsI, hoI⟩ := hI
  obtain ⟨_, _, hsII, hoII, _⟩ := hII
  exact ⟨hsI.trans hoII.symm, hoI.trans hsII.symm⟩

/-- **UPH within a single verb**: worry's eventive and stative readings
    share the same theta grid but differ in causal source.
    This is Kim's strongest test case — same lexical item, two readings. -/
theorem worry_uniform_projection :
    worry_eventive.subjectTheta = worry_stative.subjectTheta ∧
    worry_eventive.objectTheta = worry_stative.objectTheta ∧
    worry_eventive.causalSource ≠ worry_stative.causalSource :=
  ⟨rfl, rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 4. Temporal Prediction from CausalSource
-- ════════════════════════════════════════════════════

variable {Time : Type*} [LinearOrder Time]

/-- **Temporal derivation (external)**: any verb with external causal source
    predicts temporal precedence and a state transition (BECOME).
    The temporal behavior FOLLOWS from the causal source, not from
    per-verb stipulation. -/
theorem external_predicts_precedence :
    (CausalSource.toLink Time .external).temporalConstraint =
      Interval.precedes ∧
    (CausalSource.toLink Time .external).involvesTransition = true :=
  ⟨rfl, rfl⟩

/-- **Temporal derivation (internal)**: any verb with internal causal source
    predicts temporal overlap and no state transition.
    Cause and effect coexist (maintenance relation). -/
theorem internal_predicts_overlap :
    (CausalSource.toLink Time .internal).temporalConstraint =
      Interval.overlaps ∧
    (CausalSource.toLink Time .internal).involvesTransition = false :=
  ⟨rfl, rfl⟩

/-- **Per-verb temporal grounding**: frighten's fragment datum (external source)
    determines specific temporal predictions. Changing the datum to `.internal`
    would change the predictions. -/
theorem frighten_temporal :
    frighten.causalSource = some .external ∧
    (CausalSource.toLink Time .external).temporalConstraint =
      Interval.precedes ∧
    (CausalSource.toLink Time .external).involvesTransition = true :=
  ⟨rfl, rfl, rfl⟩

/-- **Per-verb temporal grounding**: concern's internal source determines
    temporal overlap and no transition. -/
theorem concern_temporal :
    concern.causalSource = some .internal ∧
    (CausalSource.toLink Time .internal).temporalConstraint =
      Interval.overlaps ∧
    (CausalSource.toLink Time .internal).involvesTransition = false :=
  ⟨rfl, rfl, rfl⟩

/-- **UPH at the causal link level**: eventive and stative Class II verbs
    share the same theta grid (from § 3) but differ in temporal and
    event-structural predictions. This is Kim's full claim: the aspectual
    split is orthogonal to argument structure. -/
theorem uph_causal_link_level :
    -- Same theta grid
    frighten.subjectTheta = concern.subjectTheta ∧
    frighten.objectTheta = concern.objectTheta ∧
    -- Different temporal behavior
    (CausalSource.toLink Time .external).temporalConstraint =
      Interval.precedes ∧
    (CausalSource.toLink Time .internal).temporalConstraint =
      Interval.overlaps ∧
    -- Different event structure
    (CausalSource.toLink Time .external).involvesTransition = true ∧
    (CausalSource.toLink Time .internal).involvesTransition = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. T/SM Restriction from Onset Condition
-- ════════════════════════════════════════════════════

/-- T/SM restriction derived: Cause occupies onset, SM also needs onset,
    but only one participant can occupy onset → they conflict.

    This theorem shows the structural basis: both Cause and SM want the
    onset position, and there's only one onset slot. -/
theorem tsm_onset_conflict :
    onsetCondition .onset = true ∧
    onsetCondition .terminus = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Proto-Role Infrastructure
-- ════════════════════════════════════════════════════

/-- Class II theta roles map to the canonical Dowty proto-role profiles
    (bridging Kim 2024 UPH to Solstad & Bott 2024 proto-role infrastructure).
    stimulus → causation + independent existence (P-Agent = 2),
    experiencer → sentience + independent existence (P-Agent = 2). -/
theorem classII_theta_matches_proto_roles :
    ThetaRole.canonicalProfile .stimulus = stimExpSubjectProfile ∧
    ThetaRole.canonicalProfile .experiencer = stimExpObjectProfile := ⟨rfl, rfl⟩

/-- Class I subject profile matches Class II object profile:
    both are experiencers (sentience + independent existence). -/
theorem classI_subject_eq_classII_object_profile :
    expStimSubjectProfile = stimExpObjectProfile := rfl

/-- B&R class → expected subject role mapping is correct for our entries. -/
theorem classI_maps_to_experiencer :
    PsychVerbClass.expectedSubjectRole .classI = some .experiencer := rfl

theorem classII_maps_to_stimulus :
    PsychVerbClass.expectedSubjectRole .classII = some .stimulus := rfl

-- ════════════════════════════════════════════════════
-- § 7. Intensionality Type-Level Properties
-- ════════════════════════════════════════════════════

/-- Internal causal source implies subject position is intensional (type level). -/
theorem internal_implies_intensional :
    subjectIntensional CausalSource.internal = true := rfl

/-- External causal source implies subject position is extensional (type level). -/
theorem external_implies_extensional :
    subjectIntensional CausalSource.external = false := rfl

-- ════════════════════════════════════════════════════
-- § 8. Derived Stimulus Type (Pesetsky 1995)
-- ════════════════════════════════════════════════════

/-! For Class II verbs, stimulus subtype is DERIVED from causal source
    via `CausalSource.toStimulusType`. No new lexical field needed —
    the existing `causalSource` field determines T vs SM.

    These theorems verify that each verb's derived stimulus type
    predicts the correct PP frame and Cause-cooccurrence behavior. -/

open Semantics.Causation.PsychCausation (StimulusType CausalSource.toStimulusType)

/-- Derive a verb's stimulus type from its causal source. -/
def derivedStimulusType (v : VerbEntry) : Option StimulusType :=
  v.causalSource.map CausalSource.toStimulusType

-- Eventive Class II → Target (T) stimulus

theorem frighten_is_target : derivedStimulusType frighten = some .target := rfl
theorem amuse_is_target : derivedStimulusType amuse = some .target := rfl
theorem fascinate_is_target : derivedStimulusType fascinate = some .target := rfl
theorem irritate_is_target : derivedStimulusType irritate = some .target := rfl
theorem annoy_is_target : derivedStimulusType annoy = some .target := rfl
theorem bore_is_target : derivedStimulusType bore = some .target := rfl
theorem charm_is_target : derivedStimulusType charm = some .target := rfl
theorem impress_is_target : derivedStimulusType impress = some .target := rfl
theorem surprise_is_target : derivedStimulusType surprise = some .target := rfl
theorem scare_is_target : derivedStimulusType scare = some .target := rfl
theorem delight_is_target : derivedStimulusType delight = some .target := rfl
theorem embarrass_is_target : derivedStimulusType embarrass = some .target := rfl
theorem upset_psych_is_target : derivedStimulusType upset_psych = some .target := rfl
theorem disgust_is_target : derivedStimulusType disgust = some .target := rfl
theorem shock_is_target : derivedStimulusType shock = some .target := rfl
theorem confuse_is_target : derivedStimulusType confuse = some .target := rfl
theorem disappoint_is_target : derivedStimulusType disappoint = some .target := rfl
theorem worry_eventive_is_target : derivedStimulusType worry_eventive = some .target := rfl

-- Stative Class II → Subject Matter (SM) stimulus

theorem concern_is_sm : derivedStimulusType concern = some .subjectMatter := rfl
theorem interest_is_sm : derivedStimulusType interest = some .subjectMatter := rfl
theorem worry_stative_is_sm : derivedStimulusType worry_stative = some .subjectMatter := rfl
theorem please_psych_is_sm : derivedStimulusType please_psych = some .subjectMatter := rfl
theorem trouble_is_sm : derivedStimulusType trouble = some .subjectMatter := rfl
theorem puzzle_is_sm : derivedStimulusType puzzle = some .subjectMatter := rfl

-- Class I → no derived stimulus type (T/SM is per-use, not lexical)

theorem enjoy_no_stimulus_type : derivedStimulusType enjoy = none := rfl
theorem like_no_stimulus_type : derivedStimulusType like = none := rfl
theorem love_no_stimulus_type : derivedStimulusType love = none := rfl
theorem hate_no_stimulus_type : derivedStimulusType hate = none := rfl
theorem fear_np_no_stimulus_type : derivedStimulusType fear_np = none := rfl
theorem dread_np_no_stimulus_type : derivedStimulusType dread_np = none := rfl

-- Derived properties of stimulus type

/-- Any verb with external causal source derives a Target stimulus
    that doesn't conflict with overt Cause. -/
theorem external_derives_target (v : VerbEntry)
    (hs : v.causalSource = some .external) :
    ∃ st : StimulusType, derivedStimulusType v = some st ∧
      st = .target ∧ st.conflictsWithCause = false := by
  simp only [derivedStimulusType, hs]
  exact ⟨.target, rfl, rfl, rfl⟩

/-- Any verb with internal causal source derives an SM stimulus
    that conflicts with overt Cause (Onset Condition). -/
theorem internal_derives_sm (v : VerbEntry)
    (hs : v.causalSource = some .internal) :
    ∃ st : StimulusType, derivedStimulusType v = some st ∧
      st = .subjectMatter ∧ st.conflictsWithCause = true := by
  simp only [derivedStimulusType, hs]
  exact ⟨.subjectMatter, rfl, rfl, rfl⟩

end Phenomena.PsychVerbs.Bridge
