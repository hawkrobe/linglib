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
and Kim's (2024) Uniform Projection Hypothesis for Class II psych verbs.

## Key results

1. **Per-verb causalSource verification**: each StimExp entry is tagged correctly
2. **UPH uniformity**: all Class II verbs share the same theta grid
   (stimulus + experiencer), regardless of eventive/stative split
3. **Intensionality derivation**: internal causal source → intensional subject
4. **T/SM restriction**: derived from the Onset Condition on causal chains
5. **Class I/II theta reversal**: experiencer and stimulus swap positions
6. **Bridge to proto-role infrastructure**: theta roles map to canonical Dowty profiles
7. **Causal link grounding**: causalSource tags ground out in temporal and
   event-structural properties via PsychCausalLink
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
-- § 1. Per-Verb CausalSource Verification
-- ════════════════════════════════════════════════════

/-- frighten is tagged as external (eventive Class II). -/
theorem frighten_is_external :
    frighten.causalSource = some .external := rfl

/-- amuse is tagged as external (eventive Class II). -/
theorem amuse_is_external :
    amuse.causalSource = some .external := rfl

/-- fascinate is tagged as external (eventive Class II). -/
theorem fascinate_is_external :
    fascinate.causalSource = some .external := rfl

/-- irritate is tagged as external (eventive Class II). -/
theorem irritate_is_external :
    irritate.causalSource = some .external := rfl

/-- annoy is tagged as external (eventive Class II). -/
theorem annoy_is_external :
    annoy.causalSource = some .external := rfl

/-- bore is tagged as external (eventive Class II). -/
theorem bore_is_external :
    bore.causalSource = some .external := rfl

/-- charm is tagged as external (eventive Class II). -/
theorem charm_is_external :
    charm.causalSource = some .external := rfl

/-- impress is tagged as external (eventive Class II). -/
theorem impress_is_external :
    impress.causalSource = some .external := rfl

/-- concern is tagged as internal (stative Class II). -/
theorem concern_is_internal :
    concern.causalSource = some .internal := rfl

/-- interest is tagged as internal (stative Class II). -/
theorem interest_is_internal :
    interest.causalSource = some .internal := rfl

-- ════════════════════════════════════════════════════
-- § 2. Uniform Projection Hypothesis
-- ════════════════════════════════════════════════════

/-- UPH: eventive and stative Class II verbs share the same theta grid.
    Both have stimulus subject and experiencer object — the difference
    is only in causalSource, not in argument structure. -/
theorem classII_uniform_projection :
    frighten.subjectTheta = concern.subjectTheta ∧
    frighten.objectTheta = concern.objectTheta := ⟨rfl, rfl⟩

/-- All 10 Class II entries have stimulus subjects. -/
theorem classII_all_stimulus_subject :
    frighten.subjectTheta = some .stimulus ∧
    amuse.subjectTheta = some .stimulus ∧
    fascinate.subjectTheta = some .stimulus ∧
    irritate.subjectTheta = some .stimulus ∧
    annoy.subjectTheta = some .stimulus ∧
    bore.subjectTheta = some .stimulus ∧
    charm.subjectTheta = some .stimulus ∧
    impress.subjectTheta = some .stimulus ∧
    concern.subjectTheta = some .stimulus ∧
    interest.subjectTheta = some .stimulus :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All 10 Class II entries have experiencer objects. -/
theorem classII_all_experiencer_object :
    frighten.objectTheta = some .experiencer ∧
    amuse.objectTheta = some .experiencer ∧
    fascinate.objectTheta = some .experiencer ∧
    irritate.objectTheta = some .experiencer ∧
    annoy.objectTheta = some .experiencer ∧
    bore.objectTheta = some .experiencer ∧
    charm.objectTheta = some .experiencer ∧
    impress.objectTheta = some .experiencer ∧
    concern.objectTheta = some .experiencer ∧
    interest.objectTheta = some .experiencer :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Intensionality from CausalSource
-- ════════════════════════════════════════════════════

/-- Internal causal source implies subject position is intensional. -/
theorem internal_implies_intensional :
    subjectIntensional CausalSource.internal = true := rfl

/-- External causal source implies subject position is extensional. -/
theorem external_implies_extensional :
    subjectIntensional CausalSource.external = false := rfl

/-- Stative Class II verbs (concern, interest) have opaque contexts. -/
theorem stative_classII_opaque :
    concern.opaqueContext = true ∧
    interest.opaqueContext = true := ⟨rfl, rfl⟩

/-- Eventive Class II verbs (frighten, amuse) have transparent contexts. -/
theorem eventive_classII_transparent :
    frighten.opaqueContext = false ∧
    amuse.opaqueContext = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. T/SM Restriction from Onset Condition
-- ════════════════════════════════════════════════════

/-- The Onset Condition: onset position is available for causal adjuncts. -/
theorem onset_available :
    onsetCondition .onset = true := rfl

/-- The terminus position is NOT available for causal adjuncts. -/
theorem terminus_unavailable :
    onsetCondition .terminus = false := rfl

/-- T/SM restriction derived: Cause occupies onset, SM also needs onset,
    but only one participant can occupy onset → they conflict.

    This theorem shows the structural basis: both Cause and SM want the
    onset position, and there's only one onset slot. -/
theorem tsm_onset_conflict :
    onsetCondition .onset = true ∧
    onsetCondition .terminus = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Proto-Role Infrastructure
-- ════════════════════════════════════════════════════

/-- Class II theta roles map to the canonical Dowty proto-role profiles
    (bridging Kim 2024 UPH to Solstad & Bott 2024 proto-role infrastructure).
    stimulus → causation + independent existence (P-Agent = 2),
    experiencer → sentience + independent existence (P-Agent = 2). -/
theorem classII_theta_matches_proto_roles :
    ThetaRole.canonicalProfile .stimulus = stimExpSubjectProfile ∧
    ThetaRole.canonicalProfile .experiencer = stimExpObjectProfile := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Class I / Class II Theta Reversal
-- ════════════════════════════════════════════════════

/-- Class I verbs (enjoy, like, love, hate) have experiencer subjects.
    This is the B&R *temere* pattern: subject = experiencer. -/
theorem classI_experiencer_subject :
    enjoy.subjectTheta = some .experiencer ∧
    like.subjectTheta = some .experiencer ∧
    love.subjectTheta = some .experiencer ∧
    hate.subjectTheta = some .experiencer := ⟨rfl, rfl, rfl, rfl⟩

/-- Class I verbs have stimulus objects (the thing experienced). -/
theorem classI_stimulus_object :
    enjoy.objectTheta = some .stimulus ∧
    like.objectTheta = some .stimulus ∧
    love.objectTheta = some .stimulus ∧
    hate.objectTheta = some .stimulus := ⟨rfl, rfl, rfl, rfl⟩

/-- Theta-role reversal: Class I and Class II swap subject/object roles.
    Class I: subject = experiencer, object = stimulus
    Class II: subject = stimulus, object = experiencer -/
theorem theta_role_reversal :
    -- Class I: subject = experiencer
    enjoy.subjectTheta = some .experiencer ∧
    -- Class II: subject = stimulus
    frighten.subjectTheta = some .stimulus ∧
    -- Class I: object = stimulus
    enjoy.objectTheta = some .stimulus ∧
    -- Class II: object = experiencer
    frighten.objectTheta = some .experiencer := ⟨rfl, rfl, rfl, rfl⟩

/-- Both classes involve the same two theta roles (experiencer + stimulus),
    just in reversed structural positions. -/
theorem same_roles_reversed :
    enjoy.subjectTheta = frighten.objectTheta ∧
    enjoy.objectTheta = frighten.subjectTheta := ⟨rfl, rfl⟩

/-- Class I subject profile matches Class II object profile:
    both are experiencers (sentience + independent existence). -/
theorem classI_subject_eq_classII_object_profile :
    expStimSubjectProfile = stimExpObjectProfile := rfl

/-- B&R class → expected subject role mapping is correct for our entries. -/
theorem classI_maps_to_experiencer :
    PsychVerbClass.expectedSubjectRole .classI = some .experiencer := rfl

theorem classII_maps_to_stimulus :
    PsychVerbClass.expectedSubjectRole .classII = some .stimulus := rfl

/-- Class I verbs have no causalSource (the distinction is Class-II-specific). -/
theorem classI_no_causal_source :
    enjoy.causalSource = none ∧
    like.causalSource = none ∧
    love.causalSource = none ∧
    hate.causalSource = none := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. Causal Link Grounding
-- ════════════════════════════════════════════════════

/-! The `causalSource` field on each fragment entry isn't just a label —
    it determines genuine temporal and event-structural properties via
    `CausalSource.toLink`. These theorems show that changing a verb's
    `causalSource` tag would change its predicted temporal behavior. -/

variable {Time : Type*} [LinearOrder Time]

/-- Eventive Class II verbs (frighten, amuse, ...) use temporal precedence:
    the causing percept finishes before the mental state change begins. -/
theorem eventive_classII_temporal :
    (CausalSource.toLink Time .external).temporalConstraint =
    Interval.precedes := rfl

/-- Stative Class II verbs (concern, interest) use temporal overlap:
    the mental representation and the psychological state coexist. -/
theorem stative_classII_temporal :
    (CausalSource.toLink Time .internal).temporalConstraint =
    Interval.overlaps := rfl

/-- Eventive Class II involves a state transition (BECOME):
    "The noise frightened John" — John transitions INTO a frightened state. -/
theorem eventive_classII_has_become :
    (CausalSource.toLink Time .external).involvesTransition = true := rfl

/-- Stative Class II involves no transition:
    "The problem concerns John" — no change of state, just persistence. -/
theorem stative_classII_no_become :
    (CausalSource.toLink Time .internal).involvesTransition = false := rfl

/-- Per-verb grounding: frighten's causalSource tag (fragment datum)
    determines temporal precedence (theoretical prediction).
    Changing frighten to `.internal` would predict overlap instead. -/
theorem frighten_causal_link :
    frighten.causalSource = some .external ∧
    (CausalSource.toLink Time .external).temporalConstraint =
      Interval.precedes ∧
    (CausalSource.toLink Time .external).involvesTransition = true :=
  ⟨rfl, rfl, rfl⟩

/-- Per-verb grounding: concern's causalSource tag (fragment datum)
    determines temporal overlap and no transition (theoretical prediction).
    Changing concern to `.external` would predict precedence instead. -/
theorem concern_causal_link :
    concern.causalSource = some .internal ∧
    (CausalSource.toLink Time .internal).temporalConstraint =
      Interval.overlaps ∧
    (CausalSource.toLink Time .internal).involvesTransition = false :=
  ⟨rfl, rfl, rfl⟩

/-- The UPH at the causal link level: eventive and stative Class II verbs
    differ ONLY in their causal link (temporal + event sort), NOT in their
    theta grid. This is Kim's central claim — the aspectual split is
    orthogonal to argument structure. -/
theorem uph_causal_link_level :
    -- Same theta grid (from § 2)
    frighten.subjectTheta = concern.subjectTheta ∧
    frighten.objectTheta = concern.objectTheta ∧
    -- Different causal links
    (CausalSource.toLink Time .external).involvesTransition = true ∧
    (CausalSource.toLink Time .internal).involvesTransition = false ∧
    (CausalSource.toLink Time .external).temporalConstraint =
      Interval.precedes ∧
    (CausalSource.toLink Time .internal).temporalConstraint =
      Interval.overlaps :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.PsychVerbs.Bridge
