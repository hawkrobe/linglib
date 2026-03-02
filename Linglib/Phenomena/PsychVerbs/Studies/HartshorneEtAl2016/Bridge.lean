import Linglib.Phenomena.PsychVerbs.Studies.HartshorneEtAl2016.Data
import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Causation.PsychCausalLink

/-!
# Bridge: @cite{hartshorne-etal-2016} ↔ @cite{kim-2024} Causal Source

@cite{hartshorne-etal-2016}
@cite{kim-2024}

Connects Hartshorne et al.'s (2016) empirical semantic type distinction
(habitual attitude vs caused episode) to @cite{kim-2024}'s causal source
distinction (internal vs external), showing that:

1. SemanticType ↔ CausalSource is an isomorphism
2. Empirical properties (duration, causation, transition) are derivable
   from CausalSource assignment
3. Temporal predictions (precedence vs overlap) follow from PsychCausalLink

## The bridge

| Hartshorne et al. | CausalSource | PsychCausalLink | Properties |
|-------------------|-------------|-----------------|------------|
| Habitual attitude | internal | maintenance | long duration, no CAUSE, no BECOME, overlap |
| Caused episode | external | eventive | short duration, CAUSE, BECOME, precedence |
-/

namespace Phenomena.PsychVerbs.Studies.HartshorneEtAl2016.Bridge

open Phenomena.PsychVerbs.Studies.HartshorneEtAl2016 (SemanticType SemanticTypeProfile
  attitudeProfile episodeProfile)
open Semantics.Causation.PsychCausation (CausalSource)
open Semantics.Causation.PsychCausalLink (PsychCausalLink eventiveLink maintenanceLink
  CausalSource.toLink)

-- ════════════════════════════════════════════════════
-- § 1. SemanticType ↔ CausalSource Isomorphism
-- ════════════════════════════════════════════════════

/-- Map Hartshorne et al.'s semantic type to Kim's CausalSource.
    Habitual attitudes = internal (mental representation maintains state);
    caused episodes = external (percept triggers state change). -/
def semanticTypeToCausalSource : SemanticType → CausalSource
  | .habitualAttitude => .internal
  | .causedEpisode => .external

/-- Map Kim's CausalSource back to semantic type. -/
def causalSourceToSemanticType : CausalSource → SemanticType
  | .internal => .habitualAttitude
  | .external => .causedEpisode

/-- Roundtrip: SemanticType → CausalSource → SemanticType. -/
theorem semanticType_source_roundtrip (t : SemanticType) :
    causalSourceToSemanticType (semanticTypeToCausalSource t) = t := by
  cases t <;> rfl

/-- Roundtrip: CausalSource → SemanticType → CausalSource. -/
theorem source_semanticType_roundtrip (s : CausalSource) :
    semanticTypeToCausalSource (causalSourceToSemanticType s) = s := by
  cases s <;> rfl

-- ════════════════════════════════════════════════════
-- § 2. Deriving Empirical Properties from CausalSource
-- ════════════════════════════════════════════════════

/-- Derive the expected empirical profile from CausalSource.

    - External: short duration (episode), causal stimulus, involves BECOME
    - Internal: long duration (attitude), no causal stimulus, no BECOME -/
def causalSourceToProfile : CausalSource → SemanticTypeProfile
  | .external => episodeProfile
  | .internal => attitudeProfile

/-- Duration: internal source → longer duration (enduring attitude). -/
theorem internal_longer_duration :
    (causalSourceToProfile .internal).longerDuration = true := rfl

/-- Duration: external source → shorter duration (transient episode). -/
theorem external_shorter_duration :
    (causalSourceToProfile .external).longerDuration = false := rfl

/-- Causation: external source → stimulus is causal. -/
theorem external_stimulus_causal :
    (causalSourceToProfile .external).stimulusCausal = true := rfl

/-- Causation: internal source → stimulus not causal. -/
theorem internal_stimulus_not_causal :
    (causalSourceToProfile .internal).stimulusCausal = false := rfl

/-- Transition: external source → involves BECOME. -/
theorem external_involves_become :
    (causalSourceToProfile .external).involvesBecome = true := rfl

/-- Transition: internal source → no BECOME. -/
theorem internal_no_become :
    (causalSourceToProfile .internal).involvesBecome = false := rfl

/-- The two causal sources predict opposite empirical profiles. -/
theorem sources_differ_on_all :
    causalSourceToProfile .external ≠ causalSourceToProfile .internal := by
  decide

-- ════════════════════════════════════════════════════
-- § 3. Consistency with SemanticType.expectedProfile
-- ════════════════════════════════════════════════════

/-- The profile derived via CausalSource agrees with the profile derived
    directly from SemanticType. This is non-trivial: we defined the two
    mappings independently and they agree. -/
theorem profile_agreement (t : SemanticType) :
    causalSourceToProfile (semanticTypeToCausalSource t) =
      t.expectedProfile := by
  cases t <;> rfl

-- ════════════════════════════════════════════════════
-- § 4. Temporal Predictions via PsychCausalLink
-- ════════════════════════════════════════════════════

/-- External source predicts transition (BECOME). -/
theorem external_predicts_transition (Time : Type*) [LinearOrder Time] :
    (CausalSource.toLink Time .external).involvesTransition = true := rfl

/-- Internal source predicts no transition. -/
theorem internal_predicts_no_transition (Time : Type*) [LinearOrder Time] :
    (CausalSource.toLink Time .internal).involvesTransition = false := rfl

/-- Consistency: PsychCausalLink's transition prediction agrees with the
    empirical profile derived from SemanticType.
    Both are derived independently — the agreement is a genuine check. -/
theorem transition_prediction_consistent (t : SemanticType) (Time : Type*) [LinearOrder Time] :
    (CausalSource.toLink Time (semanticTypeToCausalSource t)).involvesTransition =
      (causalSourceToProfile (semanticTypeToCausalSource t)).involvesBecome := by
  cases t <;> rfl

end Phenomena.PsychVerbs.Studies.HartshorneEtAl2016.Bridge
