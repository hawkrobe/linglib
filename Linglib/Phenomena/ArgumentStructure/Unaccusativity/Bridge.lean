import Linglib.Phenomena.ArgumentStructure.Unaccusativity.Data
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Semantics.Events.ProtoRoles
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Phenomena.AuxiliaryVerbs.Selection

/-!
# Unaccusativity Bridge

Connects empirical diagnostic data to lexical annotations, syntactic theory
(Voice, TransitivityClass, auxiliary selection), and semantic proto-role
predictions.

## Storment (2026)

Quotative inversion (QI) is an unaccusativity diagnostic: manner-of-speaking
verbs like *whisper* permit QI ("whispered Mary") because they are unaccusative,
while agentive communication verbs like *speak* block QI (*"spoke Mary") because
they are unergative.

## Dowty Divergence

Proto-role counting (Dowty 1991) predicts MoS verb subjects as proto-agents
(volitional, sentient speaker), yet QI classifies these verbs as unaccusative.
This is a known divergence: unaccusativity is a syntactic diagnostic that does
not always align with semantic proto-role predictions.
-/

namespace Phenomena.ArgumentStructure.Unaccusativity.Bridge

open Fragments.English.Predicates.Verbal
open Phenomena.ArgumentStructure.Unaccusativity.Data
open Phenomena.AuxiliaryVerbs.Selection (TransitivityClass canonicalSelection)
open Minimalism (VoiceFlavor)

-- ════════════════════════════════════════════════════
-- § 1. Per-Verb Annotation Theorems
-- ════════════════════════════════════════════════════

/-! Each theorem ties to exactly one verb's `unaccusative` field.
    Changing the annotation breaks exactly one theorem. -/

theorem whisper_unaccusative : whisper.unaccusative = true := rfl
theorem murmur_unaccusative : murmur.unaccusative = true := rfl
theorem shout_unaccusative : shout.unaccusative = true := rfl
theorem cry_unaccusative : cry.unaccusative = true := rfl
theorem scream_unaccusative : scream.unaccusative = true := rfl
theorem seem_unaccusative : seem.unaccusative = true := rfl
theorem arrive_unaccusative : arrive.unaccusative = true := rfl

theorem speak_not_unaccusative : speak.unaccusative = false := rfl
theorem talk_not_unaccusative : talk.unaccusative = false := rfl
theorem run_not_unaccusative : run.unaccusative = false := rfl
theorem sleep_not_unaccusative : sleep.unaccusative = false := rfl
theorem kick_not_unaccusative : kick.unaccusative = false := rfl

-- ════════════════════════════════════════════════════
-- § 2. Storment's Generalization (QI ↔ Unaccusativity)
-- ════════════════════════════════════════════════════

/-! Each theorem connects a diagnostic datum to the corresponding
    lexical annotation. If either changes, the theorem breaks. -/

theorem qi_whisper_agrees :
    qi_whisper.result = .passes ∧ whisper.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_murmur_agrees :
    qi_murmur.result = .passes ∧ murmur.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_shout_agrees :
    qi_shout.result = .passes ∧ shout.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_cry_agrees :
    qi_cry.result = .passes ∧ cry.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_scream_agrees :
    qi_scream.result = .passes ∧ scream.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_speak_agrees :
    qi_speak.result = .fails ∧ speak.unaccusative = false := ⟨rfl, rfl⟩

theorem qi_talk_agrees :
    qi_talk.result = .fails ∧ talk.unaccusative = false := ⟨rfl, rfl⟩

theorem there_arrive_agrees :
    there_arrive.result = .passes ∧ arrive.unaccusative = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. TransitivityClass Derivation
-- ════════════════════════════════════════════════════

/-- Derive `TransitivityClass` from `VerbCore` fields:
    unaccusative → `.unaccusative`, complement-taking → `.transitive`,
    otherwise → `.unergative`. -/
def deriveTransitivityClass (v : Core.Verbs.VerbCore) : TransitivityClass :=
  if v.unaccusative then .unaccusative
  else match v.complementType with
    | .none => .unergative
    | _ => .transitive

theorem whisper_transitivity :
    deriveTransitivityClass whisper.toVerbCore = .unaccusative := rfl

theorem murmur_transitivity :
    deriveTransitivityClass murmur.toVerbCore = .unaccusative := rfl

theorem speak_transitivity :
    deriveTransitivityClass speak.toVerbCore = .unergative := rfl

theorem talk_transitivity :
    deriveTransitivityClass talk.toVerbCore = .unergative := rfl

theorem arrive_transitivity :
    deriveTransitivityClass arrive.toVerbCore = .unaccusative := rfl

theorem kick_transitivity :
    deriveTransitivityClass kick.toVerbCore = .transitive := rfl

theorem seem_transitivity :
    deriveTransitivityClass seem.toVerbCore = .unaccusative := rfl

-- ════════════════════════════════════════════════════
-- § 4. Voice Bridge
-- ════════════════════════════════════════════════════

/-- Map unaccusativity to Voice flavor: unaccusative verbs project
    non-thematic Voice (no external argument); others project agentive Voice. -/
def unaccToVoice (unacc : Bool) : VoiceFlavor :=
  if unacc then .nonThematic else .agentive

theorem whisper_voice :
    unaccToVoice whisper.unaccusative = .nonThematic := rfl

theorem murmur_voice :
    unaccToVoice murmur.unaccusative = .nonThematic := rfl

theorem speak_voice :
    unaccToVoice speak.unaccusative = .agentive := rfl

theorem talk_voice :
    unaccToVoice talk.unaccusative = .agentive := rfl

theorem arrive_voice :
    unaccToVoice arrive.unaccusative = .nonThematic := rfl

theorem seem_voice :
    unaccToVoice seem.unaccusative = .nonThematic := rfl

-- ════════════════════════════════════════════════════
-- § 5. Auxiliary Selection Bridge
-- ════════════════════════════════════════════════════

/-! In split-auxiliary languages (Italian, French, German), unaccusative
    verbs select *be* and unergative verbs select *have*.
    We verify this via `canonicalSelection ∘ deriveTransitivityClass`. -/

theorem whisper_canonical_aux :
    canonicalSelection (deriveTransitivityClass whisper.toVerbCore) = .be := rfl

theorem murmur_canonical_aux :
    canonicalSelection (deriveTransitivityClass murmur.toVerbCore) = .be := rfl

theorem speak_canonical_aux :
    canonicalSelection (deriveTransitivityClass speak.toVerbCore) = .have := rfl

theorem talk_canonical_aux :
    canonicalSelection (deriveTransitivityClass talk.toVerbCore) = .have := rfl

-- ════════════════════════════════════════════════════
-- § 6. Levin Class + Theta Role Bridge
-- ════════════════════════════════════════════════════

theorem whisper_levin_class :
    whisper.levinClass = some .mannerOfSpeaking := rfl

theorem murmur_levin_class :
    murmur.levinClass = some .mannerOfSpeaking := rfl

theorem speak_levin_class :
    speak.levinClass = some .mannerOfSpeaking := rfl

theorem whisper_theme_subject :
    whisper.subjectTheta = some .theme := rfl

theorem speak_agent_subject :
    speak.subjectTheta = some .agent := rfl

-- ════════════════════════════════════════════════════
-- § 7. Dowty Divergence
-- ════════════════════════════════════════════════════

/-! MoS verb subjects are volitional, sentient speakers — Dowty's proto-role
    counting yields P-Agent > P-Patient, predicting unergative.
    But QI says these verbs are unaccusative. This is a documented
    divergence between semantic proto-role predictions and syntactic
    diagnostics. -/

open Semantics.Events.ProtoRoles

/-- MoS subject entailment profile: volitional (P-Agent), sentient (P-Agent),
    exists independently (P-Agent), but no P-Patient entailments. -/
def mosSubjectProfile : EntailmentProfile where
  volition := true
  sentience := true
  causation := false
  movement := false
  independentExistence := true
  changeOfState := false
  incrementalTheme := false
  causallyAffected := false
  stationary := false
  dependentExistence := false

theorem mos_predicts_unergative :
    predictsUnergative mosSubjectProfile = true := by native_decide

theorem mos_not_unaccusative_by_counting :
    predictsUnaccusative mosSubjectProfile = false := by native_decide

/-- Divergence: Dowty predicts MoS subjects are unergative,
    but QI (Storment 2026) classifies them as unaccusative. -/
theorem whisper_dowty_diverges :
    predictsUnergative mosSubjectProfile = true ∧
    whisper.unaccusative = true := ⟨by native_decide, rfl⟩

end Phenomena.ArgumentStructure.Unaccusativity.Bridge
