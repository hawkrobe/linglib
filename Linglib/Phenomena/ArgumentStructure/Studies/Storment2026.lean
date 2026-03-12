import Linglib.Phenomena.ArgumentStructure.Unaccusativity.Data
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Movement.Smuggling
import Linglib.Phenomena.AuxiliaryVerbs.Selection
import Linglib.Phenomena.FillerGap.Islands.Data

/-!
# Unaccusativity Bridge @cite{storment-2026}

Connects empirical diagnostic data to lexical annotations, syntactic theory
(Voice, TransitivityClass, auxiliary selection, smuggling), and semantic
proto-role predictions.

## @cite{storment-2026}: QI via Smuggling

Quotative inversion (QI) is an unaccusativity diagnostic: manner-of-speaking
verbs like *whisper* permit QI ("whispered Mary") because they are unaccusative,
while agentive communication verbs like *speak* block QI (*"spoke Mary") because
they are unergative.

The **syntactic mechanism** is smuggling: VP moves to
Spec-VoiceP, making the theme subject accessible to T⁰ for Case licensing.
This is possible iff Voice is not a phase head (non-thematic Voice),
which correlates with unaccusativity.

## QI ∥ LI (Unified Smuggling)

@cite{storment-2026} argues QI and locative inversion share the same mechanism: @cite{collins-2005} @cite{dowty-1991} @cite{lu-degen-2025}
smuggling of VP to Spec-VoiceP. Both are blocked by the transitivity constraint
(§5) and both require non-phase Voice. They differ in input (quote vs locative PP).

## Dowty Divergence

Proto-role counting predicts MoS verb subjects as proto-agents
(volitional, sentient speaker), yet QI classifies these verbs as unaccusative.
This is a known divergence: unaccusativity is a syntactic diagnostic that does
not always align with semantic proto-role predictions.
-/

namespace Phenomena.ArgumentStructure.Unaccusativity.Bridge

open Fragments.English.Predicates.Verbal
open Phenomena.ArgumentStructure.Unaccusativity.Data
open Phenomena.AuxiliaryVerbs.Selection (TransitivityClass canonicalSelection)
open Minimalism (VoiceFlavor VoiceHead licensesQI)
-- ConstraintType, constraintSource are at root namespace (no namespace in Islands/Data.lean)

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
theorem mumble_unaccusative : mumble.unaccusative = true := rfl
theorem mutter_unaccusative : mutter.unaccusative = true := rfl
theorem shriek_unaccusative : shriek.unaccusative = true := rfl
theorem yell_unaccusative : yell.unaccusative = true := rfl
theorem groan_unaccusative : groan.unaccusative = true := rfl
theorem grumble_unaccusative : grumble.unaccusative = true := rfl
theorem hiss_unaccusative : hiss.unaccusative = true := rfl
theorem sigh_unaccusative : sigh.unaccusative = true := rfl
theorem whimper_unaccusative : whimper.unaccusative = true := rfl
theorem snap_unaccusative : snap.unaccusative = true := rfl

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

theorem qi_mumble_agrees :
    qi_mumble.result = .passes ∧ mumble.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_mutter_agrees :
    qi_mutter.result = .passes ∧ mutter.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_shriek_agrees :
    qi_shriek.result = .passes ∧ shriek.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_yell_agrees :
    qi_yell.result = .passes ∧ yell.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_groan_agrees :
    qi_groan.result = .passes ∧ groan.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_grumble_agrees :
    qi_grumble.result = .passes ∧ grumble.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_hiss_agrees :
    qi_hiss.result = .passes ∧ hiss.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_sigh_agrees :
    qi_sigh.result = .passes ∧ sigh.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_whimper_agrees :
    qi_whimper.result = .passes ∧ whimper.unaccusative = true := ⟨rfl, rfl⟩

theorem qi_snap_agrees :
    qi_snap.result = .passes ∧ snap.unaccusative = true := ⟨rfl, rfl⟩

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

-- ════════════════════════════════════════════════════
-- § 7. Dowty Divergence
-- ════════════════════════════════════════════════════

/-! MoS verb subjects are volitional, sentient speakers — Dowty's proto-role
    counting yields P-Agent > P-Patient, predicting unergative.
    But QI says these verbs are unaccusative. This is a documented
    divergence between semantic proto-role predictions and syntactic
    diagnostics. -/

open Semantics.Lexical.Verb.EntailmentProfile

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
    but QI classifies them as unaccusative. -/
theorem whisper_dowty_diverges :
    predictsUnergative mosSubjectProfile = true ∧
    whisper.unaccusative = true := ⟨by native_decide, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Smuggling Bridge (@cite{collins-2005} → @cite{storment-2026})
-- ════════════════════════════════════════════════════

/-! The smuggling analysis (@cite{collins-2005}, applied to QI by @cite{storment-2026})
    derives QI licensing from two independently motivated properties:

    1. **Voice is non-phase** (= unaccusative): complement remains extractable
    2. **Verb has a complement** (the quote): there is something to smuggle

    We verify that `licensesQI` (defined in `Movement/Smuggling.lean` over
    Voice + complement availability) matches the empirical QI diagnostic data
    when applied to the Voice and complement type derived from each verb's
    lexical entry. -/

/-- Derive whether a verb has a complement (ComplementType ≠.none). -/
def hasComplement (v : Core.Verbs.VerbCore) : Bool :=
  v.complementType != .none

/-- Derive Voice head from unaccusativity annotation. -/
def voiceFor (v : Core.Verbs.VerbCore) : VoiceHead :=
  if v.unaccusative then Minimalism.voiceAnticausative
  else Minimalism.voiceAgent

/-- Derived QI licensing: combines Voice (from unaccusativity) and
    complement availability (from complementType). -/
def derivedQI (v : Core.Verbs.VerbCore) : Bool :=
  licensesQI (voiceFor v) (hasComplement v)

-- Per-verb verification: derivedQI matches empirical QI diagnostic results

theorem whisper_qi_derived :
    derivedQI whisper.toVerbCore = true := rfl

theorem murmur_qi_derived :
    derivedQI murmur.toVerbCore = true := rfl

theorem shout_qi_derived :
    derivedQI shout.toVerbCore = true := rfl

theorem cry_qi_derived :
    derivedQI cry.toVerbCore = true := rfl

theorem scream_qi_derived :
    derivedQI scream.toVerbCore = true := rfl

theorem mumble_qi_derived :
    derivedQI mumble.toVerbCore = true := rfl

theorem mutter_qi_derived :
    derivedQI mutter.toVerbCore = true := rfl

theorem shriek_qi_derived :
    derivedQI shriek.toVerbCore = true := rfl

theorem yell_qi_derived :
    derivedQI yell.toVerbCore = true := rfl

theorem groan_qi_derived :
    derivedQI groan.toVerbCore = true := rfl

theorem grumble_qi_derived :
    derivedQI grumble.toVerbCore = true := rfl

theorem hiss_qi_derived :
    derivedQI hiss.toVerbCore = true := rfl

theorem sigh_qi_derived :
    derivedQI sigh.toVerbCore = true := rfl

theorem whimper_qi_derived :
    derivedQI whimper.toVerbCore = true := rfl

theorem snap_qi_derived :
    derivedQI snap.toVerbCore = true := rfl

/-- `speak` is blocked: agentive Voice makes vP a phase (blocks smuggling),
    AND it has no complement (.none) — doubly ruled out. -/
theorem speak_qi_blocked :
    derivedQI speak.toVerbCore = false := rfl

theorem talk_qi_blocked :
    derivedQI talk.toVerbCore = false := rfl

/-- `arrive` is unaccusative but has no complement to smuggle —
    so it doesn't license QI. This is correct: *"arrived Mary" requires
    a fronted locative (LI), not a fronted quote (QI). -/
theorem arrive_no_qi :
    derivedQI arrive.toVerbCore = false := rfl

-- Consistency: derivedQI agrees with diagnostic data for all tested verbs.

theorem qi_data_consistent :
    (qi_whisper.result = .passes) = (derivedQI whisper.toVerbCore) ∧
    (qi_murmur.result = .passes) = (derivedQI murmur.toVerbCore) ∧
    (qi_shout.result  = .passes) = (derivedQI shout.toVerbCore) ∧
    (qi_cry.result    = .passes) = (derivedQI cry.toVerbCore) ∧
    (qi_scream.result = .passes) = (derivedQI scream.toVerbCore) ∧
    (qi_mumble.result = .passes) = (derivedQI mumble.toVerbCore) ∧
    (qi_mutter.result = .passes) = (derivedQI mutter.toVerbCore) ∧
    (qi_shriek.result = .passes) = (derivedQI shriek.toVerbCore) ∧
    (qi_yell.result   = .passes) = (derivedQI yell.toVerbCore) ∧
    (qi_groan.result  = .passes) = (derivedQI groan.toVerbCore) ∧
    (qi_grumble.result = .passes) = (derivedQI grumble.toVerbCore) ∧
    (qi_hiss.result   = .passes) = (derivedQI hiss.toVerbCore) ∧
    (qi_sigh.result   = .passes) = (derivedQI sigh.toVerbCore) ∧
    (qi_whimper.result = .passes) = (derivedQI whimper.toVerbCore) ∧
    (qi_snap.result   = .passes) = (derivedQI snap.toVerbCore) ∧
    (qi_speak.result  = .passes) = (derivedQI speak.toVerbCore) ∧
    (qi_talk.result   = .passes) = (derivedQI talk.toVerbCore) := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 9. QI ∥ LI: Distributional Contrasts (@cite{storment-2026}, §6)
-- ════════════════════════════════════════════════════

/-! Quotative inversion and locative inversion share the same mechanism
    (smuggling of VP to Spec-VoiceP, @cite{storment-2026} §6) but differ in
    their inputs and distribution:

    - QI requires a quote complement; LI requires a fronted locative PP
    - Both are subject to the transitivity constraint (§5): multiple DP
      arguments block inversion due to Case licensing limitations
    - QI degrades with pronominal subjects; LI categorically blocks them

    Despite sharing a mechanism, their distributional differences confirm
    they are distinct diagnostic constructions with different triggers. -/

/-- whisper passes QI but is only marginal in LI —
    same mechanism (smuggling), different inputs. -/
theorem qi_li_diverge_on_whisper :
    qi_whisper.result = .passes ∧
    loc_whisper.result = .marginal := ⟨rfl, rfl⟩

/-- LI blocks transitive verbs; QI with just a quote complement
    is fine, but both show a transitivity constraint with multiple
    DP arguments. -/
theorem li_blocks_transitive :
    li_kick.result = .fails ∧
    qi_whisper_transitive.result = .passes := ⟨rfl, rfl⟩

/-- LI categorically blocks pronominal subjects;
    QI merely degrades them. -/
theorem li_vs_qi_pronouns :
    li_arrive_pronoun.result = .fails ∧
    qi_whisper_pronoun.result = .marginal := ⟨rfl, rfl⟩

/-- The transitivity constraint (§5): QI is blocked when multiple DP
    arguments compete for Case licensing. -/
theorem qi_transitivity_constraint :
    qi_whisper_double_obj.result = .fails ∧
    qi_whisper_transitive.result = .passes := ⟨rfl, rfl⟩

/-- Unified smuggling analysis (§6): LI with `arrive` works because
    arrive projects non-thematic (non-phase) Voice, permitting VP to
    smuggle to Spec-VoiceP — the same mechanism that licenses QI. -/
theorem li_arrive_smuggling_unified :
    unaccToVoice arrive.unaccusative = .nonThematic ∧
    loc_arrive.result = .passes := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 10. MoS Island ↔ QI Cross-Reference
-- ════════════════════════════════════════════════════

/-! MoS verbs participate in two seemingly opposite phenomena:

    1. **MoS islands**: wh-extraction FROM WITHIN
       the complement is degraded (discourse backgroundedness)
    2. **Quotative inversion**: VP-smuggling to Spec-VoiceP
       is grammatical (A-movement, not extraction from complement)

    These are not contradictory — they're different operations:
    - MoS islands: wh-movement from within CP complement (blocked by discourse)
    - QI smuggling: A-movement of VP to Spec-VoiceP (licensed by syntax)

    The asymmetry validates both analyses simultaneously: MoS islands are
    discourse-sourced (not syntactic), so they don't block the syntactic
    VP-movement that produces QI. -/

/-- MoS islands are discourse-sourced, not syntactic — so they don't
    block the syntactic smuggling operation that produces QI. -/
theorem mos_island_compatible_with_qi :
    constraintSource .mannerOfSpeaking = .discourse ∧
    derivedQI whisper.toVerbCore = true := ⟨rfl, rfl⟩

/-- The extraction asymmetry: sub-extraction from MoS complement is
    discourse-blocked, but whole-complement fronting (QI) is
    syntactically licensed. Same verbs, same complements, different
    operations, different sources. -/
theorem mos_extraction_asymmetry :
    -- Sub-extraction blocked (discourse-sourced island)
    constraintSource .mannerOfSpeaking = .discourse ∧
    -- VP-smuggling licensed (non-phase Voice)
    derivedQI whisper.toVerbCore = true ∧
    derivedQI murmur.toVerbCore = true ∧
    derivedQI shout.toVerbCore = true ∧
    derivedQI mumble.toVerbCore = true ∧
    derivedQI mutter.toVerbCore = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. QI Derivation (@cite{storment-2026}, §4)
-- ════════════════════════════════════════════════════

/-! The smuggling derivation of QI assigns each major constituent to
    a structural position. Each position has observable consequences
    that are tested against the §3 structural evidence data.

    1. **Theme** → Spec-TP (A-movement): controls agreement, licenses
       raising, does NOT license parasitic gaps (A ≠ Ā)
    2. **Agent** → Spec-vP (in-situ): conjoint domain in Setswana,
       does not control agreement (defective circumvention)
    3. **VP** → Spec-VoiceP (smuggling): VP-internal material precedes
       Agent; vP-external adjuncts follow Agent
    4. **Quote** → DiscourseP (clause-external): can split around
       V + Agent, need not be grammatical -/

/-- Structural position in QI derivation. -/
inductive QIPosition where
  | specTP       -- Theme's final position (A-movement target)
  | specVoiceP   -- VP's position after smuggling
  | specvP       -- Agent's in-situ position
  | discourseP   -- Quote's clause-external position
  deriving DecidableEq, Repr, BEq

/-- The QI derivation assigns constituents to structural positions.
    Each position has testable predictions (§3). -/
structure QIDerivation where
  themePosition : QIPosition
  agentPosition : QIPosition
  vpPosition : QIPosition
  quotePosition : QIPosition
  deriving Repr, BEq

/-- The smuggling derivation of QI. -/
def qiSmuggling : QIDerivation where
  themePosition := .specTP
  agentPosition := .specvP
  vpPosition := .specVoiceP
  quotePosition := .discourseP

-- ════════════════════════════════════════════════════
-- § 12. Derivation → Structural Evidence (§4 → §3)
-- ════════════════════════════════════════════════════

/-! Each structural position predicts observable properties.
    We verify each prediction against the §3 data. -/

open Phenomena.ArgumentStructure.Unaccusativity.Data (QIStructuralDatum)

/-- Theme in Spec-TP → agreement can track agent via defective
    circumvention: probe first hits phi-deficient Theme, then
    optionally re-probes and finds Agent (§3.1). -/
theorem theme_specTP_agreement :
    qiSmuggling.themePosition = .specTP ∧
    qi_agreement_english.result = .passes := ⟨rfl, rfl⟩

/-- Theme in Spec-TP → Setswana SM surfaces as default SM17 because
    Theme is phi-deficient; probe doesn't reach Agent (§3.1). -/
theorem theme_specTP_setswana_sm17 :
    qiSmuggling.themePosition = .specTP ∧
    qi_agreement_setswana.result = .passes := ⟨rfl, rfl⟩

/-- Theme in Spec-TP → A-movement → parasitic gaps NOT licensed.
    A-movement chains cannot license PGs; only Ā-chains can (§3.2). -/
theorem theme_specTP_no_parasitic_gap :
    qiSmuggling.themePosition = .specTP ∧
    qi_parasitic_gap_blocked.result = .fails := ⟨rfl, rfl⟩

/-- Theme in Spec-TP → compatible with subject-to-subject raising.
    Theme can A-move through intermediate Spec-TP positions (§3.3). -/
theorem theme_specTP_raising :
    qiSmuggling.themePosition = .specTP ∧
    qi_raising.result = .passes := ⟨rfl, rfl⟩

/-- Agent in Spec-vP → Setswana disjoint morpheme blocked.
    Disjoint form requires the subject to be vP-external;
    Agent remains vP-internal in QI (§3.4). -/
theorem agent_specvP_conjoint :
    qiSmuggling.agentPosition = .specvP ∧
    qi_conjoint_disjoint.result = .fails := ⟨rfl, rfl⟩

/-- Quote in DiscourseP → quote can split around verb + agent.
    A constituent in Spec-TP cannot split; DiscourseP can (§3.5). -/
theorem quote_discourseP_split :
    qiSmuggling.quotePosition = .discourseP ∧
    qi_quote_split.result = .passes := ⟨rfl, rfl⟩

/-- Quote in DiscourseP → quote need not be grammatical.
    Clause-external status means quote is not subject to
    clausal well-formedness requirements (§3.5). -/
theorem quote_discourseP_nongrammatical :
    qiSmuggling.quotePosition = .discourseP ∧
    qi_quote_nongrammatical.result = .passes := ⟨rfl, rfl⟩

/-- VP smuggling predicts: VP-internal material (complements) precedes
    Agent; vP-external material (adjuncts) follows Agent. The ordering
    data from Setswana (§2) confirms both predictions. -/
theorem vp_smuggling_ordering :
    qiSmuggling.vpPosition = .specVoiceP ∧
    -- VP-internal complement precedes Agent
    qi_ordering_complement.result = .passes ∧
    -- vP-external adjuncts follow Agent
    qi_ordering_depictive.result = .passes ∧
    qi_ordering_manner.result = .passes ∧
    qi_ordering_purpose.result = .passes := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 13. @cite{levin-1993} Class Bridge
-- ════════════════════════════════════════════════════

/-! Levin & Rappaport @cite{levin-hovav-1995} predict unaccusativity from verb class
    membership: CoS classes (§45) predict unaccusative for their inchoative
    alternant, manner-of-motion (§51.3) predicts unergative, inherently
    directed motion (§51.1) predicts unaccusative, and emission classes
    (§43) predict unaccusative.

    The function `LevinClass.predictsUnaccusative` (in RootDimensions.lean)
    encodes these predictions. Here we verify them against Fragment entries
    that carry both `.levinClass` and `.unaccusative` annotations. -/

-- Per-verb agreement: Levin prediction matches empirical annotation

/-- arrive (§51.1 inherentlyDirectedMotion) → predicted + empirically unaccusative. -/
theorem arrive_levin_agrees :
    arrive.levinClass = some .inherentlyDirectedMotion
    ∧ LevinClass.predictsUnaccusative .inherentlyDirectedMotion = true
    ∧ arrive.unaccusative = true := ⟨rfl, rfl, rfl⟩

/-- run (§51.3 mannerOfMotion) → predicted + empirically unergative. -/
theorem run_levin_agrees :
    run.levinClass = some .mannerOfMotion
    ∧ LevinClass.predictsUnaccusative .mannerOfMotion = false
    ∧ run.unaccusative = false := ⟨rfl, rfl, rfl⟩

/-- exist (§47) → predicted + empirically unaccusative. -/
theorem exist_levin_agrees :
    exist.levinClass = some .exist
    ∧ LevinClass.predictsUnaccusative .exist = true
    ∧ exist.unaccusative = true := ⟨rfl, rfl, rfl⟩

/-- appear (§48) → predicted + empirically unaccusative. -/
theorem appear_levin_agrees :
    appear.levinClass = some .appear
    ∧ LevinClass.predictsUnaccusative .appear = true
    ∧ appear.unaccusative = true := ⟨rfl, rfl, rfl⟩

/-- glow (§43.1 lightEmission) → predicted + empirically unaccusative. -/
theorem glow_levin_agrees :
    glow.levinClass = some .lightEmission
    ∧ LevinClass.predictsUnaccusative .lightEmission = true
    ∧ glow.unaccusative = true := ⟨rfl, rfl, rfl⟩

/-- buzz (§43.2 soundEmission) → predicted + empirically unaccusative. -/
theorem buzz_levin_agrees :
    buzz.levinClass = some .soundEmission
    ∧ LevinClass.predictsUnaccusative .soundEmission = true
    ∧ buzz.unaccusative = true := ⟨rfl, rfl, rfl⟩

/-- bleed (§43.4 substanceEmission) → predicted + empirically unaccusative. -/
theorem bleed_levin_agrees :
    bleed.levinClass = some .substanceEmission
    ∧ LevinClass.predictsUnaccusative .substanceEmission = true
    ∧ bleed.unaccusative = true := ⟨rfl, rfl, rfl⟩

/-- rust (§45.5 entitySpecificCoS) → predicted + empirically unaccusative. -/
theorem rust_levin_agrees :
    rust.levinClass = some .entitySpecificCoS
    ∧ LevinClass.predictsUnaccusative .entitySpecificCoS = true
    ∧ rust.unaccusative = true := ⟨rfl, rfl, rfl⟩

/-- fidget (§49 bodyInternalMotion) → predicted + empirically unergative. -/
theorem fidget_levin_agrees :
    fidget.levinClass = some .bodyInternalMotion
    ∧ LevinClass.predictsUnaccusative .bodyInternalMotion = false
    ∧ fidget.unaccusative = false := ⟨rfl, rfl, rfl⟩

/-- kick (§18.1 hit) → predicted + empirically not unaccusative. -/
theorem kick_levin_agrees :
    kick.levinClass = some .hit
    ∧ LevinClass.predictsUnaccusative .hit = false
    ∧ kick.unaccusative = false := ⟨rfl, rfl, rfl⟩

-- The MoS divergence: Levin class predicts unergative, but empirically unaccusative

/-- MoS verbs: Levin class does NOT predict unaccusativity (agentive manner
    activity), but they ARE empirically unaccusative (@cite{storment-2026} QI
    diagnostic). This divergence motivates Storment's syntactic analysis
    (smuggling) over a purely lexical-semantic account of unaccusativity. -/
theorem mos_levin_diverges :
    LevinClass.predictsUnaccusative .mannerOfSpeaking = false
    ∧ whisper.levinClass = some .mannerOfSpeaking
    ∧ whisper.unaccusative = true
    ∧ speak.levinClass = some .mannerOfSpeaking
    ∧ speak.unaccusative = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The MoS split: both whisper and speak are §37.3 mannerOfSpeaking,
    but they diverge on unaccusativity. Levin class membership alone
    cannot explain this. -/
theorem mos_within_class_split :
    whisper.levinClass = speak.levinClass
    ∧ whisper.unaccusative = true
    ∧ speak.unaccusative = false := ⟨rfl, rfl, rfl⟩

-- CoS classes: causative/inchoative alternation → unaccusative inchoative

/-- Break (§45.1): the Fragment entry is the transitive causative form
    (unaccusative = false), but the class predicts an unaccusative
    inchoative alternant ("the vase broke"). The causative/inchoative
    alternation is the bridge between the transitive entry and the
    predicted unaccusativity. -/
theorem break_causativeInchoative_unaccusative :
    break_.levinClass = some .break_
    ∧ LevinClass.break_.participatesIn .causativeInchoative = true
    ∧ LevinClass.predictsUnaccusative .break_ = true
    ∧ break_.unaccusative = false  -- Fragment entry is the transitive form
    := ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.ArgumentStructure.Unaccusativity.Bridge
