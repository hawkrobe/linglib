import Linglib.Theories.Syntax.Case.Dependent
import Linglib.Theories.Syntax.Minimalism.Voice
import Linglib.Fragments.Japanese.Predicates
import Linglib.Fragments.Japanese.Passive

/-!
# @cite{ozaki-2026} — Japanese Accusative/Ablative Alternation: Data
@cite{ozaki-2026}

Empirical data from @cite{ozaki-2026} on Japanese departure verbs
that alternate between accusative *-o* and ablative *kara* marking
on the source argument.

## Key Empirical Facts

1. **Alternation**: Departure verbs like *hanareru* 'leave' and *deru*
   'exit' allow both ACC and ABL on the source:
   - "Taro-ga mura-**o** hanare-ta" (ACC)
   - "Taro-ga mura-**kara** hanare-ta" (ABL)

2. **Argumenthood of source**: The source behaves as an argument regardless
   of case — it can undergo VP ellipsis and long-distance scrambling.

3. **Unaccusativity**: These verbs are unaccusative:
   - Only indirect passive (*-rare*), no direct passive (*-niyotte*)
   - *Nani-o* wh-adjunct test patterns with unaccusatives

## Theory-Neutral

This file contains no theoretical commitments. See Bridge.lean for
connection to dependent case theory and Minimalist syntax.

-/

namespace Phenomena.Case.Ozaki2026.Data

-- ============================================================================
-- § 1: Data Types
-- ============================================================================

/-- Case marking on the source argument of alternation verbs. -/
inductive CaseMarking where
  | accusative   -- *-o*
  | ablative     -- *kara*
  | nominative   -- *-ga*
  | dative       -- *-ni*
  deriving DecidableEq, Repr

open Fragments.Japanese.Passive (PassiveType)

/-- Diagnostics for argumenthood (vs. adjuncthood). -/
inductive ArgumenthoodDiagnostic where
  | ellipsis                -- VP ellipsis includes the constituent
  | longDistanceScrambling  -- Constituent can scramble long-distance
  deriving DecidableEq, Repr

/-- Diagnostics for unaccusativity. -/
inductive UnaccusativityDiagnostic where
  | passivization   -- Only indirect passive available
  | naniOWhAdjunct  -- *nani-o* wh-adjunct test: blocked = unaccusative
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Data Structures
-- ============================================================================

/-- A single case alternation datum: a verb form with a source argument
    in a particular case, plus grammaticality. -/
structure AlternationDatum where
  verb : String
  sourceCase : CaseMarking
  grammatical : Bool
  sentence : String
  exampleNum : String
  deriving DecidableEq, Repr

/-- An unaccusativity diagnostic datum. -/
structure UnaccusativityDatum where
  verb : String
  diagnostic : UnaccusativityDiagnostic
  passiveType : Option PassiveType
  grammatical : Bool
  sentence : String
  exampleNum : String
  deriving DecidableEq, Repr

/-- An argumenthood diagnostic datum. -/
structure ArgumenthoodDatum where
  verb : String
  sourceCase : CaseMarking
  diagnostic : ArgumenthoodDiagnostic
  grammatical : Bool
  sentence : String
  exampleNum : String
  deriving DecidableEq, Repr

-- ============================================================================
-- § 3: Alternation Data
-- ============================================================================

/-! ### *hanareru* 'leave' — ACC/ABL alternation (ex. 1)

"Taro-ga mura-{o/kara} hanare-ta." (Taro-NOM village-{ACC/from} leave-PAST) -/

def hanareru_acc : AlternationDatum where
  verb := "hanareru"
  sourceCase := .accusative
  grammatical := true
  sentence := "Taro-ga mura-o hanare-ta"
  exampleNum := "1"

def hanareru_abl : AlternationDatum where
  verb := "hanareru"
  sourceCase := .ablative
  grammatical := true
  sentence := "Taro-ga mura-kara hanare-ta"
  exampleNum := "1"

/-! ### *deru* 'exit' — ACC/ABL alternation (implicit in ex. 9)

The paper uses *deru* with "eki" (station) in the ellipsis diagnostic
(ex. 9). The basic alternation is implicit: "Taro-ga eki-{o/kara} deta." -/

def deru_acc : AlternationDatum where
  verb := "deru"
  sourceCase := .accusative
  grammatical := true
  sentence := "Taro-ga eki-o deta"
  exampleNum := "9"

def deru_abl : AlternationDatum where
  verb := "deru"
  sourceCase := .ablative
  grammatical := true
  sentence := "Taro-ga eki-kara deta"
  exampleNum := "9"

def alternationData : List AlternationDatum :=
  [hanareru_acc, hanareru_abl, deru_acc, deru_abl]

-- ============================================================================
-- § 4: Argumenthood Data
-- ============================================================================

/-! ### VP ellipsis — source elides as argument (ex. 9–10)

@cite{funakoshi-2016}'s generalization: adjuncts can only be elided if no
other VP-internal elements are present. The source of *deru* elides
even with an overt adverb *suguni* 'quickly', confirming argumenthood.
The continuation (10) is non-contradictory, showing the elided reading
is available. -/

def deru_ellipsis_acc : ArgumenthoodDatum where
  verb := "deru"
  sourceCase := .accusative
  diagnostic := .ellipsis
  grammatical := true
  sentence := "Taro-wa suguni eki-o deta ga, Hanako-wa suguni denakatta"
  exampleNum := "9"

def deru_ellipsis_abl : ArgumenthoodDatum where
  verb := "deru"
  sourceCase := .ablative
  diagnostic := .ellipsis
  grammatical := true
  sentence := "Taro-wa suguni eki-kara deta ga, Hanako-wa suguni denakatta"
  exampleNum := "9"

/-! ### Long-distance scrambling — source scrambles freely (ex. 13)

@cite{saito-1985}: arguments can undergo long-distance scrambling, adjuncts
cannot. The source of *hanareru* scrambles out of the embedded clause,
confirming argumenthood regardless of case marking. -/

def hanareru_scrambling_acc : ArgumenthoodDatum where
  verb := "hanareru"
  sourceCase := .accusative
  diagnostic := .longDistanceScrambling
  grammatical := true
  sentence := "Mura-o Taro-wa [Hanako-ga __ hanareta to] itta"
  exampleNum := "13"

def hanareru_scrambling_abl : ArgumenthoodDatum where
  verb := "hanareru"
  sourceCase := .ablative
  diagnostic := .longDistanceScrambling
  grammatical := true
  sentence := "Mura-kara Taro-wa [Hanako-ga __ hanareta to] itta"
  exampleNum := "13"

def argumenthoodData : List ArgumenthoodDatum :=
  [deru_ellipsis_acc, deru_ellipsis_abl, hanareru_scrambling_acc, hanareru_scrambling_abl]

-- ============================================================================
-- § 5: Unaccusativity Data
-- ============================================================================

/-! ### Passive — only indirect passive available (ex. 14, 20)

Japanese has two passives: indirect (*-rare-*, adversative, available
to all verbs including unaccusatives) and direct (*-niyotte*, requires
thematic Voice). If alternation verbs had thematic Voice, direct passive
should be possible — but it is not (ex. 20). -/

def hanareru_indirect_passive : UnaccusativityDatum where
  verb := "hanareru"
  diagnostic := .passivization
  passiveType := some .indirect
  grammatical := true
  sentence := "Sono mura-ga Taro-ni hanare-rare-ta"
  exampleNum := "14"

def hanareru_direct_passive : UnaccusativityDatum where
  verb := "hanareru"
  diagnostic := .passivization
  passiveType := some .direct
  grammatical := false
  sentence := "*Sono mura-ga Taro-niyotte hanare-rare-ta"
  exampleNum := "20"

/-! ### *nani-o* wh-adjunct — blocked with unaccusatives (ex. 26)

@cite{kurafuji-1997}: *nani-o* 'what-ACC' can mean 'why' with unergatives
and transitives, but not with unaccusatives. Alternation verbs block
this reading, patterning with unaccusatives. -/

def hanareru_nanio : UnaccusativityDatum where
  verb := "hanareru"
  diagnostic := .naniOWhAdjunct
  passiveType := none
  grammatical := false
  sentence := "*Nani-o Taro-wa mura-o hanare-teiru no"
  exampleNum := "26"

def unaccusativityData : List UnaccusativityDatum :=
  [hanareru_indirect_passive, hanareru_direct_passive, hanareru_nanio]

-- ============================================================================
-- § 6: Verification Theorems
-- ============================================================================

/-- Both ACC and ABL variants are grammatical for alternation verbs. -/
theorem both_variants_grammatical :
    alternationData.all (·.grammatical) = true := by native_decide

/-- All argumenthood diagnostics succeed regardless of case marking. -/
theorem argumenthood_regardless_of_case :
    argumenthoodData.all (·.grammatical) = true := by native_decide

/-- Direct passive is ungrammatical (hallmark of unaccusativity). -/
theorem direct_passive_blocked :
    hanareru_direct_passive.grammatical = false := rfl

/-- Indirect passive is grammatical (expected for unaccusatives). -/
theorem indirect_passive_ok :
    hanareru_indirect_passive.grammatical = true := rfl

/-- *Nani-o* is blocked — patterns with unaccusatives, not transitives. -/
theorem nanio_blocked :
    hanareru_nanio.grammatical = false := rfl

/-- Four alternation data points total. -/
theorem alternation_count : alternationData.length = 4 := rfl

/-- Four argumenthood data points total. -/
theorem argumenthood_count : argumenthoodData.length = 4 := rfl

/-- Three unaccusativity data points total. -/
theorem unaccusativity_count : unaccusativityData.length = 3 := rfl

-- ============================================================================
-- § Bridge: Dependent Case × Minimalist Syntax
-- ============================================================================

open Minimalism
open Syntax.Case
open Fragments.Japanese.Predicates

/-- Departure verbs predict no external argument: non-thematic Voice
    does not assign a θ-role (@cite{kratzer-1996}, @cite{schaefer-2025}). -/
theorem departure_no_external :
    voiceAnticausative.assignsTheta = false := rfl

/-- Departure verbs have inchoative event structure (vGO + vBE, no vDO).
    Verified via `buildDecomposition` from `Core/Voice.lean`. -/
theorem departure_is_inchoative :
    isInchoative (buildDecomposition voiceAnticausative [.vCAUSE, .vGO, .vBE]) = true := by
  native_decide

/-- Non-thematic Voice assigns no θ-role. -/
theorem departure_voice_no_theta :
    voiceAnticausative.assignsTheta = false := rfl

/-- ACC variant produces dependent ACC on source, unmarked NOM on leaver. -/
theorem acc_derivation_correct :
    getCaseOf "source" accVariantResult = some .acc ∧
    getCaseOf "leaver" accVariantResult = some .nom := by native_decide

/-- ABL variant produces lexical ABL on source, unmarked NOM on leaver. -/
theorem abl_derivation_correct :
    getCaseOf "source" ablVariantResult = some .abl ∧
    getCaseOf "leaver" ablVariantResult = some .nom := by native_decide

/-- In the ACC variant, source case is dependent. -/
theorem acc_source_from_configuration :
    getSourceOf "source" accVariantResult = some .dependent := by native_decide

/-- In the ABL variant, source case is lexical. -/
theorem abl_source_from_lexical_p :
    getSourceOf "source" ablVariantResult = some .lexical := by native_decide

/-- Anticausative Voice is not a phase head. -/
theorem agree_acc_needs_phase_head :
    voiceAnticausative.phaseHead = false := rfl

/-- Agentive Voice IS a phase head. -/
theorem agentive_has_phase_head :
    voiceAgent.phaseHead = true := rfl

/-- The accusative unaccusative paradox. -/
theorem accusative_unaccusative_paradox :
    voiceAnticausative.assignsTheta = false ∧
    voiceAnticausative.phaseHead = false ∧
    getCaseOf "source" accVariantResult = some .acc ∧
    getSourceOf "source" accVariantResult = some .dependent := by
  exact ⟨rfl, rfl, by native_decide, by native_decide⟩

/-- Fragment entry for *hanareru* is marked unaccusative. -/
theorem hanareru_is_unaccusative :
    Fragments.Japanese.Predicates.hanareru.unaccusative = true := rfl

/-- Fragment entry for *deru* is marked unaccusative. -/
theorem deru_is_unaccusative :
    Fragments.Japanese.Predicates.deru.unaccusative = true := rfl

/-- Fragment entry for *hanareru* is not passivizable. -/
theorem hanareru_not_passivizable :
    Fragments.Japanese.Predicates.hanareru.passivizable = false := rfl

/-- Fragment entry for *deru* is not passivizable. -/
theorem deru_not_passivizable :
    Fragments.Japanese.Predicates.deru.passivizable = false := rfl

/-- Non-passivizability aligns with direct passive being ungrammatical. -/
theorem passive_data_matches_fragment :
    hanareru_direct_passive.grammatical = false ∧
    Fragments.Japanese.Predicates.hanareru.passivizable = false := ⟨rfl, rfl⟩

/-- Non-passivizability follows from Voice theory. -/
theorem passive_follows_from_voice :
    voiceAnticausative.assignsTheta = false ∧
    Fragments.Japanese.Predicates.hanareru.passivizable = false := ⟨rfl, rfl⟩

/-- Verb forms in Data match Fragment entries. -/
theorem hanareru_form_matches :
    hanareru_acc.verb = Fragments.Japanese.Predicates.hanareru.form := rfl

theorem deru_form_matches :
    deru_acc.verb = Fragments.Japanese.Predicates.deru.form := rfl

/-- All argumenthood diagnostics succeed. -/
theorem source_is_argument_both_frames :
    argumenthoodData.all (·.grammatical) = true := by native_decide

-- ============================================================================
-- § Voice Derivation Bridge
-- ============================================================================

/-- Hanareru's unaccusativity is DERIVED from its voice type, not stipulated.
    `derivedUnaccusative` uses the `voiceType` field to compute unaccusativity
    via `VoiceType.assignsTheta`. -/
theorem hanareru_unaccusative_derived :
    Fragments.Japanese.Predicates.hanareru.toVerbCore.derivedUnaccusative = true := rfl

/-- Deru's unaccusativity is DERIVED from its voice type. -/
theorem deru_unaccusative_derived :
    Fragments.Japanese.Predicates.deru.toVerbCore.derivedUnaccusative = true := rfl

/-- The stored `unaccusative` flag agrees with the derived value.
    This consistency check ensures that the stipulated field and the
    Voice-based derivation produce the same answer. -/
theorem hanareru_stored_matches_derived :
    Fragments.Japanese.Predicates.hanareru.unaccusative =
    Fragments.Japanese.Predicates.hanareru.toVerbCore.derivedUnaccusative := rfl

theorem deru_stored_matches_derived :
    Fragments.Japanese.Predicates.deru.unaccusative =
    Fragments.Japanese.Predicates.deru.toVerbCore.derivedUnaccusative := rfl

/-- Direct passive requires thematic Voice, which departure verbs lack. -/
theorem direct_passive_requires_voice :
    PassiveType.requiresThematicVoice .direct = true ∧
    voiceAnticausative.assignsTheta = false := ⟨rfl, rfl⟩

end Phenomena.Case.Ozaki2026.Data
