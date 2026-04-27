import Linglib.Theories.Syntax.Minimalist.Voice
import Linglib.Theories.Syntax.Minimalist.Applicative
import Linglib.Theories.Syntax.Minimalist.VerbalDecomposition
import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalist.VoiceTheta
import Linglib.Fragments.Icelandic.Predicates

/-!
# @cite{wood-2015} — Icelandic Morphosyntax and Argument Structure
@cite{wood-2015} @cite{kratzer-1996} @cite{pylkkanen-2008} @cite{schaefer-2008} @cite{cuervo-2003}

@cite{wood-2015} establishes that Icelandic -st (from historical
reflexive *sik*) spells out Voice across MULTIPLE syntactic
configurations, not a single "reflexive" or "anticausative" morpheme.

## Key Claims Formalized

1. **Voice–CAUSE independence** (Ch. 3): The causal relation is shared
   across causative and anticausative alternants. Voice contributes
   only whether an external argument is introduced. (Note:
   @cite{wood-2015} uses a single v head; the VerbHead decomposition
   here follows @cite{cuervo-2003}'s notation to model the same
   independence structurally.)

2. **-st as elsewhere exponent of Voice** (Ch. 3, §3.3–3.5): -st
   spells out non-agentive Voice across anticausative, middle,
   reflexive, experiencer, inherent, and reciprocal configurations.
   The morphological uniformity masks syntactic diversity.

3. **Voice parameterization** (Ch. 3): @cite{wood-2015}'s Voice_{D}
   vs Voice_{} distinction (whether Voice projects a specifier)
   is modeled here using the ±θ/±D grid from @cite{schaefer-2008}.

4. **Applicative interaction** (Ch. 5): @cite{wood-2015} shows -st
   cannot merge in SpecApplP because Appl assigns dative case
   and -st lacks case features. The high/low Appl interaction
   theorems below follow @cite{pylkkanen-2008} and @cite{schaefer-2008},
   not @cite{wood-2015}'s Icelandic-specific analysis (which argues
   Icelandic lacks true high applicatives).
-/

namespace Wood2015

open Minimalist
open Fragments.Icelandic.Predicates
open Minimalist.VoiceTheta

-- ============================================================================
-- § 1: Voice–CAUSE Independence (Ch. 3)
-- ============================================================================

/-- The causal relation is shared across causative and anticausative
    alternants (@cite{wood-2015} Ch. 3). Modeled here using
    @cite{cuervo-2003}'s VerbHead decomposition: the causative has
    [vDO, vCAUSE, vGO, vBE]; the anticausative has [vCAUSE, vGO, vBE]. -/
theorem cause_shared_across_alternation :
    let causativeDecomp := buildDecomposition voiceAgent opnast.rootStructure
    let anticausativeDecomp := buildDecomposition voiceAnticausative opnast.rootStructure
    hasCause causativeDecomp = true ∧
    hasCause anticausativeDecomp = true := by
  native_decide

/-- The causative alternation for *opna/opnast*: same root, different Voice. -/
theorem opna_alternation :
    isCausative (buildDecomposition voiceAgent opnast.rootStructure) = true ∧
    isInchoative (buildDecomposition voiceAnticausative opnast.rootStructure) = true := by
  native_decide

/-- Voice alone determines causativity for change-of-state roots. -/
theorem voice_alone_determines_causativity :
    buildDecomposition voiceAgent [.vCAUSE, .vGO, .vBE] =
      [.vDO, .vCAUSE, .vGO, .vBE] ∧
    buildDecomposition voiceAnticausative [.vCAUSE, .vGO, .vBE] =
      [.vCAUSE, .vGO, .vBE] := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: -st as Elsewhere Exponent (Ch. 3, §3.3–3.5)
-- ============================================================================

/-- -st spells out Voice across all six construction types.
    Despite morphological uniformity, the underlying Voice configurations
    differ in ±θ/±D parameters. -/
theorem st_covers_all_types :
    voiceToSuffix (StType.voiceFlavor .anticausative) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .middle) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .reflexive) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .subjectExp) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .inherent) = some "-st" ∧
    voiceToSuffix (StType.voiceFlavor .reciprocal) = some "-st" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Despite shared morphology, the Voice configurations differ.
    Anticausative and middle Voice do NOT assign θ; reflexive does. -/
theorem st_hides_theta_diversity :
    let anticVoice : VoiceHead := { flavor := StType.voiceFlavor .anticausative,
                                    hasD := true, phaseHead := false }
    let midVoice : VoiceHead := { flavor := StType.voiceFlavor .middle,
                                  hasD := false, phaseHead := false }
    let reflVoice : VoiceHead := { flavor := StType.voiceFlavor .reflexive,
                                   hasD := true, phaseHead := true }
    anticVoice.assignsTheta = false ∧
    midVoice.assignsTheta = false ∧
    reflVoice.assignsTheta = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: ±θ/±D Parameterization (@cite{schaefer-2008})
-- ============================================================================

/-- The six -st types occupy distinct cells in the ±θ/±D space
    (@cite{schaefer-2008}). @cite{wood-2015}'s Voice_{D}/Voice_{}
    distinction maps approximately to the ±D axis; Voice semantics
    (Ø vs AGENT) maps to the ±θ axis. -/
theorem parametric_diversity :
    -- [−θ, +D]: anticausative
    (VoiceFlavor.toParams (StType.voiceFlavor .anticausative)).selectsSpecifier = some true ∧
    (VoiceFlavor.toParams (StType.voiceFlavor .anticausative)).extArgSemantics = some .expletive ∧
    -- [−θ, −D]: middle
    (VoiceFlavor.toParams (StType.voiceFlavor .middle)).selectsSpecifier = some false ∧
    (VoiceFlavor.toParams (StType.voiceFlavor .middle)).extArgSemantics = some .expletive ∧
    -- [+θ, +D]: reflexive
    (VoiceFlavor.toParams (StType.voiceFlavor .reflexive)).selectsSpecifier = some true ∧
    (VoiceFlavor.toParams (StType.voiceFlavor .reflexive)).extArgSemantics = some .thematicArgument ∧
    -- [+θ, +D]: experiencer
    (VoiceFlavor.toParams (StType.voiceFlavor .subjectExp)).selectsSpecifier = some true ∧
    (VoiceFlavor.toParams (StType.voiceFlavor .subjectExp)).extArgSemantics = some .thematicArgument :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: High vs Low Applicative Interaction (@cite{pylkkanen-2008}, @cite{schaefer-2008})
-- ============================================================================

/-- High applicatives are blocked when Voice has no event semantics
    (@cite{pylkkanen-2008}, @cite{schaefer-2008}). Note: @cite{wood-2015}
    Ch. 5 argues Icelandic lacks true high applicatives; the asymmetry
    formalized here follows the cross-linguistic typology. -/
theorem ethical_blocked_in_middle :
    applHigh.licensedWith voiceMiddle = false := rfl

/-- Low applicatives survive when Voice has no event semantics
    because they relate to the theme, not the event (@cite{pylkkanen-2008}). -/
theorem possessive_survives_middle :
    applLowRecipient.licensedWith voiceMiddle = true := rfl

/-- In anticausatives, possessive datives also survive. -/
theorem possessive_survives_anticausative :
    applLowRecipient.licensedWith voiceAnticausative = true := rfl

/-- High applicatives ARE licensed with agentive Voice. -/
theorem ethical_ok_in_active :
    applHigh.licensedWith voiceAgent = true := rfl

/-- The full asymmetry: high applicatives require Voice with event
    semantics; low applicatives are independent of Voice
    (@cite{pylkkanen-2008}, @cite{schaefer-2008}). -/
theorem dative_voice_asymmetry :
    -- Ethical dative: blocked when Voice has no semantics
    applHigh.licensedWith voiceMiddle = false ∧
    applHigh.licensedWith voiceAgent = true ∧
    -- Possessive dative: always licensed
    applLowRecipient.licensedWith voiceMiddle = true ∧
    applLowRecipient.licensedWith voiceAgent = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Theta Role Predictions
-- ============================================================================

/-- Reflexive Voice predicts agent θ-role (agent acts on self). -/
theorem reflexive_predicts_agent :
    VoiceFlavor.thetaRole .reflexive = some .agent := rfl

/-- Experiencer Voice predicts experiencer θ-role. -/
theorem experiencer_predicts_experiencer :
    VoiceFlavor.thetaRole .experiencer = some .experiencer := rfl

/-- Anticausative Voice predicts no external θ-role. -/
theorem anticausative_predicts_none :
    VoiceFlavor.thetaRole .nonThematic = none := rfl

/-- Middle Voice predicts no external θ-role. -/
theorem middle_predicts_none :
    VoiceFlavor.thetaRole .expletive = none := rfl

-- ============================================================================
-- § 6: -st Blocked from SpecApplP (@cite{wood-2015} Ch. 5, §5.3.2)
-- ============================================================================

/-- @cite{wood-2015}'s key applicative claim: -st cannot merge in
    SpecApplP because Appl assigns dative case and -st lacks case
    features. This contrasts with SpecVoiceP and SpecpP, where Voice
    and p do NOT assign case to their specifiers. -/
theorem st_blocked_from_specApplP :
    -- -st (caseless) blocked from SpecApplP
    applLowRecipient.specCanBearCase false = false ∧
    -- But case-bearing DPs can merge in SpecApplP
    applLowRecipient.specCanBearCase true = true := ⟨rfl, rfl⟩

/-- In ditransitive -st alternations, Appl datives are retained
    because Appl assigns case independently of Voice. Direct object
    datives (from v) are lost through impoverishment
    (@cite{wood-2015} Ch. 5, §5.3.1). -/
theorem appl_dative_retained_with_st :
    -- Low Appl licensed even when Voice is anticausative
    applLowRecipient.licensedWith voiceAnticausative = true := rfl

-- ============================================================================
-- § 7: Fragment Consistency
-- ============================================================================

/-- All anticausative -st verbs have change-of-state root structure. -/
theorem anticausative_verbs_are_cos :
    (allStVerbs.filter (fun v => v.stType == .anticausative)).all
      (fun v => v.rootStructure.contains .vGO) = true := by native_decide

/-- All alternating -st verbs have active counterparts. -/
theorem alternating_verbs_have_actives :
    (allStVerbs.filter (·.hasActiveVariant)).all
      (fun v => v.activeForm.isSome) = true := by native_decide

/-- Inherent -st verbs (nálgast, minnast) have no active variant. -/
theorem inherent_verbs_no_active :
    nalgast.hasActiveVariant = false ∧ minnast.hasActiveVariant = false := ⟨rfl, rfl⟩

/-- Subject-experiencer verb leiðast has no active variant. -/
theorem subjectexp_no_active : leidast.hasActiveVariant = false := rfl

/-- Ten -st verb entries in the fragment. -/
theorem verb_count : allStVerbs.length = 10 := rfl

end Wood2015
