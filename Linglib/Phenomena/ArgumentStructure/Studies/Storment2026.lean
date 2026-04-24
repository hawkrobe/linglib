import Linglib.Phenomena.ArgumentStructure.Unaccusativity.Data
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Interfaces.SyntaxSemantics.VerbSmuggling
import Linglib.Theories.Syntax.Minimalism.Voice
import Linglib.Theories.Syntax.Minimalism.Movement.Smuggling
import Linglib.Theories.Syntax.Minimalism.Movement.InverseVoice
import Linglib.Theories.Syntax.Minimalism.Probing.DefectiveCircumvention
import Linglib.Phenomena.AuxiliaryVerbs.Selection

/-!
# Quotative Inversion as Smuggling
@cite{storment-2026}

Formalizes @cite{storment-2026}: the smuggling derivation of quotative
inversion in English and Setswana.

## Storment's central claims

- **§2 + §3**: In QI clauses (`"Hello," said Mary`), the VP containing
  the quote moves to a position above the agentive AGENT, which remains
  in-situ in Spec,vP. Evidence: agreement, parasitic gaps, raising,
  conjoint/disjoint marking in Setswana.
- **§4**: This is **smuggling** (@cite{collins-2005}): the VP moves to
  Spec,VoiceP, making the theme accessible to T⁰ for Case licensing.
  The smuggling projection is identified as VoiceP, which is *not* the
  external-argument-introducing head (departing from
  @cite{kratzer-1996}/Pylkkänen).
- **§5**: The transitivity constraint — QI is blocked when multiple DPs
  compete for Case licensing — falls out from the Case-licensing
  configuration after smuggling.
- **§6**: Locative inversion shares the same mechanism. QI and LI are
  both nonactive inverse-voice constructions.

## Cross-paper meta-bridges (live elsewhere per CLAUDE.md convention)

The following comparisons are the formalizer's synthesis, not Storment's
claims. They live in topic-named files alongside this study:

- `../Unaccusativity/ProtoRoles.lean` — Dowty proto-role profiles vs.
  Storment's QI-based unaccusativity classification (the MoS divergence)
- `../Unaccusativity/VerbClasses.lean` — Levin verb classes vs. the QI
  classification (alignment + the §37.3 within-class split)
- `../Unaccusativity/IslandSensitivity.lean` — @cite{storment-2026}'s
  smuggling-licenses-QI prediction vs. @cite{lu-pan-degen-2025}'s
  discourse-sourced MoS island finding (compatibility, not contradiction)
-/

namespace Phenomena.ArgumentStructure.Unaccusativity.Bridge

open Core.Verbs
open Fragments.English.Predicates.Verbal
open Phenomena.ArgumentStructure.Unaccusativity.Data
open Phenomena.AuxiliaryVerbs.Selection (TransitivityClass canonicalSelection)
open Minimalism (VoiceFlavor VoiceHead voiceAnticausative voiceAgent)

/-! ## §1 + §2. Lexical annotations and QI data

Per @cite{storment-2026}, every MoS verb passes the QI diagnostic and
is classified unaccusative; the canonical communication verbs `speak`/
`talk` fail QI and are unergative. Quantified theorems collapse the
per-verb pattern; specific instances are recoverable by `fin_cases`. -/

/-- MoS verbs annotated unaccusative on the basis of the QI diagnostic. -/
def mosUnaccusatives : List VerbEntry :=
  [whisper, murmur, shout, cry, scream, mumble, mutter,
   shriek, yell, groan, grumble, hiss, sigh, whimper, snap]

/-- Canonical unergative communication verbs that fail QI. -/
def communicationUnergatives : List VerbEntry := [speak, talk]

theorem mos_unaccusatives_annotated :
    ∀ v ∈ mosUnaccusatives, v.unaccusative = true := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_annotated :
    ∀ v ∈ communicationUnergatives, v.unaccusative = false := by
  intro v hv; fin_cases hv <;> rfl

theorem seem_unaccusative : seem.unaccusative = true := rfl
theorem arrive_unaccusative : arrive.unaccusative = true := rfl

/-! ## §3. TransitivityClass derivation

Maps a `VerbCore` to its three-way transitivity classification used by
the auxiliary-selection system (`Phenomena/AuxiliaryVerbs/Selection.lean`).
Stays in this study file because `TransitivityClass` lives in `Phenomena/`
and cannot be imported by `Theories/`. -/

/-- Derive `TransitivityClass` from `VerbCore` fields. -/
def deriveTransitivityClass (v : VerbCore) : TransitivityClass :=
  if v.unaccusative then .unaccusative
  else match v.complementType with
    | .none => .unergative
    | _ => .transitive

theorem mos_unaccusatives_transitivity :
    ∀ v ∈ mosUnaccusatives,
      deriveTransitivityClass v.toVerbCore = .unaccusative := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_transitivity :
    ∀ v ∈ communicationUnergatives,
      deriveTransitivityClass v.toVerbCore = .unergative := by
  intro v hv; fin_cases hv <;> rfl

theorem kick_transitive : deriveTransitivityClass kick.toVerbCore = .transitive := rfl

/-! ## §4. Voice bridge

`VerbCore.voiceFor` (defined in `Theories/Interfaces/SyntaxSemantics/
VerbSmuggling.lean`) maps unaccusative→non-thematic Voice and
unergative→agentive Voice. Per @cite{storment-2026}'s §4.3, the Voice
head is the smuggling projection (not the external-argument introducer
of @cite{kratzer-1996}); permitting smuggling is equivalent to being
non-phase, which is equivalent to not introducing an external argument. -/

theorem mos_unaccusatives_nonThematic_voice :
    ∀ v ∈ mosUnaccusatives, v.toVerbCore.voiceFor = voiceAnticausative := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_agentive_voice :
    ∀ v ∈ communicationUnergatives, v.toVerbCore.voiceFor = voiceAgent := by
  intro v hv; fin_cases hv <;> rfl

/-! ## §5. Auxiliary selection bridge

In split-auxiliary languages (Italian, French, German), unaccusatives
select *be* and unergatives select *have*. -/

theorem mos_unaccusatives_select_be :
    ∀ v ∈ mosUnaccusatives,
      canonicalSelection (deriveTransitivityClass v.toVerbCore) = .be := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_select_have :
    ∀ v ∈ communicationUnergatives,
      canonicalSelection (deriveTransitivityClass v.toVerbCore) = .have := by
  intro v hv; fin_cases hv <;> rfl

/-! ## §6. Levin §37.3 mannerOfSpeaking class membership

Pure data — the divergence and within-class split analysis lives in
`../Unaccusativity/VerbClasses.lean`. -/

theorem whisper_levinClass : whisper.levinClass = some .mannerOfSpeaking := rfl
theorem speak_levinClass : speak.levinClass = some .mannerOfSpeaking := rfl

/-! ## §8. Smuggling derivation of QI

`VerbCore.derivedQI` (defined in `Theories/Interfaces/SyntaxSemantics/
VerbSmuggling.lean`) derives QI licensing from two independently
motivated properties: (1) Voice is non-phase (= unaccusative);
(2) verb has a complement (the quote).

These two properties are then verified against the empirical QI
diagnostic data: every MoS unaccusative with a complement is correctly
predicted to license QI; agentive `speak`/`talk` is correctly predicted
to block QI; unaccusative `arrive` (no complement) is correctly
predicted not to license QI (it requires LI, not QI). -/

theorem mos_unaccusatives_derivedQI :
    ∀ v ∈ mosUnaccusatives, v.toVerbCore.derivedQI = true := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_derivedQI :
    ∀ v ∈ communicationUnergatives, v.toVerbCore.derivedQI = false := by
  intro v hv; fin_cases hv <;> rfl

/-- `arrive` is unaccusative but has no complement: doesn't license QI.
    This is correct — `*"arrived Mary"` requires a fronted locative
    (LI), not a fronted quote (QI). -/
theorem arrive_no_qi : arrive.toVerbCore.derivedQI = false := rfl

/-- Consistency: each (verb, QI-datum) pair has its empirical result
    matching `derivedQI`. Pairs the diagnostic data in
    `Unaccusativity/Data.lean` with the smuggling prediction. -/
theorem qi_data_matches_derivedQI :
    ∀ p ∈ ([(qi_whisper,    whisper.toVerbCore),
            (qi_murmur,     murmur.toVerbCore),
            (qi_shout,      shout.toVerbCore),
            (qi_cry,        cry.toVerbCore),
            (qi_scream,     scream.toVerbCore),
            (qi_mumble,     mumble.toVerbCore),
            (qi_mutter,     mutter.toVerbCore),
            (qi_shriek,     shriek.toVerbCore),
            (qi_yell,       yell.toVerbCore),
            (qi_groan,      groan.toVerbCore),
            (qi_grumble,    grumble.toVerbCore),
            (qi_hiss,       hiss.toVerbCore),
            (qi_sigh,       sigh.toVerbCore),
            (qi_whimper,    whimper.toVerbCore),
            (qi_snap,       snap.toVerbCore),
            (qi_speak,      speak.toVerbCore),
            (qi_talk,       talk.toVerbCore)] :
            List (DiagnosticDatum × VerbCore)),
      (p.1.result = .passes) ↔ (p.2.derivedQI = true) := by
  intro p hp; fin_cases hp <;> decide

/-! ## §9. QI ∥ LI distributional contrasts (Storment §6)

Storment §6: QI and LI share the smuggling mechanism but differ in
their inputs (quote vs. locative PP) and distribution. Both are subject
to the transitivity constraint (§5). The shared inverse-voice family
membership is captured by `Minimalism.qiCanonical` and `liCanonical` in
`Theories/Syntax/Minimalism/Movement/InverseVoice.lean`. -/

/-- whisper passes QI but is only marginal in LI — same mechanism
    (smuggling), different inputs. -/
theorem qi_li_diverge_on_whisper :
    qi_whisper.result = .passes ∧ loc_whisper.result = .marginal :=
  ⟨rfl, rfl⟩

/-- The transitivity constraint (§5): QI is blocked with multiple DP
    arguments (using `warn` per Storment eq. 125, naturally
    ditransitive); QI is fine with a quote + PP goal. -/
theorem qi_transitivity_constraint :
    qi_warn_double_obj.result = .fails ∧
    qi_whisper_transitive.result = .passes :=
  ⟨rfl, rfl⟩

/-- LI categorically blocks pronominal subjects; QI merely degrades them. -/
theorem li_vs_qi_pronouns :
    li_arrive_pronoun.result = .fails ∧
    qi_whisper_pronoun.result = .marginal :=
  ⟨rfl, rfl⟩

/-- LI blocks transitive verbs, just as QI does. -/
theorem li_blocks_transitive : li_kick.result = .fails := rfl

/-- Unified smuggling analysis (§6): LI with `arrive` works because
    arrive projects non-thematic Voice, permitting VP-smuggling — the
    same mechanism that licenses QI. -/
theorem li_arrive_smuggling_unified :
    arrive.toVerbCore.voiceFor = voiceAnticausative ∧
    loc_arrive.result = .passes :=
  ⟨rfl, rfl⟩

/-! ## §11 + §12. The QI derivation (Storment §3 + §4)

The smuggling derivation assigns each major constituent to a structural
position. Each position predicts observable consequences tested against
the §3 structural-evidence data.

**Quote vs. quotative operator** (Storment §3.5, eq. 103). The quote
itself is *not* in the syntactic derivation — it may be totally absent
from QI clauses (`Says me!`). What sits in Spec,TP is a *null quotative
operator* (the THEME), bound by a `Discourse⁰[QUOT]` head in DiscourseP.
The fields below distinguish the operator's landing site (Spec,TP) from
the quote's binding head (DiscourseP). -/

/-- Structural position in the QI derivation. -/
inductive QIPosition where
  | specTP       -- A-movement landing site (theme/operator)
  | specVoiceP   -- VP's smuggling landing site
  | specvP       -- Agent's in-situ position
  | discourseQUOT -- DiscourseP head bearing [QUOT] feature (binds operator)
  deriving DecidableEq, Repr

/-- The QI derivation assigns four major constituents to structural
    positions. Note that `quoteBinder` is the binding *head* in
    DiscourseP, not the quote itself (which is not in the syntax —
    Storment §3.5). -/
structure QIDerivation where
  themePosition : QIPosition          -- null quotative operator's landing site
  agentPosition : QIPosition          -- in-situ
  vpPosition : QIPosition             -- smuggled-to position
  quoteBinder : QIPosition            -- binding head, not the quote itself
  deriving Repr, BEq

/-- Storment's smuggling derivation of QI. -/
def qiSmuggling : QIDerivation where
  themePosition := .specTP
  agentPosition := .specvP
  vpPosition := .specVoiceP
  quoteBinder := .discourseQUOT

/-! Each structural position predicts an observable property. We verify
each prediction against the §3 data. The bridge theorems below pair
the position assignment (Storment's claim) with the empirical observation
(also Storment's claim). -/

open Phenomena.ArgumentStructure.Unaccusativity.Data (QIStructuralDatum)

/-- Theme-as-operator in Spec,TP → agreement can track agent via
    defective circumvention (§3.1). -/
theorem theme_specTP_agreement :
    qiSmuggling.themePosition = .specTP ∧
    qi_agreement_english.result = .passes :=
  ⟨rfl, rfl⟩

/-- Theme-as-operator is phi-deficient → Setswana SM surfaces as
    default SM17 (§3.1). -/
theorem theme_specTP_setswana_sm17 :
    qiSmuggling.themePosition = .specTP ∧
    qi_agreement_setswana.result = .passes :=
  ⟨rfl, rfl⟩

/-- Theme-as-operator A-moves → cannot license parasitic gaps (§3.2). -/
theorem theme_specTP_no_parasitic_gap :
    qiSmuggling.themePosition = .specTP ∧
    qi_parasitic_gap_blocked.result = .fails :=
  ⟨rfl, rfl⟩

/-- Theme-as-operator A-moves → compatible with subject-to-subject
    raising (§3.3). -/
theorem theme_specTP_raising :
    qiSmuggling.themePosition = .specTP ∧
    qi_raising.result = .passes :=
  ⟨rfl, rfl⟩

/-- Agent in Spec,vP → Setswana disjoint morpheme blocked (§3.4). -/
theorem agent_specvP_conjoint :
    qiSmuggling.agentPosition = .specvP ∧
    qi_conjoint_disjoint.result = .fails :=
  ⟨rfl, rfl⟩

/-- Quote (separately from operator) bound by Discourse⁰[QUOT] → can
    split around verb + agent, need not be grammatical (§3.5). -/
theorem quote_discourseQUOT_split :
    qiSmuggling.quoteBinder = .discourseQUOT ∧
    qi_quote_split.result = .passes ∧
    qi_quote_nongrammatical.result = .passes :=
  ⟨rfl, rfl, rfl⟩

/-- VP smuggling predicts: VP-internal material (complements) precedes
    Agent; vP-external material (adjuncts) follows Agent (§2). -/
theorem vp_smuggling_ordering :
    qiSmuggling.vpPosition = .specVoiceP ∧
    qi_ordering_complement.result = .passes ∧
    qi_ordering_depictive.result = .passes ∧
    qi_ordering_manner.result = .passes ∧
    qi_ordering_purpose.result = .passes :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §13. Inverse-voice family membership

QI is one instance of the inverse-voice family (§4.3 + §6 + §7). The
canonical instance lives in `Theories/Syntax/Minimalism/Movement/
InverseVoice.lean`; here we just affirm membership. -/

theorem qi_is_inverse_voice :
    Minimalism.qiCanonical.kind = .quotativeInversion ∧
    Minimalism.qiCanonical.licensed = true :=
  ⟨rfl, rfl⟩

theorem qi_li_share_voice :
    Minimalism.qiCanonical.voice = Minimalism.liCanonical.voice :=
  rfl

/-! ## §14. Defective circumvention derives the agreement contrast

Storment §3.1.4 (eq. 59): the difference between Setswana QI agreement
(always SM17 default) and English QI agreement (optionally tracks the
postverbal agent) reduces to a single parameter — whether the probe T⁰
is allowed to re-probe past the defective quotative-theme operator. The
defective-circumvention operation is in `Theories/Syntax/Minimalism/
Probing/DefectiveCircumvention.lean`; here we wire it to the QI
agreement data.

The theorems abstract over the precise feature bundles and feature-
compatibility predicate — Storment's substantive claim is that the
*operation* is the same and only the `allowReprobe` parameter varies. -/

open Minimalism.Probing
open Minimalism (FeatureBundle)

/-- The same defective-probing situation produces Setswana's
    obligatory default agreement (no re-probe) and English's optional
    agent-tracking agreement (re-probe with compatible features) — a
    single Bool parameter accounts for the cross-linguistic split. -/
theorem setswana_vs_english_reduces_to_reprobe
    (probe alpha beta : FeatureBundle)
    (compat : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compat alpha beta = true) :
    defectiveCircumvention probe alpha beta false compat = .defaultAgreement ∧
    defectiveCircumvention probe alpha beta true  compat = .trackLower :=
  ⟨defectiveCircumvention_default_when_no_reprobe _ _ _ _ hd,
   defectiveCircumvention_tracks_lower _ _ _ _ hd hc⟩

/-- Storment's English-specific prediction: a 1st/2nd person agent
    (whose phi-features clash with the defective theme's [3]) cannot
    license re-probe — `*"What do we do now?" ask we`. The derivation
    crashes on feature incompatibility (eq. 46, page 14). -/
theorem english_qi_clash_on_incompatible_agent
    (probe alpha beta : FeatureBundle)
    (compat : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compat alpha beta = false) :
    defectiveCircumvention probe alpha beta true compat = .featureClash :=
  defectiveCircumvention_clash_on_incompatible _ _ _ _ hd hc

end Phenomena.ArgumentStructure.Unaccusativity.Bridge
