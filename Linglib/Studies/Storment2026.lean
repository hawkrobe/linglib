import Linglib.Data.Examples.Storment2026
import Linglib.Data.Examples.LevinRappaportHovav1995
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Semantics.Lexical.VerbSmuggling
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Movement.Smuggling
import Linglib.Syntax.Minimalist.Movement.InverseVoice
import Linglib.Syntax.Minimalist.Features
import Linglib.Semantics.ArgumentStructure.AuxiliarySelection

/-!
# Quotative Inversion as Smuggling
[storment-2026]

Formalizes [storment-2026]: the smuggling derivation of quotative
inversion in English and Setswana.

## Storment's central claims

- **§2 + §3**: In QI clauses (`"Hello," said Mary`), the VP containing
  the quote moves to a position above the agentive AGENT, which remains
  in-situ in Spec,vP. Evidence: agreement, parasitic gaps, raising,
  conjoint/disjoint marking in Setswana.
- **§4**: This is **smuggling** ([collins-2005]): the VP moves to
  Spec,VoiceP, making the theme accessible to T⁰ for Case licensing.
  The smuggling projection is identified as VoiceP, which is *not* the
  external-argument-introducing head (departing from
  [kratzer-1996]/Pylkkänen).
- **§5**: The transitivity constraint — QI is blocked when multiple DPs
  compete for Case licensing — falls out from the Case-licensing
  configuration after smuggling.
- **§6**: Locative inversion shares the same mechanism. QI and LI are
  both nonactive inverse-voice constructions.

Example rows live in `Data/Examples/Storment2026.json` (QI/LI data) and
`Data/Examples/LevinRappaportHovav1995.json` (classic locative-inversion
diagnostics).
-/

namespace Storment2026

open Semantics.Lexical
open English.Predicates.Verbal
open Data.Examples
open ArgumentStructure.AuxiliarySelection (TransitivityClass canonicalSelection)
open Minimalist (Voice.Flavor Voice.Head Voice.anticausative Voice.agentive)

/-! ## §1 + §2. Lexical annotations and QI data

Per [storment-2026], every MoS verb passes the QI diagnostic and
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

Maps a `Verb` to the three-way transitivity classification used by
the auxiliary-selection substrate (`Typology/AuxiliaryVerbs.lean`). -/

/-- Derive `TransitivityClass` from `Verb` fields. -/
def deriveTransitivityClass (v : Verb) : TransitivityClass :=
  if v.unaccusative then .unaccusative
  else match v.complementType with
    | .none => .unergative
    | _ => .transitive

theorem mos_unaccusatives_transitivity :
    ∀ v ∈ mosUnaccusatives,
      deriveTransitivityClass v.toVerb = .unaccusative := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_transitivity :
    ∀ v ∈ communicationUnergatives,
      deriveTransitivityClass v.toVerb = .unergative := by
  intro v hv; fin_cases hv <;> rfl

theorem kick_transitive : deriveTransitivityClass kick.toVerb = .transitive := rfl

/-! ## §4. Voice bridge

`Verb.voiceFor` (defined in `Semantics/Lexical/VerbSmuggling.lean`)
maps unaccusative→non-thematic Voice and
unergative→agentive Voice. Per [storment-2026]'s §4.3, the Voice
head is the smuggling projection (not the external-argument introducer
of [kratzer-1996]); permitting smuggling is equivalent to being
non-phase, which is equivalent to not introducing an external argument. -/

theorem mos_unaccusatives_nonThematic_voice :
    ∀ v ∈ mosUnaccusatives, v.toVerb.voiceFor = Voice.anticausative := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_agentive_voice :
    ∀ v ∈ communicationUnergatives, v.toVerb.voiceFor = Voice.agentive := by
  intro v hv; fin_cases hv <;> rfl

/-! ## §5. Auxiliary selection bridge

In split-auxiliary languages (Italian, French, German), unaccusatives
select *be* and unergatives select *have*. -/

theorem mos_unaccusatives_select_be :
    ∀ v ∈ mosUnaccusatives,
      canonicalSelection (deriveTransitivityClass v.toVerb) = .be := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_select_have :
    ∀ v ∈ communicationUnergatives,
      canonicalSelection (deriveTransitivityClass v.toVerb) = .have := by
  intro v hv; fin_cases hv <;> rfl

/-! ## §6. Levin §37.3 mannerOfSpeaking class membership

Pure data — the divergence and within-class split analysis lives in
`../Unaccusativity/VerbClasses.lean`. -/

theorem whisper_levinClass : whisper.levinClass = some .mannerOfSpeaking := rfl
theorem speak_levinClass : speak.levinClass = some .mannerOfSpeaking := rfl

/-! ## §8. Smuggling derivation of QI

`Verb.derivedQI` (defined in `Semantics/Lexical/VerbSmuggling.lean`)
derives QI licensing from two independently
motivated properties: (1) Voice is non-phase (= unaccusative);
(2) verb has a complement (the quote).

These two properties are then verified against the empirical QI
diagnostic data: every MoS unaccusative with a complement is correctly
predicted to license QI; agentive `speak`/`talk` is correctly predicted
to block QI; unaccusative `arrive` (no complement) is correctly
predicted not to license QI (it requires LI, not QI). -/

theorem mos_unaccusatives_derivedQI :
    ∀ v ∈ mosUnaccusatives, v.toVerb.derivedQI = true := by
  intro v hv; fin_cases hv <;> rfl

theorem communication_unergatives_derivedQI :
    ∀ v ∈ communicationUnergatives, v.toVerb.derivedQI = false := by
  intro v hv; fin_cases hv <;> rfl

/-- `arrive` is unaccusative but has no complement: doesn't license QI.
    This is correct — `*"arrived Mary"` requires a fronted locative
    (LI), not a fronted quote (QI). -/
theorem arrive_no_qi : arrive.toVerb.derivedQI = false := rfl

/-- Consistency: each (QI row, verb) pair has its judgment matching
    `derivedQI`. Pairs the rows of `Data/Examples/Storment2026.json`
    with the smuggling prediction. -/
theorem qi_data_matches_derivedQI :
    ∀ p ∈ ([(Examples.qi_whisper,    whisper.toVerb),
            (Examples.qi_murmur,     murmur.toVerb),
            (Examples.qi_shout,      shout.toVerb),
            (Examples.qi_cry,        cry.toVerb),
            (Examples.qi_scream,     scream.toVerb),
            (Examples.qi_mumble,     mumble.toVerb),
            (Examples.qi_mutter,     mutter.toVerb),
            (Examples.qi_shriek,     shriek.toVerb),
            (Examples.qi_yell,       yell.toVerb),
            (Examples.qi_groan,      groan.toVerb),
            (Examples.qi_grumble,    grumble.toVerb),
            (Examples.qi_hiss,       hiss.toVerb),
            (Examples.qi_sigh,       sigh.toVerb),
            (Examples.qi_whimper,    whimper.toVerb),
            (Examples.qi_snap,       snap.toVerb),
            (Examples.qi_speak,      speak.toVerb),
            (Examples.qi_talk,       talk.toVerb)] :
            List (LinguisticExample × Verb)),
      (p.1.judgment = .acceptable) ↔ (p.2.derivedQI = true) := by
  intro p hp; fin_cases hp <;> decide

/-! ## §9. QI ∥ LI distributional contrasts (Storment §6)

Storment §6: QI and LI share the smuggling mechanism but differ in
their inputs (quote vs. locative PP) and distribution. Both are subject
to the transitivity constraint (§5). The shared inverse-voice family
membership is captured by `Minimalist.qiCanonical` and `liCanonical` in
`Syntax/Minimalism/Movement/InverseVoice.lean`. -/

/-- whisper passes QI but is only marginal in LI — same mechanism
    (smuggling), different inputs. -/
theorem qi_li_diverge_on_whisper :
    Examples.qi_whisper.judgment = .acceptable ∧
    LevinRappaportHovav1995.Examples.loc_whisper.judgment = .marginal :=
  ⟨rfl, rfl⟩

/-- The transitivity constraint (§5): QI is blocked with multiple DP
    arguments (using `warn` per Storment eq. 125, naturally
    ditransitive); QI is fine with a quote + PP goal. -/
theorem qi_transitivity_constraint :
    Examples.qi_warn_double_obj.judgment = .unacceptable ∧
    Examples.qi_whisper_transitive.judgment = .acceptable :=
  ⟨rfl, rfl⟩

/-- LI categorically blocks pronominal subjects; QI merely degrades them. -/
theorem li_vs_qi_pronouns :
    Examples.li_arrive_pronoun.judgment = .unacceptable ∧
    Examples.qi_whisper_pronoun.judgment = .marginal :=
  ⟨rfl, rfl⟩

/-- LI blocks transitive verbs, just as QI does. -/
theorem li_blocks_transitive : Examples.li_kick.judgment = .unacceptable := rfl

/-- Unified smuggling analysis (§6): LI with `arrive` works because
    arrive projects non-thematic Voice, permitting VP-smuggling — the
    same mechanism that licenses QI. -/
theorem li_arrive_smuggling_unified :
    arrive.toVerb.voiceFor = Voice.anticausative ∧
    LevinRappaportHovav1995.Examples.loc_arrive.judgment = .acceptable :=
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
each prediction against the §3 rows. The bridge theorems below pair
the position assignment (Storment's claim) with the empirical observation
(also Storment's claim). -/

/-- Theme-as-operator in Spec,TP → agreement can track agent via
    defective circumvention (§3.1). -/
theorem theme_specTP_agreement :
    qiSmuggling.themePosition = .specTP ∧
    Examples.qi_agreement_english.judgment = .acceptable :=
  ⟨rfl, rfl⟩

/-- Theme-as-operator is phi-deficient → Setswana SM surfaces as
    default SM17 (§3.1). -/
theorem theme_specTP_setswana_sm17 :
    qiSmuggling.themePosition = .specTP ∧
    Examples.qi_agreement_setswana.judgment = .acceptable :=
  ⟨rfl, rfl⟩

/-- Theme-as-operator A-moves → cannot license parasitic gaps, unlike
    the A-bar-moved preposed quote of the non-QI baseline (§3.2). -/
theorem theme_specTP_no_parasitic_gap :
    qiSmuggling.themePosition = .specTP ∧
    Examples.qi_parasitic_gap_blocked.judgment = .unacceptable ∧
    Examples.qi_parasitic_gap_baseline.judgment = .acceptable :=
  ⟨rfl, rfl, rfl⟩

/-- Theme-as-operator A-moves → compatible with subject-to-subject
    raising (§3.3). -/
theorem theme_specTP_raising :
    qiSmuggling.themePosition = .specTP ∧
    Examples.qi_raising.judgment = .acceptable :=
  ⟨rfl, rfl⟩

/-- Agent in Spec,vP → Setswana disjoint morpheme blocked (§3.4). -/
theorem agent_specvP_conjoint :
    qiSmuggling.agentPosition = .specvP ∧
    Examples.qi_conjoint_disjoint.judgment = .unacceptable :=
  ⟨rfl, rfl⟩

/-- Quote (separately from operator) bound by Discourse⁰[QUOT] → can
    split around verb + agent, need not be grammatical (§3.5). -/
theorem quote_discourseQUOT_split :
    qiSmuggling.quoteBinder = .discourseQUOT ∧
    Examples.qi_quote_split.judgment = .acceptable ∧
    Examples.qi_quote_nongrammatical.judgment = .acceptable :=
  ⟨rfl, rfl, rfl⟩

/-- VP smuggling predicts: VP-internal material (complements) precedes
    Agent; vP-external material (adjuncts) follows Agent (§2). -/
theorem vp_smuggling_ordering :
    qiSmuggling.vpPosition = .specVoiceP ∧
    Examples.qi_ordering_complement.judgment = .acceptable ∧
    Examples.qi_ordering_depictive.judgment = .acceptable ∧
    Examples.qi_ordering_manner.judgment = .acceptable ∧
    Examples.qi_ordering_purpose.judgment = .acceptable :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §13. Inverse-voice family membership

QI is one instance of the inverse-voice family (§4.3 + §6 + §7). The
canonical instance lives in `Syntax/Minimalism/Movement/
InverseVoice.lean`; here we just affirm membership. -/

theorem qi_is_inverse_voice :
    Minimalist.qiCanonical.kind = .quotativeInversion ∧
    Minimalist.qiCanonical.licensed = true :=
  ⟨rfl, rfl⟩

theorem qi_li_share_voice :
    Minimalist.qiCanonical.voice = Minimalist.liCanonical.voice :=
  rfl

/-! ## §14. Defective circumvention derives the agreement contrast

Storment §3.1.4 (eq. 59): the difference between Setswana QI agreement
(always SM17 default) and English QI agreement (optionally tracks the
postverbal agent) reduces to a single parameter — whether the probe T⁰
is allowed to re-probe past the defective quotative-theme operator.
Roberts's *defective goal* and the *defective-circumvention* operation
are defined inline below (folded in from the former single-consumer
`Minimalist/Probing/`); the theorems then wire them to the QI data.

The theorems abstract over the precise feature bundles and feature-
compatibility predicate — Storment's substantive claim is that the
*operation* is the same and only the `allowReprobe` parameter varies. -/

open Minimalist (FeatureBundle)

/-- A goal `G` is **defective** w.r.t. a probe `P` iff `G`'s formal
    features are a proper subset of `P`'s, so checking is incomplete
    ([roberts-2010], ch. 2; eq. (49) in [storment-2026]). The feature
    comparison is over the bundles' grammatical-feature lists
    (`FeatureBundle.toGramFeatures`). -/
def DefectiveGoal (probe goal : FeatureBundle) : Prop :=
  goal.toGramFeatures ⊆ probe.toGramFeatures ∧
    ∃ f ∈ probe.toGramFeatures, f ∉ goal.toGramFeatures

instance (probe goal : FeatureBundle) : Decidable (DefectiveGoal probe goal) := by
  unfold DefectiveGoal; infer_instance

/-- The empty goal is defective w.r.t. any nonempty probe. -/
theorem DefectiveGoal.empty_of_nonempty (probe : FeatureBundle)
    (h : probe ≠ ⊥) : DefectiveGoal probe ⊥ := by
  refine ⟨List.nil_subset _, ?_⟩
  have hne : probe.toGramFeatures ≠ [] := by
    intro he
    refine h (funext λ t => ?_)
    have hnone := (List.filterMap_eq_nil_iff.mp he) t (by cases t <;> decide)
    cases hp : probe t with
    | absent => rfl
    | unvalued => rw [hp] at hnone; exact absurd hnone (by simp)
    | valued v => rw [hp] at hnone; exact absurd hnone (by simp)
  match hp : probe.toGramFeatures, hne with
  | f :: _, _ => exact ⟨f, List.mem_cons_self, List.not_mem_nil⟩

/-- A defective goal is missing some feature the probe has. -/
theorem DefectiveGoal.exists_missing {probe goal : FeatureBundle}
    (h : DefectiveGoal probe goal) :
    ∃ f ∈ probe.toGramFeatures, f ∉ goal.toGramFeatures := h.2

/-- A defective goal's features are all in the probe. -/
theorem DefectiveGoal.subset {probe goal : FeatureBundle}
    (h : DefectiveGoal probe goal) :
    goal.toGramFeatures ⊆ probe.toGramFeatures := h.1

/-- No goal is defective w.r.t. itself. -/
theorem DefectiveGoal.irrefl (fb : FeatureBundle) : ¬ DefectiveGoal fb fb := by
  intro ⟨_, f, hf, hnf⟩; exact hnf hf

/-- The four outcomes of a probe that may invoke defective circumvention
    ([storment-2025] ch. 2; eq. 59 in [storment-2026]): the probe Agrees
    with a higher defective goal α, then conditionally re-probes past α
    to a lower, more specified goal β. -/
inductive ProbingOutcome where
  /-- α was not defective; α suffices, no re-probe. -/
  | trackHigher
  /-- α defective; re-probe disallowed; default features spell out. -/
  | defaultAgreement
  /-- α defective; re-probe to β succeeded (features compatible). -/
  | trackLower
  /-- α defective; re-probe to β attempted but features conflict; crash. -/
  | featureClash
  deriving DecidableEq, Repr

/-- Defective-circumvention probing, parameterized by `allowReprobe`
    (may the probe search past a defective goal) and `compatible`
    (can circumvention complete without feature conflict). -/
def defectiveCircumvention
    (probe alpha beta : FeatureBundle) (allowReprobe : Bool)
    (compatible : FeatureBundle → FeatureBundle → Bool) : ProbingOutcome :=
  if DefectiveGoal probe alpha then
    if allowReprobe then
      (if compatible alpha beta then .trackLower else .featureClash)
    else .defaultAgreement
  else .trackHigher

/-- A non-defective higher goal never invokes circumvention. -/
theorem defectiveCircumvention_trackHigher_of_nondefective
    (probe alpha beta : FeatureBundle) (allowReprobe : Bool)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (h : ¬ DefectiveGoal probe alpha) :
    defectiveCircumvention probe alpha beta allowReprobe compatible = .trackHigher := by
  unfold defectiveCircumvention; simp [h]

/-- Defective higher goal, re-probe disallowed → default agreement
    (Setswana case). -/
theorem defectiveCircumvention_default_when_no_reprobe
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) :
    defectiveCircumvention probe alpha beta false compatible = .defaultAgreement := by
  unfold defectiveCircumvention; simp [hd]

/-- Defective higher goal, re-probe allowed, β compatible → tracks β
    (English `advise the dieticians`). -/
theorem defectiveCircumvention_tracks_lower
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compatible alpha beta = true) :
    defectiveCircumvention probe alpha beta true compatible = .trackLower := by
  unfold defectiveCircumvention; simp [hd, hc]

/-- Defective higher goal, re-probe allowed, β incompatible → crash
    (English `*ask we`). -/
theorem defectiveCircumvention_clash_on_incompatible
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compatible alpha beta = false) :
    defectiveCircumvention probe alpha beta true compatible = .featureClash := by
  unfold defectiveCircumvention; simp [hd, hc]

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

end Storment2026
