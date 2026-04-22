import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Fragments.Mayan.Mam.VoiceSystem
import Linglib.Theories.Syntax.Minimalism.Agree
import Linglib.Theories.Interfaces.SyntaxPhonology.Minimalism.Spellout
import Linglib.Theories.Syntax.Minimalism.ObligatoryOperations
import Linglib.Theories.Morphology.DM.Impoverishment

/-!
# Minimalism Agree-Conditioned Pronoun Spellout in Mam

@cite{scott-2023} @cite{chomsky-2000} @cite{deal-2024} @cite{elkins-torrence-brown-2026} @cite{preminger-2014}

Connects the Agree operation (feature valuation) and probe restriction to the empirical distribution of overt vs.
reduced pronouns in SJA Mam.

## The Derivation

In a Mam transitive clause with a 3SG agent and 3SG patient:

1. **Voice probes for φ**: Voice has [uPerson, uNumber]. It Agrees with
   the agent in Spec,VoiceP, valuing [Person:3, Number:sg]. Voice also
   assigns inherent ERG case to the agent. The valued φ-features spell
   out as Set A "t-" on Voice.

2. **Infl probes for φ**: Infl has a φ-probe with a disjunctive
   satisfaction condition [SAT: φ or Voice_TR].
   In a transitive clause, the probe encounters transitive Voice and
   **stops** — no φ-features are copied to Infl. The Set B slot is
   filled by the Elsewhere form "tz'=" (default 2/3SG).

3. **Object is case-licensed by Voice**: The patient receives structural
   ACC from Voice (low-abs syntax; @cite{scott-2023}, §3.4). Infl's probe
   never reaches the object because it was satisfied by Voice_TR.

4. **Pronoun realization follows**: Agreed-with arguments (agent, S)
   undergo pronoun reduction — agreement morphology redundantly
   expresses their φ-features, triggering deletion of the pronominal
   base (@cite{scott-2023}, ch. 4). The patient, lacking φ-agreement, must
   be a full overt pronoun.

## Two Paths to Set B "tz'="

A key insight of Scott's analysis is that the same Set B form "tz'=" arises
via two distinct mechanisms:

- **Intransitive**: Infl's probe succeeds, copies S's φ-features
  (e.g., [3SG]) → no more specific Set B entry matches → Elsewhere
  "tz'=" is selected.
- **Transitive**: Infl's probe is blocked by Voice_TR → no φ-features
  on Infl → Elsewhere "tz'=" is selected.

Both yield "tz'=", but the intransitive case involves real agreement while
the transitive case involves probe failure. This bridge demonstrates
both paths.

-/

namespace Scott2023

open Minimalism Fragments.Mayan.Mam

-- ============================================================================
-- § 0: Minimalism-Specific Vocabulary (Set A / Set B as VI entries)
-- ============================================================================

/-! These Vocabulary Insertion entries encode the Fragment's theory-neutral
    marker tables as Minimalism feature bundles, enabling the Agree → Spellout
    pipeline. The Fragment (`Agreement.lean`) stores the markers as simple
    person × number → string tables; here they are parameterized by
    `FeatureBundle` and `Cat` for use with `spellout`. -/

/-- Set A (ERG) vocabulary entries: φ-features on Voice (.v)
    yield the morphological exponent (@cite{scott-2023}, Table 2.8). -/
def setAVocab : Vocabulary :=
  [ { features := [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
    , exponent := "n-/w-"
    , context := some .v }
  , { features := [.valued (.phi (.person .second)), .valued (.phi (.number .sg))]
    , exponent := "t-"
    , context := some .v }
  , { features := [.valued (.phi (.person .third)), .valued (.phi (.number .sg))]
    , exponent := "t-"
    , context := some .v }
  , { features := [.valued (.phi (.person .first)), .valued (.phi (.number .pl))]
    , exponent := "q-"
    , context := some .v }
  , { features := [.valued (.phi (.person .second)), .valued (.phi (.number .pl))]
    , exponent := "ky-"
    , context := some .v }
  , { features := [.valued (.phi (.person .third)), .valued (.phi (.number .pl))]
    , exponent := "ky-"
    , context := some .v } ]

/-- Set B (ABS) vocabulary entries: φ-features on Infl (.T)
    yield the morphological exponent (@cite{scott-2023}, Table 3.5).
    The Elsewhere entry (no features, tz'=) surfaces when no more
    specific entry matches. -/
def setBVocab : Vocabulary :=
  [ { features := [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
    , exponent := "chin"
    , context := some .T }
  , { features := [.valued (.phi (.person .first)), .valued (.phi (.number .pl))]
    , exponent := "qo"
    , context := some .T }
  , { features := [.valued (.phi (.person .second)), .valued (.phi (.number .pl))]
    , exponent := "chi"
    , context := some .T }
  , { features := [.valued (.phi (.person .third)), .valued (.phi (.number .pl))]
    , exponent := "chi"
    , context := some .T }
  -- Elsewhere: default 2/3SG (tz'=)
  , { features := []
    , exponent := "tz'="
    , context := some .T } ]

/-- Which Minimalist head φ-Agrees with each argument position. -/
def agreeProbe : MamArgPosition → Option Cat
  | .agent   => some .v   -- Voice probes, agent in Spec,VoiceP
  | .patient => none      -- Infl probe blocked by Voice_TR
  | .intranS => some .T   -- Infl probes, S in its domain

-- ============================================================================
-- § 1: Probe Feature Bundles
-- ============================================================================

/-- Voice's probe features: [uPerson, uNumber].
    Placeholder values (.third, .sg) are irrelevant — `sameType` matching
    ensures any Person/Number goal is found regardless. -/
def voiceProbe : FeatureBundle :=
  [.unvalued (.phi (.person .third)), .unvalued (.phi (.number .sg))]

/-- Infl's probe features: [uPerson, uNumber].
    In intransitives, these are valued by S. In transitives, the probe
    is blocked by Voice_TR before reaching any DP. -/
def inflProbe : FeatureBundle :=
  [.unvalued (.phi (.person .third)), .unvalued (.phi (.number .sg))]

-- ============================================================================
-- § 2: Goal Feature Bundles (3SG test case)
-- ============================================================================

/-- A 3SG DP's features: [Person:3, Number:sg]. -/
def dp3sg : FeatureBundle :=
  [.valued (.phi (.person .third)), .valued (.phi (.number .sg))]

-- ============================================================================
-- § 3: Agree Valuation — Voice agrees with agent
-- ============================================================================

/-- Voice's [uPerson] is valued as [Person:3] from a 3SG agent. -/
theorem voice_agrees_person :
    applyAgree voiceProbe dp3sg (.phi (.person .third)) =
    some [.valued (.phi (.person .third)), .unvalued (.phi (.number .sg))] := by
  native_decide

/-- After person agreement, Voice's [uNumber] is valued as [Number:sg].
    This is the second step of φ-Agree: person first, then number. -/
theorem voice_agrees_number :
    let afterPerson := [.valued (.phi (.person .third)), .unvalued (.phi (.number .sg))]
    applyAgree afterPerson dp3sg (.phi (.number .sg)) =
    some [.valued (.phi (.person .third)), .valued (.phi (.number .sg))] := by
  native_decide

/-- Full φ-valuation of Voice by a 3SG agent: both person and number valued. -/
def voiceFullyAgreed : FeatureBundle :=
  [.valued (.phi (.person .third)), .valued (.phi (.number .sg))]

/-- The two-step Agree pipeline produces a fully valued bundle. -/
theorem voice_agree_pipeline :
    (applyAgree voiceProbe dp3sg (.phi (.person .third))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number .sg))) =
    some voiceFullyAgreed := by
  native_decide

-- ============================================================================
-- § 4: Set A Spellout — Voice → agreement morphology
-- ============================================================================

/-- Set A spellout: Voice's valued [Person:3, Number:sg] yields "t-" (A2/3SG). -/
theorem setA_spellout_3sg :
    spellout setAVocab voiceFullyAgreed (some .v) = some "t-" := by
  native_decide

/-- Set A spellout for 1SG: Voice with [Person:1, Number:sg] yields A1SG marker. -/
theorem setA_spellout_1sg :
    let v1sg : FeatureBundle :=
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
    spellout setAVocab v1sg (some .v) = some "n-/w-" := by
  native_decide

-- ============================================================================
-- § 5: Set B — Two Paths to "tz'="
-- ============================================================================

/-- **Intransitive path**: Infl Agrees with a 3SG intransitive S, copies
    [Person:3, Number:sg]. No Set B entry is specified for these features
    (1SG=chin, 1PL=qo, 2/3PL=chi — none match 3SG), so the Elsewhere
    entry is selected: "tz'=". -/
theorem setB_intransitive_3sg :
    let inflAgreed : FeatureBundle :=
      [.valued (.phi (.person .third)), .valued (.phi (.number .sg))]
    spellout setBVocab inflAgreed (some .T) = some "tz'=" := by
  native_decide

/-- **Transitive path**: Infl's probe is blocked by Voice_TR → no
    φ-features are copied → the Infl node has an empty feature bundle.
    The Elsewhere entry matches (empty features are a subset of anything)
    and "tz'=" is selected.

    This is the DEFAULT Set B — it appears in transitives regardless of
    the object's person/number features. -/
theorem setB_transitive_default :
    let inflBlocked : FeatureBundle := []
    spellout setBVocab inflBlocked (some .T) = some "tz'=" := by
  native_decide

/-- The two paths produce the same exponent — the surface form is
    identical even though the underlying mechanism differs (real agreement
    vs. probe failure). -/
theorem setB_same_surface :
    let inflAgreed3sg : FeatureBundle :=
      [.valued (.phi (.person .third)), .valued (.phi (.number .sg))]
    let inflBlocked : FeatureBundle := []
    spellout setBVocab inflAgreed3sg (some .T) =
    spellout setBVocab inflBlocked (some .T) := by
  native_decide

/-- Set B spellout for 1SG intransitive: Infl copies [Person:1, Number:sg]
    from S, yielding "chin" — NOT the Elsewhere form. This is real
    agreement, producing a distinct exponent. -/
theorem setB_intransitive_1sg :
    let t1sg : FeatureBundle :=
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
    spellout setBVocab t1sg (some .T) = some "chin" := by
  native_decide

/-- In a transitive with a 1SG object, the default "tz'=" still appears —
    NOT "chin". This is because Infl's probe was blocked by Voice_TR,
    so the object's 1SG features are never copied to Infl. -/
theorem setB_transitive_ignores_object :
    -- Even though the object is 1SG, Infl shows default "tz'=", not "chin"
    let inflBlocked : FeatureBundle := []
    spellout setBVocab inflBlocked (some .T) = some "tz'=" ∧
    -- Compare: a 1SG intransitive S would trigger "chin"
    let inflAgreed1sg : FeatureBundle :=
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
    spellout setBVocab inflAgreed1sg (some .T) = some "chin" := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 6: Probe Restriction — Why objects lack φ-agreement
-- ============================================================================

/-- Infl's probe has a disjunctive satisfaction condition [SAT: φ or
    Voice_TR]. In transitives, the probe encounters transitive Voice and
    stops before reaching any DP. This is modeled by the fact that the
    Infl node ends up with an empty feature bundle (no φ-features copied).

    In intransitives, Voice is not transitive → the probe continues →
    finds S → copies φ.

    This mechanism replaces the older
    "closest-goal intervention" account: it is NOT that the agent
    intervenes between Infl and the object, but that the probe is
    STOPPED by the VoiceP phase boundary. -/
theorem probe_restriction_yields_default :
    -- Transitive: probe blocked → empty → Elsewhere
    spellout setBVocab ([] : FeatureBundle) (some .T) = some "tz'=" ∧
    -- Intransitive 1SG: probe succeeds → "chin" (not default)
    spellout setBVocab
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
      (some .T) = some "chin" := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 7: Intransitive Pipeline — Infl Agrees with S
-- ============================================================================

/-- In an intransitive clause, Infl probes for φ and Agrees with S.
    This is REAL agreement — the probe copies S's φ-features.
    The resulting valued features spell out as Set B. -/
theorem intransitive_pipeline_1sg :
    -- Infl Agrees with 1SG S
    (applyAgree inflProbe
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
      (.phi (.person .third))).bind
      (λ fb => applyAgree fb
        [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
        (.phi (.number .sg))) =
    some [.valued (.phi (.person .first)), .valued (.phi (.number .sg))] ∧
    -- Spells out as "chin" (not default "tz'=")
    spellout setBVocab
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
      (some .T) = some "chin" := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 8: Transitive Pipeline — Voice Agrees, Infl Blocked
-- ============================================================================

/-- The complete prediction for a 3SG transitive clause:

    1. Voice Agrees with agent → [Person:3, Number:sg] on Voice
    2. [Person:3, Number:sg] on Voice spells out as Set A "t-"
    3. Infl's probe is blocked by Voice_TR → empty bundle on Infl
    4. Empty Infl spells out as Elsewhere Set B "tz'="
    5. Patient is not φ-Agreed-with → overt pronoun required -/
theorem full_pipeline_3sg_transitive :
    -- Step 1-2: Voice Agrees and spells out as Set A
    (applyAgree voiceProbe dp3sg (.phi (.person .third))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number .sg))) = some voiceFullyAgreed ∧
    spellout setAVocab voiceFullyAgreed (some .v) = some "t-" ∧
    -- Step 3-4: Infl probe blocked → default Set B
    spellout setBVocab ([] : FeatureBundle) (some .T) = some "tz'=" ∧
    -- Step 5: patient is not eligible for reduction → overt pronoun
    MamArgPosition.patient.canBeReduced = false := by
  exact ⟨by native_decide, by native_decide, by native_decide, rfl⟩

/-- The pipeline generalizes: for every argument position, the predicted
    pronoun reduction matches the observed pattern. -/
theorem all_positions_match :
    mamArgPositions.all (λ pos => pos.canBeReduced == pos.isPhiAgreed) = true := by
  native_decide

-- ============================================================================
-- § 9: Cross-Paradigm Spellout
-- ============================================================================

/-- Set A and Set B have different contexts: Set A on Voice (.v), Set B
    on Infl (.T). The same valued features produce different exponents
    depending on which head hosts them. -/
theorem setA_setB_differ_by_context :
    spellout setAVocab voiceFullyAgreed (some .v) ≠
    spellout setBVocab voiceFullyAgreed (some .v) := by
  native_decide

/-- Set A vocabulary does NOT match Infl context. -/
theorem setA_wrong_context :
    spellout setAVocab voiceFullyAgreed (some .T) = none := by
  native_decide

/-- Set B vocabulary does NOT match Voice context (for specified entries).
    Only the Elsewhere entry could match (it has no features), but it
    requires Infl context. -/
theorem setB_wrong_context :
    spellout setBVocab voiceFullyAgreed (some .v) = none := by
  native_decide

-- ============================================================================
-- § 10: The Tripartite Agreement Pattern
-- ============================================================================

/-- The three argument positions each have distinct agreement marking
    patterns, yielding morphological tripartite alignment (Scott p. 113):

    - Agent (ERG): Set A agreement from Voice
    - Intransitive S (ABS): Set B agreement from Infl
    - Patient (ACC): default Set B (Infl probe blocked)

    These three cases each have distinct underlying syntactic case values,
    assigned by different heads (Voice for ERG/ACC, Infl for ABS). -/
theorem agreement_is_tripartite :
    -- Agreed-with positions: agent (ERG, by Voice) and S (ABS, by Infl)
    MamArgPosition.agent.isPhiAgreed = true ∧
    MamArgPosition.agent.case = .erg ∧
    MamArgPosition.intranS.isPhiAgreed = true ∧
    MamArgPosition.intranS.case = .abs ∧
    -- Not agreed-with: patient (ACC, from Voice but no φ-Agree)
    MamArgPosition.patient.isPhiAgreed = false ∧
    MamArgPosition.patient.case = .acc := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Agreement probes are on different heads: Voice for Set A, Infl for
    Set B. The patient's lack of agreement is NOT because both heads
    target the agent — it's because Infl's probe is blocked by VoiceP. -/
theorem different_probe_heads :
    agreeProbe .agent = some .v ∧
    agreeProbe .intranS = some .T ∧
    agreeProbe .patient = none := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 11: Connecting to Obligatory Operations (@cite{preminger-2014}, Ch. 5)
-- ============================================================================

/-- The transitive Set B default is an instance of Preminger's probe failure:
    Infl's probe searches an empty domain (blocked by Voice_TR) and finds no
    DP with matching φ-features. `attemptAgree` maps the `none` result from
    `applyAgree` to `ProbeOutcome.unvalued`. -/
theorem transitive_is_probe_failure :
    attemptAgree inflProbe [] (.phi (.person .third)) = .unvalued := by
  native_decide

/-- The intransitive case is real agreement: Infl's probe finds S and copies
    its φ-features. `attemptAgree` maps the `some _` result to `.valued`. -/
theorem intransitive_is_real_agreement :
    attemptAgree inflProbe
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
      (.phi (.person .third)) = .valued := by
  native_decide

/-- Under Preminger's obligatory-no-crash model, probe failure converges
    and produces Elsewhere morphology — exactly the Set B "tz'=" we observe
    in Mam transitives. This connects the abstract failure model to the
    concrete spellout: `ProbeOutcome.unvalued` → `PFRealization.elsewhere`
    → the Elsewhere Vocabulary entry → "tz'=". -/
theorem probe_failure_converges_with_elsewhere :
    derivationConverges .obligatoryNocrash .unvalued = true ∧
    ProbeOutcome.unvalued.pfRealization = .elsewhere := ⟨rfl, rfl⟩

-- ============================================================================
-- § 12: Deriving Probe Blocking from SatisfactionCond (@cite{deal-2024})
-- ============================================================================

/-! The Fragment file (`Agreement.lean`) stipulates `isPhiAgreed := false` for
    patients. Here we DERIVE that result from the `SatisfactionCond` machinery
    in `Agree.lean`: Infl's disjunctive probe [SAT: φ or Voice_TR] encounters
    transitive Voice and stops without copying features.

    This closes the gap between stipulation and derivation: the patient's
    lack of φ-agreement is not an axiom but a consequence of probe
    satisfaction theory. -/

/-- In a transitive clause, `mamInflSatisfaction` is satisfied by Voice_TR
    (head encounter .v) and copies no features — matching the Fragment's
    `patient.isPhiAgreed = false`. -/
theorem satisfaction_derives_patient_no_agree :
    mamInflSatisfaction.isSatisfied [] (some .v) = true ∧
    mamInflSatisfaction.copiedFeatures [] (some .v) = false ∧
    MamArgPosition.patient.isPhiAgreed = false := ⟨by native_decide, by native_decide, rfl⟩

/-- In an intransitive clause, `mamInflSatisfaction` is satisfied by
    φ-features and DOES copy them — matching `intranS.isPhiAgreed = true`. -/
theorem satisfaction_derives_intranS_agree :
    let dp1sg := [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
    mamInflSatisfaction.isSatisfied dp1sg none = true ∧
    mamInflSatisfaction.copiedFeatures dp1sg none = true ∧
    MamArgPosition.intranS.isPhiAgreed = true := ⟨by native_decide, by native_decide, rfl⟩

/-- The satisfaction condition's `copiedFeatures` result aligns exactly with
    the Fragment's `isPhiAgreed` for both Infl-probed positions:
    - patient (transitive): copiedFeatures = false = isPhiAgreed
    - intranS (intransitive): copiedFeatures = true = isPhiAgreed -/
theorem satisfaction_matches_fragment :
    mamInflSatisfaction.copiedFeatures [] (some .v) =
      MamArgPosition.patient.isPhiAgreed ∧
    mamInflSatisfaction.copiedFeatures
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]
      none =
      MamArgPosition.intranS.isPhiAgreed := ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 13: Unified Agree — Ā-agreement and φ-agreement as One Operation
-- (renumbered from former § 12)
-- ============================================================================

/-! Voice⁰ in Mam carries two independent probes:

1. **φ-probe** [uPerson, uNumber]: Agrees with agent in Spec,VoiceP,
   yielding Set A morphology (e.g., "t-" for 3SG).
2. **Oblique probe** [uOblique]: Agrees with a passing Ā-moved oblique,
   yielding =(y)a' on Voice⁰.

Both are instances of the same abstract Agree operation: probe searches
c-command domain, finds closest matching goal, copies features, and the
valued features are spelled out by Vocabulary Insertion. They differ only
in which features they probe for and what vocabulary entries match.

This section makes the unity explicit by running both pipelines in
parallel and showing they produce different exponents from the same
mechanism.

See also: `ElkinsTorrenceBrown2026` for the
full =(y)a' analysis. -/

/-- Voice's oblique probe features (from VoiceSystem). -/
private def voiceOblProbe : FeatureBundle := mamVoice.features

/-- Both probes on Voice are unvalued features — both act as probes
    in the sense of Agree. -/
theorem both_probes_unvalued :
    voiceProbe.all GramFeature.isUnvalued = true ∧
    voiceOblProbe.all GramFeature.isUnvalued = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- φ-Agree and oblique-Agree are parallel instances of the same
    operation: probe, value, spellout. They differ only in which
    features are probed and which vocabulary entries match.

    - φ-Agree: Voice + 3SG agent → [Person:3, Number:sg] → Set A "t-"
    - Oblique-Agree: Voice + oblique → [+oblique] → =(y)a'

    Both pipelines use `applyAgree` for valuation and `spellout` for
    morphological realization. -/
theorem phi_and_oblique_agree_parallel :
    -- φ-Agree pipeline: value person, then number, then spellout
    (applyAgree voiceProbe dp3sg (.phi (.person .third))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number .sg))) = some voiceFullyAgreed ∧
    spellout setAVocab voiceFullyAgreed (some .v) = some "t-" ∧
    -- Oblique-Agree pipeline: value oblique, then spellout
    applyAgree voiceOblProbe [.valued (.oblique true)] (.oblique false) =
      some [.valued (.oblique true)] ∧
    spellout [eqYaVocab] [.valued (.oblique true)] (some .Voice) = some "=(y)a'" := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- § 14: Impoverishment — Connecting to DM (@cite{scott-2023}, §4.4.3)
-- ============================================================================

/-! Scott's impoverishment rule (ex. 84/94):

    `[+/−singular] → ∅ / [+author]^F`

    Deletes [±singular] from first person pronouns that have been
    agreed with (marked by the F diacritic). This bleeds insertion of
    the pronominal base morphemes *qin* ([+author,+singular]) and *qo*
    ([+author,−singular]), yielding reduced pronouns.

    We model this using `Morphology.DM.Impoverishment.ImpoverishmentRule`.
    The condition checks for [+author] (= first person in our feature
    system), and the target is [±singular] (= number). -/

/-- The Mam first-person impoverishment rule: delete [±singular]
    (number) when the bundle contains [+author] (first person) features
    that have been agreed with.

    Built via the `paradigmatic` smart constructor — the F-diacritic
    condition only inspects the focus bundle (the agreed-with pronoun's
    own features), so the rule is paradigmatic by construction. -/
def mamImpoverishmentRule : Morphology.DM.Impoverishment.ImpoverishmentRule :=
  Morphology.DM.Impoverishment.paradigmatic
    -- Check for [+author] (= valued first person): the F diacritic
    -- condition is modeled by this rule only being applied in
    -- agreed-with contexts (subj/poss position, not objects).
    (λ fb => fb.any (λ f => match f with
      | .valued (.phi (.person .first)) => true
      | _ => false))
    (.phi (.number .sg))

/-- Mam's rule is paradigmatic — discharged by the smart constructor. -/
theorem mamImpoverishment_paradigmatic :
    Morphology.DM.Impoverishment.Paradigmatic mamImpoverishmentRule :=
  Morphology.DM.Impoverishment.paradigmatic_isParadigmatic _ _

/-- The impoverishment rule fires for 1st person bundles. -/
theorem impoverishment_fires_1sg :
    mamImpoverishmentRule.condition
      (Morphology.DM.Impoverishment.Neighborhood.ofBundle
        [.valued (.phi (.person .first)), .valued (.phi (.number .sg))]) := by
  decide

/-- The impoverishment rule does NOT fire for 3rd person bundles. -/
theorem impoverishment_blocked_3sg :
    ¬ mamImpoverishmentRule.condition
        (Morphology.DM.Impoverishment.Neighborhood.ofBundle
          [.valued (.phi (.person .third)), .valued (.phi (.number .sg))]) := by
  decide

/-- After impoverishment, the number feature is deleted from 1st
    person bundles, bleeding insertion of the base morpheme *qin*. -/
theorem impoverishment_deletes_number :
    mamImpoverishmentRule.applyToBundle
      [.valued (.phi (.person .first)), .valued (.phi (.number .sg))] =
    [.valued (.phi (.person .first))] := by
  decide

/-- Without impoverishment (3rd person), the number feature survives. -/
theorem no_impoverishment_preserves :
    mamImpoverishmentRule.applyToBundle
      [.valued (.phi (.person .third)), .valued (.phi (.number .sg))] =
    [.valued (.phi (.person .third)), .valued (.phi (.number .sg))] := by
  decide

end Scott2023
