import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Fragments.Mayan.Mam.VoiceSystem
import Linglib.Theories.Syntax.Minimalism.Core.ObligatoryOperations

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
   filled by the Elsewhere form "∅" (default 2/3SG).

3. **Object is case-licensed by Voice**: The patient receives structural
   ACC from Voice (low-abs syntax; @cite{scott-2023}, §3.4). Infl's probe
   never reaches the object because it was satisfied by Voice_TR.

4. **Pronoun realization follows**: Agreed-with arguments (agent, S)
   undergo pronoun reduction — agreement morphology redundantly
   expresses their φ-features, triggering deletion of the pronominal
   base (@cite{scott-2023}, ch. 4). The patient, lacking φ-agreement, must
   be a full overt pronoun.

## Two Paths to Set B "∅"

A key insight of Scott's analysis is that the same Set B form "∅" arises
via two distinct mechanisms:

- **Intransitive**: Infl's probe succeeds, copies S's φ-features
  (e.g., [3SG]) → no more specific Set B entry matches → Elsewhere
  "∅" is selected.
- **Transitive**: Infl's probe is blocked by Voice_TR → no φ-features
  on Infl → Elsewhere "∅" is selected.

Both yield "∅", but the intransitive case involves real agreement while
the transitive case involves probe failure. This bridge demonstrates
both paths.

-/

namespace Phenomena.Agreement.Studies.Scott2023

open Minimalism Fragments.Mayan.Mam

-- ============================================================================
-- § 1: Probe Feature Bundles
-- ============================================================================

/-- Voice's probe features: [uPerson, uNumber].
    Placeholder values (0, false) are irrelevant — `sameType` matching
    ensures any Person/Number goal is found regardless. -/
def voiceProbe : FeatureBundle :=
  [.unvalued (.phi (.person .third)), .unvalued (.phi (.number false))]

/-- Infl's probe features: [uPerson, uNumber].
    In intransitives, these are valued by S. In transitives, the probe
    is blocked by Voice_TR before reaching any DP. -/
def inflProbe : FeatureBundle :=
  [.unvalued (.phi (.person .third)), .unvalued (.phi (.number false))]

-- ============================================================================
-- § 2: Goal Feature Bundles (3SG test case)
-- ============================================================================

/-- A 3SG DP's features: [Person:3, Number:sg]. -/
def dp3sg : FeatureBundle :=
  [.valued (.phi (.person .third)), .valued (.phi (.number false))]

-- ============================================================================
-- § 3: Agree Valuation — Voice agrees with agent
-- ============================================================================

/-- Voice's [uPerson] is valued as [Person:3] from a 3SG agent. -/
theorem voice_agrees_person :
    applyAgree voiceProbe dp3sg (.phi (.person .third)) =
    some [.valued (.phi (.person .third)), .unvalued (.phi (.number false))] := by
  native_decide

/-- After person agreement, Voice's [uNumber] is valued as [Number:sg].
    This is the second step of φ-Agree: person first, then number. -/
theorem voice_agrees_number :
    let afterPerson := [.valued (.phi (.person .third)), .unvalued (.phi (.number false))]
    applyAgree afterPerson dp3sg (.phi (.number false)) =
    some [.valued (.phi (.person .third)), .valued (.phi (.number false))] := by
  native_decide

/-- Full φ-valuation of Voice by a 3SG agent: both person and number valued. -/
def voiceFullyAgreed : FeatureBundle :=
  [.valued (.phi (.person .third)), .valued (.phi (.number false))]

/-- The two-step Agree pipeline produces a fully valued bundle. -/
theorem voice_agree_pipeline :
    (applyAgree voiceProbe dp3sg (.phi (.person .third))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number false))) =
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
      [.valued (.phi (.person .first)), .valued (.phi (.number false))]
    spellout setAVocab v1sg (some .v) = some "n-/w-" := by
  native_decide

-- ============================================================================
-- § 5: Set B — Two Paths to "∅"
-- ============================================================================

/-- **Intransitive path**: Infl Agrees with a 3SG intransitive S, copies
    [Person:3, Number:sg]. No Set B entry is specified for these features
    (1SG=chin, 1PL=qo, 2/3PL=chi — none match 3SG), so the Elsewhere
    entry is selected: "∅". -/
theorem setB_intransitive_3sg :
    let inflAgreed : FeatureBundle :=
      [.valued (.phi (.person .third)), .valued (.phi (.number false))]
    spellout setBVocab inflAgreed (some .T) = some "∅" := by
  native_decide

/-- **Transitive path**: Infl's probe is blocked by Voice_TR → no
    φ-features are copied → the Infl node has an empty feature bundle.
    The Elsewhere entry matches (empty features are a subset of anything)
    and "∅" is selected.

    This is the DEFAULT Set B — it appears in transitives regardless of
    the object's person/number features. -/
theorem setB_transitive_default :
    let inflBlocked : FeatureBundle := []
    spellout setBVocab inflBlocked (some .T) = some "∅" := by
  native_decide

/-- The two paths produce the same exponent — the surface form is
    identical even though the underlying mechanism differs (real agreement
    vs. probe failure). -/
theorem setB_same_surface :
    let inflAgreed3sg : FeatureBundle :=
      [.valued (.phi (.person .third)), .valued (.phi (.number false))]
    let inflBlocked : FeatureBundle := []
    spellout setBVocab inflAgreed3sg (some .T) =
    spellout setBVocab inflBlocked (some .T) := by
  native_decide

/-- Set B spellout for 1SG intransitive: Infl copies [Person:1, Number:sg]
    from S, yielding "chin" — NOT the Elsewhere form. This is real
    agreement, producing a distinct exponent. -/
theorem setB_intransitive_1sg :
    let t1sg : FeatureBundle :=
      [.valued (.phi (.person .first)), .valued (.phi (.number false))]
    spellout setBVocab t1sg (some .T) = some "chin" := by
  native_decide

/-- In a transitive with a 1SG object, the default "∅" still appears —
    NOT "chin". This is because Infl's probe was blocked by Voice_TR,
    so the object's 1SG features are never copied to Infl. -/
theorem setB_transitive_ignores_object :
    -- Even though the object is 1SG, Infl shows default "∅", not "chin"
    let inflBlocked : FeatureBundle := []
    spellout setBVocab inflBlocked (some .T) = some "∅" ∧
    -- Compare: a 1SG intransitive S would trigger "chin"
    let inflAgreed1sg : FeatureBundle :=
      [.valued (.phi (.person .first)), .valued (.phi (.number false))]
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
    spellout setBVocab ([] : FeatureBundle) (some .T) = some "∅" ∧
    -- Intransitive 1SG: probe succeeds → "chin" (not default)
    spellout setBVocab
      [.valued (.phi (.person .first)), .valued (.phi (.number false))]
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
      [.valued (.phi (.person .first)), .valued (.phi (.number false))]
      (.phi (.person .third))).bind
      (λ fb => applyAgree fb
        [.valued (.phi (.person .first)), .valued (.phi (.number false))]
        (.phi (.number false))) =
    some [.valued (.phi (.person .first)), .valued (.phi (.number false))] ∧
    -- Spells out as "chin" (not default "∅")
    spellout setBVocab
      [.valued (.phi (.person .first)), .valued (.phi (.number false))]
      (some .T) = some "chin" := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 8: Transitive Pipeline — Voice Agrees, Infl Blocked
-- ============================================================================

/-- The complete prediction for a 3SG transitive clause:

    1. Voice Agrees with agent → [Person:3, Number:sg] on Voice
    2. [Person:3, Number:sg] on Voice spells out as Set A "t-"
    3. Infl's probe is blocked by Voice_TR → empty bundle on Infl
    4. Empty Infl spells out as Elsewhere Set B "∅"
    5. Patient is not φ-Agreed-with → overt pronoun required -/
theorem full_pipeline_3sg_transitive :
    -- Step 1-2: Voice Agrees and spells out as Set A
    (applyAgree voiceProbe dp3sg (.phi (.person .third))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number false))) = some voiceFullyAgreed ∧
    spellout setAVocab voiceFullyAgreed (some .v) = some "t-" ∧
    -- Step 3-4: Infl probe blocked → default Set B
    spellout setBVocab ([] : FeatureBundle) (some .T) = some "∅" ∧
    -- Step 5: patient requires overt pronoun
    MamArgPosition.patient.canBeNull = false := by
  exact ⟨by native_decide, by native_decide, by native_decide, rfl⟩

/-- The pipeline generalizes: for every argument position, the predicted
    pronoun reduction matches the observed pattern. -/
theorem all_positions_match :
    mamArgPositions.all (λ pos => pos.canBeNull == pos.isPhiAgreed) = true := by
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
    MamArgPosition.agent.agreeProbe = some .v ∧
    MamArgPosition.intranS.agreeProbe = some .T ∧
    MamArgPosition.patient.agreeProbe = none := ⟨rfl, rfl, rfl⟩

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
      [.valued (.phi (.person .first)), .valued (.phi (.number false))]
      (.phi (.person .third)) = .valued := by
  native_decide

/-- Under Preminger's obligatory-no-crash model, probe failure converges
    and produces Elsewhere morphology — exactly the Set B "∅" we observe
    in Mam transitives. This connects the abstract failure model to the
    concrete spellout: `ProbeOutcome.unvalued` → `PFRealization.elsewhere`
    → the Elsewhere Vocabulary entry → "∅". -/
theorem probe_failure_converges_with_elsewhere :
    derivationConverges .obligatoryNocrash .unvalued = true ∧
    ProbeOutcome.unvalued.pfRealization = .elsewhere := ⟨rfl, rfl⟩

-- ============================================================================
-- § 12: Unified Agree — Ā-agreement and φ-agreement as One Operation
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

See also: `Phenomena.FillerGap.Studies.ElkinsTorrenceBrown2026` for the
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
      (λ fb => applyAgree fb dp3sg (.phi (.number false))) = some voiceFullyAgreed ∧
    spellout setAVocab voiceFullyAgreed (some .v) = some "t-" ∧
    -- Oblique-Agree pipeline: value oblique, then spellout
    applyAgree voiceOblProbe [.valued (.oblique true)] (.oblique false) =
      some [.valued (.oblique true)] ∧
    spellout [eqYaVocab] [.valued (.oblique true)] (some .Voice) = some "=(y)a'" := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end Phenomena.Agreement.Studies.Scott2023
