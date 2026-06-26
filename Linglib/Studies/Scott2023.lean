import Linglib.Syntax.Case.Dependent
import Linglib.Syntax.Case.Alignment
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Minimalist.Probe.Basic
import Linglib.Syntax.Minimalist.Probe.Satisfaction
import Linglib.Morphology.DM.VocabSimple
import Linglib.Morphology.DM.Impoverishment
import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Fragments.Mayan.Params

/-!
# [scott-2023] — Pronouns and Agreement in San Juan Atitán Mam

[scott-2023] [woolford-1997] [marantz-1991] [baker-2015] [chomsky-2000]
[deal-2024] [elkins-torrence-brown-2026] [preminger-2014] [england-2017]

Single study file for [scott-2023] (UC Berkeley dissertation), in three
sections.

## Voice-based case

Scott treats case as assigned directly by functional heads keyed to argument
position, building on [woolford-1997]'s claim that ergative is
lexical/inherent Case assigned with θ-role rather than configurationally
derived. Each case has a dedicated assigner:

- **Voice → ERG** (inherent, to the agent in Spec,VoiceP)
- **Voice → ACC** (structural, to the patient — low-abs syntax, §3.4)
- **Infl → ABS** (structural, to the intransitive subject)

This produces a tripartite underlying system (ERG ≠ ACC ≠ ABS) visible
through the Mam agreement patterns. The Mam data discriminate between three
theories of case assignment: Agree-based ([chomsky-2000], [chomsky-2001]:
ACC requires a phase head), dependent case ([marantz-1991], [baker-2015]:
Voice flavor is irrelevant), and Voice-based (this analysis: the Voice head
selects ERG vs. ACC by θ-role; neither phase-hood nor NP configuration does
the work). The theorems stage the contrast. See `Studies/Woolford1997.lean`
for the predecessor analysis.

## Agree-conditioned pronoun spellout

Connects Agree (feature valuation) and probe restriction to the distribution
of overt vs. reduced pronouns. In a transitive clause: Voice probes the
agent (Set A spellout, inherent ERG); Infl's probe has a disjunctive
satisfaction condition [SAT: φ or Voice_TR] and **stops** at transitive
Voice, so no φ reaches Infl and the Set B slot falls to the Elsewhere form
"tz'=". Agreed-with arguments (A, S) undergo pronoun reduction — agreement
redundantly expresses their φ-features, triggering deletion of the
pronominal base (ch. 4) — while the unagreed patient must be a full overt
pronoun. The same "tz'=" thus arises by two paths: real agreement with a
3SG S (no more specific entry matches) vs. probe failure in transitives.

## Super-extended ergativity

Theory-neutral data on split ergativity. Matrix clauses are tripartite
(A: Set A; S: Set B; P: default Set B). In certain dependent clauses
(purpose *tu'n*, reason, *taj* 'when'), alignment shifts to what
[england-2017] calls **super-extended ergativity**: Set A extends to ALL
arguments — the system becomes neutral. The trigger is clause type, not
aspect or person. Only default 2/3SG Set A (t-) is allowed for objects
in SEE clauses ([scott-2023], §2.6.3, ex. 196). Mam's SEE split is not a
binary ergative/accusative toggle, so `Syntax.Case.SplitErgativity` does
not fit; the custom `MamAlignment` struct captures the
tripartite-to-neutral contrast directly.
-/

namespace Scott2023

/-! ### Voice-based case -/

section VoiceCase

open Minimalist
open Syntax.Case

-- ============================================================================
-- § 1: Voice Assigns Case by Argument Position
-- ============================================================================

/-- Scott 2023's central case-theoretic claim: Voice (and Infl) assign
    case directly based on argument position. A → ERG, P → ACC,
    S → ABS — three distinct cases from three different heads, with
    the assignment fixed by θ-position rather than by Agree or by NP
    configuration. -/
theorem voice_assigns_case_by_position :
    Mam.ArgPosition.case .A = .erg ∧
    Mam.ArgPosition.case .P = .acc ∧
    Mam.ArgPosition.case .S = .abs := ⟨rfl, rfl, rfl⟩

/-- The three argument positions receive three distinct cases — a
    tripartite underlying system (ERG ≠ ACC ≠ ABS) at the case-assignment
    layer, prior to any morphological syncretism. Inherits from
    `Alignment.tripartite_distinguishes_all` via the substrate connection. -/
theorem voice_based_tripartite :
    Mam.ArgPosition.case .A ≠
      Mam.ArgPosition.case .P ∧
    Mam.ArgPosition.case .A ≠
      Mam.ArgPosition.case .S ∧
    Mam.ArgPosition.case .P ≠
      Mam.ArgPosition.case .S :=
  Alignment.tripartite_distinguishes_all

-- ============================================================================
-- § 2: Contrast with Agree-Based Case
-- ============================================================================

/-! Agree-based case ties ACC to a *phase head* (v*). Voice flavors that
    are not phase heads (anticausative, passive) cannot assign ACC under
    this view, predicting a gap for unaccusative patients. Scott 2023's
    Voice-based assignment makes no such phase-head requirement. -/

/-- Under Agree, anticausative Voice is not a phase head, so it cannot
    serve as an ACC assigner. -/
theorem agree_anticausative_not_phase :
    ¬ voiceAnticausative.IsPhasal := by decide

/-- Under Agree, agentive Voice (v*) is a phase head and can assign ACC. -/
theorem agree_voice_is_phase_head :
    voiceAgent.IsPhasal := by decide

-- ============================================================================
-- § 3: Contrast with Dependent Case
-- ============================================================================

/-! Dependent case is *Voice-blind* — the algorithm sees only NP
    configuration (higher vs. lower) and lexical case, not θ-role or
    Voice flavor. Two caseless NPs in a domain produce ACC on the lower
    one regardless of whether the higher NP is an agent or a derived
    subject. Scott's Voice-based assignment, by contrast, would only
    assign ACC under transitive Voice with an agent. -/

/-- Dependent case yields ACC for the lower of two caseless NPs whether
    or not the higher NP carries an agent θ-role. The algorithm never
    inspects Voice flavor. -/
theorem dependent_case_ignores_voice :
    let transitive : List NPInDomain :=
      [ { label := "agent", lexicalCase := none },
        { label := "theme", lexicalCase := none } ]
    let unaccusative : List NPInDomain :=
      [ { label := "experiencer", lexicalCase := none },
        { label := "theme", lexicalCase := none } ]
    getCaseOf "theme" (assignCases .accusative transitive) =
      getCaseOf "theme" (assignCases .accusative unaccusative) := by
  decide

/-- Dependent case in tripartite mode produces a parallel ERG/ACC split
    from the same configuration — but assigns it on positional grounds
    (higher NP gets ERG, lower NP gets ACC), not on θ-role grounds.
    Voice-based case derives the same surface pattern via a different
    mechanism, with the assigners keyed to θ-role rather than to NP
    configuration. -/
theorem dependent_case_tripartite :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .tripartite nps) = some .erg ∧
    getCaseOf "lower" (assignCases .tripartite nps) = some .acc := by
  decide

end VoiceCase

/-! ### Agree-conditioned pronoun spellout -/

section AgreeSpellout

open Minimalist Mam
open Agreement

-- ============================================================================
-- § 0: Minimalism-Specific Vocabulary (Set A / Set B as VI entries)
-- ============================================================================

/-! These Vocabulary Insertion entries encode the Fragment's theory-neutral
    marker tables as Minimalism feature bundles, enabling the Agree → Spellout
    pipeline. The Fragment (`Agreement.lean`) stores the markers as simple
    person × number → string tables; here they are parameterized by
    `FeatureBundle` and `Cat` for use with `spellout`. -/

/-- Set A (ERG) vocabulary entries: φ-features on Voice (.v)
    yield the morphological exponent ([scott-2023] Table 2.8).
    All six cells have specific entries. -/
def setAVocab : Vocabulary :=
  makePersonVocab Agreement.Cell.pnCells Agreement.Cell.toPhiFeatures
    (fun c => (setAExponent.realize c).getD "") (some .v)

/-- Set B (ABS) vocabulary entries: φ-features on Infl (.T)
    yield the morphological exponent ([scott-2023] Table 3.5).
    Per Scott's DM analysis, only 1SG/1PL/2PL/3PL have specific
    entries; 2SG and 3SG fall through to the Elsewhere entry
    (no features, tz'=) which surfaces when no specific entry
    matches — also catching the blocked-Infl-probe case in transitives. -/
def setBVocab : Vocabulary :=
  makePersonVocab setBSpecificCells Agreement.Cell.toPhiFeatures
    (fun c => (setBExponent.realize c).getD "") (some .T) ++
    [{ features := ⊥, exponent := defaultSetB, context := some .T }]

/-- Which Minimalist head φ-Agrees with each argument position.
    Ditransitive R/T default to none (not modeled). -/
def agreeProbe : ArgPosition → Option Cat
  | .A => some .v   -- Voice probes, A in Spec,VoiceP
  | .P => none      -- Infl probe blocked by Voice_TR
  | .S => some .T   -- Infl probes, S in its domain
  | .R | .T => none

-- ============================================================================
-- § 1: Probe Feature Bundles
-- ============================================================================

/-- Voice's probe features: [uPerson, uNumber].
    Placeholder values (.third, .Sing) are irrelevant — `sameType` matching
    ensures any Person/Number goal is found regardless. -/
def voiceProbe : FeatureBundle :=
  .ofGramFeatures [.unvalued (.phi (.person .third)), .unvalued (.phi (.number .singular))]

/-- Infl's probe features: [uPerson, uNumber].
    In intransitives, these are valued by S. In transitives, the probe
    is blocked by Voice_TR before reaching any DP. -/
def inflProbe : FeatureBundle :=
  .ofGramFeatures [.unvalued (.phi (.person .third)), .unvalued (.phi (.number .singular))]

-- ============================================================================
-- § 2: Goal Feature Bundles (3SG test case)
-- ============================================================================

/-- A 3SG DP's features: [Person:3, Number:sg]. -/
def dp3sg : FeatureBundle :=
  .ofGramFeatures [.valued (.phi (.person .third)), .valued (.phi (.number .singular))]

-- ============================================================================
-- § 3: Agree Valuation — Voice agrees with agent
-- ============================================================================

/-- Voice's [uPerson] is valued as [Person:3] from a 3SG agent. -/
theorem voice_agrees_person :
    applyAgree voiceProbe dp3sg (.phi (.person .third)) =
    some (.ofGramFeatures
      [.valued (.phi (.person .third)), .unvalued (.phi (.number .singular))]) := by
  native_decide

/-- After person agreement, Voice's [uNumber] is valued as [Number:sg].
    This is the second step of φ-Agree: person first, then number. -/
theorem voice_agrees_number :
    let afterPerson : FeatureBundle := .ofGramFeatures
      [.valued (.phi (.person .third)), .unvalued (.phi (.number .singular))]
    applyAgree afterPerson dp3sg (.phi (.number .singular)) =
    some (.ofGramFeatures
      [.valued (.phi (.person .third)), .valued (.phi (.number .singular))]) := by
  native_decide

/-- Full φ-valuation of Voice by a 3SG agent: both person and number valued. -/
def voiceFullyAgreed : FeatureBundle :=
  .ofGramFeatures [.valued (.phi (.person .third)), .valued (.phi (.number .singular))]

/-- The two-step Agree pipeline produces a fully valued bundle. -/
theorem voice_agree_pipeline :
    (applyAgree voiceProbe dp3sg (.phi (.person .third))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number .singular))) =
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
    let v1sg : FeatureBundle := .ofGramFeatures
      [.valued (.phi (.person .first)), .valued (.phi (.number .singular))]
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
    let inflAgreed : FeatureBundle := .ofGramFeatures
      [.valued (.phi (.person .third)), .valued (.phi (.number .singular))]
    spellout setBVocab inflAgreed (some .T) = some "tz'=" := by
  native_decide

/-- **Transitive path**: Infl's probe is blocked by Voice_TR → no
    φ-features are copied → the Infl node has an empty feature bundle.
    The Elsewhere entry matches (empty features are a subset of anything)
    and "tz'=" is selected.

    This is the DEFAULT Set B — it appears in transitives regardless of
    the object's person/number features. -/
theorem setB_transitive_default :
    let inflBlocked : FeatureBundle := ⊥
    spellout setBVocab inflBlocked (some .T) = some "tz'=" := by
  native_decide

/-- The two paths produce the same exponent — the surface form is
    identical even though the underlying mechanism differs (real agreement
    vs. probe failure). -/
theorem setB_same_surface :
    let inflAgreed3sg : FeatureBundle := .ofGramFeatures
      [.valued (.phi (.person .third)), .valued (.phi (.number .singular))]
    let inflBlocked : FeatureBundle := ⊥
    spellout setBVocab inflAgreed3sg (some .T) =
    spellout setBVocab inflBlocked (some .T) := by
  native_decide

/-- Set B spellout for 1SG intransitive: Infl copies [Person:1, Number:sg]
    from S, yielding "chin" — NOT the Elsewhere form. This is real
    agreement, producing a distinct exponent. -/
theorem setB_intransitive_1sg :
    let t1sg : FeatureBundle := .ofGramFeatures
      [.valued (.phi (.person .first)), .valued (.phi (.number .singular))]
    spellout setBVocab t1sg (some .T) = some "chin" := by
  native_decide

/-- In a transitive with a 1SG object, the default "tz'=" still appears —
    NOT "chin". This is because Infl's probe was blocked by Voice_TR,
    so the object's 1SG features are never copied to Infl. -/
theorem setB_transitive_ignores_object :
    -- Even though the object is 1SG, Infl shows default "tz'=", not "chin"
    let inflBlocked : FeatureBundle := ⊥
    spellout setBVocab inflBlocked (some .T) = some "tz'=" ∧
    -- Compare: a 1SG intransitive S would trigger "chin"
    let inflAgreed1sg : FeatureBundle := .ofGramFeatures
      [.valued (.phi (.person .first)), .valued (.phi (.number .singular))]
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
    halted by head-encounter satisfaction at transitive Voice
    ([deal-2024]-style [SAT: φ or Voice_TR]; see the derived probe
    table below for the search-level statement). -/
theorem probe_restriction_yields_default :
    -- Transitive: probe blocked → empty → Elsewhere
    spellout setBVocab (⊥ : FeatureBundle) (some .T) = some "tz'=" ∧
    -- Intransitive 1SG: probe succeeds → "chin" (not default)
    spellout setBVocab
      (.ofGramFeatures
        [.valued (.phi (.person .first)), .valued (.phi (.number .singular))])
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
      (.ofGramFeatures
        [.valued (.phi (.person .first)), .valued (.phi (.number .singular))])
      (.phi (.person .third))).bind
      (λ fb => applyAgree fb
        (.ofGramFeatures
          [.valued (.phi (.person .first)), .valued (.phi (.number .singular))])
        (.phi (.number .singular))) =
    some (.ofGramFeatures
      [.valued (.phi (.person .first)), .valued (.phi (.number .singular))]) ∧
    -- Spells out as "chin" (not default "tz'=")
    spellout setBVocab
      (.ofGramFeatures
        [.valued (.phi (.person .first)), .valued (.phi (.number .singular))])
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
      (λ fb => applyAgree fb dp3sg (.phi (.number .singular))) = some voiceFullyAgreed ∧
    spellout setAVocab voiceFullyAgreed (some .v) = some "t-" ∧
    -- Step 3-4: Infl probe blocked → default Set B
    spellout setBVocab (⊥ : FeatureBundle) (some .T) = some "tz'=" ∧
    -- Step 5: patient is not eligible for reduction → overt pronoun
    ¬ ArgPosition.CanBeReduced .P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · decide

/-- The pipeline generalizes: for every argument position, reduction
    eligibility ≡ φ-agreement (definitionally — `CanBeReduced := IsPhiAgreed`). -/
theorem all_positions_match (pos : ArgPosition) :
    pos.CanBeReduced ↔ pos.IsPhiAgreed :=
  Iff.rfl

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
    -- Agreed-with positions: A (ERG, by Voice) and S (ABS, by Infl)
    ArgPosition.IsPhiAgreed .A ∧
    ArgPosition.case .A = .erg ∧
    ArgPosition.IsPhiAgreed .S ∧
    ArgPosition.case .S = .abs ∧
    -- Not agreed-with: P (ACC, from Voice but no φ-Agree)
    ¬ ArgPosition.IsPhiAgreed .P ∧
    ArgPosition.case .P = .acc :=
  ⟨trivial, rfl, trivial, rfl, by decide, rfl⟩

/-- Agreement probes are on different heads: Voice for Set A, Infl for
    Set B. The patient's lack of agreement is NOT because both heads
    target the agent — it's because Infl's probe is blocked by VoiceP. -/
theorem different_probe_heads :
    agreeProbe .A = some .v ∧
    agreeProbe .S = some .T ∧
    agreeProbe .P = none := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 11: Connecting to Obligatory Operations ([preminger-2014], Ch. 5)
-- ============================================================================

/-- The transitive Set B default is an instance of Preminger's probe failure:
    Infl's φ-probe searches an empty domain (blocked by Voice_TR) and finds no
    DP with matching φ-features, so its outcome is `unvalued` ([preminger-2014]
    Ch. 5). Under the obligatory-operations model this does not crash; the
    unvalued (empty) bundle spells out as the Elsewhere entry — the Set B "tz'="
    observed in Mam transitives. -/
theorem transitive_is_probe_failure :
    (phiProbe (.phi (.person .third))).outcome [⊥] = .unvalued := by
  native_decide

/-- The intransitive case is real agreement: Infl's φ-probe finds S, so its
    outcome is `valued`. -/
theorem intransitive_is_real_agreement :
    (phiProbe (.phi (.person .third))).outcome
      [.ofGramFeatures
        [.valued (.phi (.person .first)), .valued (.phi (.number .singular))]]
      = .valued := by
  native_decide

-- ============================================================================
-- § 12: Deriving Probe Blocking from SatisfactionCond ([deal-2024])
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
    `¬ IsPhiAgreed .P`. -/
theorem satisfaction_derives_patient_no_agree :
    mamInflSatisfaction.isSatisfied ⊥ (some .v) = true ∧
    mamInflSatisfaction.copiedFeatures ⊥ (some .v) = false ∧
    ¬ ArgPosition.IsPhiAgreed .P :=
  ⟨by native_decide, by native_decide, by decide⟩

/-- In an intransitive clause, `mamInflSatisfaction` is satisfied by
    φ-features and DOES copy them — matching `IsPhiAgreed .S`. -/
theorem satisfaction_derives_intranS_agree :
    let dp1sg : FeatureBundle := .ofGramFeatures
      [.valued (.phi (.person .first)), .valued (.phi (.number .singular))]
    mamInflSatisfaction.isSatisfied dp1sg none = true ∧
    mamInflSatisfaction.copiedFeatures dp1sg none = true ∧
    ArgPosition.IsPhiAgreed .S :=
  ⟨by native_decide, by native_decide, trivial⟩

/-- The satisfaction condition's `copiedFeatures` Bool aligns with
    the Fragment's `IsPhiAgreed` Prop for both Infl-probed positions:
    - patient (transitive): copiedFeatures = false ↔ ¬ IsPhiAgreed .P
    - intranS (intransitive): copiedFeatures = true ↔ IsPhiAgreed .S -/
theorem satisfaction_matches_fragment :
    (mamInflSatisfaction.copiedFeatures ⊥ (some .v) = true ↔
      ArgPosition.IsPhiAgreed .P) ∧
    (mamInflSatisfaction.copiedFeatures
      (.ofGramFeatures
        [.valued (.phi (.person .first)), .valued (.phi (.number .singular))])
      none = true ↔
      ArgPosition.IsPhiAgreed .S) := by
  refine ⟨?_, ?_⟩
  · constructor <;> intro h <;> first | (native_decide) | trivial
  · exact ⟨fun _ => trivial, fun _ => by native_decide⟩

/-! ### Deriving the probe table from relativized search (`Probe/Basic.lean`)

The `agreeProbe` table stipulates which head agrees with which
position. Here it is DERIVED: each probe runs `Probe.search` over the
goal sequence of its clause, relativized to its satisfaction
condition. `.P => none` falls out of Voice_TR halting Infl's search
before any DP (`infl_truncated_at_voiceTR`) plus Voice's own search
stopping at the closer agent (`voice_finds_A`). The stipulation moves
from the conclusion (the table) to independently motivated premises:
`mamInflSatisfaction` (`Agree.lean`) and the clause spine's encounter
order (Infl > Voice_TR > A > P). The goal lists are stipulated
linearizations per clause type, not computed from a `SyntacticObject`
— the tree-geometric derivation exists in `Agree.lean` but is
`native_decide`-bound; this level matches `Probing.lean`'s altitude. -/

/-- An element a probe encounters while walking its search domain:
    the argument position it realizes (`none` for non-DP heads like
    Voice_TR), its feature bundle, and its head category (`none` for
    DP goals). The `(FeatureBundle, Option Cat)` pair is exactly the
    argument signature of `SatisfactionCond.isSatisfied`. -/
structure Encounter where
  pos : Option ArgPosition
  feats : FeatureBundle
  cat : Option Cat

/-- The probe a `SatisfactionCond` denotes over `Encounter`s: the
    substrate's generic `SatisfactionCond.toProbe`
    (`Probe/Satisfaction.lean`) instantiated at the `Encounter`
    projections — visibility = halting ([deal-2024] interaction),
    activity = feature copying (satisfaction). -/
def satProbe (cond : SatisfactionCond) : Probe Encounter :=
  cond.toProbe Encounter.feats Encounter.cat

/-- The argument position a probe φ-agrees with: `(satProbe cond).agree`
    — the probe agrees with the found element only if satisfaction
    copied features (feature match, not head encounter). -/
def agreesWith (cond : SatisfactionCond) (goals : List Encounter) :
    Option ArgPosition :=
  ((satProbe cond).agree goals).bind (·.pos)

/-- Transitive Voice as an encounter: a head of category `.v`, no
    φ-features visible to the probe. -/
def voiceTR : Encounter := ⟨none, ⊥, some .v⟩

/-- A DP goal realizing position `p` with φ-bundle `φ`. -/
def dpGoal (p : ArgPosition) (φ : FeatureBundle) : Encounter := ⟨some p, φ, none⟩

/-- Voice's probe: standard φ feature-match (no head-encounter disjunct). -/
def voiceSat : SatisfactionCond := .featureMatch (.phi (.person .third))

/-- A probe over an empty search space agrees with nothing. -/
theorem agreesWith_nil (cond : SatisfactionCond) :
    agreesWith cond [] = none := rfl

/-- Voice's goal sequence in the clause containing position `p`:
    Voice probes only in transitives; the agent is closest. -/
def voiceGoals (φA φP : FeatureBundle) : ArgPosition → List Encounter
  | .A | .P => [dpGoal .A φA, dpGoal .P φP]
  | _ => []

/-- Infl's goal sequence in the clause containing position `p`. In a
    transitive clause Infl c-commands VoiceP, so the FIRST element its
    downward search encounters is the Voice_TR head, before either DP.
    In an intransitive there is no transitive Voice; the search reaches
    S directly. -/
def inflGoals (φA φP φS : FeatureBundle) : ArgPosition → List Encounter
  | .A | .P => [voiceTR, dpGoal .A φA, dpGoal .P φP]
  | .S => [dpGoal .S φS]
  | .R | .T => []

/-- **The key derivation**: Infl's search over ANY transitive goal
    sequence (Voice_TR first) yields no agreement target — by `rfl`,
    for arbitrary material below Voice. The search halts at Voice_TR
    (head encounter satisfies), no features are copied, so no DP is
    agreed with. -/
theorem infl_truncated_at_voiceTR (rest : List Encounter) :
    agreesWith mamInflSatisfaction (voiceTR :: rest) = none := rfl

/-- In an intransitive, Infl's search finds S and copies its features,
    provided S bears person. -/
theorem infl_finds_S (φS : FeatureBundle)
    (hS : hasValuedFeature φS (.phi (.person .third)) = true) :
    agreesWith mamInflSatisfaction [dpGoal .S φS] = some .S := by
  simp [agreesWith, satProbe, SatisfactionCond.toProbe, Probe.agree, Probe.search,
    Option.filter_some, dpGoal, mamInflSatisfaction_isSatisfied,
    mamInflSatisfaction_copiedFeatures, hS]

/-- Voice's search finds the agent (closest goal), provided A bears
    person. -/
theorem voice_finds_A (φA φP : FeatureBundle)
    (hA : hasValuedFeature φA (.phi (.person .third)) = true) :
    agreesWith voiceSat [dpGoal .A φA, dpGoal .P φP] = some .A := by
  simp [agreesWith, satProbe, SatisfactionCond.toProbe, Probe.agree, Probe.search,
    Option.filter_some, dpGoal, voiceSat, SatisfactionCond.isSatisfied,
    SatisfactionCond.copiedFeatures, hA]

/-- DERIVED probe table: which head φ-agrees with position `p`,
    computed by running each probe's `Probe.search` over the goal
    sequence of the clause containing `p`. -/
def derivedAgreeProbe (φA φP φS : FeatureBundle) (p : ArgPosition) :
    Option Cat :=
  if agreesWith voiceSat (voiceGoals φA φP p) = some p then some .v
  else if agreesWith mamInflSatisfaction (inflGoals φA φP φS p) = some p
    then some .T
  else none

/-- The stipulated table coincides with the derivation, for any clause
    whose A and S bear person features. -/
theorem agreeProbe_eq_derived (φA φP φS : FeatureBundle)
    (hA : hasValuedFeature φA (.phi (.person .third)) = true)
    (hS : hasValuedFeature φS (.phi (.person .third)) = true) :
    ∀ p, agreeProbe p = derivedAgreeProbe φA φP φS p := by
  intro p
  cases p with
  | A => simp [agreeProbe, derivedAgreeProbe, voiceGoals,
      voice_finds_A φA φP hA]
  | P => simp [agreeProbe, derivedAgreeProbe, voiceGoals, inflGoals,
      voice_finds_A φA φP hA, infl_truncated_at_voiceTR]
  | S => simp [agreeProbe, derivedAgreeProbe, voiceGoals, inflGoals,
      infl_finds_S φS hS, agreesWith_nil]
  | R => rfl
  | T => rfl

/-- Concrete instantiation (3SG transitive + 3SG intransitive),
    kernel-checked end to end. -/
theorem agreeProbe_eq_derived_3sg :
    ∀ p, agreeProbe p = derivedAgreeProbe dp3sg dp3sg dp3sg p := by
  intro p; cases p <;> rfl

/-- φ-valuation outcome of a probe with a satisfaction condition:
    valued iff the search found a goal AND satisfaction copied
    features. NOTE: this is NOT `(satProbe cond).outcome` — a
    head-encounter halt satisfies the search but leaves the probe
    φ-unvalued. -/
def valuationOutcome (cond : SatisfactionCond) (goals : List Encounter) :
    Probe.Outcome :=
  if (agreesWith cond goals).isSome then .valued else .unvalued

/-- Transitive Infl: search halts at Voice_TR, probe stays unvalued,
    and converges with Elsewhere morphology — the §11 facts, now
    derived from the goal sequence rather than from a stipulated
    empty bundle. -/
theorem transitive_unvalued_elsewhere (rest : List Encounter) :
    valuationOutcome mamInflSatisfaction (voiceTR :: rest) = .unvalued := rfl

/-- Contrast: `Probe.outcome` relativized to the satisfaction condition
    reports `.valued` in the transitive — the search DID find a halting
    element. The valuation/satisfaction distinction is exactly
    [deal-2024]'s interaction-vs-satisfaction split. -/
theorem searchOutcome_valued_but_unvalued (rest : List Encounter) :
    (satProbe mamInflSatisfaction).outcome (voiceTR :: rest) = .valued ∧
    valuationOutcome mamInflSatisfaction (voiceTR :: rest) = .unvalued :=
  ⟨rfl, rfl⟩

-- The former §13 (Unified Agree — bridging Scott 2023's φ-Agree pipeline
-- with Elkins-Torrence-Brown 2026's oblique-Agree pipeline) violated the
-- chronological dependency rule (a 2023 study cross-referencing a 2026
-- study). It moved to `Studies/ElkinsTorrenceBrown2026.lean`
-- (the later paper, which can correctly back-reference Scott 2023's
-- φ-probe + Set A vocabulary defs).

-- ============================================================================
-- § 14: Impoverishment — Connecting to DM ([scott-2023], §4.4.3)
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
    (λ fb => (Minimalist.FeatureBundle.toGramFeatures fb).any (λ f => match f with
      | .valued (.phi (.person .first)) => true
      | _ => false))
    (.phi (.number .singular))

/-- Mam's rule is paradigmatic — discharged by the smart constructor. -/
theorem mamImpoverishment_paradigmatic :
    Morphology.DM.Impoverishment.Paradigmatic mamImpoverishmentRule :=
  Morphology.DM.Impoverishment.paradigmatic_isParadigmatic _ _

/-- The impoverishment rule fires for 1st person bundles. -/
theorem impoverishment_fires_1sg :
    mamImpoverishmentRule.condition
      (Morphology.DM.Impoverishment.Neighborhood.ofBundle
        (.ofGramFeatures
          [.valued (.phi (.person .first)), .valued (.phi (.number .singular))])) := by
  decide

/-- The impoverishment rule does NOT fire for 3rd person bundles. -/
theorem impoverishment_blocked_3sg :
    ¬ mamImpoverishmentRule.condition
        (Morphology.DM.Impoverishment.Neighborhood.ofBundle
          (.ofGramFeatures
            [.valued (.phi (.person .third)), .valued (.phi (.number .singular))])) := by
  decide

/-- After impoverishment, the number feature is deleted from 1st
    person bundles, bleeding insertion of the base morpheme *qin*. -/
theorem impoverishment_deletes_number :
    mamImpoverishmentRule.applyToBundle
      (.ofGramFeatures
        [.valued (.phi (.person .first)), .valued (.phi (.number .singular))]) =
    .ofGramFeatures [.valued (.phi (.person .first))] := by
  decide

/-- Without impoverishment (3rd person), the number feature survives. -/
theorem no_impoverishment_preserves :
    mamImpoverishmentRule.applyToBundle
      (.ofGramFeatures
        [.valued (.phi (.person .third)), .valued (.phi (.number .singular))]) =
    .ofGramFeatures
      [.valued (.phi (.person .third)), .valued (.phi (.number .singular))] := by
  decide

end AgreeSpellout

/-! ### Super-extended ergativity -/

section SuperExtendedErgativity

open Mayan (MarkerSet)

-- ============================================================================
-- § 1: Clause-Type-Conditioned Alignment
-- ============================================================================

/-- The Mam alignment in a given clause type. -/
structure MamAlignment where
  /-- Marker set for S (intransitive subject) -/
  sMarker : MarkerSet
  /-- Marker set for A (transitive agent) -/
  aMarker : MarkerSet
  /-- Marker set for O (transitive patient) -/
  oMarker : MarkerSet
  deriving DecidableEq, Repr

/-- Matrix clause alignment: tripartite.
    S = Set B (ABS), A = Set A (ERG), O = default Set B (no agreement). -/
def matrixAlignment : MamAlignment :=
  { sMarker := .setB, aMarker := .setA, oMarker := .setB }

/-- Super-extended ergative alignment: neutral (all Set A). -/
def seeAlignment : MamAlignment :=
  { sMarker := .setA, aMarker := .setA, oMarker := .setA }

-- ============================================================================
-- § 2: Verification
-- ============================================================================

/-- Matrix alignment is tripartite: S, A, O each have distinct marking
    patterns (S ≠ A by marker set; S ≡ O by marker set but S has real
    agreement while O has default — the tripartite distinction is
    agreement-based, not marker-set-based). -/
theorem matrix_s_ne_a : matrixAlignment.sMarker ≠ matrixAlignment.aMarker := by
  decide

/-- SEE alignment is neutral: all arguments get the same marker set. -/
theorem see_is_neutral :
    seeAlignment.sMarker = seeAlignment.aMarker ∧
    seeAlignment.aMarker = seeAlignment.oMarker := ⟨rfl, rfl⟩

/-- The split: matrix and SEE differ in S marking and O marking. -/
theorem split_ergativity :
    matrixAlignment.sMarker ≠ seeAlignment.sMarker ∧
    matrixAlignment.oMarker ≠ seeAlignment.oMarker ∧
    matrixAlignment.aMarker = seeAlignment.aMarker := by
  exact ⟨by decide, by decide, rfl⟩

/-- A is invariant across the split: Set A in both matrix and SEE. -/
theorem a_invariant :
    matrixAlignment.aMarker = seeAlignment.aMarker := rfl

-- ============================================================================
-- § 3: Subordinators That Trigger SEE
-- ============================================================================

/-- Subordinators that trigger super-extended ergativity in SJA Mam. -/
inductive SEETrigger where
  | tun      -- *tu'n*: purpose/reason clauses
  | taj      -- *taj*: 'when' (past)
  | aj       -- *aj*: 'when' (future)
  | chix     -- *ch'ix*: 'almost'
  | nim      -- *ni'm*: 'right now'
  | nanx     -- *na'nx*: 'not yet'
  deriving DecidableEq, Repr

/-- All SEE triggers yield the same neutral alignment. -/
def seeTriggerAlignment (_ : SEETrigger) : MamAlignment := seeAlignment

-- ============================================================================
-- § 4: Object Agreement Restriction in SEE
-- ============================================================================

/-- In SEE clauses, object Set A markers are restricted to the default
    2/3SG form (t-). Agreeing Set A markers for the object are
    ungrammatical. This parallels the default Set B (tz'=) pattern for
    objects in matrix clauses. -/
def objectSetAIsDefault : Bool := true

/-- The parallel: in BOTH matrix and SEE, the object slot shows default
    (non-agreeing) morphology. The default marker just changes:
    - Matrix: default Set B (tz'=)
    - SEE: default Set A (t-) -/
theorem object_default_parallel :
    objectSetAIsDefault = true := rfl

end SuperExtendedErgativity

end Scott2023
