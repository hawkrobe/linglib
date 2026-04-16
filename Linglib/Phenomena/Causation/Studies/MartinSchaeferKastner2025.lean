import Linglib.Theories.Pragmatics.GriceanMaxims
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Fragments.French.Predicates

/-!
# @cite{martin-schaefer-kastner-2025} — The Lexical Pragmatics of Reflexive Marking

Martin, Fabienne, Florian Schäfer & Itamar Kastner. 2025. The lexical
pragmatics of reflexive marking. *Language* 101(3): 524–571.

## Core thesis

French anticausatives marked with *se* or left unmarked do not differ in
meaning. Rather, cooperative speakers manage the voice ambiguity introduced
by *se* (which can mark both anticausative and reflexive voice) in line with
the Manner supermaxim "Be perspicuous." The choice between ±*se* is driven
by three interacting factors:

1. **Verb class** (limited-control vs. in-control)
2. **Animacy** of the sole DP argument (human vs. nonhuman)
3. **Agent bias** — the tendency to interpret human DPs as agents

## Three generalizations (Table 1)

- **Unmarked limited-control preference** (human DP): limited-control ±*se*
  verbs (*rougir* 'blush') prefer the −*se* form. Rationale: −*se* is
  unambiguously anticausative; +*se* introduces a reflexive parse that
  clashes with shared assumptions (the change is not under the human's
  control). Avoiding ambiguity is optimal.

- **Marked in-control preference** (human DP): in-control ±*se* verbs
  (*plier* 'bend') prefer the +*se* form. Rationale: choosing −*se*
  would trigger a 'no-agent' inference (the speaker avoided the
  ambiguous form, signaling no agentive construal), which clashes with
  shared assumptions (the change IS typically under the human's control).
  Maintaining ambiguity is optimal.

- **Marked responsibility preference** (nonhuman DP): the +*se* form is
  preferred when the speaker aims to present the nonhuman as responsible.
  Only the *se*-marked form allows a reflexive parse, which is the only
  grammatical way to assign agency to a nonhuman sole argument.

## Bridges

- `VoiceFlavor.nonThematic` (@cite{schaefer-2008}): the anticausative voice
  flavor — contributes no semantics. Both ±*se* anticausatives have this.
- `VoiceFlavor.reflexive`: the reflexive voice flavor — assigns agent + theme
  to the sole DP. Only available with *se*.
- `MannerSubmaxim.avoidAmbiguity`: the Manner sub-maxim driving the
  unmarked limited-control preference.
- `cosSubjectProfile` / `motionCosSubjectProfile`: entailment profiles for
  anticausative subjects. ControlLevel cross-cuts these: limited-control
  and in-control property-change verbs share the same profile.

## Relationship to @cite{koontz-garboden-2009}

MSK2025 presupposes K-G 2009's reflexive-anticausative syncretism: *se*
marks both anticausative and reflexive voice because anticausativization
IS reflexivization. The pragmatic effects arise precisely because this
syncretism creates voice ambiguity that speakers must manage.
-/

namespace Phenomena.Causation.Studies.MartinSchaeferKastner2025

open Minimalism (VoiceFlavor)
open Semantics.Lexical.Verb.EntailmentProfile (EntailmentProfile predictsUnaccusative)
open Pragmatics.GriceanMaxims (MannerSubmaxim)
open Fragments.French.Predicates

-- ============================================================================
-- § 1: Core Types
-- ============================================================================

/-- Morphological class of an anticausative with respect to *se*-marking.
    @cite{martin-schaefer-kastner-2025} §1:
    - −*se*: AC form cannot have *se* (*changer de position*)
    - +*se*: AC form must have *se* (*s'affaiblir*)
    - ±*se*: AC form optionally has *se* (*casser*, *plier*, *rougir*) -/
inductive SeMarking where
  | minusSe     -- Unmarked anticausative (−se AC-verb)
  | plusSe      -- Marked anticausative (+se AC-verb)
  | plusMinusSe -- Optionally marked anticausative (±se AC-verb)
  deriving DecidableEq, Repr

/-- Lexical-semantic class of a change-of-state verb based on whether
    the change is typically under the human undergoer's control.
    @cite{martin-schaefer-kastner-2025} §1.1.

    This classification reflects shared world knowledge about human
    agency, NOT lexical-semantic structure. Property-change verbs from
    both classes share the same entailment profile (`cosSubjectProfile`);
    the distinction is pragmatic (see `control_level_not_from_entailments`). -/
inductive ControlLevel where
  /-- Change typically NOT under human control: *rougir* 'blush',
      *pâlir* 'get pale', *rajeunir* 'rejuvenate'. -/
  | limitedControl
  /-- Change typically under human control: *plier* 'bend',
      *(s')approcher* 'get close', *(se) courber* 'bend/curve'. -/
  | inControl
  deriving DecidableEq, Repr

/-- Animacy of the sole DP argument. -/
inductive Animacy where
  | human
  | nonhuman
  deriving DecidableEq, Repr

/-- Speaker's communicative goal regarding agency attribution.
    G3 (responsibility preference) is conditional on this goal:
    with nonhuman DPs, +*se* is preferred only when the speaker
    aims to present the entity as responsible. -/
inductive ResponsibilityGoal where
  | neutral              -- No particular goal regarding agency
  | conveyResponsibility -- Speaker aims to present entity as responsible
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Control Level and Entailment Profiles
-- ============================================================================

/-- ControlLevel is NOT derivable from Dowty's entailment profiles.
    Limited-control property-change verbs (*rougir*) and in-control
    property-change verbs (*refroidir*) share the same entailment
    profile: both lack volition, sentience, causation, and movement.

    The classification reflects shared world knowledge:
    - *rougir* 'blush': blushing is not typically under human control
    - *refroidir* 'cool down': cooling can be under human control

    Both are non-volitional changes of state with no movement. -/
theorem control_level_not_from_entailments :
    rougir.subjectEntailments = refroidir.subjectEntailments := by native_decide

/-- Movement in the entailment profile is a SUFFICIENT but not NECESSARY
    condition for in-control status. Motion verbs like *approcher* have
    movement AND are in-control. But property-change verbs like
    *refroidir* are in-control WITHOUT movement. -/
theorem movement_sufficient_not_necessary :
    approcher.subjectEntailments = some motionCosSubjectProfile ∧
    refroidir.subjectEntailments = some cosSubjectProfile ∧
    motionCosSubjectProfile.movement = true ∧
    cosSubjectProfile.movement = false := by decide

-- ============================================================================
-- § 3: Voice Ambiguity — the *se* syncretism
-- ============================================================================

/-- Voice flavors available for a form WITHOUT *se*.
    Only the anticausative (non-thematic) parse is available.
    The DP is a theme, not an agent. -/
def bareVoiceOptions : List VoiceFlavor := [.nonThematic]

/-- Voice flavors available for a form WITH *se*.
    Both anticausative and reflexive parses are available —
    this is the reflexive-anticausative syncretism
    (@cite{schaefer-2008}, @cite{koontz-garboden-2009}).

    K-G 2009's reflexivization analysis predicts exactly this
    syncretism: *se* marks reflexivization, which covers both
    the reflexive reading (the entity acts on itself) and the
    anticausative reading (EFFECTOR = THEME, agentivity bleached
    by underspecification). -/
def seVoiceOptions : List VoiceFlavor := [.nonThematic, .reflexive]

/-- The *se*-marked form is ambiguous: it has strictly more voice parses. -/
theorem se_is_ambiguous : seVoiceOptions.length > bareVoiceOptions.length := by decide

/-- The bare form is unambiguous for anticausative voice. -/
theorem bare_is_unambiguous : bareVoiceOptions = [.nonThematic] := rfl

/-- Both forms share the anticausative parse. -/
theorem shared_anticausative_parse :
    VoiceFlavor.nonThematic ∈ bareVoiceOptions ∧
    VoiceFlavor.nonThematic ∈ seVoiceOptions := ⟨List.mem_cons_self .., List.mem_cons_self ..⟩

/-- The reflexive parse is available only with *se*. -/
theorem reflexive_only_with_se :
    VoiceFlavor.reflexive ∈ seVoiceOptions ∧
    VoiceFlavor.reflexive ∉ bareVoiceOptions := by decide

-- ============================================================================
-- § 4: Agent Bias
-- ============================================================================

/-- Agent bias: human DPs in subject position are preferentially
    interpreted as agents (@cite{bickel-etal-2015}, @cite{sauppe-etal-2023}).
    With nonhuman DPs, the reflexive parse is not a priori salient. -/
def reflexiveParseSalient (anim : Animacy) : Bool :=
  match anim with
  | .human => true
  | .nonhuman => false

-- ============================================================================
-- § 5: Preference Predictions — the three generalizations
-- ============================================================================

/-- Whether the non-target sense (reflexive) clashes with shared
    assumptions about the event.

    - Limited-control verbs: the reflexive parse (DP = agent of own change)
      clashes with the assumption that the change is not under the human's
      control. Reflexive parse = misleading.
    - In-control verbs: the reflexive parse aligns with the assumption
      that the change IS under the human's control. Reflexive parse = not
      misleading. -/
def reflexiveParseClashes (ctrl : ControlLevel) : Bool :=
  match ctrl with
  | .limitedControl => true
  | .inControl => false

/-- The predicted preference for the form of ±*se* AC-verbs.
    Returns `some true` if +*se* is preferred, `some false` if −*se*
    is preferred, `none` if no preference arises.

    Derived compositionally from the paper's §2.2 reasoning:

    1. Is the reflexive parse salient? (`reflexiveParseSalient`)
       Agent bias activates with human DPs, making the reflexive parse
       of *se* a priori salient. With nonhuman DPs, no ambiguity to manage.

    2. If salient, does it clash with shared assumptions? (`reflexiveParseClashes`)
       - YES (limited-control): reflexive parse misleading → AVOID
         ambiguity → prefer bare (−*se*). @cite{dowty-1980}: if structure A
         is ambiguous between X and Y while B has only X, reserve A for Y.
       - NO (in-control): bare form's anti-implicature ("no agent") clashes
         instead → MAINTAIN ambiguity → prefer +*se*.

    §2.3 reframes "Avoid ambiguity" as "MANAGE ambiguity" — a single
    Manner principle with two optimal strategies depending on whether
    the nontarget sense aligns with or clashes against shared assumptions.

    For nonhuman DPs, see `predictSePreferenceExt` which incorporates
    the speaker's responsibility goal (G3). -/
def predictSePreference (ctrl : ControlLevel) (anim : Animacy) : Option Bool :=
  if !reflexiveParseSalient anim then none          -- no ambiguity to manage
  else if reflexiveParseClashes ctrl then some false -- avoid ambiguity: prefer bare
  else some true                                     -- maintain ambiguity: prefer +se

/-- Extended preference prediction incorporating the speaker's
    communicative goal (G3: responsibility preference for nonhuman DPs).

    With nonhuman DPs in neutral contexts, neither form is preferred
    (agent bias inactive). But when the speaker aims to convey that
    the nonhuman entity is responsible for the change, +*se* is
    preferred: only the *se*-marked form allows a reflexive parse,
    which is the only grammatical way to assign agency to a nonhuman
    sole argument. -/
def predictSePreferenceExt (ctrl : ControlLevel) (anim : Animacy)
    (goal : ResponsibilityGoal) : Option Bool :=
  match anim with
  | .human => predictSePreference ctrl .human
  | .nonhuman => match goal with
    | .neutral => none
    | .conveyResponsibility => some true  -- G3: prefer +se

/-- The pragmatic principle behind each preference. -/
def preferenceRationale (ctrl : ControlLevel) (anim : Animacy) :
    Option MannerSubmaxim :=
  match anim, ctrl with
  | .human, .limitedControl => some .avoidAmbiguity  -- avoid misleading reflexive parse
  | .human, .inControl      => some .avoidAmbiguity  -- avoid misleading no-agent inference
  | .nonhuman, _            => none                  -- no Manner pressure

-- ============================================================================
-- § 6: Generalization Theorems
-- ============================================================================

/-- **Generalization 1 — Unmarked limited-control preference (human DP).**
    With a limited-control ±*se* verb and a human DP, the −*se* form is
    preferred (experiment 1a: neutral/inchoative contexts). -/
theorem unmarked_limited_control_preference :
    predictSePreference .limitedControl .human = some false := rfl

/-- **Generalization 2 — Marked in-control preference (human DP).**
    With an in-control ±*se* verb and a human DP, the +*se* form is
    preferred (experiment 1b: all three contexts). -/
theorem marked_in_control_preference :
    predictSePreference .inControl .human = some true := rfl

/-- **Generalization 3 — Marked responsibility preference (nonhuman DP).**
    With a nonhuman DP, +*se* is preferred when the speaker aims to
    present the entity as responsible. Only *se* allows the reflexive
    parse, which is the only grammatical way to assign agency to a
    nonhuman sole argument. Control level is irrelevant — the mechanism
    (reflexive parse as sole agency channel) applies uniformly. -/
theorem marked_responsibility_preference :
    predictSePreferenceExt .limitedControl .nonhuman .conveyResponsibility = some true ∧
    predictSePreferenceExt .inControl .nonhuman .conveyResponsibility = some true := ⟨rfl, rfl⟩

/-- In neutral contexts with nonhuman DPs, no preference is predicted
    (agent bias inactive, no pragmatic pressure). -/
theorem no_preference_nonhuman_neutral :
    predictSePreferenceExt .limitedControl .nonhuman .neutral = none ∧
    predictSePreferenceExt .inControl .nonhuman .neutral = none := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Choice Prerequisite
-- ============================================================================

/-- Pragmatic form preferences arise ONLY with ±*se* verbs, where the
    speaker has a genuine choice between bare and *se*-marked forms.

    - −*se* verbs: only the bare form exists → no choice, no pragmatics
    - +*se* verbs: only the *se* form exists → no choice, no pragmatics
    - ±*se* verbs: both forms available → speaker must manage ambiguity

    The number of available forms determines whether pragmatic pressure
    applies. -/
def availableForms (marking : SeMarking) : Nat :=
  match marking with
  | .minusSe     => 1  -- bare only
  | .plusSe      => 1  -- se only
  | .plusMinusSe => 2  -- both

/-- Only ±*se* verbs have a genuine choice between forms. -/
theorem choice_only_with_plusMinusSe (m : SeMarking) :
    availableForms m > 1 ↔ m = .plusMinusSe := by
  cases m <;> simp [availableForms]

-- ============================================================================
-- § 8: Unaccusativity Bridge
-- ============================================================================

/-- All anticausative verb profiles predict unaccusativity
    (no volition, no causation, has P-Patient features).
    This is expected: anticausative subjects are derived internal
    arguments. -/
theorem cos_profile_unaccusative :
    predictsUnaccusative cosSubjectProfile = true := by native_decide

theorem motion_cos_profile_unaccusative :
    predictsUnaccusative motionCosSubjectProfile = true := by native_decide

-- ============================================================================
-- § 9: Against the Causation Claim
-- ============================================================================

/-- The causation claim (@cite{labelle-1992}, @cite{labelle-doron-2010})
    predicts that the presence vs. absence of *se* correlates with external
    vs. internal causation ACROSS THE BOARD. But the preferences documented
    here arise ONLY with ±*se* verbs (where the speaker has a choice) and
    ONLY with human DPs (where agent bias is active). This is incompatible
    with a semantic distinction between ±*se* forms.

    Formally: the same verb class (±*se*) shows OPPOSITE preferences
    depending on control level — limited-control prefers −*se*, in-control
    prefers +*se*. A semantic account predicting uniform behavior for all
    ±*se* verbs is falsified. -/
theorem opposite_preferences_falsify_uniform_semantics :
    predictSePreference .limitedControl .human ≠
    predictSePreference .inControl .human := by decide

-- ============================================================================
-- § 10: Experimental Data (raw means)
-- ============================================================================

/-- Raw mean acceptability ratings (7-point Likert scale).
    Encoded as rationals (×1000) for decidable comparison.
    From experiments 1a and 1b. -/
structure ConditionMean where
  context : String
  animacy : Animacy
  /-- +se mean × 1000 (rational encoding) -/
  plusSeMean : Nat
  /-- −se mean × 1000 (rational encoding) -/
  minusSeMean : Nat
  deriving Repr, DecidableEq

/-- Experiment 1a: limited-control verbs (Table 2).
    Values are raw means × 1000. -/
def experiment1a_data : List ConditionMean :=
  [ ⟨"inchoative", .human,    4109, 6321⟩
  , ⟨"inchoative", .nonhuman, 5167, 5583⟩
  , ⟨"neutral",    .human,    3218, 6526⟩
  , ⟨"neutral",    .nonhuman, 4616, 5282⟩
  , ⟨"reflexive",  .human,    4904, 3551⟩
  , ⟨"reflexive",  .nonhuman, 5917, 6449⟩ ]

/-- Experiment 1b: in-control verbs (Table 4).
    Values are raw means × 1000. -/
def experiment1b_data : List ConditionMean :=
  [ ⟨"inchoative", .human,    5590, 3506⟩
  , ⟨"inchoative", .nonhuman, 6051, 6237⟩
  , ⟨"neutral",    .human,    5904, 3628⟩
  , ⟨"neutral",    .nonhuman, 5641, 5269⟩
  , ⟨"reflexive",  .human,    5891, 2994⟩
  , ⟨"reflexive",  .nonhuman, 6308, 5654⟩ ]

/-- **G1 confirmed**: for limited-control verbs with human DPs in the
    neutral context, −*se* ratings (6.526) exceed +*se* ratings (3.218). -/
theorem exp1a_neutral_human_confirms_G1 :
    (3218 : Nat) < 6526 := by omega

/-- **G2 confirmed**: for in-control verbs with human DPs in the
    neutral context, +*se* ratings (5.904) exceed −*se* ratings (3.628). -/
theorem exp1b_neutral_human_confirms_G2 :
    (3628 : Nat) < 5904 := by omega

/-- **G1 reverses in reflexive context**: with limited-control verbs,
    human DPs in the reflexive context prefer +*se* (4.904 > 3.551).
    This is expected: the reflexive context forces an agentive construal,
    which only +*se* can express. -/
theorem exp1a_reflexive_human_reversal :
    (3551 : Nat) < 4904 := by omega

/-- **G2 holds in reflexive context too**: with in-control verbs,
    human DPs in the reflexive context strongly prefer +*se* (5.891 > 2.994). -/
theorem exp1b_reflexive_human_confirms_G2 :
    (2994 : Nat) < 5891 := by omega

end Phenomena.Causation.Studies.MartinSchaeferKastner2025
