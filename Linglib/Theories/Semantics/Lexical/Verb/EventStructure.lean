/-
# Event Structure Templates

Verbs decompose into **templates** (structural meaning that determines
argument realization) filled by **roots** (idiosyncratic content).
Templates compose via CAUSE; which sub-predicate determines argument
realization yields different syntactic frames.

Key insight from @cite{rappaport-hovav-levin-2024}: verbs of motion + sustained contact (sweep,
rub, scrape) have two grammatically relevant predicates — MOVE and CONTACT.
Which predicate determines argument realization yields variable agentivity
and distinct syntactic frames.

## Bridges

- `Template.toAspectualProfile` → `AspectualProfile` (aspect)
- `motionContact_variable_agentivity` → `sweepBasicSubjectProfile` (proto-roles)
- `contact_determines_implies_effector_subject` → `isEffector` (proto-roles)
- `lexicalize_increases_agentivity` → `pAgentScore` ordering (proto-roles)
- `hasResultState` → bieventive sub-event boundary (@cite{krejci-2012}; @cite{dowty-1979})
- `cause_implies_resultState` → CAUSE entails result state
- `intransitiveVariant` → causative/inchoative alternation (@cite{krejci-2012}; @cite{rappaport-hovav-levin-1998})

-/

import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Core.Lexical.DiathesisAlternation

namespace Semantics.Lexical.Verb.EventStructure

open Core.Verbs
open Semantics.Lexical.Verb.EntailmentProfile
open Semantics.Tense.Aspect.LexicalAspect

-- ════════════════════════════════════════════════════
-- § 1. Event Structure Templates (@cite{rappaport-hovav-levin-1998} + 2024)
-- ════════════════════════════════════════════════════

/-- Canonical event structure templates.
    The first four are from @cite{rappaport-hovav-levin-1998}. `motionContact` is from @cite{rappaport-hovav-levin-2024}
    for the sweep/rub/scrape class: [x MOVE y] WHILE [x CONTACT y]. -/
inductive Template where
  | state          -- [x ⟨STATE⟩]
  | activity       -- [x ACT]
  | achievement    -- [BECOME [x ⟨STATE⟩]]
  | accomplishment -- [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]]
  | motionContact  -- [x MOVE y] WHILE [x CONTACT y]
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Template Properties
-- ════════════════════════════════════════════════════

/-- Does the template involve CAUSE? -/
def Template.hasCause : Template → Bool
  | .accomplishment => true
  | _ => false

/-- Does the template have an external causer position? -/
def Template.hasExternalCauser : Template → Bool
  | .accomplishment => true
  | _ => false

/-- How many grammatically relevant predicates? -/
def Template.predicateCount : Template → Nat
  | .state => 1
  | .activity => 1
  | .achievement => 1
  | .accomplishment => 2  -- ACT + BECOME
  | .motionContact => 2   -- MOVE + CONTACT

/-- Predicted aspectual profile for each template. -/
def Template.toAspectualProfile : Template → AspectualProfile
  | .state => stateProfile
  | .activity => activityProfile
  | .achievement => achievementProfile
  | .accomplishment => accomplishmentProfile
  | .motionContact => activityProfile  -- Atelic by default (sweep is an activity)

/-- Predicted Vendler class for each template (derived from profile). -/
def Template.vendlerClass (t : Template) : VendlerClass :=
  t.toAspectualProfile.toVendlerClass

-- ════════════════════════════════════════════════════
-- § 3. Bieventive Structure Diagnostics
-- (@cite{krejci-2012}; @cite{dowty-1979}; @cite{koontz-garboden-2009})
-- ════════════════════════════════════════════════════

/-! Templates with complex internal structure — multiple sub-events connected
    by CAUSE or embedding BECOME — license scopal ambiguities that
    mono-eventive templates do not.

    At the template level, three diagnostics from @cite{dowty-1979} reduce
    to two structural properties already defined above:

    1. ***again*/*re-* ambiguity** tracks `hasResultState`: templates
       embedding [BECOME [STATE]] allow restitutive readings where a
       scopal modifier targets just the result sub-event.
    2. **Negation over CAUSE** (@cite{koontz-garboden-2009}) tracks
       `hasCause`: negation can scope narrowly over CAUSE, denying
       the causal link while maintaining the result.
    3. **"By itself" licensing** (@cite{koontz-garboden-2009}) also tracks
       `hasCause`: "without outside help" requires CAUSE in the meaning.

    @cite{krejci-2012}'s insight is that some verbs assigned simpler templates
    (eat, wash, dress, learn) nonetheless pass all three diagnostics — evidence
    that they have bieventive, causative event structures in their simple forms.
    This verb-level property is captured in `RootTypology` and `ArgDerivation`,
    not at the template level here. -/

/-- Does the template embed a result state under BECOME?
    Templates with [BECOME [STATE]] have a sub-event boundary that
    scopal modifiers (*again*, *re-*, *almost*) can target independently. -/
def Template.hasResultState : Template → Bool
  | .achievement => true      -- [BECOME [x ⟨STATE⟩]]
  | .accomplishment => true   -- [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]]
  | _ => false

/-- CAUSE implies a result state (accomplishment embeds BECOME). -/
theorem cause_implies_resultState (t : Template) :
    t.hasCause = true → t.hasResultState = true := by
  cases t <;> simp [Template.hasCause, Template.hasResultState]

/-! ### Causative/Inchoative Alternation

    The accomplishment template [[x ACT] CAUSE [BECOME [y STATE]]]
    has an intransitive variant. On the **deletion** analysis
    (@cite{krejci-2012}; @cite{rappaport-hovav-levin-1998}), this is
    the achievement [BECOME [x STATE]], obtained by stripping the
    external cause — yielding a monoeventive representation.

    On the competing **reflexivization** analysis (@cite{koontz-garboden-2009};
    @cite{chierchia-2004}), anticausativization does NOT delete CAUSE.
    Instead, the reflexive clitic (*se*, *sich*) identifies the EFFECTOR
    with the THEME: the derived inchoative retains the full causative
    structure [∃v[CAUSE(v,e) ∧ EFFECTOR(v,x) ∧ BECOME(e,s) ∧ THEME(s,x)]].
    This preserves the Monotonicity Hypothesis and explains why
    anticausative morphology cross-linguistically coincides with reflexive
    morphology (Haspelmath 1990: 9/13 languages).

    `Template.intransitiveVariant` below implements the deletion view at the
    template level. The reflexivization analysis is formalized in
    `KoontzGarboden2009`. -/

/-- The intransitive variant of a template on the **deletion** analysis,
    stripping the external cause. Only accomplishments have an alternation
    partner.

    NOTE: this implements one specific analysis. On the reflexivization
    analysis (@cite{koontz-garboden-2009}), the intransitive variant retains
    CAUSE with reflexivized arguments. -/
def Template.intransitiveVariant : Template → Option Template
  | .accomplishment => some .achievement
  | _ => none

/-- The intransitive variant retains the result state
    (BECOME STATE survives stripping of ACT CAUSE). -/
theorem intransitive_has_resultState (t t' : Template) :
    t.intransitiveVariant = some t' → t'.hasResultState = true := by
  cases t <;> simp [Template.intransitiveVariant, Template.hasResultState]
  rintro rfl; rfl

/-- The intransitive variant loses CAUSE (on the deletion analysis).
    @cite{koontz-garboden-2009} disputes this — see `AnticausativeAnalysis`. -/
theorem intransitive_no_cause (t t' : Template) :
    t.intransitiveVariant = some t' → t'.hasCause = false := by
  cases t <;> simp [Template.intransitiveVariant, Template.hasCause]
  rintro rfl; rfl

/-- Only accomplishments have an intransitive variant
    (only templates with CAUSE can undergo the alternation). -/
theorem only_accomplishment_alternates (t : Template) :
    t.intransitiveVariant.isSome → t = .accomplishment := by
  cases t <;> simp [Template.intransitiveVariant]

-- ════════════════════════════════════════════════════
-- § 4. Argument Realization from Templates
-- ════════════════════════════════════════════════════

/-- Predicted subject entailment profile for each template. -/
def Template.subjectProfile : Template → EntailmentProfile
  | .state =>
    -- State holder: sentience + IE only
    ⟨false, true, false, false, true, false, false, false, false, false⟩
  | .activity =>
    -- Activity: V+S+M+IE (no causation — the template [x ACT] does not
    -- entail causing a change in another participant; Dowty P-Agent #3
    -- requires "another participant"). Transitive activities (hit) add
    -- C at the class level via root-contributed objects.
    ⟨true, true, false, true, true, false, false, false, false, false⟩
  | .achievement =>
    -- Achievement subject: M+IE+CoS (undergoes change)
    ⟨false, false, false, true, true, true, false, false, false, false⟩
  | .accomplishment =>
    -- Accomplishment subject: V+S+C+M+IE (full proto-agent, causes result)
    ⟨true, true, true, true, true, false, false, false, false, false⟩
  | .motionContact =>
    -- Motion+contact subject: M+IE only (underspecified for agentivity)
    sweepBasicSubjectProfile

/-- Predicted object entailment profile (if any). -/
def Template.objectProfile : Template → Option EntailmentProfile
  | .state => none
  | .activity => none
  | .achievement => none
  | .accomplishment =>
    -- Result patient: CoS+CA (undergoes caused change).
    -- IT (incremental theme) is NOT included in the template default —
    -- not all accomplishment objects measure the event. Verbs with IT
    -- (eat, build) add it at the class level.
    some ⟨false, false, false, false, false, true, false, true, false, false⟩
  | .motionContact =>
    -- Force recipient: CA+St (causally affected, stationary surface)
    some ⟨false, false, false, false, false, false, false, true, true, false⟩

/-- Accomplishment subject is a full agent (5 P-Agent entailments). -/
theorem accomplishment_subject_is_agent :
    (Template.subjectProfile .accomplishment).pAgentScore = 5 := by native_decide

/-- motionContact subject has the same profile as basic sweep
    (movement + IE, underspecified for agentivity). -/
theorem motionContact_variable_agentivity :
    Template.subjectProfile .motionContact = sweepBasicSubjectProfile := rfl

-- ════════════════════════════════════════════════════
-- § 5. Which Predicate Determines Argument Realization
-- ════════════════════════════════════════════════════

/-- For motionContact verbs, which sub-predicate determines argument
    realization (@cite{rappaport-hovav-levin-2024} §3.3–3.4). -/
inductive DeterminingPredicate where
  | motion   -- MOVE determines: unaccusative/transitive+PP frames
  | contact  -- CONTACT determines: simple transitive frame
  deriving DecidableEq, Repr

/-- When CONTACT determines argument realization, the subject is an
    effector (movement + IE → external argument). This yields the simple
    transitive frame: "The wind swept the deck". -/
theorem contact_determines_implies_effector_subject :
    isEffector (Template.subjectProfile .motionContact) = true := by native_decide

/-- The motionContact object profile exists and is a force recipient. -/
theorem motionContact_object_is_forceRecipient :
    ∃ p, Template.objectProfile .motionContact = some p ∧
    isForceRecipient p = true := ⟨_, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Instrument Lexicalization (@cite{rappaport-hovav-levin-2024} §3.5)
-- ════════════════════════════════════════════════════

/-- Instrument lexicalization adds agentivity to a template by restricting
    the moving entity to a specific instrument, forcing volition + sentience
    + causation. The result is the broom-sweep subject profile. -/
def Template.lexicalizeInstrument : Template → EntailmentProfile
  | .motionContact => sweepBroomSubjectProfile
  | t => t.subjectProfile  -- No-op for other templates

/-- Instrument lexicalization strictly increases agentivity for motionContact
    templates (@cite{rappaport-hovav-levin-2024} §3.5: broom-sweep is more agentive than basic sweep). -/
theorem lexicalize_increases_agentivity :
    (Template.lexicalizeInstrument .motionContact).pAgentScore >
    (Template.subjectProfile .motionContact).pAgentScore := by native_decide

/-- Lexicalized motionContact has full proto-agent profile (5 entailments). -/
theorem lexicalized_is_full_agent :
    (Template.lexicalizeInstrument .motionContact).pAgentScore = 5 := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to @cite{levin-1993} Verb Classes
-- ════════════════════════════════════════════════════

/-! Levin classes map to event structure templates via meaning components.
    The core correspondence (@cite{rappaport-hovav-levin-1998} §3; @cite{rappaport-hovav-levin-2010} §2):

    | Meaning component pattern | Template | Example class |
    |---|---|---|
    | CoS + causation | accomplishment | break (45.1), destroy (44) |
    | CoS, no causation | achievement | appear (48.1), calve (28) |
    | No CoS, no motion | state | exist (47.1), admire (31.2) |
    | Otherwise | activity | hit (18.1), run (51.3) |

    The `motionContact` template is specific to the sweep/rub/scrape
    class and requires a class-specific override. -/

-- ════════════════════════════════════════════════════
-- § 8. Process vs State-Change (@cite{bohnemeyer-2004})
-- ════════════════════════════════════════════════════

/-- The fundamental binary distinction in event types: whether a predicate
    encodes a process (PROC only) or a state change (involves CHANGE).

    This crosscuts Vendler's four-way classification: degree achievements
    are Vendler activities or accomplishments depending on scale boundedness
    but are event-structurally state-change predicates (@cite{bohnemeyer-2004} §5).

    @cite{bohnemeyer-2004} argues this is the primary semantic distinction
    governing verb classification in Yukatek Maya — more fundamental than
    Vendler classes for predicting argument linking and transitivization. -/
inductive EventType where
  | process     -- PROC only: walk, sing, roll, buzz
  | stateChange -- Involves CHANGE: die, break, grow, darken, sit
  deriving DecidableEq, Repr

/-- Derive event type from template.
    Activities and motionContact are processes; states, achievements, and
    accomplishments involve state change. -/
def Template.eventType : Template → EventType
  | .activity => .process
  | .motionContact => .process
  | _ => .stateChange

/-- Whether a process is internally caused — the event is instigated by
    a participant — or externally caused — occurring "spontaneously"
    without an instigator.

    This is a per-verb property of the ROOT, not of the template.
    Two activity verbs can differ: *sing* (internal) vs *roll* (external).

    @cite{levin-hovav-1995} §4; @cite{bohnemeyer-2004} §2,6.

    @cite{koontz-garboden-2009} §4.1: externally caused COS verbs have
    CAUSE+EFFECTOR in their LSR and license *por sí solo* 'by itself'.
    Internally caused COS verbs (*empeorar*, *hervir*, *crecer*) lack CAUSE
    in their LSR and reject *por sí solo*. -/
inductive CausationType where
  | internal   -- instigated by a participant (sing, walk, write, play)
  | external   -- no instigator; "spontaneous" (break, fall, roll, buzz)
  deriving DecidableEq, Repr

/-- Externally caused COS verbs have CAUSE in their LSR;
    internally caused COS verbs do not (@cite{koontz-garboden-2009} §4.1;
    @cite{levin-hovav-1995} §4).

    This determines whether derived inchoatives (on the reflexivization
    analysis) retain a CAUSE operator. -/
def CausationType.hasCauseInLSR : CausationType → Bool
  | .external => true
  | .internal => false

/-- *por sí solo* / *by itself* is licensed iff CAUSE is present in the
    LSR (@cite{koontz-garboden-2009} §4.1). Stative predicates and
    internally caused COS verbs reject it. -/
def CausationType.licensesBySelf : CausationType → Bool
  | .external => true
  | .internal => false

end Semantics.Lexical.Verb.EventStructure

namespace Core.Verbs

/-- Predicted event structure template from meaning components. -/
def MeaningComponents.predictedTemplate : MeaningComponents → Semantics.Lexical.Verb.EventStructure.Template
  | mc => if mc.changeOfState && mc.causation then .accomplishment
    else if mc.changeOfState then .achievement
    else if !mc.motion && !mc.contact then .state
    else .activity

/-- Predicted template for a Levin class, with class-specific overrides. -/
def LevinClass.eventTemplate : LevinClass → Semantics.Lexical.Verb.EventStructure.Template
  -- motionContact is class-specific (sweep/rub/scrape)
  | .wipe => .motionContact
  | c => c.meaningComponents.predictedTemplate

end Core.Verbs

namespace Semantics.Lexical.Verb.EventStructure
open Core.Verbs

/-! ### Verification: canonical quadruple -/

/-- Break → accomplishment (CoS + causation → [ACT CAUSE BECOME]). -/
theorem break_is_accomplishment :
    LevinClass.break_.eventTemplate = .accomplishment := rfl

/-- Hit → activity (contact + motion, no CoS → [ACT]). -/
theorem hit_is_activity :
    LevinClass.hit.eventTemplate = .activity := rfl

/-- Touch → activity (contact only, no CoS). -/
theorem touch_is_activity :
    LevinClass.touch.eventTemplate = .activity := rfl

/-- Cut → accomplishment (CoS + causation). -/
theorem cut_is_accomplishment :
    LevinClass.cut.eventTemplate = .accomplishment := rfl

/-! ### Change-of-state classes → accomplishment -/

/-- All §45 CoS classes map to accomplishment. -/
theorem cos_classes_accomplishment :
    LevinClass.break_.eventTemplate = .accomplishment
    ∧ LevinClass.bend.eventTemplate = .accomplishment
    ∧ LevinClass.cooking.eventTemplate = .accomplishment
    ∧ LevinClass.otherCoS.eventTemplate = .accomplishment
    ∧ LevinClass.destroy.eventTemplate = .accomplishment := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Motion classes → activity -/

/-- Motion verbs are activities (no CoS, have motion). -/
theorem motion_is_activity :
    LevinClass.mannerOfMotion.eventTemplate = .activity
    ∧ LevinClass.inherentlyDirectedMotion.eventTemplate = .activity := ⟨rfl, rfl⟩

/-! ### Stative classes → state -/

/-- Perception/psych statives map to state template. -/
theorem stative_classes_state :
    LevinClass.exist.eventTemplate = .state
    ∧ LevinClass.admire.eventTemplate = .state
    ∧ LevinClass.want.eventTemplate = .state := ⟨rfl, rfl, rfl⟩

/-! ### Achievement classes -/

/-- Appear (CoS without causation) → achievement. -/
theorem appear_is_achievement :
    LevinClass.appear.eventTemplate = .achievement := rfl

/-- Calve (CoS without causation) → achievement. -/
theorem calve_is_achievement :
    LevinClass.calve.eventTemplate = .achievement := rfl

/-! ### Special: motionContact -/

/-- Wipe class → motionContact (class-specific override). -/
theorem wipe_is_motionContact :
    LevinClass.wipe.eventTemplate = .motionContact := rfl

/-! ### Template → aspectual class consistency -/

/-- Accomplishment classes (break, cut) are predicted telic. -/
theorem break_telic :
    LevinClass.break_.eventTemplate.vendlerClass = .accomplishment := rfl

/-- Activity classes (hit, run) are predicted atelic. -/
theorem hit_atelic :
    LevinClass.hit.eventTemplate.vendlerClass = .activity := rfl

/-- State classes (exist, admire) are predicted stative. -/
theorem exist_stative :
    LevinClass.exist.eventTemplate.vendlerClass = .state := rfl

/-! ### § 9. Bridge: Event Structure ↔ Diathesis Alternation

`predictedTemplate` and `predictedAlternation` are two predictions computed from the
same `MeaningComponents` feature vector. This section proves their agreement and shows
that `MeaningComponents.fuse` simultaneously derives both template shift and new
alternation predictions from a single componentwise OR operation.

The central theorem — `ci_alternation_iff_template_alternates` — says the
causative/inchoative alternation is exactly the syntactic reflex of having an
accomplishment event template (which has an intransitive variant), modulo
`instrumentSpec`. This connects @cite{levin-1993}'s diathesis alternation diagnostics
to @cite{rappaport-hovav-levin-1998}'s event structure decomposition. -/

/-- The causative/inchoative alternation is available iff the verb's event template
    has an intransitive variant (i.e., is an accomplishment), given no instrumentSpec.

    Both conditions reduce to `changeOfState ∧ causation`, making the alternation
    prediction and the event structure prediction two views of a single semantic fact. -/
theorem ci_alternation_iff_template_alternates (mc : MeaningComponents)
    (h_inst : mc.instrumentSpec = false) :
    mc.predictedAlternation .causativeInchoative = true ↔
    mc.predictedTemplate.intransitiveVariant.isSome = true := by
  rcases mc with ⟨cos, con, mot, caus, inst, man⟩
  subst h_inst
  cases cos <;> cases con <;> cases mot <;> cases caus <;>
    simp_all [MeaningComponents.predictedAlternation, MeaningComponents.predictedTemplate,
              Template.intransitiveVariant]

/-- instrumentSpec breaks the template↔alternation correspondence: cut verbs have
    accomplishment template (they cause state change) but cannot undergo
    causative/inchoative alternation (instrument specification requires an agent).

    This is why `ci_alternation_iff_template_alternates` requires
    `instrumentSpec = false` — the hypothesis is necessary, not just sufficient. -/
theorem instrumentSpec_breaks_correspondence :
    LevinClass.cut.eventTemplate = .accomplishment ∧
    LevinClass.cut.eventTemplate.intransitiveVariant = some .achievement ∧
    LevinClass.cut.meaningComponents.predictedAlternation .causativeInchoative = false :=
  ⟨rfl, rfl, rfl⟩

/-- Fusion with CoS + causation yields accomplishment template regardless of
    the verb's original template. The resultative construction adds
    [CAUSE [BECOME [STATE]]], upgrading any verb to accomplishment. -/
theorem fuse_cos_caus_yields_accomplishment (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true) :
    (v.fuse c).predictedTemplate = .accomplishment := by
  rcases v with ⟨cos, con, mot, caus, inst, man⟩
  rcases c with ⟨cos', con', mot', caus', inst', man'⟩
  simp_all [MeaningComponents.fuse, MeaningComponents.predictedTemplate]

/-- One fusion, three consequences: accomplishment template, causative/inchoative
    alternation, and intransitive variant — all from a single componentwise OR. -/
theorem fuse_dual_prediction (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true)
    (hInstV : v.instrumentSpec = false) (hInstC : c.instrumentSpec = false) :
    (v.fuse c).predictedTemplate = .accomplishment ∧
    (v.fuse c).predictedAlternation .causativeInchoative = true ∧
    (v.fuse c).predictedTemplate.intransitiveVariant = some .achievement := by
  have h_tmpl := fuse_cos_caus_yields_accomplishment v c hCoS hCaus
  have h_inst : (v.fuse c).instrumentSpec = false := by
    rcases v with ⟨_, _, _, _, inst, _⟩; rcases c with ⟨_, _, _, _, inst', _⟩
    simp_all [MeaningComponents.fuse]
  exact ⟨h_tmpl,
    (ci_alternation_iff_template_alternates _ h_inst).mpr
      (by simp [h_tmpl, Template.intransitiveVariant]),
    by simp [h_tmpl, Template.intransitiveVariant]⟩

/-- Fusion-induced Vendler class shift: fusion with CoS + causation
    yields accomplishment Vendler class (telic, bounded). -/
theorem fuse_vendler_class_shift (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true) :
    (v.fuse c).predictedTemplate.vendlerClass = .accomplishment := by
  rw [fuse_cos_caus_yields_accomplishment v c hCoS hCaus]; rfl

/-- Fusion with CoS + causation yields result state, enabling *again*/*re-*
    restitutive readings (@cite{dowty-1979}). -/
theorem fuse_cos_caus_has_result_state (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true) :
    (v.fuse c).predictedTemplate.hasResultState = true := by
  rw [fuse_cos_caus_yields_accomplishment v c hCoS hCaus]; rfl

/-- Fusion with CoS + causation yields CAUSE structure, enabling
    negation-over-CAUSE readings and *by itself* modification
    (@cite{koontz-garboden-2009}). -/
theorem fuse_cos_caus_has_cause (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true) :
    (v.fuse c).predictedTemplate.hasCause = true := by
  rw [fuse_cos_caus_yields_accomplishment v c hCoS hCaus]; rfl

end Semantics.Lexical.Verb.EventStructure
