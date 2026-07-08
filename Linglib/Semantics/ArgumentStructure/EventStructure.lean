import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Features.Aktionsart
import Linglib.Semantics.ArgumentStructure.DiathesisAlternation
import Linglib.Semantics.Verb.Root.Closure

/-!
# Event Structure Templates

Verbs decompose into **templates** (structural meaning that determines
argument realization) filled by **roots** (idiosyncratic content).
Templates compose via CAUSE; which sub-predicate determines argument
realization yields different syntactic frames.

The four templates here are [rappaport-hovav-levin-1998]'s; the
enriched two-predicate event structure for the wiping-verbs class
([rappaport-hovav-levin-2024]) is paper-anchored at
`Studies/RappaportHovavLevin2024.lean`.

## Bridges

- `Template.toAspectualProfile` → `AspectualProfile` (aspect)
- `HasResultState` → bieventive sub-event boundary ([krejci-2012]; [dowty-1979]; structural-scope alternative: [von-stechow-1996], [beck-2005])
- `cause_implies_resultState` → CAUSE entails result state
- `intransitiveVariant` → causative/inchoative alternation ([krejci-2012]; [rappaport-hovav-levin-1998])

-/

namespace ArgumentStructure.EventStructure
open Features

/-! ### Event structure templates -/

/-- Canonical event structure templates per [rappaport-hovav-levin-1998]. -/
inductive Template where
  | state          -- [x ⟨STATE⟩]
  | activity       -- [x ACT]
  | achievement    -- [BECOME [x ⟨STATE⟩]]
  | accomplishment -- [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]]
  deriving DecidableEq, Repr

/-! ### Template properties -/

/-- Does the template involve CAUSE? At the template level this coincides
with having an external causer position: only `.accomplishment` decomposes
as `[[x ACT] CAUSE [BECOME [y STATE]]]` per [rappaport-hovav-levin-1998]. -/
def Template.HasCause : Template → Prop
  | .accomplishment => True
  | _ => False

instance (t : Template) : Decidable t.HasCause := by
  cases t <;> unfold Template.HasCause <;> infer_instance

/-- The external-causer position is present iff the template has CAUSE
in its decomposition. -/
abbrev Template.HasExternalCauser : Template → Prop := Template.HasCause

/-- How many grammatically relevant predicates? -/
def Template.predicateCount : Template → Nat
  | .state => 1
  | .activity => 1
  | .achievement => 1
  | .accomplishment => 2  -- ACT + BECOME

/-- Predicted aspectual profile for each template. -/
def Template.toAspectualProfile : Template → AspectualProfile
  | .state => stateProfile
  | .activity => activityProfile
  | .achievement => achievementProfile
  | .accomplishment => accomplishmentProfile

/-- Predicted Vendler class for each template (derived from profile). -/
def Template.vendlerClass (t : Template) : VendlerClass :=
  t.toAspectualProfile.toVendlerClass

/-! ### Bieventive structure diagnostics -/

/-! Templates with complex internal structure — multiple sub-events connected
    by CAUSE or embedding BECOME — license scopal ambiguities that
    mono-eventive templates do not.

    At the template level, three diagnostics from [dowty-1979] reduce
    to two structural properties already defined above:

    1. ***again*/*re-* ambiguity** tracks `HasResultState`: templates
       embedding [BECOME [STATE]] allow restitutive readings where a
       scopal modifier targets just the result sub-event. The
       structural-scope rival ([von-stechow-1996], [beck-2005])
       derives restitutive readings from adverbial attachment levels
       rather than lexical entailment; the lexical-decomposition account
       encoded here is one of two live analyses.
    2. **Negation over CAUSE** ([koontz-garboden-2009]) tracks
       `HasCause`: negation can scope narrowly over CAUSE, denying
       the causal link while maintaining the result.
    3. **"By itself" licensing** ([koontz-garboden-2009]) also tracks
       `HasCause`: "without outside help" requires CAUSE in the meaning.

    [krejci-2012]'s insight is that some verbs assigned simpler templates
    (eat, wash, dress, learn) nonetheless pass all three diagnostics — evidence
    that they have bieventive, causative event structures in their simple forms.
    This verb-level property is captured in `RootTypology` and `ArgDerivation`,
    not at the template level here. -/

/-- Does the template embed a result state under BECOME?
    Templates with [BECOME [STATE]] have a sub-event boundary that
    scopal modifiers (*again*, *re-*, *almost*) can target independently. -/
def Template.HasResultState : Template → Prop
  | .achievement => True      -- [BECOME [x ⟨STATE⟩]]
  | .accomplishment => True   -- [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]]
  | _ => False

instance (t : Template) : Decidable t.HasResultState := by
  cases t <;> unfold Template.HasResultState <;> infer_instance

/-- CAUSE implies a result state (accomplishment embeds BECOME). -/
theorem cause_implies_resultState (t : Template) :
    t.HasCause → t.HasResultState := by
  cases t <;> decide

/-! ### From root signature to template ([beavers-koontz-garboden-2020] §1.3)

`Template` is a **function** of the root's collocational kind signature, not a
parallel theory: `.cause` → accomplishment, `.result` → achievement, `.manner` →
activity, else state. The `HasCause`/`HasResultState` diagnostics then reduce to
signature membership (`ofKinds_hasCause_iff`/`hasResultState_iff`), so the
denotational result entailment and `cause_implies_resultState` are one fact seen
through the signature. -/

section Signature
open Verb (LexKind Root)

/-- The event-structure template determined by a root's (closed) kind signature. -/
def Template.ofKinds (σ : Root.Kinds) : Template :=
  if LexKind.cause ∈ σ then .accomplishment
  else if LexKind.result ∈ σ then .achievement
  else if LexKind.manner ∈ σ then .activity
  else .state

/-- `HasCause` reduces to carrying the `cause` kind. -/
theorem ofKinds_hasCause_iff (σ : Root.Kinds) :
    (Template.ofKinds σ).HasCause ↔ LexKind.cause ∈ σ := by
  unfold Template.ofKinds
  split_ifs <;> simp_all [Template.HasCause]

/-- For a well-formed (collocationally closed) signature, `HasResultState`
    reduces to carrying the `result` kind — via `cause` ⟹ `result`. -/
theorem ofKinds_hasResultState_iff {σ : Root.Kinds}
    (h : σ.WellFormed) :
    (Template.ofKinds σ).HasResultState ↔ LexKind.result ∈ σ := by
  have hcr : LexKind.cause ∈ σ → LexKind.result ∈ σ := by
    intro hc
    have hr : LexKind.result ∈ Root.Kinds.close σ :=
      (Root.Kinds.mem_close_iff σ LexKind.result).mpr
        ⟨LexKind.cause, hc, by decide⟩
    have he : Root.Kinds.close σ = σ := h
    rwa [he] at hr
  unfold Template.ofKinds
  split_ifs with hc hr hm <;> simp_all [Template.HasResultState]

/-- A root's event-structure template, read off its collocational closure. -/
def _root_.Verb.Root.template (r : Root) : Template :=
  Template.ofKinds r.closedKinds

/-- A root entails a result state (template-level) iff it carries `result` —
    the [beavers-koontz-garboden-2020] result entailment, bridged to the
    `EventStructure` template diagnostic. -/
theorem _root_.Verb.Root.template_hasResultState_iff (r : Root) :
    r.template.HasResultState ↔ LexKind.result ∈ r.closedKinds := by
  apply ofKinds_hasResultState_iff
  show Root.Kinds.close r.closedKinds = r.closedKinds
  unfold Verb.Root.closedKinds
  exact Root.Kinds.close_idem _

end Signature

/-! ### Causative/Inchoative Alternation

    The accomplishment template [[x ACT] CAUSE [BECOME [y STATE]]]
    has an intransitive variant. On the **deletion** analysis
    ([krejci-2012]; [rappaport-hovav-levin-1998]), this is
    the achievement [BECOME [x STATE]], obtained by stripping the
    external cause — yielding a monoeventive representation.

    On the competing **reflexivization** analysis ([koontz-garboden-2009];
    [chierchia-2004]), anticausativization does NOT delete CAUSE.
    Instead, the reflexive clitic (*se*, *sich*) identifies the EFFECTOR
    with the THEME: the derived inchoative retains the full causative
    structure [∃v[CAUSE(v,e) ∧ EFFECTOR(v,x) ∧ BECOME(e,s) ∧ THEME(s,x)]].
    This preserves the Monotonicity Hypothesis and explains the
    cross-linguistic tendency for anticausative morphology to coincide
    with reflexive morphology (Haspelmath's typological work on the
    causative-anticausative alternation; see [alexiadou-schaefer-2015]
    for the modern cross-linguistic picture). -- UNVERIFIED: original
    text cited "Haspelmath 1990: 9/13 languages" — Haspelmath 1990 is on
    passives; the typology of C/I alternation is in Haspelmath 1993,
    figure unverified.

    `Template.intransitiveVariant` below implements the deletion view at the
    template level. The reflexivization analysis is formalized in
    `KoontzGarboden2009`. -/

/-- The intransitive variant of a template on the **deletion** analysis,
    stripping the external cause. Only accomplishments have an alternation
    partner.

    NOTE: this implements one specific analysis. On the reflexivization
    analysis ([koontz-garboden-2009]), the intransitive variant retains
    CAUSE with reflexivized arguments. -/
def Template.intransitiveVariant : Template → Option Template
  | .accomplishment => some .achievement
  | _ => none

/-- The intransitive variant retains the result state
    (BECOME STATE survives stripping of ACT CAUSE). -/
theorem intransitive_has_resultState (t t' : Template) :
    t.intransitiveVariant = some t' → t'.HasResultState := by
  cases t <;> simp [Template.intransitiveVariant]
  rintro rfl; decide

/-- The intransitive variant loses CAUSE (on the deletion analysis).
    [koontz-garboden-2009] disputes this on Monotonicity-Hypothesis
    grounds; see `Studies/KoontzGarboden2009.lean`. -/
theorem intransitive_no_cause (t t' : Template) :
    t.intransitiveVariant = some t' → ¬ t'.HasCause := by
  cases t <;> simp [Template.intransitiveVariant]
  rintro rfl; decide

/-- Only accomplishments have an intransitive variant
    (only templates with CAUSE can undergo the alternation). -/
theorem only_accomplishment_alternates (t : Template) :
    t.intransitiveVariant.isSome → t = .accomplishment := by
  cases t <;> simp [Template.intransitiveVariant]

/-! ### Argument realization from templates -/

/-- Predicted subject entailment profile for each template. The state
default is the sentient state-holder (S+IE, the admire-type value); this
conflates two Dowty-honest state profiles — sentience-entailed psych states
vs. bare desire states (IE alone, [dowty-1991] (29e)) — which the class map
separates as `psychState` vs `desire` in `LevinClassProfiles.lean` (not
importable here: it sits downstream of this file). -/
def Template.subjectProfile : Template → EntailmentProfile
  | .state          => { sentience := true, independentExistence := true }
  | .activity       => activitySubjectProfile
  | .achievement    => achievementSubjectProfile
  | .accomplishment => accomplishmentSubjectProfile

/-- Predicted object entailment profile (if any). The accomplishment
default carries no IT; per-verb IT additions live at the Fragment level. -/
def Template.objectProfile : Template → Option EntailmentProfile
  | .accomplishment => some accomplishmentObjectProfile
  | _ => none

/-- Accomplishment subject is a full agent (5 P-Agent entailments). -/
theorem accomplishment_subject_is_agent :
    (Template.subjectProfile .accomplishment).pAgentScore = 5 := by decide

/-! ### Bridge to [levin-1993] verb classes -/

/-! Levin classes map to event structure templates via meaning components
    ([rappaport-hovav-levin-1998]; [rappaport-hovav-levin-2010]):

    | Meaning component pattern | Template | Example class |
    |---|---|---|
    | CoS + causation | accomplishment | break (45.1), destroy (44) |
    | CoS, no causation | achievement | appear (48.1), calve (28) |
    | No CoS, no motion | state | exist (47.1), admire (31.2) |
    | Otherwise | activity | hit (18.1), run (51.3) |

    The wiping-verbs class (10.4) gets the activity template via the
    decision tree, with its motion-and-sustained-contact substructure
    formalized at `Studies/RappaportHovavLevin2024.lean`. -/

/-! ### Process vs state-change ([bohnemeyer-2004]) -/

/-- The fundamental binary distinction in event types: whether a predicate
    encodes a process (PROC only) or a state change (involves CHANGE).

    This crosscuts Vendler's four-way classification: degree achievements
    are Vendler activities or accomplishments depending on scale boundedness
    but are event-structurally state-change predicates ([bohnemeyer-2004]
    on degree achievements within the Yukatek transitivity system).

    [bohnemeyer-2004] argues this is the primary semantic distinction
    governing verb classification in Yukatek Maya — more fundamental than
    Vendler classes for predicting argument linking and transitivization. -/
inductive EventType where
  | process     -- PROC only: walk, sing, roll, buzz
  | stateChange -- Involves CHANGE: die, break, grow, darken, sit
  deriving DecidableEq, Repr

/-- Derive event type from template. Activities are processes; states,
    achievements, and accomplishments involve state change. -/
def Template.eventType : Template → EventType
  | .activity => .process
  | _ => .stateChange

/-- Whether a process is internally caused — the event is instigated by
    a participant — or externally caused — occurring "spontaneously"
    without an instigator.

    This is a per-verb property of the ROOT, not of the template.
    Two activity verbs can differ: *sing* (internal) vs *roll* (external).

    [levin-hovav-1995] on the internal/external causation distinction
    in Unaccusativity; [bohnemeyer-2004] on internal/external
    causation in Yukatek argument linking.

    [koontz-garboden-2009]: externally caused COS verbs have
    CAUSE+EFFECTOR in their LSR and license *por sí solo* 'by itself'.
    Internally caused COS verbs (*empeorar*, *hervir*, *crecer*) lack CAUSE
    in their LSR and reject *por sí solo*. -/
inductive InternalExternalCause where
  | internal   -- instigated by a participant (sing, walk, write, play)
  | external   -- no instigator; "spontaneous" (break, fall, roll, buzz)
  deriving DecidableEq, Repr

/-- Externally caused COS verbs have CAUSE in their LSR;
    internally caused COS verbs do not ([koontz-garboden-2009];
    [levin-hovav-1995]). Per [koontz-garboden-2009], this
    licenses *por sí solo* / *by itself* modification on externally
    caused inchoatives and rejects it on internally caused ones.

    This determines whether derived inchoatives (on the reflexivization
    analysis) retain a CAUSE operator. -/
def InternalExternalCause.HasCauseInLSR : InternalExternalCause → Prop
  | .external => True
  | .internal => False

instance (c : InternalExternalCause) : Decidable c.HasCauseInLSR := by
  cases c <;> unfold InternalExternalCause.HasCauseInLSR <;> infer_instance

end ArgumentStructure.EventStructure

namespace ArgumentStructure

/-- Predicted event structure template from meaning components. -/
def MeaningComponents.predictedTemplate : MeaningComponents → ArgumentStructure.EventStructure.Template
  | mc => if mc.changeOfState && mc.causation then .accomplishment
    else if mc.changeOfState then .achievement
    else if !mc.motion && !mc.contact then .state
    else .activity

/-- Predicted template for a Levin class. -/
def LevinClass.eventTemplate : LevinClass → ArgumentStructure.EventStructure.Template
  | c => c.meaningComponents.predictedTemplate

end ArgumentStructure

namespace ArgumentStructure.EventStructure

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

/-! ### Wiping verbs (Levin 10.4) -/

/-- Wipe class → accomplishment (changeOfState + causation per
its MeaningComponents). The two-predicate (motion + sustained contact)
substructure is at `Studies/RappaportHovavLevin2024.lean`. -/
theorem wipe_is_accomplishment :
    LevinClass.wipe.eventTemplate = .accomplishment := rfl

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

/-! ### Bridge: Event Structure ↔ Diathesis Alternation

`predictedTemplate` and `predictedAlternation` are two predictions computed from the
same `MeaningComponents` feature vector. This section proves their agreement and shows
that `MeaningComponents.fuse` simultaneously derives both template shift and new
alternation predictions from a single componentwise OR operation.

The central theorem — `ci_alternation_iff_template_alternates` — says the
causative/inchoative alternation is exactly the syntactic reflex of having an
accomplishment event template (which has an intransitive variant), modulo
`instrumentSpec`. This connects [levin-1993]'s diathesis alternation diagnostics
to [rappaport-hovav-levin-1998]'s event structure decomposition. -/

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
    restitutive readings on the lexical-decomposition account
    ([dowty-1979]; cf. structural-scope rival [von-stechow-1996],
    [beck-2005]). -/
theorem fuse_cos_caus_has_result_state (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true) :
    (v.fuse c).predictedTemplate.HasResultState := by
  rw [fuse_cos_caus_yields_accomplishment v c hCoS hCaus]; decide

/-- Fusion with CoS + causation yields CAUSE structure, enabling
    negation-over-CAUSE readings and *by itself* modification
    ([koontz-garboden-2009]). -/
theorem fuse_cos_caus_has_cause (v c : MeaningComponents)
    (hCoS : c.changeOfState = true) (hCaus : c.causation = true) :
    (v.fuse c).predictedTemplate.HasCause := by
  rw [fuse_cos_caus_yields_accomplishment v c hCoS hCaus]; decide

end ArgumentStructure.EventStructure
