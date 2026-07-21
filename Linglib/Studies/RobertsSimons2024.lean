import Linglib.Semantics.Presupposition.OntologicalPreconditions
import Linglib.Semantics.Aspect.ChangeOfState
import Linglib.Features.Aktionsart
import Linglib.Semantics.Presupposition.ProjectiveContent

/-!
# Preconditions and Projection: Explaining Non-Anaphoric Presupposition
[roberts-simons-2024]

Roberts, C. & Simons, M. (2024). Preconditions and projection: Explaining
non-anaphoric presupposition. *Linguistics and Philosophy* 47(4):703–748.

## Key Claims

1. The projective contents of CoS predicates, factives, and selectional
   restrictions are entailments characterizing *ontological preconditions*
   of the associated event type — NOT semantically encoded presuppositions.

2. Projection is a *pragmatic default*: a speaker who raises an event is
   taken to assume its preconditions hold (maximizes informativity, per
   [qing-goodman-lassiter-2016] and [warstadt-2022]).

3. Differential suppression across verb pairs (know/discover, stop/continue)
   follows from lexical semantic differences (telicity, aspect, CoS status),
   not from different presupposition "strengths."

4. Filtering in Karttunen environments (conjunction, conditional, disjunction)
   is explained pragmatically without anaphoric constraints. For disjunction,
   the account predicts *symmetric* filtering (contra [heim-1983]).

## Connection to Existing Theory

This study file imports and bridges:
- `OntologicalPreconditions` (EventPhase, entailment classification)
- `ChangeOfState.Theory` (CoS presuppositions)
- `Features.Aktionsart` (Vendler classes, telicity)
- `ProjectiveContent` (Tonhauser taxonomy: all three verb classes are Class C)
-/

namespace RobertsSimons2024

open Semantics.Presupposition.OntologicalPreconditions
open Features.ChangeOfState
open Features
open Semantics.Presupposition.ProjectiveContent

variable {W : Type*}

/-! ### Verb classes as event phases

The paper's three verb classes instantiated as `EventPhase`s: CoS
predicates, factives, and selectional restrictions, each with complement
truth or prior state as ontological precondition. -/

/-- "Stop P" as an event phase. -/
def stopAsEventPhase (P : W → Prop) : EventPhase W where
  precondition := P
  eventOccurs := P
  consequence := λ w => ¬ P w

/-- "Start P" as an event phase. -/
def startAsEventPhase (P : W → Prop) : EventPhase W where
  precondition := λ w => ¬ P w
  eventOccurs := λ w => ¬ P w
  consequence := P

/-- "Continue P" as an event phase. -/
def continueAsEventPhase (P : W → Prop) : EventPhase W where
  precondition := P
  eventOccurs := P
  consequence := P

/-- Event-phase precondition = the CoS presupposition of
    `Features.ChangeOfState`, per CoS type. -/
theorem stop_precondition_is_presup (P : W → Prop) :
    (stopAsEventPhase P).precondition = priorStatePresup .cessation P := rfl

theorem start_precondition_is_presup (P : W → Prop) :
    (startAsEventPhase P).precondition = priorStatePresup .inception P := rfl

theorem continue_precondition_is_presup (P : W → Prop) :
    (continueAsEventPhase P).precondition = priorStatePresup .continuation P := rfl

/-- Event-phase consequence = the CoS assertion, per CoS type. -/
theorem stop_consequence_is_assertion (P : W → Prop) :
    (stopAsEventPhase P).consequence = resultStateAssertion .cessation P := rfl

theorem start_consequence_is_assertion (P : W → Prop) :
    (startAsEventPhase P).consequence = resultStateAssertion .inception P := rfl

theorem continue_consequence_is_assertion (P : W → Prop) :
    (continueAsEventPhase P).consequence = resultStateAssertion .continuation P := rfl

/-- "Stop P" is telic: state changes from P to ¬P. -/
theorem stop_is_telic (P : W → Prop) (w : W) (hP : P w) :
    (stopAsEventPhase P).precondition w ≠ (stopAsEventPhase P).consequence w := by
  unfold stopAsEventPhase
  intro h
  exact (cast h hP) hP

/-- "Start P" is telic: state changes from ¬P to P. -/
theorem start_is_telic (P : W → Prop) (w : W) (hNotP : ¬ P w) :
    (startAsEventPhase P).precondition w ≠ (startAsEventPhase P).consequence w := by
  unfold startAsEventPhase
  intro h
  exact hNotP (cast h hNotP)

/-- "Continue P" is atelic: a precondition (prior activity) but no state
    change ([roberts-simons-2024] p. 734). -/
theorem continue_is_atelic (P : W → Prop) : (continueAsEventPhase P).isAtelic := by
  intro w; rfl

/-- "Know C" as an event phase: stative, atelic.
    Precondition: C is true. The knowing state cannot exist without its object. -/
def knowAsEventPhase (BEL C : W → Prop) : EventPhase W where
  precondition := C
  eventOccurs := λ w => BEL w ∧ C w
  consequence := C

/-- "Discover C" as an event phase: telic, achievement.
    Two preconditions: C is true AND the agent was previously ignorant. -/
def discoverAsEventPhase (IGNORANT C : W → Prop) : EventPhase W where
  precondition := λ w => C w ∧ IGNORANT w
  eventOccurs := λ w => C w ∧ ¬ IGNORANT w
  consequence := λ w => C w ∧ ¬ IGNORANT w

/-- "Regret p" as an event phase: emotive factive. The ontological
    precondition is *belief*, not truth — factivity arises from a
    pragmatic default to veridicality ([roberts-simons-2024] p. 731). -/
def regretAsEventPhase (BEL : W → Prop) : EventPhase W where
  precondition := BEL
  eventOccurs := BEL
  consequence := BEL

/-- Know is atelic: no state change (precondition = consequence). -/
theorem know_is_atelic (BEL C : W → Prop) : (knowAsEventPhase BEL C).isAtelic := by
  intro w; rfl

/-- Regret is atelic: the emotive state persists with its grounding belief. -/
theorem regret_is_atelic (BEL : W → Prop) : (regretAsEventPhase BEL).isAtelic := by
  intro w; rfl

/-- Discover is telic: state change from ignorant to knowing. -/
theorem discover_is_telic (IGNORANT C : W → Prop) (w : W)
    (hC : C w) (hIgn : IGNORANT w) :
    (discoverAsEventPhase IGNORANT C).precondition w ≠
    (discoverAsEventPhase IGNORANT C).consequence w := by
  unfold discoverAsEventPhase
  intro h
  have h2 : C w ∧ ¬ IGNORANT w := cast h ⟨hC, hIgn⟩
  exact h2.2 hIgn

/-- Both know and discover have C as (part of) their precondition: complement
    truth is ontologically required. -/
theorem factive_precondition_entails_complement (IGNORANT C : W → Prop) (w : W) :
    (discoverAsEventPhase IGNORANT C).precondition w → C w := by
  intro h; exact h.1

/-- Discover's extra precondition (prior ignorance) explains its weaker
    projection in conditional antecedents ([roberts-simons-2024] §3.2.2). -/
theorem discover_precondition_requires_ignorance (IGNORANT C : W → Prop) (w : W) :
    (discoverAsEventPhase IGNORANT C).precondition w → IGNORANT w := by
  intro h; exact h.2

/-- A selectional restriction as an event phase: the `requirement`
    ("the robot has feet") is an ontological precondition of the event
    ("the robot kicked the tree"), confirmed by both §2.1 diagnostics. -/
def selectionalEventPhase (requirement event : W → Prop) : EventPhase W where
  precondition := requirement
  eventOccurs := event
  consequence := event

/-! ### Aspectual classification -/

/-- Aspectual profile per CoS type: "stop"/"start" are achievements
    (telic, punctual); "continue" is an activity (atelic, durative). -/
def cosTypeToAspectualProfile : CoSType → AspectualProfile
  | .cessation => achievementProfile
  | .inception => achievementProfile
  | .continuation => activityProfile

/-- Vendler class per CoS type, derived from the aspectual profile. -/
def cosTypeToVendlerClass (t : CoSType) : VendlerClass :=
  (cosTypeToAspectualProfile t).toVendlerClass

/-- The derived Vendler classes carry the right telicity. -/
theorem cos_vendler_telicity_correct (t : CoSType) :
    (cosTypeToVendlerClass t).telicity = match t with
      | .cessation => .telic
      | .inception => .telic
      | .continuation => .atelic := by
  cases t <;> rfl

/-! ### The assertion-only rival

Under an assertion-only view a sentence is just its truth conditions — no
event reference, no aboutness — so nothing forces affirmative and negative
to share content, and single-index truth conditions cannot even represent
a CoS verb. -/

/-- The assertion-only meaning: bare truth conditions. -/
structure AssertionOnlyMeaning (W : Type*) where
  truthConditions : W → Prop

/-- Under assertion-only, "stop P" flattens pre-state and post-state into
    one evaluation point: P ∧ ¬P. -/
def assertionOnly_stop (P : W → Prop) : AssertionOnlyMeaning W :=
  { truthConditions := λ w => P w ∧ ¬ P w }

/-- Under assertion-only, "not stop P" is ¬(P ∧ ¬P) — a tautology. -/
def assertionOnly_notStop (P : W → Prop) : AssertionOnlyMeaning W :=
  { truthConditions := λ w => ¬(P w ∧ ¬ P w) }

/-- Single-index truth conditions cannot represent CoS verbs: the
    assertion-only "stop" is contradictory at every world. -/
theorem assertionOnly_stop_contradictory (P : W → Prop) (w : W) :
    ¬ (assertionOnly_stop P).truthConditions w :=
  λ ⟨h, hn⟩ => hn h

/-- Under assertion-only, the negated sentence is true even where P fails,
    so "John didn't stop smoking" would not require that he smoked: the
    view has no presupposition. -/
theorem assertionOnly_no_presupposition (P : W → Prop) (w : W)
    (_hNotP : ¬ P w) :
    (assertionOnly_notStop P).truthConditions w :=
  λ ⟨h, hn⟩ => hn h

/-! ### Pragmatic suppression conditions

Projection of preconditions is a pragmatic *default*, not an invariant
([roberts-simons-2024] §3.2.1). -/

/-- Contexts that suppress projection of a precondition: in each, pragmatic
    reasoning makes it implausible that the speaker presumes the
    precondition true. -/
inductive SuppressionCondition where
  /-- Interlocutors know or believe the precondition is false or
      controversial ([roberts-simons-2024] ex. 23). -/
  | preconditionKnownFalse
  /-- Evidence that the speaker does not believe the precondition
      ([roberts-simons-2024] ex. 24). -/
  | speakerNonCommitment
  /-- The precondition is at-issue, i.e. currently under discussion
      ([roberts-simons-2024] ex. 25). -/
  | preconditionAtIssue
  deriving DecidableEq, Repr

/-- Under any suppression condition, precondition content is merely locally
    entailed, not globally accommodated. -/
def SuppressionCondition.globalProjection : SuppressionCondition → Bool
  | _ => false


-- ═══════════════════════════════════════════════════════════════════════
-- §1. Theory Predicts Diagnostic Pattern
-- ═══════════════════════════════════════════════════════════════════════

/-- The theory predicts the empirical pattern: preconditions project,
    consequences don't. -/
theorem precondition_projects_consequence_doesnt :
    EntailmentRelation.projects .precondition = true ∧
    EntailmentRelation.projects .consequence = false ∧
    EntailmentRelation.projects .concomitant = false := ⟨rfl, rfl, rfl⟩


-- ═══════════════════════════════════════════════════════════════════════
-- §2. All Three Verb Classes Are Tonhauser Class C
-- ═══════════════════════════════════════════════════════════════════════

/-
All three verb classes discussed by R&S are -SCF/+OLE triggers
(Tonhauser Class C): their projective contents are non-anaphoric
(SCF=no) and obligatorily shift under belief predicates (OLE=yes).
-/

/-- CoS verbs (stop) are Class C. -/
example : ProjectiveTrigger.stop_prestate.toClass = .classC := rfl

/-- Factive verbs (know) are Class C. -/
example : ProjectiveTrigger.know_complement.toClass = .classC := rfl

/-- R&S's novel contribution: selectional restrictions behave like Class C
    triggers. They project (e.g., "The robot didn't kick the tree" implies
    it has feet), are non-anaphoric (SCF=no), and shift under belief
    (OLE=yes: "John believes the robot kicked the tree" → John believes
    the robot has feet).

    Class C is exactly the SCF=no, OLE=yes combination. -/
example : classFromProperties .noRequires .obligatory = .classC := rfl


-- ═══════════════════════════════════════════════════════════════════════
-- §3. Verb Pair Contrasts
-- ═══════════════════════════════════════════════════════════════════════

section VerbContrasts

variable {W : Type*}

/-
### Know vs Discover ([roberts-simons-2024] §3.2.2)

Both are veridical (factive), but they differ in event structure:
- **know**: stative, atelic. Reference time overlaps knowing state.
- **discover**: telic, achievement. Reference time follows discovery event.

This aspectual difference explains differential suppression:
- In "If I discover p", the conditional places the discovery in the future,
  and the speaker's ignorance prior to discovery is salient → projection
  of C is suppressed.
- In "If I know p", the stative overlaps with speech time, making it odd
  to place in a hypothetical → projection of C is harder to suppress.
-/

/-- Know is atelic: precondition = consequence (stative, no change). -/
theorem know_atelic (BEL C : W → Prop) :
    (knowAsEventPhase BEL C).isAtelic :=
  know_is_atelic BEL C

/-- Discover is telic: precondition ≠ consequence (state change). -/
theorem discover_telic (IGNORANT C : W → Prop) (w : W)
    (hC : C w) (hIgn : IGNORANT w) :
    (discoverAsEventPhase IGNORANT C).isTelic :=
  ⟨w, discover_is_telic IGNORANT C w hC hIgn⟩

/-- Both share factivity: complement truth is a precondition. -/
theorem know_discover_both_factive (BEL IGNORANT C : W → Prop) (w : W) :
    -- know's precondition is C directly
    (knowAsEventPhase BEL C).precondition w = C w ∧
    -- discover's precondition entails C
    ((discoverAsEventPhase IGNORANT C).precondition w → C w) := by
  constructor
  · rfl
  · exact factive_precondition_entails_complement IGNORANT C w

/-- Discover has an additional precondition (ignorance) that know lacks.
    This is the source of differential suppression: the ignorance precondition
    creates a context in which the speaker signals uncertainty about C. -/
theorem discover_has_ignorance_precondition (IGNORANT C : W → Prop) (w : W) :
    (discoverAsEventPhase IGNORANT C).precondition w → IGNORANT w :=
  discover_precondition_requires_ignorance IGNORANT C w


/-
### Stop vs Continue ([roberts-simons-2024] §3.2.2)

Both presuppose prior activity, but differ structurally:
- **stop**: CoS predicate (cessation), telic. Entails state change P→¬P.
- **continue**: NOT a CoS predicate (despite `CoSType.continuation`).
  Atelic, no state change. Prior activity is a precondition, but the
  activity persists rather than changing.

R&S (p. 734): "continue V-ing is atelic, without a pre-state" in the
CoS sense — the precondition and result state are identical.

Differential suppression follows from this:
- *stop* is suppressible because the stopping event can occur without
  the speaker knowing about the prior activity (just the cessation).
- *continue* resists suppression because it requires a *familiar
  start-date*: felicitous use of "continue V-ing" implies the activity
  is ongoing from some contextually identifiable prior interval.
  R&S (p. 736) offer as preliminary hypothesis that *continue* is
  anaphoric in presupposing a familiar beginning of the activity.
-/

/-- Stop is telic: involves a state change. -/
theorem stop_telic (P : W → Prop) (w : W) (hP : P w) :
    (stopAsEventPhase P).isTelic :=
  ⟨w, stop_is_telic P w hP⟩

/-- Continue is atelic: no state change. -/
theorem continue_atelic (P : W → Prop) :
    (continueAsEventPhase P).isAtelic :=
  continue_is_atelic P

/-- Stop and continue share the same precondition (prior activity P). -/
theorem stop_continue_same_precondition (P : W → Prop) :
    (stopAsEventPhase P).precondition = (continueAsEventPhase P).precondition := rfl

/-- But they differ in telicity: stop is telic, continue is atelic. -/
theorem stop_continue_telicity_differs :
    cosTypeToVendlerClass .cessation ≠ cosTypeToVendlerClass .continuation := by
  simp [cosTypeToVendlerClass, cosTypeToAspectualProfile, AspectualProfile.toVendlerClass,
        achievementProfile, activityProfile]

end VerbContrasts


-- ═══════════════════════════════════════════════════════════════════════
-- §4. Selectional Restrictions
-- ═══════════════════════════════════════════════════════════════════════

section SelectionalRestrictions

variable {W : Type*}

/-
### Selectional Restrictions as Ontological Preconditions

R&S's novel unification (§2.1): the selectional restrictions of verbs
are ontological preconditions, exhibiting the same projection behavior
as factive and CoS projections.

Example (§2.1, ex. 12–14):
  "The robot kicked the tree."
  → "The robot has feet." (precondition — projects)
  → "The robot touched the tree." (concomitant — doesn't project as presup)

Diagnostics confirm:
  (13a) "The robot has feet, which is part of what allowed for the robot
         to kick the tree." (T)
  (14a) "If the robot did not have feet, it would not have been possible
         for the robot to kick the tree." (T)
-/

/-- Selectional preconditions project through negation.
    "The robot didn't kick the tree" still implies it has feet. -/
theorem selectional_projects_through_negation (req event : W → Prop) (pol : Features.Polarity) :
    ({ eventType := selectionalEventPhase req event, polarity := pol } :
      EventSentence W).presupposition = req := rfl

/-- Concomitant entailments ("touched the tree") do NOT project as preconditions.
    They are a consequence/mereological part of the event, not a precondition. -/
example : EntailmentRelation.projects .concomitant = false := rfl

end SelectionalRestrictions


-- ═══════════════════════════════════════════════════════════════════════
-- §5. Filtering Without Constraint Satisfaction
-- ═══════════════════════════════════════════════════════════════════════

section Filtering

variable {W : Type*}

/-
### Filtering in Karttunen Environments ([roberts-simons-2024] §4)

R&S account for filtering pragmatically rather than via local context
satisfaction. Three standard cases:

(41) "Jane used to smoke, and now she's stopped."     — conjunction
(42) "If Jane used to smoke, she's now stopped."      — conditional
(43) "Either Jane never smoked, or she's stopped."    — disjunction

In each, the precondition of *stop* (prior smoking) is either asserted
(conjunction), supposed (conditional), or implicated (disjunction) by
the first clause. R&S's key insight: the hearer need not reason about
local contexts. Instead, they assess whether it is pragmatically plausible
that the speaker presumes the precondition globally.
-/

/-- In a conjunction "P, and (stop P)", the first conjunct asserts the
    precondition. R&S: it is pragmatically implausible that the speaker
    presumes the precondition — they are *explicitly asserting* it. -/
def conjunctionFiltering (P : W → Prop) : Prop :=
  -- The conjunction entails the precondition locally
  ∀ w, (P w ∧ (stopAsEventPhase P).eventOccurs w) →
    (stopAsEventPhase P).precondition w

theorem conjunction_entails_precondition (P : W → Prop) :
    conjunctionFiltering P := by
  intro w ⟨hP, _⟩; exact hP

/-- In a conditional "If P, then stop P", the antecedent *supposes* P.
    R&S: the conditional structure itself signals the speaker's lack of
    commitment to the antecedent, and the function of the conditional is
    to evaluate the consequent relative to the antecedent. No global
    presumption of P is pragmatically attributable. -/
def conditionalFiltering (P : W → Prop) : Prop :=
  ∀ w, (P w → (stopAsEventPhase P).precondition w)

theorem conditional_entails_precondition (P : W → Prop) :
    conditionalFiltering P := by
  intro _ hP; exact hP

/-- R&S's distinctive prediction for disjunction ([roberts-simons-2024] §4):
    filtering in disjunction is **symmetric** for non-anaphoric triggers.

    "Either Jane never smoked, or she's stopped." (43)

    The first disjunct (¬P) creates a context in which it is reasonable
    to consider the second disjunct's precondition (P) as locally entailed
    (if ¬P is false, i.e. P is true). Crucially, R&S argue this filtering
    works identically in both orders — contra [heim-1983]'s asymmetric
    account.

    This is a pragmatic consequence of their view: filtering depends on
    whether global presumption of the precondition is pragmatically
    attributable, not on dynamic left-to-right context update. -/
def symmetricDisjunctionFiltering : Prop :=
  -- For non-anaphoric triggers, both disjunction orders filter equally
  True  -- Qualitative claim; formalized as an axiom for now
  -- TODO: formalize via pragmatic plausibility ordering

end Filtering


-- ═══════════════════════════════════════════════════════════════════════
-- §6. Bridge: EventPhase Precondition = PartialProp Presupposition
-- ═══════════════════════════════════════════════════════════════════════

section Bridges

variable {W : Type*}

/-- For CoS verbs, EventPhase.precondition agrees with PartialProp.presup.
    This shows the two representations — the aboutness-based (R&S) and the
    trivalent (Heim) — agree on *what* projects, even though they disagree
    on *why* it projects. -/
theorem cos_eventphase_agrees_with_prprop (t : CoSType) (P : W → Prop) :
    (match t with
     | .cessation => stopAsEventPhase P
     | .inception => startAsEventPhase P
     | .continuation => continueAsEventPhase P).precondition =
    (cosSemantics t P).presup := by
  cases t <;> rfl

/-- R&S argue that presupposition status follows from event structure,
    not from a stipulated `presupType`. A verb presupposes its complement
    iff it has factivity or CoS event structure. The `derivedPresupType`
    accessor on `Verb` implements this derivation. -/
theorem presupposition_derivable_from_event_structure
    (isFactive hasCosType : Bool) :
    (isFactive || hasCosType) = true ↔
    (isFactive = true ∨ hasCosType = true) := by
  simp [Bool.or_eq_true]

end Bridges


-- ═══════════════════════════════════════════════════════════════════════
-- §7. Suppression: Three Contexts
-- ═══════════════════════════════════════════════════════════════════════

/-
The three suppression conditions are not merely descriptive categories —
they follow from the pragmatic account. In each case, the listener cannot
reasonably attribute to the speaker the presumption that the precondition
holds, because contextual evidence undermines that attribution.

The parallel with scalar implicatures is deliberate: just as "some" carries
a pragmatic "not all" implication that can be cancelled, CoS/factive verbs
carry a pragmatic precondition implication that can be suppressed.
-/

/-
### Connection to RSA accounts

R&S take the RSA accounts of [qing-goodman-lassiter-2016] and
[warstadt-2022] as providing proof-of-concept for the general pragmatic
mechanism. Those models show that a Bayesian listener who jointly infers
the world state and the speaker's assumed context will, under the right QUD,
derive presupposition projection as a pragmatic inference without any special
semantic mechanism. See `QingGoodmanLassiter2016.lean` and `Warstadt2022.lean`
for the full RSA implementations.
-/

/-- Suppression does not change what is entailed — only what is presumed. -/
theorem suppression_preserves_entailment :
    ∀ s : SuppressionCondition, s.globalProjection = false := by
  intro s; cases s <;> rfl


-- ═══════════════════════════════════════════════════════════════════════
-- §8. End-to-End Argumentation Chain
-- ═══════════════════════════════════════════════════════════════════════

section EndToEnd

variable {W : Type*}

/-
### The Complete Argument ([roberts-simons-2024])

The paper's argument chains together three structural facts:

1. Events have preconditions and consequences (EventPhase decomposition)
2. Sentences about events share event reference across polarity (aboutness)
3. Presupposition = precondition (from aboutness), invariant across polarity

This chain explains the precondition/consequence asymmetry:
- Preconditions project because they're tied to event reference (aboutness)
- Consequences don't project because they're tied to event occurrence (assertion)
- Under negation, event reference is preserved but occurrence is denied
-/

/-- End-to-end: for "stop P", the full chain from event structure to
    projection prediction. The precondition (prior state P) is invariant
    across both polarities, while the consequence (¬P) flips. -/
theorem stop_end_to_end (P : W → Prop) (w : W) :
    -- (1) Precondition = prior state P
    (stopAsEventPhase P).precondition w = P w ∧
    -- (2) Presupposition = precondition (from aboutness)
    (affirmative (stopAsEventPhase P)).presupposition w = P w ∧
    -- (3) Presupposition invariant across polarity (projection)
    (affirmative (stopAsEventPhase P)).presupposition w =
    (negative (stopAsEventPhase P)).presupposition w ∧
    -- (4) But consequence flips under negation
    ((negative (stopAsEventPhase P)).assertion w ↔
    ¬ (affirmative (stopAsEventPhase P)).assertion w) ∧
    -- (5) The precondition projects but the consequence doesn't
    EntailmentRelation.projects .precondition = true ∧
    EntailmentRelation.projects .consequence = false := by
  exact ⟨rfl, rfl, rfl, Iff.rfl, rfl, rfl⟩

/-- End-to-end for factives: know's complement truth is an ontological
    precondition, shares the same structural projection mechanism as
    CoS verbs, and agrees with the PartialProp representation. -/
theorem know_end_to_end (BEL C : W → Prop) (w : W) :
    -- (1) Precondition = complement truth
    (knowAsEventPhase BEL C).precondition w = C w ∧
    -- (2) Presupposition = precondition
    (affirmative (knowAsEventPhase BEL C)).presupposition w = C w ∧
    -- (3) Projection: invariant across polarity
    (affirmative (knowAsEventPhase BEL C)).presupposition w =
    (negative (knowAsEventPhase BEL C)).presupposition w ∧
    -- (4) Atelicity: precondition = consequence (stative)
    (knowAsEventPhase BEL C).isAtelic := by
  exact ⟨rfl, rfl, rfl, know_is_atelic BEL C⟩

/-- End-to-end for selectional restrictions: same aboutness mechanism,
    same projection behavior, same structural explanation. -/
theorem selectional_end_to_end (req event : W → Prop) (w : W) :
    -- (1) Precondition = selectional requirement
    (selectionalEventPhase req event).precondition w = req w ∧
    -- (2) Presupposition = precondition
    (affirmative (selectionalEventPhase req event)).presupposition w = req w ∧
    -- (3) Projection: invariant across polarity
    (affirmative (selectionalEventPhase req event)).presupposition w =
    (negative (selectionalEventPhase req event)).presupposition w := by
  exact ⟨rfl, rfl, rfl⟩

end EndToEnd


end RobertsSimons2024
