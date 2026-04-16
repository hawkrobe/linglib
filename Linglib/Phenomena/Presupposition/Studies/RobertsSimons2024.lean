import Linglib.Theories.Semantics.Presupposition.OntologicalPreconditions
import Linglib.Theories.Semantics.Lexical.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Phenomena.Presupposition.Diagnostics
import Linglib.Phenomena.Presupposition.ProjectiveContent

/-!
# Preconditions and Projection: Explaining Non-Anaphoric Presupposition
@cite{roberts-simons-2024}

Roberts, C. & Simons, M. (2024). Preconditions and projection: Explaining
non-anaphoric presupposition. *Linguistics and Philosophy* 47(4):703–748.

## Key Claims

1. The projective contents of CoS predicates, factives, and selectional
   restrictions are entailments characterizing *ontological preconditions*
   of the associated event type — NOT semantically encoded presuppositions.

2. Projection is a *pragmatic default*: a speaker who raises an event is
   taken to assume its preconditions hold (maximizes informativity, per
   @cite{qing-goodman-lassiter-2016} and @cite{warstadt-2022}).

3. Differential suppression across verb pairs (know/discover, stop/continue)
   follows from lexical semantic differences (telicity, aspect, CoS status),
   not from different presupposition "strengths."

4. Filtering in Karttunen environments (conjunction, conditional, disjunction)
   is explained pragmatically without anaphoric constraints. For disjunction,
   the account predicts *symmetric* filtering (contra @cite{heim-1983}).

## Connection to Existing Theory

This study file imports and bridges:
- `OntologicalPreconditions` (EventPhase, entailment classification)
- `ChangeOfState.Theory` (CoS presuppositions)
- `LexicalAspect` (Vendler classes, telicity)
- `ProjectiveContent` (Tonhauser taxonomy: all three verb classes are Class C)
- `Diagnostics` (empirical diagnostic data)
-/

namespace RobertsSimons2024

open Semantics.Presupposition.OntologicalPreconditions
open Semantics.Lexical.Verb.ChangeOfState
open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Phenomena.Presupposition.Diagnostics
open Phenomena.Presupposition.ProjectiveContent


-- ═══════════════════════════════════════════════════════════════════════
-- §1. Theory Predicts Diagnostic Pattern
-- ═══════════════════════════════════════════════════════════════════════

/-- The theory predicts the empirical pattern: preconditions project,
    consequences don't. Verified against diagnostic data. -/
theorem precondition_projects_consequence_doesnt :
    EntailmentRelation.projects .precondition = true ∧
    EntailmentRelation.projects .consequence = false ∧
    EntailmentRelation.projects .concomitant = false := ⟨rfl, rfl, rfl⟩

/-- Diagnostic data confirms: prior state passes "allows for", projects.
    Result state fails "allows for", doesn't project. -/
theorem theoryPredictsPattern :
    stopPattern.priorPassesAllowsFor = true ∧
    priorStateProjection.projectsThroughNegation = true ∧
    stopPattern.resultFailsAllowsFor = true ∧
    resultStateProjection.projectsThroughNegation = false :=
  ⟨rfl, rfl, rfl, rfl⟩


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
### Know vs Discover (@cite{roberts-simons-2024} §3.2.2)

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
theorem know_atelic (BEL C : W → Bool) :
    (knowAsEventPhase BEL C).isAtelic :=
  know_is_atelic BEL C

/-- Discover is telic: precondition ≠ consequence (state change). -/
theorem discover_telic (IGNORANT C : W → Bool) (w : W)
    (hC : C w = true) (hIgn : IGNORANT w = true) :
    (discoverAsEventPhase IGNORANT C).isTelic :=
  ⟨w, discover_is_telic IGNORANT C w hC hIgn⟩

/-- Both share factivity: complement truth is a precondition. -/
theorem know_discover_both_factive (BEL IGNORANT C : W → Bool) (w : W) :
    -- know's precondition is C directly
    (knowAsEventPhase BEL C).precondition w = C w ∧
    -- discover's precondition entails C
    ((discoverAsEventPhase IGNORANT C).precondition w = true → C w = true) := by
  constructor
  · rfl
  · exact factive_precondition_entails_complement IGNORANT C w

/-- Discover has an additional precondition (ignorance) that know lacks.
    This is the source of differential suppression: the ignorance precondition
    creates a context in which the speaker signals uncertainty about C. -/
theorem discover_has_ignorance_precondition (IGNORANT C : W → Bool) (w : W) :
    (discoverAsEventPhase IGNORANT C).precondition w = true → IGNORANT w = true :=
  discover_precondition_requires_ignorance IGNORANT C w


/-
### Stop vs Continue (@cite{roberts-simons-2024} §3.2.2)

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
theorem stop_telic (P : W → Bool) (w : W) (hP : P w = true) :
    (stopAsEventPhase P).isTelic :=
  ⟨w, stop_is_telic P w hP⟩

/-- Continue is atelic: no state change. -/
theorem continue_atelic (P : W → Bool) :
    (continueAsEventPhase P).isAtelic :=
  continue_is_atelic P

/-- Stop and continue share the same precondition (prior activity P). -/
theorem stop_continue_same_precondition (P : W → Bool) :
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
theorem selectional_projects_through_negation (req event : W → Bool) (pol : Core.Polarity) :
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
### Filtering in Karttunen Environments (@cite{roberts-simons-2024} §4)

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
def conjunctionFiltering (P : W → Bool) : Prop :=
  -- The conjunction entails the precondition locally
  ∀ w, (P w = true ∧ (stopAsEventPhase P).eventOccurs w = true) →
    (stopAsEventPhase P).precondition w = true

theorem conjunction_entails_precondition (P : W → Bool) :
    conjunctionFiltering P := by
  intro w ⟨hP, _⟩; exact hP

/-- In a conditional "If P, then stop P", the antecedent *supposes* P.
    R&S: the conditional structure itself signals the speaker's lack of
    commitment to the antecedent, and the function of the conditional is
    to evaluate the consequent relative to the antecedent. No global
    presumption of P is pragmatically attributable. -/
def conditionalFiltering (P : W → Bool) : Prop :=
  ∀ w, (P w = true → (stopAsEventPhase P).precondition w = true)

theorem conditional_entails_precondition (P : W → Bool) :
    conditionalFiltering P := by
  intro _ hP; exact hP

/-- R&S's distinctive prediction for disjunction (@cite{roberts-simons-2024} §4):
    filtering in disjunction is **symmetric** for non-anaphoric triggers.

    "Either Jane never smoked, or she's stopped." (43)

    The first disjunct (¬P) creates a context in which it is reasonable
    to consider the second disjunct's precondition (P) as locally entailed
    (if ¬P is false, i.e. P is true). Crucially, R&S argue this filtering
    works identically in both orders — contra @cite{heim-1983}'s asymmetric
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
-- §6. Bridge: EventPhase Precondition = PrProp Presupposition
-- ═══════════════════════════════════════════════════════════════════════

section Bridges

variable {W : Type*}

/-- For CoS verbs, EventPhase.precondition agrees with PrProp.presup.
    This shows the two representations — the aboutness-based (R&S) and the
    trivalent (Heim) — agree on *what* projects, even though they disagree
    on *why* it projects. -/
theorem cos_eventphase_agrees_with_prprop (t : CoSType) (P : W → Bool) :
    (match t with
     | .cessation => stopAsEventPhase P
     | .inception => startAsEventPhase P
     | .continuation => continueAsEventPhase P).precondition =
    (cosSemantics t P).presup := by
  cases t <;> rfl

/-- R&S argue that presupposition status follows from event structure,
    not from a stipulated `presupType`. A verb presupposes its complement
    iff it has factivity or CoS event structure. The `derivedPresupType`
    accessor on `VerbCore` implements this derivation. -/
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

R&S take the RSA accounts of @cite{qing-goodman-lassiter-2016} and
@cite{warstadt-2022} as providing proof-of-concept for the general pragmatic
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
### The Complete Argument (@cite{roberts-simons-2024})

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
theorem stop_end_to_end (P : W → Bool) (w : W) :
    -- (1) Precondition = prior state P
    (stopAsEventPhase P).precondition w = P w ∧
    -- (2) Presupposition = precondition (from aboutness)
    (affirmative (stopAsEventPhase P)).presupposition w = P w ∧
    -- (3) Presupposition invariant across polarity (projection)
    (affirmative (stopAsEventPhase P)).presupposition w =
    (negative (stopAsEventPhase P)).presupposition w ∧
    -- (4) But consequence flips under negation
    (negative (stopAsEventPhase P)).assertion w =
    !(affirmative (stopAsEventPhase P)).assertion w ∧
    -- (5) The precondition projects but the consequence doesn't
    EntailmentRelation.projects .precondition = true ∧
    EntailmentRelation.projects .consequence = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- End-to-end for factives: know's complement truth is an ontological
    precondition, shares the same structural projection mechanism as
    CoS verbs, and agrees with the PrProp representation. -/
theorem know_end_to_end (BEL C : W → Bool) (w : W) :
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
theorem selectional_end_to_end (req event : W → Bool) (w : W) :
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
