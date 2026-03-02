import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Theories.Semantics.Presupposition.OntologicalPreconditions
import Linglib.Phenomena.Presupposition.ProjectiveContent
import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2024.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{solstad-bott-2024} — Projectivity Bridge

@cite{solstad-bott-2024} @cite{tonhauser-beaver-roberts-simons-2013} @cite{heim-1983} @cite{schlenker-2009}

Connects occasion verb presupposition to the @cite{tonhauser-beaver-roberts-simons-2013} taxonomy
and formalizes the cataphoric resolution result from Experiment 3.

## Key claims (S&P 17:11)

1. **Occasion verbs trigger projective content** (Exp 1): occasion verb content
   survives embedding under negation, questions, modals, and conditionals.
2. **No strong contextual felicity** (Exp 2): occasion verbs are felicitous
   "out of the blue" — their presupposition can be informative (accommodated).
3. **Cataphoric resolution is possible** (Exp 3): occasion verb presuppositions
   can be resolved by subsequent material (consequent of a conditional),
   supporting **symmetric** filtering over @cite{heim-1983}'s asymmetric left-to-right algorithm.

## Tonhauser classification

These properties place occasion verbs in **Class C** (SCF=no, OLE=yes),
alongside factive verbs (*know*) and change-of-state verbs (*stop*).

## Symmetric vs asymmetric filtering

@cite{heim-1983}: local context at position i is computed from material to the
LEFT of i only → presuppositions in the antecedent cannot be resolved by
the consequent.

Schlenker (2008, 2009): local context considers material on BOTH sides →
cataphoric resolution is predicted.

Solstad & Bott's Experiment 3 supports symmetric filtering: occasion verb
presuppositions in the antecedent CAN be satisfied by the consequent.
-/

namespace Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge.Projectivity

open Semantics.Presupposition.LocalContext
open Semantics.Presupposition.OntologicalPreconditions
open Phenomena.Presupposition.ProjectiveContent
open Core.Presupposition
open Core.CommonGround

-- ════════════════════════════════════════════════════
-- § 1. Occasion Verbs are Class C Triggers
-- ════════════════════════════════════════════════════

/-- Occasion verbs are Class C in the @cite{tonhauser-beaver-roberts-simons-2013} taxonomy:
    SCF=no (can be informative), OLE=yes (attributed to attitude holder). -/
theorem occasion_verb_is_classC :
    ProjectiveTrigger.occasion_verb.toClass = .classC := rfl

/-- Class C triggers do not require prior establishment in context. -/
theorem classC_no_scf :
    ProjectiveClass.classC.scf = .noRequires := rfl

/-- Class C triggers have obligatory local effect under belief embedding. -/
theorem classC_has_ole :
    ProjectiveClass.classC.ole = .obligatory := rfl

/-- Occasion verbs pattern with *stop* and *know* — all Class C. -/
theorem occasion_verb_patterns_with_stop_know :
    ProjectiveTrigger.occasion_verb.toClass =
    ProjectiveTrigger.stop_prestate.toClass ∧
    ProjectiveTrigger.occasion_verb.toClass =
    ProjectiveTrigger.know_complement.toClass := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Occasion Verb Presupposition as EventPhase
-- ════════════════════════════════════════════════════

/-- Model an occasion verb's presupposition as an EventPhase.

    Example: "The judge punished Peter"
    - precondition = Peter did something wrong (the occasion)
    - eventOccurs = the judge's punishing action
    - consequence = Peter is punished

    The precondition (occasion) is what projects. -/
def occasionEventPhase {W : Type*}
    (occasion : W → Bool)     -- The occasioning eventuality
    (engagement : W → Bool)   -- The agent's action
    (outcome : W → Bool)      -- Result state
    : EventPhase W where
  precondition := occasion
  eventOccurs := engagement
  consequence := outcome

/-- Occasion presupposition projects through negation.
    "The judge didn't punish Peter" still presupposes Peter did something wrong. -/
theorem occasion_presup_projects {W : Type*}
    (occasion engagement outcome : W → Bool) :
    (affirmative (occasionEventPhase occasion engagement outcome)).presupposition =
    (negative (occasionEventPhase occasion engagement outcome)).presupposition := rfl

-- ════════════════════════════════════════════════════
-- § 3. Asymmetric Filtering (Heim 1983)
-- ════════════════════════════════════════════════════

/-- Under Heim's asymmetric filtering, the local context at the antecedent
    of a conditional is just the global context — no material from the
    consequent is available. So if the occasion verb is in the antecedent,
    its presupposition PROJECTS (is not filtered).

    "If the judge punishes Peter, he was convicted."
    At "punishes" (antecedent): local context = global context.
    Presupposition "Peter did something wrong" is NOT entailed → projects. -/
theorem heim_antecedent_projects {W : Type*}
    (c : ContextSet W) (trigger _consequence : PrProp W)
    (h : ∃ w, c w ∧ trigger.presup w = false) :
    presupProjects (initialLocalCtx c) trigger := by
  obtain ⟨w, hw_in, hpresup_false⟩ := h
  intro hfilter
  have := hfilter w hw_in
  simp [hpresup_false] at this

-- ════════════════════════════════════════════════════
-- § 4. Symmetric Filtering (Schlenker 2008, 2009)
-- ════════════════════════════════════════════════════

/-- Under symmetric filtering, material from the consequent IS available
    to resolve presuppositions in the antecedent. We model this by
    providing the consequent's assertion to the local context at the
    antecedent position.

    "If the judge punishes Peter, he was convicted."
    Symmetric local context at "punishes": c + [Peter was convicted].
    Presupposition "Peter did something wrong" IS entailed → filtered. -/
def symmetricLocalCtxAntecedent {W : Type*}
    (c : LocalCtx W) (consequent : PrProp W) : LocalCtx W :=
  { worlds := ContextSet.update c.worlds consequent.assertion
  , position := c.position
  , depth := c.depth }

/-- When the consequent entails the occasion presupposition,
    symmetric filtering predicts the presupposition is filtered. -/
theorem symmetric_filters_when_consequent_entails {W : Type*}
    (c : LocalCtx W) (trigger consequent : PrProp W)
    (h : ∀ w, c.worlds w → consequent.assertion w = true → trigger.presup w = true) :
    presupFiltered (symmetricLocalCtxAntecedent c consequent) trigger := by
  intro w hw
  have ⟨hw_in, hcons⟩ := hw
  exact h w hw_in hcons

-- ════════════════════════════════════════════════════
-- § 5. Solstad & Bott (2024) Experiment 3 Result
-- ════════════════════════════════════════════════════

/-- The key empirical finding: cataphoric resolution succeeds for occasion
    verbs (Exp 3, S&P 17:11). Participants accepted conditionals where:
    - The antecedent contains an occasion verb (trigger)
    - The consequent provides the occasion (resolver)

    This is predicted by symmetric but NOT asymmetric filtering:
    - Symmetric: consequent material available → presupposition filtered ✓
    - Asymmetric: only left-to-right → presupposition projects ✗

    The theorem shows that given a world model where the consequent
    entails the occasion, symmetric filtering correctly predicts
    the presupposition is filtered (matching experimental judgments). -/
theorem cataphoric_resolution_possible {W : Type*}
    (c : LocalCtx W) (trigger consequent : PrProp W)
    (h_entails : ∀ w, c.worlds w → consequent.assertion w = true →
                       trigger.presup w = true) :
    -- Symmetric filtering: presupposition IS filtered
    presupFiltered (symmetricLocalCtxAntecedent c consequent) trigger := by
  exact symmetric_filters_when_consequent_entails c trigger consequent h_entails

-- ════════════════════════════════════════════════════
-- § 6. Projection vs Implicative Inference
-- ════════════════════════════════════════════════════

/-- The occasion presupposition (projective content) is distinct from the
    implicative inference (at-issue content). For "manage to VP":

    - Implicative inference: VP occurred (at-issue, cancels under negation)
      "John didn't manage to open the door" → door was NOT opened
    - Occasion presupposition: opening was difficult (projective, survives negation)
      "John didn't manage to open the door" → opening WAS difficult

    The fragment encodes this: `manage` has `implicativeBuilder` (at-issue)
    while `manage_occasion` additionally has `presupType` (projective). -/
theorem manage_projection_vs_implicature :
    -- Default manage: implicative but no presupposition type
    Fragments.English.Predicates.Verbal.manage.implicativeBuilder = some .positive ∧
    Fragments.English.Predicates.Verbal.manage.presupType = none ∧
    -- Occasion sense: same implicative PLUS presupposition
    Fragments.English.Predicates.Verbal.manage_occasion.implicativeBuilder = some .positive ∧
    Fragments.English.Predicates.Verbal.manage_occasion.presupType = some .softTrigger :=
  ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge.Projectivity
