import Linglib.Theories.Semantics.Presupposition.OntologicalPreconditions
import Linglib.Phenomena.ImplicitCausality.Studies.SolstadBott2024.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Solstad & Bott (2024) — Presupposition Bridge

@cite{solstad-bott-2024}

Connects occasion verb presupposition to EventPhase infrastructure.

## Core claim

Occasion verbs (manage, dare, bother, hesitate) presuppose a prior
**occasioning eventuality** — a circumstance that makes the complement
action relevant. This is an ontological precondition in the sense of
Roberts & Simons (2024): the occasion must exist for the event denoted
by the verb to be possible.

Example: "John managed to open the door" presupposes that opening the
door was difficult / required effort — the occasion (difficulty) is a
precondition for the managing event.

## Connection to EventPhase

The occasion presupposition maps directly to `EventPhase.precondition`:
- **Precondition**: The occasioning eventuality (difficulty, reluctance, etc.)
- **Event**: The subject's engagement with the complement action
- **Consequence**: The complement state (for manage: complement is true)

This reuses the existing projection mechanism: the presupposition projects
through negation because it's tied to event reference (aboutness), not
to the assertion.
-/

namespace Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge

open Semantics.Presupposition.OntologicalPreconditions
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Occasion Presupposition as EventPhase
-- ════════════════════════════════════════════════════

/-- Model an occasion verb's presupposition as an EventPhase.

    - precondition = occasioning eventuality (e.g., difficulty, reluctance)
    - eventOccurs  = subject's engagement with the complement
    - consequence  = complement outcome

    The precondition is what projects; the consequence is at-issue. -/
def occasionEventPhase {W : Type*}
    (occasion : W → Bool)     -- The occasioning eventuality
    (engagement : W → Bool)   -- Subject's engagement
    (outcome : W → Bool)      -- Complement outcome
    : EventPhase W where
  precondition := occasion
  eventOccurs := engagement
  consequence := outcome

-- ════════════════════════════════════════════════════
-- § 2. Well-formedness
-- ════════════════════════════════════════════════════

/-- Well-formedness for occasion verbs: engagement requires the occasion.

    You can't "manage to VP" unless VP was difficult (the occasion).
    You can't "dare to VP" unless there was something intimidating (the occasion). -/
theorem occasion_wellformed {W : Type*}
    (occasion engagement outcome : W → Bool)
    (h : ∀ w, engagement w → occasion w) :
    (occasionEventPhase occasion engagement outcome).wellFormed :=
  h

-- ════════════════════════════════════════════════════
-- § 3. Projection Through Negation
-- ════════════════════════════════════════════════════

/-- The occasion presupposition projects through negation, by the
    same mechanism as "stop" — it's tied to aboutness, not assertion.

    "John didn't manage to open the door" still presupposes that
    opening the door was difficult. -/
theorem occasion_presup_projects {W : Type*}
    (occasion engagement outcome : W → Bool) :
    (affirmative (occasionEventPhase occasion engagement outcome)).presupposition =
    (negative (occasionEventPhase occasion engagement outcome)).presupposition := rfl

/-- The shared presupposition IS the occasion. -/
theorem occasion_presup_is_occasion {W : Type*}
    (occasion engagement outcome : W → Bool) :
    (affirmative (occasionEventPhase occasion engagement outcome)).presupposition =
    occasion := rfl

-- ════════════════════════════════════════════════════
-- § 4. Bridge to Fragment: presupType = softTrigger
-- ════════════════════════════════════════════════════

/-- "manage" (occasion sense) is annotated as a soft presupposition trigger.

    The default `manage` entry omits presupType (traditional implicative analysis);
    `manage_occasion` adds it (Solstad & Bott 2024 analysis). -/
theorem manage_occasion_is_soft_trigger :
    manage_occasion.presupType = some .softTrigger := rfl

/-- "dare" is annotated as a soft presupposition trigger. -/
theorem dare_is_soft_trigger :
    dare.presupType = some .softTrigger := rfl

/-- "bother" is annotated as a soft presupposition trigger. -/
theorem bother_is_soft_trigger :
    bother.presupType = some .softTrigger := rfl

/-- "hesitate" is annotated as a soft presupposition trigger. -/
theorem hesitate_is_soft_trigger :
    hesitate.presupType = some .softTrigger := rfl

/-- All four occasion verbs are soft triggers — their occasion
    presupposition can be locally accommodated. -/
theorem all_occasion_verbs_soft :
    manage_occasion.presupType = some .softTrigger ∧
    dare.presupType = some .softTrigger ∧
    bother.presupType = some .softTrigger ∧
    hesitate.presupType = some .softTrigger :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The default `manage` has no presupType — the occasion presupposition
    is only visible under the Solstad & Bott (2024) analysis. -/
theorem manage_default_no_presup :
    manage.presupType = none := rfl

/-- Both senses share the same implicative semantics. -/
theorem manage_senses_share_implicative :
    manage.implicativeBuilder = manage_occasion.implicativeBuilder := rfl

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Fragment: Complement Structure
-- ════════════════════════════════════════════════════

/-- All four occasion verbs take infinitival complements. -/
theorem occasion_verbs_infinitival :
    manage_occasion.complementType = .infinitival ∧
    dare.complementType = .infinitival ∧
    bother.complementType = .infinitival ∧
    hesitate.complementType = .infinitival :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- All four occasion verbs are subject-control. -/
theorem occasion_verbs_subject_control :
    manage_occasion.controlType = .subjectControl ∧
    dare.controlType = .subjectControl ∧
    bother.controlType = .subjectControl ∧
    hesitate.controlType = .subjectControl :=
  ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.ImplicitCausality.Studies.SolstadBott2024.Bridge
