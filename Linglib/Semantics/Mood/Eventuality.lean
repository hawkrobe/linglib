/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.TypeStar
import Linglib.Semantics.Mood.Defs

/-!
# Event-level mood operators

This file defines the event-level dimension of grammatical mood,
following [grano-2024]: mood morphemes operate on the eventuality
argument of the complement clause. Indicative existentially closes
it, yielding a proposition; subjunctive leaves it open, as required
by causatives, intention reports, aspectual predicates, and
memory/perception reports.
-/

namespace Mood

variable {Event : Type*}

/-- The indicative existentially closes the complement's event
argument, yielding a proposition ([grano-2024], (87)). -/
def INDev (P : Event → Prop) : Prop := ∃ e, P e

/-- The subjunctive leaves the complement's event argument open for
abstraction ([grano-2024], (88a)). -/
def SBJVev₁ (P : Event → Prop) : Event → Prop := P

/-- The *intend* subjunctive: the attitude state must causally bring
about the described event ([grano-2024], (134); [searle-1983]). -/
def SBJVev₂ {W : Type*}
    (causeStar : Event → Event → W → Prop)  -- CAUSE*(state, event, world)
    (content : Event → W → Prop)          -- content of the attitude state
    (P : W → Event → Prop)               -- world-indexed event predicate
    (e : Event) : Prop :=
  ∀ w, content e w → ∃ e', causeStar e e' w ∧ P w e'

/-! ### Mood as event closure, by constructor -/

/-- The result of a mood's event-level denotation: the event argument
closed to a proposition, or still open for abstraction. -/
inductive EventDenotation (Event : Type*) where
  /-- The event argument has been existentially closed. -/
  | closed (p : Prop)
  /-- The event argument remains open for abstraction. -/
  | abstracted (p : Event → Prop)

/-- The event-level denotation of a complement under each grammatical
mood ([grano-2024]). -/
def Grammatical.eventDenotation (P : Event → Prop) :
    Grammatical → EventDenotation Event
  | .indicative  => .closed (INDev P)
  | .subjunctive => .abstracted (SBJVev₁ P)

/-- Indicative closes the event argument — why indicative complements
cannot feed CAUSE* or aspectual operators ([grano-2024]). -/
@[simp] theorem eventDenotation_indicative (P : Event → Prop) :
    Grammatical.indicative.eventDenotation P = .closed (∃ e, P e) := rfl

/-- Subjunctive leaves the event argument open — why subjunctive
complements feed eventuality abstraction ([grano-2024]). -/
@[simp] theorem eventDenotation_subjunctive (P : Event → Prop) :
    Grammatical.subjunctive.eventDenotation P = .abstracted P := rfl

end Mood
