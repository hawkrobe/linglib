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
memory/perception reports. `Grammatical.eventDenotation` assigns each
mood its operator, landing in the constructor-distinguished
`EventDenotation`, so the closed/open contrast is read off the
constructor rather than stipulated in a feature table. The
situation-level dimension is `Semantics/Mood/Situation.lean`, the
dynamic lifts `Semantics/Mood/Dynamic.lean`.
-/

namespace Mood

variable {Event : Type*}

/-- Indicative closure of the eventuality argument ([grano-2024], (87)):
`⟦INDIC⟧ = λP.∃e.P(e)`. The complement denotes a proposition. -/
def INDev (P : Event → Prop) : Prop := ∃ e, P e

/-- Subjunctive non-closure ([grano-2024], (88a); Subjunctive₃ (135) in
his §7 unified theory): `⟦SBJV₁⟧ = λP.P`. The complement stays an event
predicate, open for abstraction — the variant for perception,
causative, and aspectual predicates, without the causal
self-reference of `SBJVev₂` or the ordering semantics of his
Subjunctive₁. -/
def SBJVev₁ (P : Event → Prop) : Event → Prop := P

/-- The *intend* variant, with causal self-reference ([grano-2024],
(134), integrating CAUSE* with [portner-rubinstein-2020]'s modal
framework): the attitude state must causally bring about the
described event "in the right way" ([searle-1983]; [harman-1976]). -/
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
mood ([grano-2024]): the assignment is the theory's sole stipulation;
openness facts follow from the constructors. -/
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
