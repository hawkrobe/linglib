/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Tense.TemporalConnectives.Basic
import Linglib.Semantics.Events.Basic

/-!
# Run-time denotations of event predicates

Lemmas relating `eventDenotation P = Event.τ '' {e | P e}` — the run-times
([krifka-1989]) of the events satisfying a neo-Davidsonian ([parsons-1990])
predicate — to the denotation patterns of `TemporalConnectives.Basic`:
`timeTrace`, `stativeDenotation`, `accomplishmentDenotation`. The
projection keeps only temporal structure (`e.sort` is discarded) and reads
an event's run-time as its located interval, the perfective default.
-/

namespace Tense.TemporalConnectives

variable {Time : Type*} [LinearOrder Time]

theorem timeTrace_eventDenotation (P : Event Time → Prop) :
    timeTrace (eventDenotation P) = { t | ∃ e, P e ∧ t ∈ e.τ } :=
  timeTrace_image Event.τ { e | P e }

theorem eventDenotation_singleton (e₀ : Event Time) :
    eventDenotation (fun e => e = e₀) = accomplishmentDenotation e₀.τ := by
  simp [eventDenotation, accomplishmentDenotation]

theorem eventDenotation_sub_stative (i : NonemptyInterval Time) (P : Event Time → Prop)
    (hP : ∀ e, P e → e.τ ≤ i) :
    eventDenotation P ⊆ stativeDenotation i := by
  rintro j ⟨e, he, rfl⟩; exact hP e he

end Tense.TemporalConnectives
