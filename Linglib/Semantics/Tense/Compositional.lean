import Linglib.Semantics.Tense.Pronoun

/-!
# Compositional tense operators
[mendes-2025] [partee-1973]

The compositional interpretation of a tense cell (`Tense/Defs.lean`) in the
situation-semantic style of [mendes-2025]: `constrain s P sit sit'` holds
when the cell `s` relates the event situation's time to the evaluation
situation's time and the payload `P` holds at the event situation.
Following [partee-1973], the event situation is retrieved (an argument),
not quantified over. `PAST`/`PRES`/`FUT` name the three atomic cells'
operators; the dynamic counterparts in `Tense/Dynamic.lean` are the same
cells behind the update spine's test filter.
-/

namespace Tense

open Core.Order (holds)
open Intensional (Index)

variable {W Time : Type*} [LinearOrder Time]

/-- The tense cell `s`, applied compositionally ([mendes-2025]):
    ⟦s⟧ = λP.λsit.λsit'. `holds s τ(sit) τ(sit')` ∧ P(sit) — the cell
    constrains the event–evaluation comparison and the payload is
    evaluated at the event situation. -/
def constrain (s : Finset Ordering) (P : (Index W Time → Prop))
    (sit sit' : Index W Time) : Prop :=
  holds s sit.time sit'.time ∧ P sit

/-- ⟦PAST⟧ = `constrain past`: the event situation precedes the
    evaluation situation. -/
abbrev PAST : (Index W Time → Prop) → Index W Time →
    Index W Time → Prop := constrain past

/-- ⟦PRES⟧ = `constrain present`: the event situation is contemporaneous
    with the evaluation situation. -/
abbrev PRES : (Index W Time → Prop) → Index W Time →
    Index W Time → Prop := constrain present

/-- ⟦FUT⟧ = `constrain future`: the event situation follows the
    evaluation situation. -/
abbrev FUT : (Index W Time → Prop) → Index W Time →
    Index W Time → Prop := constrain future

@[simp] theorem constrain_past_iff (P : (Index W Time → Prop))
    (sit sit' : Index W Time) :
    constrain past P sit sit' ↔ sit.time < sit'.time ∧ P sit := by
  simp [constrain]

@[simp] theorem constrain_present_iff (P : (Index W Time → Prop))
    (sit sit' : Index W Time) :
    constrain present P sit sit' ↔ sit.time = sit'.time ∧ P sit := by
  simp [constrain]

@[simp] theorem constrain_future_iff (P : (Index W Time → Prop))
    (sit sit' : Index W Time) :
    constrain future P sit sit' ↔ sit'.time < sit.time ∧ P sit := by
  simp [constrain]

end Tense
