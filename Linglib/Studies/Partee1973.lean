import Linglib.Semantics.Tense.Compositional

/-!
# Partee (1973): Some Structural Analogies between Tenses and Pronouns in English

This file formalizes the analogy of [partee-1973]: tenses show the same three uses as
pronouns, deictic, anaphoric, and bound, and so refer to times as pronouns refer to
individuals rather than quantifying over them as the operators of [prior-1967] do. Past tense
introduces a temporal variable resolved by an assignment to a contextually salient time
(`parteeStoveExample`), so *I didn't turn off the stove* is false when the stove was turned
off at that time, whereas the Priorean reading, that there is some past time at which it was
not turned off, is trivially true (`stove_refutes_prior`); in a narrative two past tenses pick
up the same salient time, as anaphoric pronouns corefer (`narrativeAnaphora`).

## Implementation notes

The temporal assignments and tense interpretation are those of
`Semantics/Tense/Compositional`, the temporal counterpart of the entity assignments of the
Montague substrate.

## References

* [partee-1973]
* [prior-1967]
-/

open Tense

namespace Partee1973

open Reference

/-- *I didn't turn off the stove*: negation over a past tense that refers to the salient time
the assignment supplies for variable `n`. -/
def parteeStoveExample {T : Type*} (turnedOff : T → Prop) (g : TemporalAssignment T) (n : ℕ) :
    Prop :=
  ¬ turnedOff (interpTense n g)

/-- The argument against [prior-1967] as a countermodel: with the stove turned off at the
salient time, the referential reading is false, while the Priorean existential reading stays
true, witnessed by any other past time. -/
theorem stove_refutes_prior :
    ¬ parteeStoveExample (· = (-1 : ℤ)) (λ _ => (-1 : ℤ)) 0 ∧
      ∃ s : Index Unit ℤ, PAST (λ s => s.time ≠ (-1 : ℤ)) s ⟨(), 0⟩ :=
  ⟨λ h => h rfl, ⟨(), -2⟩, by decide, by decide⟩

/-- *He turned the corner. He saw a house.*: both past tenses refer to the same narrative time,
as anaphoric pronouns corefer with an established individual. -/
def narrativeAnaphora {T : Type*} (P Q : T → Prop) (g : TemporalAssignment T) (n : ℕ) : Prop :=
  P (interpTense n g) ∧ Q (interpTense n g)

end Partee1973
