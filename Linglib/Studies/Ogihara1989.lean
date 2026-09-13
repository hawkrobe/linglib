import Linglib.Semantics.Tense.Compositional

/-!
# Ogihara (1989): Temporal Reference in English and Japanese

This file formalizes the integrated theory of temporal reference with which the first
chapter of [ogihara-1989] closes, reconciling the quantificational analysis of tense of
[prior-1967] with the referential analysis of [partee-1973]: the quantificational approach
is basically correct, and the referential character of tenses is a contextual restriction
on the quantificational force of the tense morphemes. The referential analysis picks the
time and the operator imposes the constraint, so the past operator applied at a
referentially determined time decomposes into the precedence of that time and the truth
of the predicate at it (`referential_past_decomposition`).

## References

* [ogihara-1989]
* [prior-1967]
* [partee-1973]
-/

open Tense

namespace Ogihara1989

open Reference

/-- The Priorean `PAST` operator, applied at a referentially determined
    time g(n), decomposes into the conjunction of (1) the referential
    time precedes the speech situation and (2) the predicate holds at the
    referential time: the referential analysis picks the time, the
    operator imposes the constraint. -/
theorem referential_past_decomposition {W T : Type*} [LinearOrder T]
    (P : (Index W T → Prop)) (g : TemporalAssignment T) (n : ℕ)
    (w : W) (speechTime : T) :
    PAST P ⟨w, interpTense n g⟩ ⟨w, speechTime⟩ ↔
    (g n < speechTime ∧ P ⟨w, g n⟩) := by
  simp

end Ogihara1989
