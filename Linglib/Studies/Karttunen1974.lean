import Linglib.Studies.Anscombe1964

/-!
# Karttunen (1974): *Until*

[karttunen-1974] argues that English has two *until*s. Durative *until* selects a durative
main clause (a state or activity), is indifferent to polarity, and asserts that the main
clause holds through a period reaching the time of the *until*-clause: on run-time
denotations, where a durative clause holds throughout each of its run-times, some run-time
of `A` contains a time of `B` (`until_`). Punctual *until* selects a punctual main clause and
is a negative polarity item, acceptable only with negation scoping over the *until*-phrase;
*not A until B* is then truth-conditionally *not A before B* (`notUntil`, the negation of
[anscombe-1964]'s *before*), every occurrence of `A` having a time of `B` at or before it
(`notUntil_iff`). What distinguishes punctual *until* from *before* under negation is a
presupposition that `A` does occur (`actualization`), which the assertion alone does not
supply (`notUntil_empty`): together they place an occurrence of `A` at or after a time of
`B` (`notUntil_actualization`) — *the princess didn't wake up until the prince kissed her*
puts the waking at the kiss or a little later, and *Nancy didn't get married until she died*
is odd because the marriage would have to follow the death.
-/

namespace Karttunen1974

open Tense Anscombe1964 NonemptyInterval

variable {Time : Type*} [LinearOrder Time] (A B : SentDenotation Time)

/-- Durative *A until B*: some run-time of `A` reaches a time of `B`. -/
def until_ : Prop := ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- Punctual *not A until B*: *not A before B*. -/
def notUntil : Prop := ¬ Anscombe.before A B

/-- The presupposition of punctual *until*: `A` does occur. -/
def actualization : Prop := ∃ t, t ∈ timeTrace A

theorem until_veridical_complement : until_ A B → ∃ t, t ∈ timeTrace B :=
  fun ⟨t, _, ht⟩ => ⟨t, ht⟩

/-- Every occurrence of `A` has a time of `B` at or before it. -/
theorem notUntil_iff : notUntil A B ↔ ∀ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, t' ≤ t := by
  simp only [notUntil, Anscombe.before, not_exists, not_and, not_forall, not_lt, exists_prop]

/-- The assertion alone holds of a clause that never happens. -/
theorem notUntil_empty : notUntil (∅ : SentDenotation Time) B :=
  fun ⟨_, ⟨_, hi, _⟩, _⟩ => hi

/-- With the presupposition, `A` occurs at or after a time of `B`. -/
theorem notUntil_actualization (h : notUntil A B) (ha : actualization A) :
    ∃ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, t' ≤ t :=
  ha.imp fun _ ht => ⟨ht, (notUntil_iff A B).1 h _ ht⟩

end Karttunen1974
