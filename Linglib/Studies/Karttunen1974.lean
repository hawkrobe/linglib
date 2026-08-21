import Linglib.Studies.Heinamaki1974

/-!
# Karttunen (1974): *Until*

[karttunen-1974] argues that English has two *until*s. Durative *until* modifies a durative
sentence (1a–d) and marks the minimum length of its interval (12)–(14), (21): on run-time
denotations, where a durative clause holds throughout each of its run-times, some run-time
of `A` reaches a time of `B` (`until_`). Punctual *until* (1e) is a negative polarity item
that locates an event in time; negation takes wide scope over it (3b), and the standard
one-*until* arguments that negation makes a sentence durative fail (8)–(10). Its logical
form is that of *before*: *A not until T* is `NOT(A BEFORE T)` (33) (`notUntil`, the
negation of [anscombe-1964]'s *before*), so every occurrence of `A` has a time of `T` at or
before it (`notUntil_iff`), and its denial is *A before T* (30)–(31) (`not_notUntil_iff`).
What distinguishes it from *before* is a pragmatic presupposition of lateness, (34):
*A before T or A when T* (`presupposition`, with [heinamaki-1974]'s *when*). The logical
form holds of a clause that never happens (`notUntil_empty`), so the commitment to *A when
T* (29b) is not asserted but follows from assertion and presupposition by disjunctive
syllogism, (36) (`notUntil_when`) — whence *Nancy didn't get married until she died* (23)
commits the speaker to a marriage at her death, which *before* would not. Finnish separates
the two *until*s, *kunnes/saakka* against *ennenkuin* (37), and its positive-polarity
*vasta*, like German *erst*, asserts *A when T* under the same presupposition (38)–(39):
for point events the two logical forms coincide given the presupposition
(`notUntil_iff_when_of_presupposition`).
-/

namespace Karttunen1974

open Tense Anscombe1964 Heinamaki1974

variable {Time : Type*} [LinearOrder Time] (A B : SentDenotation Time)

/-- Durative *A until B*: some run-time of `A` reaches a time of `B`. -/
def until_ : Prop := ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- Punctual *A not until B*, (33): *A not before B*. -/
def notUntil : Prop := ¬ Anscombe.before A B

/-- The presupposition of lateness, (34): *A before B or A when B*. -/
def presupposition : Prop := Anscombe.before A B ∨ when_ A B

theorem until_veridical_complement : until_ A B → ∃ t, t ∈ timeTrace B :=
  fun ⟨t, _, ht⟩ => ⟨t, ht⟩

/-- Every occurrence of `A` has a time of `B` at or before it. -/
theorem notUntil_iff : notUntil A B ↔ ∀ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, t' ≤ t := by
  simp only [notUntil, Anscombe.before, not_exists, not_and, not_forall, not_lt, exists_prop]

/-- Denying *A not until B* is asserting *A before B*, (30)–(31). -/
theorem not_notUntil_iff : ¬ notUntil A B ↔ Anscombe.before A B := not_not

/-- The logical form holds of a clause that never happens. -/
theorem notUntil_empty : notUntil (∅ : SentDenotation Time) B :=
  fun ⟨_, ⟨_, hi, _⟩, _⟩ => hi

/-- Disjunctive syllogism, (36): assertion and presupposition together yield *A when B*. -/
theorem notUntil_when (h : notUntil A B) (hp : presupposition A B) : when_ A B :=
  hp.resolve_left h

theorem mem_timeTrace_pure (a t : Time) :
    t ∈ timeTrace ({NonemptyInterval.pure a} : SentDenotation Time) ↔ t = a := by
  simp only [mem_timeTrace, Set.mem_singleton_iff, exists_eq_left, NonemptyInterval.mem_pure]

/-- For point events under the presupposition, *A not until B* and *A when B* — the logical
forms of Finnish *ennenkuin* and *vasta*, (39) — say the same. -/
theorem notUntil_iff_when_of_presupposition (a b : Time)
    (hp : presupposition {NonemptyInterval.pure a} {NonemptyInterval.pure b}) :
    notUntil {NonemptyInterval.pure a} {NonemptyInterval.pure b} ↔
      when_ {NonemptyInterval.pure a} {NonemptyInterval.pure b} := by
  simp only [notUntil, Anscombe.before, when_, presupposition, mem_timeTrace_pure,
    exists_eq_left, forall_eq] at hp ⊢
  exact ⟨hp.resolve_left, fun h => by subst h; exact lt_irrefl _⟩

end Karttunen1974
