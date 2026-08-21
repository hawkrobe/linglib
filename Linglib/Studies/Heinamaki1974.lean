import Linglib.Studies.Anscombe1964

/-!
# Heinämäki (1974): English temporal connectives

[heinamaki-1974] gives truth conditions for the English temporal connectives in terms of
the times at which the two clauses hold. On run-time denotations they are relations between
the clauses' time traces: *A when B* asserts that the two hold at a common time (`when_`),
*A while B* that every time of `A` is a time of `B` (`while_`), *A whenever B* the converse
containment (`whenever`), *A since B* that some time of `B` lies at or before every time of
`A` (`since`), and *A by B* that some time of `A` lies at or before every time of `B`
(`by_`). *Since* and *by* are the non-strict counterparts of [anscombe-1964]'s *before*, with
the roles of the clauses exchanged, so *before* entails *by* but not conversely
(`before_by`, `by_not_before`). The existential connectives commit the speaker to both
clauses (`when_veridical_complement`, `since_veridical_complement`, `by_veridical_main`);
the universal ones do so only given the clause they quantify over
(`while_veridical_complement`), and are not symmetric (`while_not_symm`).
-/

namespace Heinamaki1974

open Tense Anscombe1964 NonemptyInterval

variable {Time : Type*} [LinearOrder Time] (A B : SentDenotation Time)

/-- *A when B*: `A` and `B` hold at a common time. -/
def when_ : Prop := ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- *A while B*: every time of `A` is a time of `B`. -/
def while_ : Prop := ∀ t ∈ timeTrace A, t ∈ timeTrace B

/-- *A whenever B*: every time of `B` is a time of `A`. -/
def whenever : Prop := ∀ t ∈ timeTrace B, t ∈ timeTrace A

/-- *A since B*: some time of `B` is at or before every time of `A`. -/
def since : Prop := ∃ t ∈ timeTrace B, ∀ t' ∈ timeTrace A, t ≤ t'

/-- *A by B*: some time of `A` is at or before every time of `B`. -/
def by_ : Prop := ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t ≤ t'

theorem when_comm : when_ A B ↔ when_ B A :=
  ⟨fun ⟨t, h₁, h₂⟩ => ⟨t, h₂, h₁⟩, fun ⟨t, h₁, h₂⟩ => ⟨t, h₂, h₁⟩⟩

theorem when_veridical_complement : when_ A B → ∃ t, t ∈ timeTrace B :=
  fun ⟨t, _, ht⟩ => ⟨t, ht⟩

theorem when_veridical_main : when_ A B → ∃ t, t ∈ timeTrace A := fun ⟨t, ht, _⟩ => ⟨t, ht⟩

theorem while_veridical_complement (hne : ∃ t, t ∈ timeTrace A) :
    while_ A B → ∃ t, t ∈ timeTrace B :=
  fun hw => hne.imp fun _ ht => hw _ ht

theorem when_of_while (hne : ∃ t, t ∈ timeTrace A) : while_ A B → when_ A B :=
  fun hw => hne.imp fun _ ht => ⟨ht, hw _ ht⟩

theorem when_of_whenever (hne : ∃ t, t ∈ timeTrace B) : whenever A B → when_ A B :=
  fun hw => hne.imp fun _ ht => ⟨hw _ ht, ht⟩

theorem since_veridical_complement : since A B → ∃ t, t ∈ timeTrace B :=
  fun ⟨t, ht, _⟩ => ⟨t, ht⟩

theorem by_veridical_main : by_ A B → ∃ t, t ∈ timeTrace A := fun ⟨t, ht, _⟩ => ⟨t, ht⟩

/-- *Before* is strict *by*. -/
theorem before_by : Anscombe.before A B → by_ A B :=
  fun ⟨t, ht, h⟩ => ⟨t, ht, fun t' ht' => (h t' ht').le⟩

/-- *While* is not symmetric: a moment inside a stretch. -/
theorem while_not_symm :
    ¬∀ A B : SentDenotation ℤ, while_ A B → while_ B A := by
  intro h
  let i₁₀ : NonemptyInterval ℤ := ⟨⟨1, 10⟩, by decide⟩
  have h5 : (pure 5 : NonemptyInterval ℤ).fst = 5 ∧ (pure 5 : NonemptyInterval ℤ).snd = 5 :=
    ⟨rfl, rfl⟩
  have h₁₀ : i₁₀.fst = 1 ∧ i₁₀.snd = 10 := ⟨rfl, rfl⟩
  have hw : while_ ({pure 5} : SentDenotation ℤ) (stativeDenotation i₁₀) := by
    rintro t ⟨i, hi, hts, htf⟩
    rw [Set.mem_singleton_iff] at hi; subst hi
    rw [timeTrace_stativeDenotation]
    exact ⟨by omega, by omega⟩
  obtain ⟨i, hi, h1, _⟩ :=
    h _ _ hw 1 (by rw [timeTrace_stativeDenotation]; exact ⟨le_rfl, by decide⟩)
  rw [Set.mem_singleton_iff] at hi; subst hi
  omega

/-- *By* allows coincidence where *before* does not: an arrival exactly at the deadline. -/
theorem by_not_before :
    ¬∀ A B : SentDenotation ℤ, by_ A B → Anscombe.before A B := by
  intro h
  have h5 : (pure 5 : NonemptyInterval ℤ).fst = 5 ∧ (pure 5 : NonemptyInterval ℤ).snd = 5 :=
    ⟨rfl, rfl⟩
  obtain ⟨t, ⟨i, hi, h1, h2⟩, hall⟩ := h {pure 5} {pure 5}
    ⟨5, ⟨pure 5, rfl, le_rfl, le_rfl⟩, fun _ ⟨j, hj, hts, _⟩ => by
      rw [Set.mem_singleton_iff] at hj; subst hj; exact hts⟩
  rw [Set.mem_singleton_iff] at hi; subst hi
  have := hall 5 ⟨pure 5, rfl, le_rfl, le_rfl⟩
  omega

end Heinamaki1974
