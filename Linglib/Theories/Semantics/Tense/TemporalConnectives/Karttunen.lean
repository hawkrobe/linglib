import Linglib.Theories.Semantics.Tense.TemporalConnectives.Anscombe

/-!
# Karttunen (1974): *Until*, *When*, and the Two-*Until* Hypothesis
@cite{karttunen-1974}

Karttunen argues that English has **two** *until*s:

- **Durative *until***: "John slept until 3pm." The main clause is durative
  (stative/activity), and *until* marks the minimum extent of the main event.
  Truth-conditionally, this is temporal overlap: A holds at the time of B.

- **Punctual *until***: "The princess didn't wake up until the prince kissed
  her." Requires negation in the main clause. Karttunen's key identity (§5,
  eq. 33): this has the logical form **NOT(A BEFORE T)**.

The punctual *until* presupposes **A BEFORE T ∨ A WHEN T** — the event
eventually happens, either before or at the complement time. The assertion
¬(A BEFORE T) then derives, via disjunctive syllogism, that A occurs at
T (temporal coincidence, i.e., *when*).

## Level

**Level 1 (point sets)**: all definitions operate on `timeTrace` projections,
at the same level as Anscombe. The five English temporal connectives reduce
to four Level 1 primitives:

- *before* = ∃∀ + ordering (Anscombe)
- *after*  = ∃∃ + ordering (Anscombe)
- *when*   = ∃ overlap (this file)
- *while*  = ∀ containment (this file)
- *until*  = ¬*before* (punctual) or *when* (durative) — derived, not primitive

## Cross-Linguistic Evidence

Finnish lexicalizes the two-*until* distinction: **kunnes** / **siihen saakka**
(durative) vs **ennenkuin** (punctual, literally 'before-than'). The Finnish
punctual form is morphologically *before*, confirming Karttunen's analysis.

## References

- Karttunen, L. (1974). Until. *CLS* 10, 284–297.
- Heinamäki, O. (1974). *Semantics of English temporal connectives*. PhD.
- Dowty, D. (1979). *Word Meaning and Montague Grammar*. Ch. 7.
-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time
open Core.Time.Interval

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § 1: Definitions
-- ============================================================================

/-- *When*: temporal coincidence (∃-overlap).
    "A when B" holds when some time point belongs to both A and B. -/
def Karttunen.when_ (A B : SentDenotation Time) : Prop :=
  ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- *While*: temporal containment (∀-inclusion).
    "A while B" holds when every time in A is also a time in B.
    Stronger than *when* (which requires only one shared point).

    This matches the implicit definition in Rett (2026, §3.3)
    used to prove *while* is not ambidirectional. -/
def Karttunen.while_ (A B : SentDenotation Time) : Prop :=
  ∀ t ∈ timeTrace A, t ∈ timeTrace B

/-- Durative *until*: the main event persists at least to the complement time.
    Truth-conditionally equivalent to *when* at Level 1: ∃-overlap.

    The difference from *when* is a **selectional restriction**: *until*
    requires A to be durative (stative/activity). Combined with the
    subinterval property of statives, overlap entails continuous persistence
    of A up to the time of B — the "minimum length" semantics
    (Karttunen 1974, p. 272). -/
def Karttunen.until (A B : SentDenotation Time) : Prop :=
  ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- Punctual *until* = ¬(*before*) (Karttunen 1974, eq. 33).
    "The princess didn't wake up until the prince kissed her"
    = NOT(the princess woke up BEFORE the prince kissed her).

    Presupposes A BEFORE T ∨ A WHEN T (lateness: the event eventually happens). -/
def Karttunen.notUntil (A B : SentDenotation Time) : Prop :=
  ¬ Anscombe.before A B

-- ============================================================================
-- § 2: Durative *Until* ↔ *When*
-- ============================================================================

/-- Durative *until* and *when* are truth-conditionally identical at Level 1.
    The linguistic differences (selectional restriction on durativity,
    endpoint semantics) are pragmatic, not truth-conditional. -/
theorem until_iff_when (A B : SentDenotation Time) :
    Karttunen.until A B ↔ Karttunen.when_ A B :=
  Iff.rfl

-- ============================================================================
-- § 3: Veridicality
-- ============================================================================

/-- *When* is veridical w.r.t. its complement: B must have a witness. -/
theorem when_veridical_complement (A B : SentDenotation Time) :
    Karttunen.when_ A B → ∃ t, t ∈ timeTrace B := by
  rintro ⟨t, _, ht⟩; exact ⟨t, ht⟩

/-- *When* is veridical w.r.t. its main clause: A must have a witness. -/
theorem when_veridical_main (A B : SentDenotation Time) :
    Karttunen.when_ A B → ∃ t, t ∈ timeTrace A := by
  rintro ⟨t, ht, _⟩; exact ⟨t, ht⟩

/-- Durative *until* is veridical w.r.t. its complement. -/
theorem until_veridical_complement (A B : SentDenotation Time) :
    Karttunen.until A B → ∃ t, t ∈ timeTrace B :=
  when_veridical_complement A B

/-- *While* is veridical w.r.t. the main clause when A is nonempty:
    if ∀t∈A, t∈B and A has a witness, then B has a witness. -/
theorem while_veridical_complement (A B : SentDenotation Time)
    (hne : ∃ t, t ∈ timeTrace A) :
    Karttunen.while_ A B → ∃ t, t ∈ timeTrace B := by
  intro hw; obtain ⟨t, ht⟩ := hne; exact ⟨t, hw t ht⟩

/-- Punctual *until* is NOT veridical by assertion alone:
    ¬(A before B) holds vacuously when A is empty. -/
theorem notUntil_not_veridical :
    ∃ (A B : SentDenotation ℤ), Karttunen.notUntil A B ∧ ¬∃ t, t ∈ timeTrace A := by
  refine ⟨∅, { Interval.point 0 }, ?_, ?_⟩
  · intro ⟨t, ⟨i, hi, _⟩, _⟩
    exact absurd hi (Set.mem_empty_iff_false i).mp
  · intro ⟨t, i, hi, _⟩
    exact absurd hi (Set.mem_empty_iff_false i).mp

-- ============================================================================
-- § 4: Karttunen's Identity
-- ============================================================================

/-- **Karttunen's main result** (eq. 33): punctual *until* unfolds to
    "every A-time has some B-time at or before it."

    "not A until B" = ¬(∃t∈A, ∀t'∈B, t<t') = ∀t∈A, ∃t'∈B, t'≤t.

    This is logically equivalent to: every occurrence of A is preceded by
    (or coincides with) some occurrence of B. -/
theorem notUntil_unfold (A B : SentDenotation Time) :
    Karttunen.notUntil A B ↔
    ∀ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, ¬(t < t') := by
  constructor
  · intro h t ht
    by_contra hall
    push_neg at hall
    exact h ⟨t, ht, hall⟩
  · intro h ⟨t, ht, hall⟩
    obtain ⟨t', ht', hle⟩ := h t ht
    exact hle (hall t' ht')

/-- Finnish confirms Karttunen: the punctual *until* form **ennenkuin**
    is morphologically *ennen* ('before') + *kuin* ('than'), i.e.,
    literal *before*-than — the negation is external to the connective.

    This is definitionally true since `notUntil = ¬before`. -/
theorem finnish_confirms_identity :
    ∀ (A B : SentDenotation Time),
      Karttunen.notUntil A B ↔ ¬ Anscombe.before A B :=
  fun _ _ => Iff.rfl

-- ============================================================================
-- § 5: Presupposition of Punctual *Until*
-- ============================================================================

/-- The presupposition of punctual *until*: A BEFORE T ∨ A WHEN T.
    The event eventually happens — either before or at the complement time.

    Combined with the assertion ¬(A BEFORE T), the presupposition yields
    A WHEN T (temporal coincidence) by disjunctive syllogism.

    This derives the intuitive meaning: "not until B" ≈ "at B". -/
theorem notUntil_with_presupposition (A B : SentDenotation Time)
    (hpre : Anscombe.before A B ∨ Karttunen.when_ A B)
    (hassert : Karttunen.notUntil A B) :
    Karttunen.when_ A B :=
  hpre.resolve_left hassert

-- ============================================================================
-- § 6: Logical Relationships
-- ============================================================================

/-- *When* is symmetric: if A overlaps B, then B overlaps A. -/
theorem when_symmetric (A B : SentDenotation Time) :
    Karttunen.when_ A B ↔ Karttunen.when_ B A := by
  constructor <;> rintro ⟨t, h1, h2⟩ <;> exact ⟨t, h2, h1⟩

/-- *While* implies *when* (when A is nonempty):
    containment is stronger than overlap. -/
theorem while_implies_when (A B : SentDenotation Time)
    (hne : ∃ t, t ∈ timeTrace A) :
    Karttunen.while_ A B → Karttunen.when_ A B := by
  intro hw
  obtain ⟨t, ht⟩ := hne
  exact ⟨t, ht, hw t ht⟩

/-- *While* is NOT symmetric: containment is asymmetric.

    Counterexample: A = point at 5, B = interval [1,10].
    A ⊆ B (5 ∈ [1,10]) but B ⊄ A (1 ∉ {5}). -/
theorem while_not_symmetric :
    ¬ ∀ (A B : SentDenotation ℤ),
      Karttunen.while_ A B → Karttunen.while_ B A := by
  intro h
  let iA : Interval ℤ := ⟨5, 5, by omega⟩
  let iB : Interval ℤ := ⟨1, 10, by omega⟩
  have hAs : iA.start = 5 := rfl
  have hAf : iA.finish = 5 := rfl
  have hBs : iB.start = 1 := rfl
  have hBf : iB.finish = 10 := rfl
  have hw : Karttunen.while_ ({iA} : SentDenotation ℤ) (stativeDenotation iB) := by
    intro t ⟨i, hi, hts, htf⟩
    simp only [Set.mem_singleton_iff] at hi; subst hi
    rw [timeTrace_stativeDenotation]
    constructor <;> omega
  have hw' := h _ _ hw
  have h1 : (1 : ℤ) ∈ timeTrace (stativeDenotation iB) := by
    rw [timeTrace_stativeDenotation]; constructor <;> omega
  obtain ⟨i, hi, hts, _⟩ := hw' 1 h1
  simp only [Set.mem_singleton_iff] at hi; subst hi
  omega

/-- *While* is transitive: temporal containment composes. -/
theorem while_transitive (A B C : SentDenotation Time) :
    Karttunen.while_ A B → Karttunen.while_ B C → Karttunen.while_ A C :=
  fun hab hbc t ht => hbc t (hab t ht)

/-- For a fixed time point t in A, if some B-time precedes t,
    then t cannot precede ALL of B. This is the per-witness form of
    the ordering consistency between *after* and *before*. -/
theorem after_witness_excludes_before_witness
    {t t' : Time} (hlt : t' < t) :
    ¬ (t < t') :=
  not_lt.mpr (le_of_lt hlt)

-- ============================================================================
-- § 7: Veridicality Summary
-- ============================================================================

/-- Veridicality summary for the five temporal connectives at Level 1:
    - *before*: complement NOT veridical (∀ vacuously true on empty B)
    - *after*:  complement veridical (∃ witness required)
    - *when*:   complement veridical (∃ overlap witness)
    - *while*:  complement veridical only when A nonempty (∀ vacuously true)
    - *until* (durative): complement veridical (= when)
    - *until* (punctual): complement NOT veridical by assertion alone

    The veridical/non-veridical split mirrors the quantifier structure:
    ∃-based connectives (after, when, durative until) are veridical;
    ∀-based connectives (before, while, punctual until) are non-veridical
    or conditionally veridical. -/
theorem veridicality_mirrors_quantifier_force :
    -- after is ∃∃ → veridical
    (∀ (A B : SentDenotation Time), Anscombe.after A B → ∃ t, t ∈ timeTrace B) ∧
    -- when is ∃-overlap → veridical
    (∀ (A B : SentDenotation Time), Karttunen.when_ A B → ∃ t, t ∈ timeTrace B) ∧
    -- before is ∃∀ → non-veridical (the ∀ over B is vacuously true on ∅)
    (∃ (A B : SentDenotation ℤ), Anscombe.before A B ∧ ¬∃ t, t ∈ timeTrace B) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro A B ⟨_, _, _, ht', _⟩; exact ⟨_, ht'⟩
  · exact when_veridical_complement
  · refine ⟨{ Interval.point 0 }, ∅, ?_, ?_⟩
    · exact ⟨0, ⟨Interval.point 0, rfl, le_refl _, le_refl _⟩,
        fun t' ⟨i, hi, _⟩ => absurd hi (Set.mem_empty_iff_false i).mp⟩
    · intro ⟨_, i, hi, _⟩; exact absurd hi (Set.mem_empty_iff_false i).mp

end Semantics.Tense.TemporalConnectives
