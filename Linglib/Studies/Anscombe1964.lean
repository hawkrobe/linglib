import Linglib.Semantics.Tense.SentDenotation
import Linglib.Data.Examples.Anscombe1964

/-!
# Anscombe 1964: before and after

*Before* and *after* are not converses: *the Parthenon was there after St. Peter's was* and
*St. Peter's was there after the Parthenon was* are compatible, while the corresponding
*before* claims are not. *Before* is asymmetric and transitive, *after* neither (*I was born
after the Parthenon was there; the Parthenon was there after I was born* would give *I was
born after I was born*), and *p before q* entails *q after p* but not conversely. *After* is
not ambiguous for all that: it has alternative verifications — beginning after, being after
the end, or merely overlapping later — none of which is constant across its uses. Rendered
by quantification over times (§IV), *p after q* says some time of *p* follows some time of
*q*, and *p before q* that some time of *p* precedes every time of *q* — a rendering Anscombe
notes fits *before ever* better than *before*. For instantaneous events the two are genuine
converses, and when a clause does not report one, a beginning or an ending is always
involved: *p before q* is *p before q began*, and *p after q* holds if *p* is after *q* began,
if *q* is before *p*, or if *p* is after *q* stopped (§X).

## Main definitions

* `Anscombe.before`, `Anscombe.after`: the §IV renderings on time traces.
* `Instantaneous`: a clause holding at a single time, where the two are converses.

## References

* [anscombe-1964]
-/

namespace Anscombe1964

open Tense Data.Examples

variable {Time : Type*} [LinearOrder Time]

/-! ### Quantification over times (§IV) -/

/-- *p before q*: a time at which *p* was before every time at which *q*. -/
def Anscombe.before (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t < t'

/-- *p after q*: a time at which *p* was after a time at which *q*. -/
def Anscombe.after (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, t' < t

/-! ### The logical properties (§II) -/

/-- *Before* is asymmetric. -/
theorem before_asymm {A B : SentDenotation Time} :
    Anscombe.before A B → ¬ Anscombe.before B A :=
  fun ⟨a, ha, hab⟩ ⟨b, hb, hba⟩ => lt_irrefl _ ((hab b hb).trans (hba a ha))

/-- *Before* is transitive. -/
theorem before_trans {A B C : SentDenotation Time} :
    Anscombe.before A B → Anscombe.before B C → Anscombe.before A C :=
  fun ⟨a, ha, hab⟩ ⟨b, hb, hbc⟩ => ⟨a, ha, fun c hc => (hab b hb).trans (hbc c hc)⟩

/-- *p before q* entails *q after p*. -/
theorem after_of_before {A B : SentDenotation Time} (h : Anscombe.before A B)
    (hB : (timeTrace B).Nonempty) : Anscombe.after B A :=
  let ⟨a, ha, hab⟩ := h
  let ⟨b, hb⟩ := hB
  ⟨b, hb, a, ha, hab b hb⟩

/-- *After* is not asymmetric: two overlapping stretches are each after the other. -/
theorem after_not_asymm :
    ∃ A B : SentDenotation ℤ, Anscombe.after A B ∧ Anscombe.after B A :=
  ⟨{NonemptyInterval.pure 0, NonemptyInterval.pure 2},
    {NonemptyInterval.pure 1, NonemptyInterval.pure 3},
    ⟨2, ⟨NonemptyInterval.pure 2, Or.inr rfl, le_rfl, le_rfl⟩,
      1, ⟨NonemptyInterval.pure 1, Or.inl rfl, le_rfl, le_rfl⟩, by decide⟩,
    ⟨3, ⟨NonemptyInterval.pure 3, Or.inr rfl, le_rfl, le_rfl⟩,
      0, ⟨NonemptyInterval.pure 0, Or.inl rfl, le_rfl, le_rfl⟩, by decide⟩⟩

/-- *After* is not transitive: *I was born after the Parthenon was there; the Parthenon was
there after I was born* does not give *I was born after I was born*. -/
theorem after_not_trans :
    ∃ A B C : SentDenotation ℤ,
      Anscombe.after A B ∧ Anscombe.after B C ∧ ¬ Anscombe.after A C := by
  refine ⟨{NonemptyInterval.pure 2}, {NonemptyInterval.pure 1, NonemptyInterval.pure 4},
    {NonemptyInterval.pure 3},
    ⟨2, ⟨NonemptyInterval.pure 2, rfl, le_rfl, le_rfl⟩,
      1, ⟨NonemptyInterval.pure 1, Or.inl rfl, le_rfl, le_rfl⟩, by decide⟩,
    ⟨4, ⟨NonemptyInterval.pure 4, Or.inr rfl, le_rfl, le_rfl⟩,
      3, ⟨NonemptyInterval.pure 3, rfl, le_rfl, le_rfl⟩, by decide⟩, ?_⟩
  rintro ⟨t, ⟨i, hi, hts, htf⟩, t', ⟨j, hj, ht's, ht'f⟩, hlt⟩
  rw [Set.mem_singleton_iff] at hi hj
  subst hi; subst hj
  simp only [NonemptyInterval.pure] at hts htf ht's ht'f
  omega

/-! ### Instantaneous events (§VI–§VIII) -/

/-- A clause reports an instantaneous event when it holds at a single time. -/
def Instantaneous (A : SentDenotation Time) : Prop := ∃ t, timeTrace A = {t}

/-- When *p* reports an instantaneous event, *p after q* is *q before p* (§X, case 2). -/
theorem after_iff_before_of_instantaneous {A B : SentDenotation Time} (hA : Instantaneous A) :
    Anscombe.after A B ↔ Anscombe.before B A := by
  obtain ⟨t, ht⟩ := hA
  simp [Anscombe.after, Anscombe.before, ht]

/-- For two instantaneous events *before* and *after* are genuine converses. -/
theorem before_iff_after_of_instantaneous {A B : SentDenotation Time}
    (hB : Instantaneous B) : Anscombe.before A B ↔ Anscombe.after B A :=
  (after_iff_before_of_instantaneous hB).symm

/-- An instantaneous *p* cannot be both before and after *q* (§X, case 1). -/
theorem before_not_after_of_instantaneous {A B : SentDenotation Time} (hA : Instantaneous A)
    (h : Anscombe.before A B) : ¬ Anscombe.after A B := by
  obtain ⟨t, ht⟩ := hA
  simp only [Anscombe.before, Anscombe.after, ht, Set.mem_singleton_iff, exists_eq_left] at h ⊢
  rintro ⟨t', ht', hlt⟩
  exact lt_asymm (h t' ht') hlt

/-- A stretch can be both before and after an instantaneous event. -/
theorem after_and_before_of_extended :
    ∃ A B : SentDenotation ℤ, Instantaneous B ∧ Anscombe.after A B ∧ Anscombe.before A B :=
  ⟨{NonemptyInterval.pure 1, NonemptyInterval.pure 7}, {NonemptyInterval.pure 4},
    ⟨4, by ext t; simp [timeTrace, NonemptyInterval.pure]; omega⟩,
    ⟨7, ⟨NonemptyInterval.pure 7, Or.inr rfl, le_rfl, le_rfl⟩,
      4, ⟨NonemptyInterval.pure 4, rfl, le_rfl, le_rfl⟩, by decide⟩,
    ⟨1, ⟨NonemptyInterval.pure 1, Or.inl rfl, le_rfl, le_rfl⟩, by
      rintro t' ⟨j, hj, hs, _⟩
      rw [Set.mem_singleton_iff] at hj
      subst hj
      simp only [NonemptyInterval.pure] at hs
      omega⟩⟩

/-! ### Beginnings and endings (§IX–§X) -/

/-- *p before q* is *p before q began*: when *q* has a first time, *p* precedes every time of
*q* iff some time of *p* precedes that first time. -/
theorem before_iff_lt_least {A B : SentDenotation Time} {lb : Time}
    (hlb : IsLeast (timeTrace B) lb) :
    Anscombe.before A B ↔ ∃ t ∈ timeTrace A, t < lb :=
  ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h lb hlb.1⟩,
    fun ⟨a, ha, h⟩ => ⟨a, ha, fun _ ht' => h.trans_le (hlb.2 ht')⟩⟩

/-- *p after q* is *p after q began* (§X, case 3a). -/
theorem after_iff_least_lt {A B : SentDenotation Time} {lb : Time}
    (hlb : IsLeast (timeTrace B) lb) :
    Anscombe.after A B ↔ ∃ t ∈ timeTrace A, lb < t :=
  ⟨fun ⟨a, ha, _, ht', h⟩ => ⟨a, ha, (hlb.2 ht').trans_lt h⟩,
    fun ⟨a, ha, h⟩ => ⟨a, ha, lb, hlb.1, h⟩⟩

/-- *p after q stopped* gives *p after q* (§X, case 3c). -/
theorem after_of_stopped {A B : SentDenotation Time} {ub : Time} (hub : ub ∈ timeTrace B)
    (h : ∃ t ∈ timeTrace A, ub < t) : Anscombe.after A B :=
  let ⟨a, ha, hlt⟩ := h
  ⟨a, ha, ub, hub, hlt⟩

/-! ### The paper's examples -/

/-- The mutual pairs: *p after q and q after p* is consistent, *p before q and q before p*
is not. -/
theorem rows_mutual :
    ∀ r ∈ Examples.all, r.feature? "pattern" = some "mutual" →
      (r.judgment = .acceptable ↔ r.feature? "connective" = some "after") := by
  decide +kernel

end Anscombe1964
