module

public import Linglib.Semantics.Aspect.Viewpoint

/-!
# The subinterval property

This file defines the subinterval property of Bennett and Partee and of Dowty. A predicate of
events has it when every subinterval of the run time of an event it holds of is the run time of
an event it holds of, which is to say that its run times form a lower set. States and activities
have the property: if John slept from one to three, he slept from one to two. Accomplishments and
achievements lack it, since no proper part of the building of a house is the building of a house.
The property draws only this line, and does not separate states from activities or
accomplishments from achievements.

For a predicate with the property the imperfective entails the perfective at the same reference
time, *Mary was running* entailing *Mary ran*: the reference time lies inside the run time of a
running, so it is itself the run time of a running. The entailment does not characterize the
property, since a predicate may validate it without being closed under subintervals.

Dowty states the property of sentences true at intervals, and an interval predicate has it when
it holds at every subinterval of an interval it holds at. The non-strict and the strict
imperfective have it whatever the predicate, and so does the negated perfective: an interval
containing no event of the predicate has no subinterval containing one. A durative claim, the
predicate at every subinterval of a span, has it too, and for a predicate with the property it
is the predicate itself.

## Main definitions

* `Aspect.HasSubintervalProperty`: the run times of the predicate form a lower set at every
  world.
* `Aspect.IntervalPred.HasSubintervalProperty`: the intervals at which an interval predicate
  holds form a lower set at every world.

## Main results

* `Aspect.hasSubintervalProperty_iff_witnesses`: every subinterval of the run time of an event of
  the predicate is the run time of an event of the predicate.
* `Aspect.HasSubintervalProperty.prfv_of_impf`: the imperfective entails the perfective.
* `Aspect.not_hasSubintervalProperty_snd_eq`: the predicate of events that end when a durative
  event ends lacks the property.
* `Aspect.exists_prfv_of_impf_not_hasSubintervalProperty`: a predicate may validate the
  entailment and lack the property.
* `Aspect.hasSubintervalProperty_unbounded`, `Aspect.hasSubintervalProperty_impf`,
  `Aspect.hasSubintervalProperty_not_prfv`: the imperfectives and the negated perfective have the
  property as interval predicates.
* `Aspect.IntervalPred.durative_iff_of_hasSubintervalProperty`: a predicate with the property
  holds throughout a span exactly when it holds at the span.

## Implementation notes

The property is divisive reference, `Mereology.DIV`, of the predicate's run times, so it is
stated on mathlib's `IsLowerSet`. The viewpoint operators quantify over events of the world of
evaluation, so the entailment is the extensional one. The imperfective paradox proper, on which
*John was building a house* is true though no house is ever built, needs a modal progressive
and is not modelled.

## References

* [bennett-partee-1972]
* [dowty-1979]
-/

@[expose] public section

namespace Aspect

open Event (τ)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] {P : W → E → Prop} {w : W}
  {t : NonemptyInterval T}

/-- A predicate of events has the subinterval property when its run times form a lower set at
every world. -/
def HasSubintervalProperty (P : W → E → Prop) : Prop :=
  ∀ w, IsLowerSet (τ '' {e | P w e})

/-- A predicate has the subinterval property exactly when every subinterval of the run time of
one of its events is the run time of one of its events. -/
theorem hasSubintervalProperty_iff_witnesses :
    HasSubintervalProperty P ↔
      ∀ (e : E) (w : W), P w e → ∀ t ≤ τ e, ∃ e' : E, τ e' = t ∧ P w e' :=
  ⟨fun h _ w hP _ ht ↦ let ⟨e', hP', hτ⟩ := h w ht (Set.mem_image_of_mem τ hP); ⟨e', hτ, hP'⟩,
    fun h w _ t ht ⟨e, hP, he⟩ ↦ let ⟨e', hτ, hP'⟩ := h e w hP t (he ▸ ht); ⟨e', hP', hτ⟩⟩

namespace HasSubintervalProperty

/-- Under the subinterval property an interval inside the run time of an event of the predicate
is a run time of the predicate. -/
theorem mem_image_of_unbounded (h : HasSubintervalProperty P) (ht : UNBOUNDED P w t) :
    t ∈ τ '' {e | P w e} :=
  let ⟨_, hs, hle⟩ := unbounded_iff_mem_lowerClosure.1 ht; h w hle hs

/-- Under the subinterval property the non-strict imperfective entails the perfective. -/
theorem prfv_of_unbounded (h : HasSubintervalProperty P) (ht : UNBOUNDED P w t) :
    PRFV P w t :=
  prfv_iff_mem_upperClosure.2 (subset_upperClosure (h.mem_image_of_unbounded ht))

/-- Under the subinterval property the imperfective entails the perfective. -/
theorem prfv_of_impf (h : HasSubintervalProperty P) (ht : IMPF P w t) : PRFV P w t :=
  h.prfv_of_unbounded (impf_entails_unbounded P w t ht)

end HasSubintervalProperty

/-- The predicate of events that end when a durative event ends lacks the subinterval property,
as the building of a house holds of no proper part that lacks the result. -/
theorem not_hasSubintervalProperty_snd_eq [Nonempty W] {e : E} (he : (τ e).fst < (τ e).snd) :
    ¬ HasSubintervalProperty fun (_ : W) (e' : E) ↦ (τ e').snd = (τ e).snd := fun h ↦ by
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h e (Classical.arbitrary W) rfl
    (.pure (τ e).fst) (NonemptyInterval.le_def.2 ⟨le_rfl, he.le⟩)
  rw [hτ] at hP
  exact he.ne hP

/-- The entailment from the imperfective to the perfective does not characterize the subinterval
property. The predicate of events that are instantaneous or run from `0` to `2` validates it,
every reference time containing an instant, and the interval from `0` to `1` is a subinterval
of one of its run times without being one. -/
theorem exists_prfv_of_impf_not_hasSubintervalProperty :
    ∃ P : Unit → NonemptyInterval ℤ → Prop,
      (∀ w t, IMPF P w t → PRFV P w t) ∧ ¬ HasSubintervalProperty P := by
  refine ⟨fun _ e ↦ e.IsPoint ∨ e = ⟨⟨0, 2⟩, by decide⟩,
    fun _ t _ ↦ ⟨.pure t.fst, NonemptyInterval.le_def.2 ⟨le_rfl, t.fst_le_snd⟩, .inl rfl⟩,
    fun h ↦ ?_⟩
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h
    ⟨⟨0, 2⟩, by decide⟩ () (.inr rfl) ⟨⟨0, 1⟩, by decide⟩
    (NonemptyInterval.le_def.2 ⟨le_rfl, by decide⟩)
  rw [Event.τ_nonemptyInterval] at hτ
  subst hτ
  rcases hP with hP | hP
  · exact absurd hP (by decide)
  · exact absurd (congrArg (·.snd) hP) (by decide)

/-! ### Interval predicates -/

/-- An interval predicate has the subinterval property when it holds at every subinterval of an
interval it holds at, so that at every world the intervals at which it holds form a lower set. -/
def IntervalPred.HasSubintervalProperty (p : IntervalPred W T) : Prop :=
  ∀ w, IsLowerSet {t | p w t}

variable (P)

/-- The non-strict imperfective has the subinterval property whatever the predicate. -/
theorem hasSubintervalProperty_unbounded : (UNBOUNDED P).HasSubintervalProperty :=
  fun _ _ _ hle ⟨e, he, hP⟩ ↦ ⟨e, hle.trans he, hP⟩

/-- The imperfective has the subinterval property whatever the predicate. -/
theorem hasSubintervalProperty_impf : (IMPF P).HasSubintervalProperty :=
  fun _ _ _ hle ⟨e, he, hP⟩ ↦ ⟨e, hle.trans_lt he, hP⟩

/-- Negation yields the subinterval property, since an interval containing no event of the
predicate has no subinterval containing one. -/
theorem hasSubintervalProperty_not_prfv :
    IntervalPred.HasSubintervalProperty fun w (t : NonemptyInterval T) ↦ ¬ PRFV P w t :=
  fun _ _ _ hle hn ⟨e, he, hP⟩ ↦ hn ⟨e, he.trans hle, hP⟩

variable {p : IntervalPred W T}

/-- A durative claim has the subinterval property whatever the predicate. -/
theorem IntervalPred.hasSubintervalProperty_durative : p.durative.HasSubintervalProperty :=
  fun _ _ _ hle h _ hj ↦ h _ (hj.trans hle)

/-- A predicate with the subinterval property holds throughout a span exactly when it holds at
the span. -/
theorem IntervalPred.durative_iff_of_hasSubintervalProperty (hp : p.HasSubintervalProperty) :
    p.durative w t ↔ p w t :=
  ⟨fun h ↦ h t le_rfl, fun h _ hj ↦ hp w hj h⟩

end Aspect
