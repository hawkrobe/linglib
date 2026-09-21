import Linglib.Semantics.Aspect.Viewpoint

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

## Main definitions

* `Aspect.HasSubintervalProperty`: the run times of the predicate form a lower set at every
  world.

## Main results

* `Aspect.hasSubintervalProperty_iff_witnesses`: every subinterval of the run time of an event of
  the predicate is the run time of an event of the predicate.
* `Aspect.HasSubintervalProperty.prfv_of_impf`: the imperfective entails the perfective.
* `Aspect.not_hasSubintervalProperty_snd_eq`: the predicate of events that end at a fixed later
  time lacks the property.
* `Aspect.exists_prfv_of_impf_not_hasSubintervalProperty`: a predicate may validate the
  entailment and lack the property.

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

namespace Aspect

variable {W T : Type*} [LinearOrder T] {P : W → Event T → Prop} {w : W}
  {t : NonemptyInterval T}

/-- A predicate of events has the subinterval property when its run times form a lower set at
every world. -/
def HasSubintervalProperty (P : W → Event T → Prop) : Prop :=
  ∀ w, IsLowerSet (eventDenotation (P w))

/-- A predicate has the subinterval property exactly when every subinterval of the run time of
one of its events is the run time of one of its events. -/
theorem hasSubintervalProperty_iff_witnesses :
    HasSubintervalProperty P ↔
      ∀ (e : Event T) (w : W), P w e → ∀ t ≤ e.τ, ∃ e' : Event T, e'.τ = t ∧ P w e' :=
  ⟨fun h _ w hP _ ht ↦ let ⟨e', hP', hτ⟩ := h w ht (mem_eventDenotation_of hP); ⟨e', hτ, hP'⟩,
    fun h w _ t ht ⟨e, hP, he⟩ ↦ let ⟨e', hτ, hP'⟩ := h e w hP t (he ▸ ht); ⟨e', hP', hτ⟩⟩

namespace HasSubintervalProperty

/-- Under the subinterval property an interval inside the run time of an event of the predicate
is a run time of the predicate. -/
theorem mem_eventDenotation_of_unbounded (h : HasSubintervalProperty P)
    (ht : UNBOUNDED P w t) : t ∈ eventDenotation (P w) :=
  let ⟨_, hs, hle⟩ := unbounded_iff_mem_lowerClosure.1 ht; h w hle hs

/-- Under the subinterval property the non-strict imperfective entails the perfective. -/
theorem prfv_of_unbounded (h : HasSubintervalProperty P) (ht : UNBOUNDED P w t) :
    PRFV P w t :=
  prfv_iff_mem_upperClosure.2 (subset_upperClosure (h.mem_eventDenotation_of_unbounded ht))

/-- Under the subinterval property the imperfective entails the perfective. -/
theorem prfv_of_impf (h : HasSubintervalProperty P) (ht : IMPF P w t) : PRFV P w t :=
  h.prfv_of_unbounded (impf_entails_unbounded P w t ht)

end HasSubintervalProperty

/-- The predicate of events that end at a fixed time lacks the subinterval property when there
is an earlier time, as the building of a house holds of no proper part that lacks the result. -/
theorem not_hasSubintervalProperty_snd_eq [Nonempty W] {t₁ t₂ : T} (hlt : t₁ < t₂) :
    ¬ HasSubintervalProperty fun (_ : W) (e : Event T) ↦ e.τ.snd = t₂ := fun h ↦ by
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h
    ⟨⟨⟨t₁, t₂⟩, hlt.le⟩, .action⟩ (Classical.arbitrary W) rfl (.pure t₁)
    (NonemptyInterval.le_def.2 ⟨le_rfl, hlt.le⟩)
  rw [hτ] at hP
  exact hlt.ne hP

/-- The entailment from the imperfective to the perfective does not characterize the subinterval
property. The predicate of events that are instantaneous or run from `0` to `2` validates it,
every reference time containing an instant, and the interval from `0` to `1` is a subinterval
of one of its run times without being one. -/
theorem exists_prfv_of_impf_not_hasSubintervalProperty :
    ∃ P : Unit → Event ℤ → Prop,
      (∀ w t, IMPF P w t → PRFV P w t) ∧ ¬ HasSubintervalProperty P := by
  refine ⟨fun _ e ↦ e.τ.IsPoint ∨ e.τ = ⟨⟨0, 2⟩, by decide⟩,
    fun _ t _ ↦ ⟨⟨.pure t.fst, .action⟩, NonemptyInterval.le_def.2 ⟨le_rfl, t.fst_le_snd⟩,
      .inl rfl⟩, fun h ↦ ?_⟩
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h
    ⟨⟨⟨0, 2⟩, by decide⟩, .action⟩ () (.inr rfl) ⟨⟨0, 1⟩, by decide⟩
    (NonemptyInterval.le_def.2 ⟨le_rfl, by decide⟩)
  rw [hτ] at hP
  rcases hP with hP | hP
  · exact absurd hP (by decide)
  · exact absurd (congrArg (·.snd) hP) (by decide)

end Aspect
