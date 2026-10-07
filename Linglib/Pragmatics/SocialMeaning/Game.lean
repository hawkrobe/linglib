module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Pragmatics.SocialMeaning.Persona

/-!
# Social meaning games

This file instantiates the Rational Speech Act pipeline on personae, Burnett's social meaning
games. A listener holds a prior over the personae of an incompatibility graph, and the meaning of
a message is its indexation, the set of personae that meet its Eckert–Montague field. The literal
listener conditions the prior on that set, the speaker is the softmax of informativity, and the
pragmatic listener inverts the speaker, so a persona two messages meet produces the one whose
field carries less prior mass more often, a persona only one message meets produces it with
certainty, and hearing a message rules out the personae it does not meet. Henderson and McCready
replace the indexation by a listener's graded likelihood of the message given the persona, of
which the indicator of the indexation is the lexicalized special case, and Burnett's review takes
this family of models as the current formalization of social meaning as reasoning.

## Main definitions

* `GroundedField.indexation`: the set of personae a message meets.

## Main results

* `GroundedField.literalListener_indexation_apply_singleton`: the literal listener conditions
  the prior on the personae the message meets.
* `GroundedField.speaker_indexation_real_singleton_lt_iff`: a persona two messages meet
  produces the one whose Eckert–Montague field carries less prior mass more often.
* `GroundedField.speaker_indexation_eq_one_of_exclusive`: a persona only one message meets
  produces it with certainty.
* `GroundedField.pragmaticListener_indexation_apply_singleton_of_not_meets`: hearing a message
  rules out the personae it does not meet.

## References

* [burnett-2019]
* [burnett-2023]
* [burnett-2026]
* [henderson-mccready-2024]
-/

@[expose] public section

namespace SocialMeaning

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

variable {M P : Type*} {G : SimpleGraph P} [Fintype P] [DecidableEq P] [DecidableRel G.Adj]

instance : MeasurableSpace (Persona G) := ⊤

instance : MeasurableSingletonClass (Persona G) :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

variable [MeasurableSpace M] [Countable M] [MeasurableSingletonClass M] (F : GroundedField M G)

/-- The indexation of a message is the set of personae it meets. -/
abbrev GroundedField.indexation (m : M) : Set (Persona G) := ↑(F.personae m)

variable (prior : Measure (Persona G)) [IsFiniteMeasure prior] {m : M} {π : Persona G}

omit [IsFiniteMeasure prior] in
/-- The literal listener conditions the prior on the personae the message meets. -/
theorem GroundedField.literalListener_indexation_apply_singleton (h : π ∈ F.personae m) :
    literalListener prior F.indexation m {π} = (prior ↑(F.personae m))⁻¹ * prior {π} :=
  literalListener_apply_singleton prior F.indexation (Finset.mem_coe.2 h)

omit [IsFiniteMeasure prior] in
theorem GroundedField.literalListener_indexation_apply_singleton_of_not_mem (h : π ∉ F.personae m) :
    literalListener prior F.indexation m {π} = 0 :=
  literalListener_apply_singleton_of_notMem prior F.indexation (Finset.mem_coe.not.2 h)

theorem GroundedField.literalListener_indexation_apply_singleton_ne_zero (h : π ∈ F.personae m)
    (h0 : prior {π} ≠ 0) : literalListener prior F.indexation m {π} ≠ 0 := by
  rw [F.literalListener_indexation_apply_singleton prior h]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h0

variable [Fintype M] {α c : ℝ}

/-- A persona two messages meet produces the one whose Eckert–Montague field carries less prior
mass more often, the more informative message. -/
theorem GroundedField.speaker_indexation_real_singleton_lt_iff (hα : 0 < α)
    (h0 : prior {π} ≠ 0) {m' : M} (h : π ∈ F.personae m) (h' : π ∈ F.personae m') :
    (speaker α (λ _ => c) (literalListener prior F.indexation) π).real {m}
        < (speaker α (λ _ => c) (literalListener prior F.indexation) π).real {m'}
      ↔ prior ↑(F.personae m') < prior ↑(F.personae m) :=
  speaker_literalListener_real_singleton_lt_iff hα c prior F.indexation h0 (Finset.mem_coe.2 h)
    (Finset.mem_coe.2 h')

/-- A persona only one message meets produces it with certainty. -/
theorem GroundedField.speaker_indexation_eq_one_of_exclusive (hα : 0 < α)
    (h0 : prior {π} ≠ 0) (h : π ∈ F.personae m)
    (hother : ∀ m' ≠ m, π ∉ F.personae m') :
    speaker α (λ _ => c) (literalListener prior F.indexation) π {m} = 1 :=
  speaker_literalListener_eq_one hα _ prior F.indexation h0
    (Finset.mem_coe.2 h) λ m' hm' => Finset.mem_coe.not.2 (hother m' hm')

/-- Hearing a message rules out the personae it does not meet, once some persona it meets has
prior mass. -/
theorem GroundedField.pragmaticListener_indexation_apply_singleton_of_not_meets
    [Nonempty (Persona G)] (hα : 0 < α) {π' : Persona G}
    (h : π ∉ F.personae m) (h' : π' ∈ F.personae m) (h0 : prior {π'} ≠ 0) :
    pragmaticListener (speaker α (λ _ => c) (literalListener prior F.indexation)) prior m {π} = 0 :=
  pragmaticListener_literalListener_apply_singleton_of_notMem α (λ _ => c) prior hα F.indexation
    (Finset.mem_coe.not.2 h) (Finset.mem_coe.2 h') h0

end SocialMeaning
