import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Tense.Embedding
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Data.Examples.Klecha2016

/-!
# Klecha (2016): Modality and Embedded Temporal Operators

This file formalizes [klecha-2016]'s account of the temporal orientation of finite clauses
embedded under attitude verbs. Its novel data, (2) and (3), are attested past-under-past
sentences with *hope* and *pray* on which the embedded event follows the attitude, readings
the Upper Limit Constraint of [abusch-1997] forbids; under *think* they are absent, (6). The
account writes the constraint into the modal base pronouns of (35): `dox` returns actual
histories, which end at the evaluation time, and `cir` future histories, which begin after
it, so a modal base admits a set of orientations for the reference time of its prejacent
(`ModalBase.orientations`), a projection of the substrate's actual and future history bases
(`ModalBase.compare_mem_orientations`). Tense is relative and the present is a non-past,
(43), and sequence of tense is morphological agreement, so a past-under-past clause has an
underlying past or non-past whose readings are the orientations that its attitude's modal
bases and its tense both admit (`readings`). *Think* combines with `dox` alone and *hope* with
either, §3.1, which leaves *think* the past and simultaneous readings and gives *hope* the
future one as well (`think_readings`, `hope_readings`); the paper's rows carry the same
verdicts (`rows_readings`).

## Implementation notes

* Histories are the substrate's indices, the temporal component of a history reduced to the
  time of its index, so the definedness of τ(k|t) in (54) and (55) is membership of the
  embedded time in the base.
* The aktionsart restriction that rules out the episodic simultaneous reading of (7a) is not
  represented; the study states the orientations that tense and modal base leave open.

## References

* [klecha-2016]
* [abusch-1997]
-/

namespace Klecha2016

open Tense HistoricalAlternatives Features Semantics.Context English.Predicates.Verbal

variable {W T : Type*}

/-- The modal base pronouns of (35): `dox` returns the actual histories 𝒜_t, ending at the
evaluation time, `cir` the future histories ℱ_t, beginning after it. -/
inductive ModalBase
  | dox
  | cir
  deriving DecidableEq, Repr

namespace ModalBase

/-- The situations a modal base makes accessible from `s`, (35): the substrate's actual and
future history bases. -/
def base [LinearOrder T] :
    ModalBase → HistoricalAlternatives W T → Index W T → Set (Index W T)
  | .dox => actualHistoryBase
  | .cir => futureHistoryBase

/-- The orientations a modal base admits for the reference time of its prejacent relative to
the evaluation time, Table 1: past and present under `dox`, future under `cir`. -/
def orientations : ModalBase → Finset Ordering
  | .dox => past ∪ present
  | .cir => future

/-- (53)–(55): the time of a situation accessible from `s` bears an admitted orientation to
the evaluation time, since τ(k|t) is defined only for `t` within the history `k`. -/
theorem compare_mem_orientations [LinearOrder T] (m : ModalBase)
    (history : HistoricalAlternatives W T) {s s' : Index W T} (h : s' ∈ m.base history s) :
    compare s'.time s.time ∈ m.orientations := by
  cases m
  · exact Finset.mem_union.2 ((lt_or_eq_of_le (actualHistoryBase_time_actual history s s' h)).elim
      (λ h => Or.inl ((compare_mem_past _ _).2 h)) (λ h => Or.inr ((compare_mem_present _ _).2 h)))
  · exact (compare_mem_future _ _).2 (futureHistoryBase_time_future history s s' h)

/-- §4.2: the Upper Limit Constraint of [abusch-1997], `Tense.upperLimitConstraint`, is the
`dox` case, derived from the modal base rather than imposed on tense. -/
theorem upperLimitConstraint_of_mem_dox [LinearOrder T] (history : HistoricalAlternatives W T)
    {s s' : Index W T} (h : s' ∈ dox.base history s) : upperLimitConstraint s'.time s.time :=
  actualHistoryBase_time_actual history s s' h

/-- The derivations of §3.3 as the four cells of modal base against tense, (43): `dox` with a
past is past, `dox` with a non-past is simultaneous, (55), `cir` with a non-past is future,
(53), and `cir` with a past is empty. -/
theorem cells :
    dox.orientations ∩ past = past ∧ dox.orientations ∩ nonpast = present ∧
      cir.orientations ∩ nonpast = future ∧ cir.orientations ∩ past = ∅ := by
  decide

end ModalBase

/-! ### Attitude verbs, §3.1 -/

/-- The modal bases an attitude verb combines with, (34): a doxastic verb `dox` alone, a
preferential verb either. -/
def modalBases : Attitude → Finset ModalBase
  | .doxastic _ => {.dox}
  | .preferential _ => {.dox, .cir}

/-- The orientations open to a clause of underlying tense `τ` embedded under an attitude of
class `a`: those admitted both by one of the attitude's modal bases and by the tense. -/
def readings (a : Attitude) (τ : Finset Ordering) : Finset Ordering :=
  (modalBases a).biUnion (·.orientations ∩ τ)

/-- The takeaway of (4)–(7): a past-under-past clause, its past morphology agreement with the
matrix tense, has an underlying past or non-past, so its readings are those of
past-under-present and present-under-present together. -/
theorem readings_union (a : Attitude) (τ₁ τ₂ : Finset Ordering) :
    readings a (τ₁ ∪ τ₂) = readings a τ₁ ∪ readings a τ₂ := by
  ext o
  simp only [readings, Finset.mem_biUnion, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨m, hm, ho, h | h⟩
    · exact Or.inl ⟨m, hm, ho, h⟩
    · exact Or.inr ⟨m, hm, ho, h⟩
  · rintro (⟨m, hm, ho, h⟩ | ⟨m, hm, ho, h⟩)
    · exact ⟨m, hm, ho, Or.inl h⟩
    · exact ⟨m, hm, ho, Or.inr h⟩

theorem past_union_nonpast : past ∪ nonpast = Finset.univ := by decide

/-- (6) and (7): under *think* an embedded clause is past or simultaneous, never future, the
upper limit, and a present under a present is simultaneous only, which the eventive of (7a)
cannot be. -/
theorem think_readings : ∀ a ∈ think.attitude.toList,
    readings a Finset.univ = past ∪ present ∧ readings a nonpast = present := by
  decide +kernel

/-- (4) and (5): under *hope* every orientation is open to a past-under-past clause, the future
one through `cir` with an underlying non-past, (48)–(54); a past under a present is past. -/
theorem hope_readings : ∀ a ∈ hope.attitude.toList,
    readings a Finset.univ = Finset.univ ∧ readings a nonpast = nonpast ∧
      readings a past = past := by
  decide +kernel

/-- (45a) \**It rains tomorrow*: the covert epistemic necessity of a matrix clause is a `dox`
modal, so a matrix non-past has present reference only, §3.2. -/
theorem matrix_nonpast_present : ModalBase.dox.orientations ∩ nonpast = present := by decide

/-! ### The data, (1)–(3) -/

/-- The attitude verb of a row, from the fragment. -/
def verbOf : String → Option VerbEntry
  | "think" => some think
  | "hope" => some hope
  | "pray" => some pray
  | _ => none

/-- The orientation cells a row reports on. -/
def cells : List (String × Finset Ordering) :=
  [("past", past), ("present", present), ("future", future)]

/-- The rows agree with the analysis: an orientation a row reports available under its verb
lies among the readings of a past-under-past clause under that verb and one reported
unavailable does not, so (2) and (3) are the attested future readings under *hope* and
*pray* and (1) the upper limit under *think*. -/
theorem rows_readings :
    ∀ e ∈ Examples.all, ∀ v ∈ (e.feature? "verb" >>= verbOf).toList, ∀ a ∈ v.attitude.toList,
      ∀ c ∈ cells, ∀ j ∈ (e.feature? c.1).toList,
        (j = "available" ↔ c.2 ⊆ readings a Finset.univ) := by
  decide +kernel

end Klecha2016
