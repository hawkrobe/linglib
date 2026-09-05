import Linglib.Semantics.Aspect.Basic

/-!
# Instantiation of sorted properties

A property of eventualities is instantiated at a reference interval by the temporal relation
its sort selects: the runtime of an event is included in the interval, the runtime of a state
overlaps it ([kamp-rohrer-1983], [partee-1984], [kamp-reyle-1993]), and a property of times
applies to the interval. Reference intervals are `Interval (WithTop T)`, so that an interval
may run to the end of time and the null interval is `⊥`. On a bounded interval the eventive
clause is the perfective viewpoint `PRFV` of [klein-1994], and the imperfective `IMPF` entails
the stative clause.

## Main definitions

* `Aspect.SortedProperty` — a property of events, of states, or of times.
* `Aspect.At` — the instantiation relation `AT(t, w, P)`.

## Main results

* `Aspect.At.mono` — instantiation of an eventuality is monotone in the interval.
* `Aspect.at_Ici_eventive_iff`, `Aspect.at_Ici_stative_iff` — instantiation at a ray: the event
  starts no earlier, the state persists at or past.
* `Aspect.at_eventive_withTop_iff_prfv` — on a bounded interval, eventive instantiation is
  `PRFV`.

## References

* [H. Kamp and C. Rohrer, *Tense in Texts* (1983)][kamp-rohrer-1983]
* [B. Partee, *Nominal and Temporal Anaphora* (1984)][partee-1984]
* [H. Kamp and U. Reyle, *From Discourse to Logic* (1993)][kamp-reyle-1993]
* [W. Klein, *Time in Language* (1994)][klein-1994]
-/

namespace Aspect

variable {W T : Type*} [LinearOrder T]

/-- A property sorted by what it is a property of: events, states, or times. -/
inductive SortedProperty (W T : Type*) [LinearOrder T]
  | eventive (P : W → Event T → Prop)
  | stative (P : W → Event T → Prop)
  | temporal (P : W → Interval (WithTop T) → Prop)

/-- A property of eventualities rather than of times. -/
def SortedProperty.IsEventuality : SortedProperty W T → Prop
  | .temporal _ => False
  | _ => True

/-- `At t w Q`: the property `Q` is instantiated in `w` at the interval `t`, by inclusion of the
runtime for events, overlap for states, and application for properties of times. -/
def At (t : Interval (WithTop T)) (w : W) : SortedProperty W T → Prop
  | .eventive P => ∃ e, P w e ∧ ↑e.τ.withTop ≤ t
  | .stative P => ∃ e, P w e ∧ ¬ Disjoint (↑e.τ.withTop) t
  | .temporal P => P w t

variable {P : W → Event T → Prop} {Q : SortedProperty W T} {r r' : Interval (WithTop T)} {w : W}

/-- An eventuality instantiated at an interval gives the interval a time. -/
theorem exists_mem_of_at (hQ : Q.IsEventuality) (h : At r w Q) : ∃ x, x ∈ r := by
  cases Q with
  | eventive R => obtain ⟨e, -, hle⟩ := h; exact ⟨_, (Interval.coe_le_iff.1 hle).1⟩
  | stative R =>
    obtain ⟨e, -, hd⟩ := h
    obtain ⟨x, -, hx⟩ := Interval.not_disjoint_iff.1 hd
    exact ⟨x, hx⟩
  | temporal R => exact hQ.elim

/-- Nothing is instantiated at the null interval but a property of times. -/
theorem not_at_bot (hQ : Q.IsEventuality) : ¬ At ⊥ w Q :=
  λ h => let ⟨_, hx⟩ := exists_mem_of_at hQ h; Interval.notMem_bot hx

/-- Instantiation of an eventuality is monotone in the interval. -/
theorem At.mono (hQ : Q.IsEventuality) (h : r ≤ r') (hr : At r w Q) : At r' w Q := by
  cases Q with
  | eventive R => obtain ⟨e, he, hle⟩ := hr; exact ⟨e, he, le_trans hle h⟩
  | stative R =>
    obtain ⟨e, he, hd⟩ := hr
    exact ⟨e, he, λ hd' => hd (hd'.mono_right h)⟩
  | temporal R => exact hQ.elim

/-- An event is instantiated at the ray from `t` when it starts no earlier than `t`. -/
@[simp] theorem at_Ici_eventive_iff {t : T} :
    At (Interval.Ici t) w (.eventive P) ↔ ∃ e, P w e ∧ t ≤ e.τ.fst := by
  simp [At, Interval.withTop_le_Ici]

/-- A state is instantiated at the ray from `t` when it persists at or past `t`. -/
@[simp] theorem at_Ici_stative_iff {t : T} :
    At (Interval.Ici t) w (.stative P) ↔ ∃ e, P w e ∧ t ≤ e.τ.snd := by
  simp [At, Interval.not_disjoint_withTop_Ici]

/-- On a bounded interval, eventive instantiation is the perfective viewpoint. -/
theorem at_eventive_withTop_iff_prfv {i : NonemptyInterval T} :
    At ↑i.withTop w (.eventive P) ↔ PRFV P w i := by
  simp [At, PRFV, and_comm]

/-- The imperfective viewpoint entails stative instantiation: proper inclusion of the interval
in the runtime gives overlap. -/
theorem at_stative_withTop_of_impf {i : NonemptyInterval T} (h : IMPF P w i) :
    At ↑i.withTop w (.stative P) := by
  obtain ⟨e, hlt, he⟩ := h
  have hle := NonemptyInterval.le_def.1 hlt.le
  refine ⟨e, he, Interval.not_disjoint_iff.2 ⟨↑i.fst, ?_, ?_⟩⟩
  · exact NonemptyInterval.mem_withTop.2 ⟨WithTop.coe_le_coe.2 hle.1,
      WithTop.coe_le_coe.2 (le_trans i.fst_le_snd hle.2)⟩
  · exact NonemptyInterval.mem_withTop.2 ⟨le_rfl, WithTop.coe_le_coe.2 i.fst_le_snd⟩

end Aspect
