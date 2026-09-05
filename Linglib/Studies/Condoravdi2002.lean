import Mathlib.Tactic.DeriveFintype
import Linglib.Data.Examples.Condoravdi2002
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Modality.ModalTypes

/-!
# Condoravdi 2002: Temporal Interpretation of Modals

Non-root modals make one contribution to temporal interpretation: they expand the time of
evaluation forward to the interval running from the perspective time to the end of time, and
instantiate the property in their scope in the worlds of a modal base. Modals for the present,
*may win*, and modals for the past, *may have won*, share this meaning; the second decomposes
into the modal over the perfect, which shifts evaluation to an interval before its reference
time, so that the past orientation is the perfect's. The adverbs *already*, *yet* and *still*
show the decomposition: they select against properties of events and are fine with a modal
plus *have* even when the verb is eventive, because the perfect turns the property of events
into a property of times. Whether the modal shifts forward is then a matter of the sort of its
complement, obligatory with events, which must fall within the forward interval, optional with
states, which need only overlap it.

Modals for the past are ambiguous. With the modal over the perfect the perspective is the time
of utterance and the orientation past, the epistemic reading of *he may have won*; with the
perfect over the modal the perspective is a past time and the orientation that time's future,
the counterfactual reading of *at that point he might still have won*. The fourth cell of the
table, past perspective with past orientation, has no expression. The frame adverbials fall
out: *yesterday* restricts the reference interval, which for a modal for the present is the
forward interval, so the intersection is null and *he may win yesterday* can never be true,
while for the modal over the perfect the reference interval precedes the present, excluding
*tomorrow* and *now*; the counterfactual scoping has the forward interval of a past time and
admits all three.

Which modal base a modal takes follows from the structure of possibilities. Historical
alternatives at a time are the worlds identical up to it, an equivalence that coarsens as time
goes back, so the live options of a world shrink as time advances: a possibility at the
present was a possibility at every earlier time. That is why *still*, presupposing a prior
positive phase, can scope over a possibility modal and *already*, presupposing a prior negative
phase, cannot. The metaphysical modal base at a time is the world's equivalence class; a
context may assign it to a possibility modal only under the diversity condition, that the base
contain worlds disagreeing on the property, and a common ground that settles the property fails
diversity. Instantiation in the past of the perspective, the modal over the perfect, or at the
present, a stative with *now*, is settled in every common ground, leaving those readings
epistemic; a future instantiation is settled only when the context says so, as in *it has been
decided who he will meet with*. The counterfactual reading is the same possibility modal at a
past perspective, whose base includes the present one; when no present alternative verifies
the possibility, the world that does lies outside the common ground, whence the implication
that the possibility went unrealized.

The semantics is stated over the paper's own interval type `Ref`, and `AT` dispatches on the
sort of the property, with `PRES`, `PERF`, `MAY`, `WOLL`, the phase adverbs and the frame
adverbials as operators on properties. `pres_may_eventive_iff` through
`pres_perf_may_eventive_iff` are the derivations of the three readings, `frame_modal_past` and
`frame_modalPerf_nonpast` the two deviant adverbial patterns, `zones_iff` the satisfiable and
unsatisfiable cells of scoping against period in a model, `may_antitone` the shrinking of
possibilities behind *still* and *already*, `settled_perf` and `settled_present` the
settledness of non-future instantiation, `not_diverse_of_settled` the exclusion of the
metaphysical base, and `counterfactual_outside_cg` the counterfactual implication. The paper's
rows are checked by `adverb_rows`, `reading_rows`, `sortal_rows`, `phase_rows` and
`german_rows`.

## Implementation notes

* An interval of the paper is a closed interval of `WithTop T`, so the forward interval `[t, _)`
  is `[t, ⊤]` and the null interval is the lattice bottom. The paper's `now` is an interval,
  albeit a short one, and is taken as a point; a modal base is indexed by the time at which the
  reference interval starts. Both are the formalizer's choices, made together: the paper's
  `MB(w, t)` takes an interval and its `w ≃_t w'` a point, and indexing by the end of the
  interval is the other way to reconcile them.
* Settledness of past and present instantiation is the paper's reading of historical
  equivalence as identity of the past; the substrate relation is abstract, so it enters as the
  hypothesis `FixesPast`, from which the two settledness theorems follow. The counterfactual
  implication likewise rests on the paper's footnote assumption, `PastAlternativesOutside`.
* The sortal restriction of the phase adverbs is partiality, an `Option`-valued operator; the
  prior-phase half of their Löbner presuppositions is stated separately, as the paper does.
* The inclusion and overlap relations of `AT` are the paper's, after Kamp and Rohrer and
  Partee; the substrate's viewpoint operators, under Klein's names, coincide with them on
  bounded intervals, `AT_eventive_ofInterval_iff` and `AT_stative_of_IMPF`. `AT` takes its
  arguments in the paper's order, and `PRES now Q` is the proposition the settledness
  theorems consume.

## TODO

* The embedded modals of *Mary believed that John may get sick*, whose perspective is the
  attitude's internal now, are informal in the paper and absent here.
* *He has still won* is excluded by the paper as well known rather than derived, and the
  German *noch* pattern that rests on it is a row, not a theorem.
* `WOLL` is stated but unconsumed: the paper gives no data for *will* and *would*.

## References

* [C. Condoravdi, *Temporal Interpretation of Modals* (2002)][condoravdi-2002]
* [F. Mondadori, *Remarks on Tense and Mood: The Perfect Future* (1978)][mondadori-1978]
* [D. Abusch, *Sequence of Tense and Temporal De Re* (1997)][abusch-1997]
* [D. Abusch, *Generalizing Tense Semantics for Future Contexts* (1998)][abusch-1998]
* [M. Enç, *Tense and Modality* (1996)][enc-1996]
* [J. Groenendijk and M. Stokhof, *Modality and Conversational Information*
  (1975)][groenendijk-stokhof-1975]
* [H. Kamp and C. Rohrer, *Tense in Texts* (1983)][kamp-rohrer-1983]
* [H. Kamp and U. Reyle, *From Discourse to Logic* (1993)][kamp-reyle-1993]
* [W. Klein, *Time in Language* (1994)][klein-1994]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [D. Lewis, *Counterfactual Dependence and Time's Arrow* (1979)][lewis-1979-time-arrow]
* [S. Löbner, *German schon, erst, noch: An Integrated Analysis* (1989)][lobner-1989]
* [B. Partee, *Nominal and Temporal Anaphora* (1984)][partee-1984]
* [R. Thomason, *Combinations of Tense and Modality* (1984)][thomason-1984]
-/

namespace Condoravdi2002

open Aspect HistoricalAlternatives Data.Examples
open Features (Dynamicity)
open Modality (TemporalPerspective TemporalOrientation)

variable {W T : Type*} [LinearOrder T]

/-! ### Intervals -/

/-- The paper's intervals: closed intervals of times, possibly running to the end of time, and
the null interval. -/
abbrev Ref (T : Type*) [LE T] := Interval (WithTop T)

namespace Ref

/-- A bounded interval of times, as a nonempty interval of `WithTop T`. -/
def lift (i : NonemptyInterval T) : NonemptyInterval (WithTop T) :=
  i.map ⟨WithTop.some, WithTop.coe_mono⟩

/-- A bounded interval of times. -/
def ofInterval (i : NonemptyInterval T) : Ref T := ↑(lift i)

/-- The point `t`. The paper's `now` is an interval, albeit a short one, taken here as a
point. -/
def point (t : T) : Ref T := Interval.pure ↑t

/-- `[t, _)`: from `t` to the end of time. -/
def ray (t : T) : Ref T := ↑(⟨(↑t, ⊤), le_top⟩ : NonemptyInterval (WithTop T))

/-- `r` precedes `r'`: every time of `r` is before every time of `r'`. -/
def Precedes (r r' : Ref T) : Prop := ∀ x ∈ r, ∀ y ∈ r', x < y

/-- `r` and `r'` share a time. -/
def Overlaps (r r' : Ref T) : Prop := ∃ x, x ∈ r ∧ x ∈ r'

/-- `r` starts at the time `t`. -/
def StartsAt (r : Ref T) (t : T) : Prop :=
  ∃ i : NonemptyInterval (WithTop T), r = ↑i ∧ i.fst = ↑t

variable {i : NonemptyInterval T} {r r' : Ref T} {t t' : T} {x : WithTop T}

@[simp] theorem mem_ofInterval : x ∈ ofInterval i ↔ ↑i.fst ≤ x ∧ x ≤ ↑i.snd := by
  simp [ofInterval, lift, NonemptyInterval.mem_def]

@[simp] theorem mem_point : x ∈ point t ↔ x = ↑t := Interval.mem_pure

@[simp] theorem mem_ray : x ∈ ray t ↔ ↑t ≤ x := by
  simp [ray, NonemptyInterval.mem_def]

@[simp] theorem notMem_bot : x ∉ (⊥ : Ref T) := by
  simp [← SetLike.mem_coe]

@[simp] theorem mem_inf : x ∈ r ⊓ r' ↔ x ∈ r ∧ x ∈ r' := by
  simp [← SetLike.mem_coe]

theorem mem_of_mem_of_le (h : r ≤ r') (hx : x ∈ r) : x ∈ r' :=
  Interval.coe_subset_coe.2 h hx

theorem point_le_iff : point t ≤ r ↔ ↑t ∈ r := by
  rw [← Interval.coe_subset_coe, point, Interval.coe_pure, Set.singleton_subset_iff,
    SetLike.mem_coe]

theorem ofInterval_le_iff : ofInterval i ≤ r ↔ ↑i.fst ∈ r ∧ ↑i.snd ∈ r := by
  induction r using Interval.recBotCoe with
  | bot => exact iff_of_false (λ h => WithBot.coe_ne_bot (le_bot_iff.1 h)) (λ h => notMem_bot h.1)
  | coe j =>
    have hi := WithTop.coe_le_coe.2 i.fst_le_snd
    refine ⟨λ h => ?_, λ ⟨h₁, h₂⟩ => WithBot.coe_le_coe.2 (NonemptyInterval.le_def.2
      ⟨(NonemptyInterval.mem_def.1 h₁).1, (NonemptyInterval.mem_def.1 h₂).2⟩)⟩
    obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 (WithBot.coe_le_coe.1 h)
    exact ⟨NonemptyInterval.mem_def.2 ⟨h₁, le_trans hi h₂⟩,
      NonemptyInterval.mem_def.2 ⟨le_trans h₁ hi, h₂⟩⟩

theorem ray_le_ray (h : t' ≤ t) : ray t ≤ ray t' :=
  WithBot.coe_le_coe.2 (NonemptyInterval.le_def.2 ⟨WithTop.coe_le_coe.2 h, le_rfl⟩)

theorem startsAt_point : (point t).StartsAt t := ⟨_, rfl, rfl⟩

/-- The start of an interval is one of its times. -/
theorem mem_of_startsAt (h : r.StartsAt t) : ↑t ∈ r := by
  obtain ⟨j, rfl, hj⟩ := h
  exact NonemptyInterval.mem_def.2 ⟨hj.le, hj ▸ j.fst_le_snd⟩

theorem precedes_point_point : (point t').Precedes (point t) ↔ t' < t := by
  simp [Precedes]

theorem precedes_ofInterval_ray : (ofInterval i).Precedes (ray t) ↔ i.snd < t := by
  refine ⟨λ h => WithTop.coe_lt_coe.1 (h _ (by simp [i.fst_le_snd]) _ (mem_ray.2 le_rfl)),
    λ h x hx y hy => ?_⟩
  rw [mem_ofInterval] at hx
  exact lt_of_le_of_lt hx.2 (lt_of_lt_of_le (WithTop.coe_lt_coe.2 h) (mem_ray.1 hy))

end Ref

/-! ### Properties and the AT relation -/

/-- A property of the paper's three sorts: of events, of states, or of times. -/
inductive Property (W T : Type*) [LinearOrder T]
  | eventive (P : W → Event T → Prop)
  | stative (P : W → Event T → Prop)
  | temporal (P : W → Ref T → Prop)

/-- A property of eventualities rather than of times. -/
def Property.IsEventuality : Property W T → Prop
  | .temporal _ => False
  | _ => True

/-- The AT relation: property `P` is instantiated in `w` at `t`, by inclusion of the runtime for
events, overlap for states, and application for properties of times. -/
def AT (t : Ref T) (w : W) : Property W T → Prop
  | .eventive P => ∃ e, P w e ∧ Ref.ofInterval e.τ ≤ t
  | .stative P => ∃ e, P w e ∧ (Ref.ofInterval e.τ).Overlaps t
  | .temporal P => P w t

variable {P : W → Event T → Prop} {Q Q' : Property W T} {r r' : Ref T} {t t' : T} {w : W}

/-- An eventuality instantiated at an interval gives the interval a time. -/
theorem exists_mem_of_AT (hQ : Q.IsEventuality) (h : AT r w Q) : ∃ x, x ∈ r := by
  cases Q with
  | eventive R => obtain ⟨e, -, hle⟩ := h; exact ⟨_, (Ref.ofInterval_le_iff.1 hle).1⟩
  | stative R => obtain ⟨e, -, x, -, hx⟩ := h; exact ⟨x, hx⟩
  | temporal R => exact hQ.elim

/-- Nothing is instantiated at the null interval but a property of times. -/
theorem not_AT_bot (hQ : Q.IsEventuality) : ¬ AT ⊥ w Q :=
  λ h => let ⟨_, hx⟩ := exists_mem_of_AT hQ h; Ref.notMem_bot hx

/-- Instantiation of an eventuality is monotone in the interval. -/
theorem AT_mono (hQ : Q.IsEventuality) (h : r ≤ r') (hr : AT r w Q) : AT r' w Q := by
  cases Q with
  | eventive R => obtain ⟨e, he, hle⟩ := hr; exact ⟨e, he, le_trans hle h⟩
  | stative R =>
    obtain ⟨e, he, x, hx, hx'⟩ := hr; exact ⟨e, he, x, hx, Ref.mem_of_mem_of_le h hx'⟩
  | temporal R => exact hQ.elim

/-- On a bounded interval, eventive instantiation is the substrate's perfective viewpoint. -/
theorem AT_eventive_ofInterval_iff {i : NonemptyInterval T} :
    AT (Ref.ofInterval i) w (.eventive P) ↔ PRFV P w i := by
  simp only [AT, PRFV, Ref.ofInterval_le_iff, Ref.mem_ofInterval, NonemptyInterval.le_def,
    WithTop.coe_le_coe]
  constructor
  · rintro ⟨e, he, ⟨h₁, -⟩, ⟨-, h₂⟩⟩; exact ⟨e, ⟨h₁, h₂⟩, he⟩
  · rintro ⟨e, ⟨h₁, h₂⟩, he⟩
    exact ⟨e, he, ⟨h₁, le_trans e.τ.fst_le_snd h₂⟩, ⟨le_trans h₁ e.τ.fst_le_snd, h₂⟩⟩

/-- The substrate's imperfective viewpoint entails stative instantiation: proper inclusion of
the interval in the runtime gives overlap. -/
theorem AT_stative_of_IMPF {i : NonemptyInterval T} (h : IMPF P w i) :
    AT (Ref.ofInterval i) w (.stative P) := by
  obtain ⟨e, hlt, he⟩ := h
  have hle := NonemptyInterval.le_def.1 hlt.le
  exact ⟨e, he, ↑i.fst, Ref.mem_ofInterval.2 ⟨WithTop.coe_le_coe.2 hle.1,
      WithTop.coe_le_coe.2 (le_trans i.fst_le_snd hle.2)⟩,
    Ref.mem_ofInterval.2 ⟨le_rfl, WithTop.coe_le_coe.2 i.fst_le_snd⟩⟩

/-! ### The operators -/

/-- Present tense: instantiation at the time of utterance. -/
def PRES (now : T) (Q : Property W T) (w : W) : Prop := AT (Ref.point now) w Q

/-- The perfect: instantiation at some interval preceding the reference interval. -/
def PERF (Q : Property W T) : Property W T :=
  .temporal λ w t => ∃ t' : NonemptyInterval (WithTop T), Ref.Precedes ↑t' t ∧ AT ↑t' w Q

/-- MAY and MIGHT: instantiation, in some world of the modal base at the start of the
reference interval, throughout the interval expanded forward to the end of time. -/
def MAY (MB : W → T → Set W) (Q : Property W T) : Property W T :=
  .temporal λ w t => ∃ t₀, t.StartsAt t₀ ∧ ∃ w' ∈ MB w t₀, AT (Ref.ray t₀) w' Q

/-- WOLL, the untensed modal of *will* and *would*: instantiation in every world of the modal
base at the start of the reference interval, throughout the forward interval. -/
def WOLL (MB : W → T → Set W) (Q : Property W T) : Property W T :=
  .temporal λ w t => ∃ t₀, t.StartsAt t₀ ∧ ∀ w' ∈ MB w t₀, AT (Ref.ray t₀) w' Q

/-- A frame adverbial such as *yesterday*: instantiation within the intersection of the
reference interval with the period named, undefined on properties of times. -/
def frame (period : Ref T) : Property W T → Option (Property W T)
  | .temporal _ => none
  | Q => some (.temporal λ w t => AT (t ⊓ period) w Q)

/-- *Already*, *yet* and *still*: the identity on properties of states and of times, undefined
on properties of events. -/
def phase : Property W T → Option (Property W T)
  | .eventive _ => none
  | Q => some Q

/-- A frame adverbial applies to a property of eventualities. -/
theorem isEventuality_of_frame {period : Ref T} (hf : frame period Q = some Q') :
    Q.IsEventuality := by
  cases Q <;> trivial

/-- Instantiation of the framed property is instantiation within the period. -/
theorem AT_of_frame {period : Ref T} (hf : frame period Q = some Q') (h : AT r w Q') :
    AT (r ⊓ period) w Q := by
  cases Q <;> cases hf <;> exact h

/-! ### The three readings -/

variable {MB : W → T → Set W} {now : T}

/-- A modal for the present with an eventive predicate, *he might run*: some world of the base
at the present has the event starting no earlier than the present. Future orientation is
obligatory. -/
theorem pres_may_eventive_iff :
    PRES now (MAY MB (.eventive P)) w ↔ ∃ w' ∈ MB w now, ∃ e, P w' e ∧ now ≤ e.τ.fst := by
  simp only [PRES, MAY, AT, Ref.ofInterval_le_iff, Ref.mem_ray, WithTop.coe_le_coe]
  constructor
  · rintro ⟨t₀, ht₀, w', hw', e, he, h, -⟩
    obtain rfl : t₀ = now := by simpa using Ref.mem_of_startsAt ht₀
    exact ⟨w', hw', e, he, h⟩
  · rintro ⟨w', hw', e, he, h⟩
    exact ⟨now, Ref.startsAt_point, w', hw', e, he, h, le_trans h e.τ.fst_le_snd⟩

/-- A modal for the present with a stative predicate, *he might be here*: some world of the base
at the present has the state persisting at or past the present. The state may have started
earlier, so future orientation is optional. -/
theorem pres_may_stative_iff :
    PRES now (MAY MB (.stative P)) w ↔ ∃ w' ∈ MB w now, ∃ e, P w' e ∧ now ≤ e.τ.snd := by
  simp only [PRES, MAY, AT, Ref.Overlaps, Ref.mem_ofInterval, Ref.mem_ray]
  constructor
  · rintro ⟨t₀, ht₀, w', hw', e, he, x, ⟨-, hx⟩, hx'⟩
    obtain rfl : t₀ = now := by simpa using Ref.mem_of_startsAt ht₀
    exact ⟨w', hw', e, he, WithTop.coe_le_coe.1 (le_trans hx' hx)⟩
  · rintro ⟨w', hw', e, he, h⟩
    exact ⟨now, Ref.startsAt_point, w', hw', e, he, ↑e.τ.snd,
      ⟨WithTop.coe_le_coe.2 e.τ.fst_le_snd, le_rfl⟩, WithTop.coe_le_coe.2 h⟩

/-- The modal over the perfect, *he may have won*: some world of the base at the present has
the event ending before the present. Present perspective, past orientation: the epistemic
reading. -/
theorem pres_may_perf_eventive_iff :
    PRES now (MAY MB (PERF (.eventive P))) w ↔
      ∃ w' ∈ MB w now, ∃ e, P w' e ∧ e.τ.snd < now := by
  simp only [PRES, MAY, PERF, AT]
  constructor
  · rintro ⟨t₀, ht₀, w', hw', t', ht', e, he, hle⟩
    obtain rfl : t₀ = now := by simpa using Ref.mem_of_startsAt ht₀
    refine ⟨w', hw', e, he, WithTop.coe_lt_coe.1 (ht' _ ?_ _ (Ref.mem_ray.2 le_rfl))⟩
    exact (Ref.ofInterval_le_iff.1 hle).2
  · rintro ⟨w', hw', e, he, h⟩
    exact ⟨now, Ref.startsAt_point, w', hw', Ref.lift e.τ,
      Ref.precedes_ofInterval_ray.2 h, e, he, le_rfl⟩

/-- The perfect over the modal, *he might have won*: some past time has, in some world of the
base at that time, the event starting no earlier than it. Past perspective, future
orientation: the counterfactual reading, Mondadori's future in the past. -/
theorem pres_perf_may_eventive_iff :
    PRES now (PERF (MAY MB (.eventive P))) w ↔
      ∃ t' < now, ∃ w' ∈ MB w t', ∃ e, P w' e ∧ t' ≤ e.τ.fst := by
  simp only [PRES, PERF, MAY, AT, Ref.ofInterval_le_iff, Ref.mem_ray, WithTop.coe_le_coe]
  constructor
  · rintro ⟨t'', ht'', t', ht', w', hw', e, he, h, -⟩
    refine ⟨t', ?_, w', hw', e, he, h⟩
    exact WithTop.coe_lt_coe.1 (ht'' _ (Ref.mem_of_startsAt ht') _ (Ref.mem_point.2 rfl))
  · rintro ⟨t', ht', w', hw', e, he, h⟩
    exact ⟨Ref.lift (NonemptyInterval.pure t'), Ref.precedes_point_point.2 ht', t',
      Ref.startsAt_point, w', hw', e, he, h, le_trans h e.τ.fst_le_snd⟩

/-! ### Frame adverbials -/

/-- A modal for the present rejects a period wholly before the present, *he may win
yesterday*: the forward interval meets it in the null interval. -/
theorem frame_modal_past {period : Ref T} (hp : period.Precedes (Ref.ray now))
    (hf : frame period Q = some Q') : ¬ PRES now (MAY MB Q') w := by
  rintro ⟨t₀, ht₀, w', -, h⟩
  obtain rfl : t₀ = now := by simpa using Ref.mem_of_startsAt ht₀
  obtain ⟨x, hx⟩ := exists_mem_of_AT (isEventuality_of_frame hf) (AT_of_frame hf h)
  simp only [Ref.mem_inf] at hx
  exact lt_irrefl _ (hp _ hx.2 _ hx.1)

/-- The modal over the perfect rejects a period lying at or after the present, *he must have
been available next month* and *it must have been raining now*: the interval the perfect
supplies precedes the present, and so the period. -/
theorem frame_modalPerf_nonpast {period : Ref T} (hp : ∀ y ∈ period, ↑now ≤ y)
    (hf : frame period Q = some Q') : ¬ PRES now (MAY MB (PERF Q')) w := by
  rintro ⟨t₀, ht₀, w', -, t', ht', h⟩
  obtain rfl : t₀ = now := by simpa using Ref.mem_of_startsAt ht₀
  obtain ⟨x, hx⟩ := exists_mem_of_AT (isEventuality_of_frame hf) (AT_of_frame hf h)
  simp only [Ref.mem_inf] at hx
  exact lt_irrefl _ (lt_of_lt_of_le (ht' _ hx.1 _ (Ref.mem_ray.2 le_rfl)) (hp _ hx.2))

/-! ### Live options shrink -/

/-- A possibility at a time was a possibility at every earlier time: the metaphysical base
widens backward and the forward interval lengthens. This is why *still*, whose presupposition
is a prior positive phase, scopes over a possibility modal, *he may still win*, and *already*,
whose presupposition is a prior negative phase, cannot, *he may already win*; read backward, it
is why *he may win this game* is false once he has lost. -/
theorem may_antitone {history : HistoricalAlternatives W T}
    (hBC : history.backwardsClosed) (hQ : Q.IsEventuality) :
    Antitone λ t : T => AT (Ref.point t) w (MAY (metaphysicalBase history) Q) := by
  rintro t' t h ⟨t₀, ht₀, w', hw', hat⟩
  obtain rfl : t₀ = t := by simpa using Ref.mem_of_startsAt ht₀
  exact ⟨t', Ref.startsAt_point, w', metaphysicalBase_antitone hBC w h hw',
    AT_mono hQ (Ref.ray_le_ray h) hat⟩

/-- The prior-phase half of Löbner's presupposition of *already*: a prior negative phase. -/
def AlreadyPresup (Q : Property W T) (w : W) (now : T) : Prop :=
  ∃ t' < now, ¬ AT (Ref.point t') w Q

/-- The prior-phase half of Löbner's presupposition of *still*: a prior positive phase. -/
def StillPresup (Q : Property W T) (w : W) (now : T) : Prop :=
  ∃ t' < now, AT (Ref.point t') w Q

/-- *He may already win*: the presupposition of *already* over a metaphysical possibility
contradicts its assertion. -/
theorem not_already_may {history : HistoricalAlternatives W T}
    (hBC : history.backwardsClosed) (hQ : Q.IsEventuality)
    (h : PRES now (MAY (metaphysicalBase history) Q) w) :
    ¬ AlreadyPresup (MAY (metaphysicalBase history) Q) w now :=
  λ ⟨_, ht', hn⟩ => hn (may_antitone hBC hQ ht'.le h)

/-- *He may still win*: the presupposition of *still* over a metaphysical possibility is not
merely consistent with the shrinking of possibilities, as the paper puts it, but entailed by
the assertion, given any earlier time. -/
theorem still_may {history : HistoricalAlternatives W T}
    (hBC : history.backwardsClosed) (hQ : Q.IsEventuality)
    (h : PRES now (MAY (metaphysicalBase history) Q) w) (ht' : t' < now) :
    StillPresup (MAY (metaphysicalBase history) Q) w now :=
  ⟨t', ht', may_antitone hBC hQ ht'.le h⟩

/-! ### Settledness and the diversity condition -/

/-- The history relation fixes the instantiation of `Q` at every interval up to its time:
worlds identical up to `t` agree on `Q` there. -/
def FixesPast (history : HistoricalAlternatives W T) (Q : Property W T) : Prop :=
  ∀ t w w', histEquiv history t w w' → ∀ r : Ref T, (∀ x ∈ r, x ≤ ↑t) → (AT r w Q ↔ AT r w' Q)

/-- Instantiation in the past of the perspective, the modal over the perfect, is settled in
every common ground. -/
theorem settled_perf {history : HistoricalAlternatives W T} (h : FixesPast history Q)
    (cg : Set W) (t : T) : settled history cg t (λ w => AT (Ref.ray t) w (PERF Q)) := by
  intro w _ w' hw'
  refine exists_congr λ r => and_congr_right λ hr => h t w w' hw' r λ x hx => ?_
  exact (hr x hx _ (Ref.mem_ray.2 le_rfl)).le

/-- Instantiation at the present, a stative with *now*, is settled in every common ground: the
forward interval restricted to the present is the present. -/
theorem settled_present {history : HistoricalAlternatives W T} (h : FixesPast history Q)
    (hf : frame (Ref.point t) Q = some Q') (cg : Set W) :
    settled history cg t (λ w => AT (Ref.ray t) w Q') := by
  intro w _ w' hw'
  cases Q <;> cases hf
  all_goals exact h t w w' hw' _ λ x hx => (Ref.mem_point.1 (Ref.mem_inf.1 hx).2).le

omit [LinearOrder T] in
/-- A common ground that settles a property fails the diversity condition for the metaphysical
base, so a context cannot assign that base to a possibility modal applying to it: the modal
over the perfect and the present-referring stative are epistemic. -/
theorem not_diverse_of_settled {history : HistoricalAlternatives W T} {cg : Set W} {t : T}
    {R : W → Prop} (h : settled history cg t R) : ¬ diverse (metaphysicalBase history) cg t R :=
  settled_not_diverse history _ cg t R (λ _ _ _ hw => hw) h

/-! ### The counterfactual implication -/

/-- The paper's footnote assumption: a past alternative of a common-ground world that is no
alternative at the time of utterance lies outside the common ground. -/
def PastAlternativesOutside (history : HistoricalAlternatives W T) (cg : Set W) (t₀ : T) :
    Prop :=
  ∀ w ∈ cg, ∀ t' ≤ t₀, ∀ w' ∈ metaphysicalBase history w t',
    w' ∉ metaphysicalBase history w t₀ → w' ∉ cg

/-- The counterfactual implication: when no present alternative verifies the past
possibility, the world that does lies outside the common ground, which is what the speaker's
backtracking to a past perspective signals. -/
theorem counterfactual_outside_cg {history : HistoricalAlternatives W T} {cg : Set W} {t₀ : T}
    (h : PastAlternativesOutside history cg t₀) (hw : w ∈ cg)
    (hcf : PRES t₀ (PERF (MAY (metaphysicalBase history) Q)) w)
    (hnow : ∀ t' < t₀, ∀ w' ∈ metaphysicalBase history w t₀, ¬ AT (Ref.ray t') w' Q) :
    ∃ t' < t₀, ∃ w' ∉ cg, w' ∈ metaphysicalBase history w t' ∧ AT (Ref.ray t') w' Q := by
  obtain ⟨t'', ht'', t', ht', w', hw', hat⟩ := hcf
  have hlt : t' < t₀ :=
    WithTop.coe_lt_coe.1 (ht'' _ (Ref.mem_of_startsAt ht') _ (Ref.mem_point.2 rfl))
  exact ⟨t', hlt, w', h w hw t' hlt.le w' hw' (λ hmem => hnow t' hlt w' hmem hat), hw', hat⟩

/-! ### Perspective and orientation -/

/-- The scopings of a possibility modal with respect to the perfect. -/
inductive Scope
  /-- The modal alone: *he may win*. -/
  | modal
  /-- The modal over the perfect: *he may have won*, the epistemic reading. -/
  | modalPerf
  /-- The perfect over the modal: *he might have won*, the counterfactual reading. -/
  | perfModal
  deriving DecidableEq, Fintype

/-- The scoping as an operator on the property under the modal. -/
def Scope.lf (MB : W → T → Set W) : Scope → Property W T → Property W T
  | .modal, Q => MAY MB Q
  | .modalPerf, Q => MAY MB (PERF Q)
  | .perfModal, Q => PERF (MAY MB Q)

/-- The time at which the modal base is evaluated, read off the three readings: the present
in `pres_may_eventive_iff` and `pres_may_perf_eventive_iff`, the past time the perfect
supplies in `pres_perf_may_eventive_iff`. -/
def Scope.perspective : Scope → TemporalPerspective
  | .modal | .modalPerf => .present
  | .perfModal => .past

/-- The direction of the instantiation from the perspective, read off the three readings: the
event starts no earlier than the perspective, or ends before it. -/
def Scope.orientation : Scope → TemporalOrientation
  | .modal | .perfModal => .future
  | .modalPerf => .past

/-- The empty cell of the paper's table: a past perspective comes with a future orientation. -/
theorem Scope.orientation_of_perspective_past :
    ∀ s : Scope, s.perspective = .past → s.orientation = .future := by
  decide

/-! ### A model -/

/-- A one-world model over integer days, with a winning on day `d`. -/
def winOn (d : ℤ) : Unit → Event ℤ → Prop := λ _ e => e.τ = NonemptyInterval.pure d

/-- The unrestricted modal base. -/
def anyWorld : Unit → ℤ → Set Unit := λ _ _ => Set.univ

/-- Where a period sits relative to the present. -/
inductive Zone
  | past | present | future
  deriving DecidableEq

/-- The day a zone names, the utterance being on day 0. -/
def Zone.day : Zone → ℤ
  | .past => -1
  | .present => 0
  | .future => 1

/-- The period a zone names: its day. -/
def Zone.period (z : Zone) : Ref ℤ := Ref.point z.day

/-- The zones a scoping's reference interval reaches: the forward interval of the present, the
intervals before it, or the forward interval of a past time. -/
def Scope.zones : Scope → Finset Zone
  | .modal => {.present, .future}
  | .modalPerf => {.past}
  | .perfModal => {.past, .present, .future}

/-- In the model, the scoping's sentence about a winning on the zone's day, framed by that day
and uttered on day 0, is true. -/
def Scope.Sat (s : Scope) (z : Zone) : Prop :=
  ∃ Q ∈ frame z.period (.eventive (winOn z.day)), PRES 0 (s.lf anyWorld Q) ()

private theorem winOn_at (d : ℤ) {r : Ref ℤ} (h : Ref.point d ≤ r) :
    AT r () (.eventive (winOn d)) :=
  ⟨⟨_, .dynamic⟩, rfl, h⟩

private theorem point_le_ray_of_le {a b : ℤ} (h : a ≤ b) : Ref.point b ≤ Ref.ray a :=
  Ref.point_le_iff.2 (Ref.mem_ray.2 (WithTop.coe_le_coe.2 h))

/-- The zone table is the satisfiability table: a scoping admits a period exactly when its
sentence about that period can be true, the deviant cells being `frame_modal_past` and
`frame_modalPerf_nonpast`, the others witnessed. -/
theorem zones_iff : ∀ s : Scope, ∀ z : Zone, z ∈ s.zones ↔ s.Sat z := by
  intro s z
  cases s <;> cases z
  · refine iff_of_false (by decide) ?_
    rintro ⟨Q, hQ, h⟩
    refine frame_modal_past ?_ (Option.mem_def.1 hQ) h
    exact λ x hx y hy => lt_of_le_of_lt (Ref.mem_point.1 hx).le
      (lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by decide)) (Ref.mem_ray.1 hy))
  · exact iff_of_true (by decide) ⟨_, rfl, 0, Ref.startsAt_point, (), trivial,
      winOn_at 0 (le_inf (point_le_ray_of_le le_rfl) le_rfl)⟩
  · exact iff_of_true (by decide) ⟨_, rfl, 0, Ref.startsAt_point, (), trivial,
      winOn_at 1 (le_inf (point_le_ray_of_le (by decide)) le_rfl)⟩
  · exact iff_of_true (by decide) ⟨_, rfl, 0, Ref.startsAt_point, (), trivial,
      Ref.lift (NonemptyInterval.pure (-1)), Ref.precedes_ofInterval_ray.2 (by decide),
      winOn_at (-1) (le_inf le_rfl le_rfl)⟩
  · refine iff_of_false (by decide) ?_
    rintro ⟨Q, hQ, h⟩
    exact frame_modalPerf_nonpast (λ y hy => (Ref.mem_point.1 hy).ge) (Option.mem_def.1 hQ) h
  · refine iff_of_false (by decide) ?_
    rintro ⟨Q, hQ, h⟩
    refine frame_modalPerf_nonpast (λ y hy => ?_) (Option.mem_def.1 hQ) h
    rw [Ref.mem_point.1 hy]
    exact WithTop.coe_le_coe.2 (by decide)
  · exact iff_of_true (by decide) ⟨_, rfl, Ref.lift (NonemptyInterval.pure (-1)),
      Ref.precedes_point_point.2 (by decide), -1, Ref.startsAt_point, (), trivial,
      winOn_at (-1) (le_inf (point_le_ray_of_le le_rfl) le_rfl)⟩
  · exact iff_of_true (by decide) ⟨_, rfl, Ref.lift (NonemptyInterval.pure (-1)),
      Ref.precedes_point_point.2 (by decide), -1, Ref.startsAt_point, (), trivial,
      winOn_at 0 (le_inf (point_le_ray_of_le (by decide)) le_rfl)⟩
  · exact iff_of_true (by decide) ⟨_, rfl, Ref.lift (NonemptyInterval.pure (-1)),
      Ref.precedes_point_point.2 (by decide), -1, Ref.startsAt_point, (), trivial,
      winOn_at 1 (le_inf (point_le_ray_of_le (by decide)) le_rfl)⟩

/-! ### The rows -/

/-- The value of a row's feature, read through a table. -/
private def parse? {α : Type*} (table : List (String × α)) (row : LinguisticExample)
    (key : String) : Option α :=
  (row.feature? key).bind (List.lookup · table)

private def scopes : List (String × Scope) :=
  [("modal", .modal), ("modalPerf", .modalPerf), ("perfModal", .perfModal)]

/-- An adverbial row: the scoping, the sort of the predicate, and the zone of the frame
adverbial. -/
structure Adverbial where
  /-- The scoping. -/
  scope : Scope
  /-- The sort of the predicate. -/
  sort : Dynamicity
  /-- The zone of the period. -/
  zone : Zone

/-- The configuration an adverbial row records. -/
def Adverbial.ofRow (row : LinguisticExample) : Option Adverbial := do
  guard (row.feature? "construction" = some "adverb")
  return ⟨← parse? scopes row "scope",
    ← parse? [("eventive", Dynamicity.dynamic), ("stative", .stative)] row "sort",
    ← parse? [("past", Zone.past), ("present", .present), ("future", .future)] row "adverb"⟩

/-- The adverbial patterns of [1], [2], [29], [34] and [35]: a frame adverbial is deviant
exactly when its zone lies outside the scoping's satisfiable cells, `zones_iff`; the one
questionable row is the eventive predicate with *now* under a modal for the present, which
the semantics admits by an event within the present. -/
theorem adverb_rows : ∀ row ∈ Examples.all, ∀ a ∈ Adverbial.ofRow row,
    (row.judgment = .ungrammatical ↔ a.zone ∉ a.scope.zones) ∧
      (row.judgment = .questionable ↔
        a.scope = .modal ∧ a.sort = .dynamic ∧ a.zone = .present) := by
  decide

/-- What the context says about the issue. -/
inductive Context
  | settled | unsettled | absent
  deriving DecidableEq

/-- A reading row: the scoping, the zone the instantiation refers to, and the context. -/
structure Reading where
  /-- The scoping. -/
  scope : Scope
  /-- The zone referred to, the present for a stative with *now*. -/
  reference : Zone
  /-- What the context says about the issue. -/
  context : Context

/-- The configuration a reading row records, and whether the paper finds the metaphysical
reading available. -/
def Reading.ofRow (row : LinguisticExample) : Option (Reading × Bool) := do
  guard (row.feature? "construction" = some "reading")
  return (⟨← parse? scopes row "scope",
    ← parse? [("past", Zone.past), ("present", .present), ("future", .future)] row "reference",
    ← parse? [("settled", Context.settled), ("open", .unsettled), ("none", .absent)] row
      "context"⟩,
    ← parse? [("available", true), ("unavailable", false)] row "metaphysical")

/-- The metaphysical base is assignable: the instantiation is neither in the past of the
perspective, `settled_perf`, nor at the present, `settled_present`, nor settled by the
context. -/
def Reading.Metaphysical (r : Reading) : Prop :=
  r.scope ≠ .modalPerf ∧ r.reference ≠ .present ∧ r.context ≠ .settled

instance (r : Reading) : Decidable r.Metaphysical := inferInstanceAs (Decidable (_ ∧ _))

/-- The readings of [6], [7], [41] and [42]: the metaphysical reading is available exactly
where settledness is not guaranteed. -/
theorem reading_rows : ∀ row ∈ Examples.all, ∀ p ∈ Reading.ofRow row,
    (p.2 = true ↔ p.1.Metaphysical) := by
  decide

/-- The complement a phase adverb applies to. -/
inductive Complement
  | eventive | perfect
  deriving DecidableEq

/-- A representative property of the complement's sort. -/
def Complement.property : Complement → Property Unit Unit
  | .eventive => .eventive λ _ _ => True
  | .perfect => PERF (.eventive λ _ _ => True)

/-- A sortal row: the complement of *already* or *yet*. -/
def Complement.ofRow (row : LinguisticExample) : Option Complement := do
  guard (row.feature? "construction" = some "sortal")
  return ← parse? [("eventive", Complement.eventive), ("perfect", .perfect)] row "complement"

/-- The sortal restriction of [14] and [15]: *already* and *yet* are acceptable exactly on the
complements where `phase` is defined, the perfect of an eventive predicate among them. -/
theorem sortal_rows : ∀ row ∈ Examples.all, ∀ c ∈ Complement.ofRow row,
    (row.judgment = .acceptable ↔ (phase c.property).isSome = true) := by
  decide

/-- The phase adverbs. -/
inductive Phase
  | already | still
  deriving DecidableEq

/-- A phase row: the adverb scoping over the possibility modal. -/
def Phase.ofRow (row : LinguisticExample) : Option Phase := do
  guard (row.feature? "construction" = some "phase")
  return ← parse? [("already", Phase.already), ("still", .still)] row "adverb"

/-- The scopings of [36], [37] and [40]: *still* over a possibility modal is acceptable and
*already* is not, `still_may` and `not_already_may`. -/
theorem phase_rows : ∀ row ∈ Examples.all, ∀ p ∈ Phase.ofRow row,
    (row.judgment = .acceptable ↔ p = .still) := by
  decide

/-- The German orders of the modal and the perfect auxiliary, which mirror scope. -/
inductive Order
  /-- *könnte ... haben*: the modal over the perfect. -/
  | modalHave
  /-- *hätte ... können*: the perfect over the modal. -/
  | hadModal
  deriving DecidableEq

/-- The order the adverb's presuppositions require: *schon* the modal over *already* over the
perfect, since *already* can scope neither over a possibility modal, `not_already_may`, nor
under it on an eventive radical, `phase`; *noch* the perfect over *still* over the modal, on
the paper's exclusion of *still* over the perfect. -/
def Phase.order : Phase → Order
  | .already => .modalHave
  | .still => .hadModal

/-- A German row: the order and the adverb. -/
def Order.ofRow (row : LinguisticExample) : Option (Order × Phase) := do
  guard (row.feature? "construction" = some "german")
  return (← parse? [("modalHave", Order.modalHave), ("hadModal", .hadModal)] row "order",
    ← parse? [("schon", Phase.already), ("noch", .still)] row "adverb")

/-- The German pattern [38]: acceptable exactly when the syntax realizes the order the adverb
requires. -/
theorem german_rows : ∀ row ∈ Examples.all, ∀ p ∈ Order.ofRow row,
    (row.judgment = .acceptable ↔ p.1 = p.2.order) := by
  decide

end Condoravdi2002
