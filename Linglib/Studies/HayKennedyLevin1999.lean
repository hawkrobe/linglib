import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Field.Rat
import Linglib.Semantics.Degree.Measure.Temporal
import Linglib.Semantics.Aspect.DegreeAchievement
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Data.Examples.HayKennedyLevin1999

/-!
# Hay, Kennedy and Levin (1999): Scalar Structure Underlies Telicity in "Degree Achievements"

This file formalizes the analysis of degree achievements in [hay-kennedy-levin-1999]: the
verb-forming morpheme contributes `INCREASE` (16), true of an event when the affected
argument's degree on the base adjective's scale at the end of the event is its degree at the
start plus a *difference value*, and the predicate is telic exactly when the difference value
is bounded: when it specifies a positive lower bound on the change (§3.1). The sources of a
bound are derived in turn: a measure phrase or `completely` (§3.1), `significantly` against
`slightly` (the monotone increasing and decreasing modifiers), the maximal value of a
closed-range base adjective (§3.2), and a conventional bound supplied by context (§3.3). A
bound that is only implicated can be cancelled and one supplied by overt material cannot
(`someAmount_cancellable`, `completely_not_cancellable`), which is why the adverbial duality
of (34) disappears in (35). The paper's closed-range and open-range classes are checked
against the English fragment's scale dimensions, and its examples are the rows.

## Implementation notes

Degrees form a densely ordered abelian group: the paper's degree addition (15) is the group's,
its maximal scale value is a degree `top` rather than a top element, and density is what
makes "some amount" and `slightly` unbounded (a smaller positive change is always
available). The readings of a description are the admissible difference values: overt
material fixes one; with none, the literal "some amount" and, when a maximal or conventional
value is salient, the implicated bounded value, since the paper derives the bound by
conversational implicature. The in-adverbial and for-adverbial tests are read as the
existence of a bounded and of an unbounded reading. The `almost` test and the causative
component of transitive degree achievements (footnote 2) are not modelled.

## TODO

* The parallel with the mass–count distinction and the redefinition of the incremental
  theme as the difference value (§4.2), which want a shared substrate with [krifka-1989]'s
  cumulativity.

## References

* [hay-kennedy-levin-1999]
* [kennedy-mcnally-2005]
* [dowty-1979]
* [krifka-1989]
-/

namespace HayKennedyLevin1999

open Data.Examples Degree Features
open English.Predicates.Verbal

/-! ### The difference value (§2) -/

section Semantics

variable {α δ T : Type*}

/-- `INCREASE` (16): `x` increases in `φ`-ness by the difference value `d` over an event that
    begins at `t₀` and ends at `t₁`. -/
def Increase [Add δ] (φ : TemporalMeasure α δ T) (x : α) (d : δ) (t₀ t₁ : T) : Prop :=
  φ x t₀ + d = φ x t₁

/-- A description whose difference value is only known to lie in `D`: (17a) with the positive
    degrees, (17b) with `{5 inches}`. -/
def Describes [Add δ] (φ : TemporalMeasure α δ T) (x : α) (D : Set δ) (t₀ t₁ : T) :
    Prop :=
  ∃ d ∈ D, Increase φ x d t₀ t₁

/-- With the difference value given, the degree at the end of the event is determined by the
    degree at its start: the source of an identifiable endpoint (§3). -/
theorem Increase.end_unique [Add δ] {φ : TemporalMeasure α δ T} {x : α} {d : δ}
    {t₀ t₁ t₂ : T} (h₁ : Increase φ x d t₀ t₁) (h₂ : Increase φ x d t₀ t₂) : φ x t₁ = φ x t₂ :=
  h₁.symm.trans h₂

variable [AddCommGroup δ] [LinearOrder δ]

/-- §3.1: a difference value is **bounded** when it specifies a positive lower bound on the
    change; once that much change has happened the truth conditions are met, so the event has
    an endpoint, and the predicate is telic. -/
def IsBounded (D : Set δ) : Prop := ∃ b, 0 < b ∧ b ∈ lowerBounds D

/-- The implicit difference value "some amount" of (9a): any positive degree. -/
def someAmount : Set δ := Set.Ioi 0

/-- A measure phrase (18): exactly `m`. -/
def measurePhrase (m : δ) : Set δ := {m}

/-- `completely` (21): the change that takes the initial degree `i` to the scale's maximal
    value `top`. -/
def completely (top i : δ) : Set δ := {top - i}

/-- `significantly` (23): at least the contextual standard `s`, a monotone increasing
    modifier. -/
def significantly (s : δ) : Set δ := Set.Ici s

/-- `slightly` (24): a positive change of at most `s`, a monotone decreasing modifier: part of a
    slight increase is a slight increase. -/
def slightly (s : δ) : Set δ := Set.Ioc 0 s

theorem isBounded_measurePhrase {m : δ} (hm : 0 < m) : IsBounded (measurePhrase m) :=
  ⟨m, hm, λ _ hd => (Set.mem_singleton_iff.1 hd).ge⟩

theorem isBounded_completely [IsOrderedAddMonoid δ] {top i : δ} (hi : i < top) :
    IsBounded (completely top i) :=
  ⟨top - i, sub_pos.2 hi, λ _ hd => (Set.mem_singleton_iff.1 hd).ge⟩

theorem isBounded_significantly {s : δ} (hs : 0 < s) : IsBounded (significantly s) :=
  ⟨s, hs, λ _ hd => hd⟩

/-- A difference value that admits arbitrarily small positive changes specifies no bound. -/
theorem not_isBounded_of_forall {D : Set δ} (h : ∀ b, 0 < b → ∃ d ∈ D, d < b) :
    ¬ IsBounded D := by
  rintro ⟨b, hb, hlow⟩
  obtain ⟨d, hd, hdb⟩ := h b hb
  exact absurd (hlow hd) (not_le.2 hdb)

theorem not_isBounded_slightly [DenselyOrdered δ] {s : δ} (hs : 0 < s) :
    ¬ IsBounded (slightly s) :=
  not_isBounded_of_forall λ b hb => by
    obtain ⟨c, hc₀, hc⟩ := exists_between (lt_min hb hs)
    exact ⟨c, ⟨hc₀, (lt_min_iff.1 hc).2.le⟩, (lt_min_iff.1 hc).1⟩

theorem not_isBounded_someAmount [DenselyOrdered δ] : ¬ IsBounded (someAmount (δ := δ)) :=
  not_isBounded_of_forall λ b hb => by
    obtain ⟨c, hc₀, hc⟩ := exists_between hb
    exact ⟨c, hc₀, hc⟩

/-! ### Readings (§3.2–§3.4) -/

/-- The overt material that can fix a difference value. -/
inductive Modifier (δ : Type*)
  | none
  | measure (m : δ)
  | completely
  | significantly (s : δ)
  | slightly (s : δ)

/-- What can bound the difference value when nothing overt does: the maximal value of a
    closed-range base adjective's scale (§3.2), or a conventional maximum for the affected
    object (§3.3). -/
structure Context (δ : Type*) where
  scaleMax : Option δ
  conventionalMax : Option δ

/-- The salient bound, if any. -/
def Context.bound (c : Context δ) : Option δ := c.scaleMax <|> c.conventionalMax

/-- The admissible difference values of a description whose affected argument starts at
    degree `i`: overt material fixes one; with none, the literal "some amount" and, when a
    bound is salient, the value the most informative interpretation implicates. -/
def readings (c : Context δ) (i : δ) : Modifier δ → Set (Set δ)
  | .none => {someAmount} ∪ (c.bound.map λ m => {completely m i}).getD ∅
  | .measure m => {measurePhrase m}
  | .completely => (c.scaleMax.map λ m => {completely m i}).getD ∅
  | .significantly s => {significantly s}
  | .slightly s => {slightly s}

/-- A telic reading: an admissible bounded difference value, what an in-adverbial needs. -/
def HasTelic (c : Context δ) (i : δ) (m : Modifier δ) : Prop :=
  ∃ D ∈ readings c i m, IsBounded D

/-- An atelic reading: an admissible unbounded difference value, what a for-adverbial
    needs. -/
def HasAtelic (c : Context δ) (i : δ) (m : Modifier δ) : Prop :=
  ∃ D ∈ readings c i m, ¬ IsBounded D

variable {c : Context δ} {i : δ}

/-- (18)–(20): a measure phrase makes the predicate telic, whatever the base adjective. -/
theorem hasTelic_measure {m : δ} (hm : 0 < m) : HasTelic c i (.measure m) :=
  ⟨_, rfl, isBounded_measurePhrase hm⟩

theorem not_hasAtelic_measure {m : δ} (hm : 0 < m) : ¬ HasAtelic c i (.measure m) :=
  λ ⟨_, hD, h⟩ => h (Set.mem_singleton_iff.1 hD ▸ isBounded_measurePhrase hm)

/-- (21)–(22), (35): `completely` makes the predicate telic and leaves no atelic reading. -/
theorem hasTelic_completely [IsOrderedAddMonoid δ] {top : δ} (hc : c.scaleMax = some top)
    (hi : i < top) :
    HasTelic c i .completely :=
  ⟨_, by simp [readings, hc], isBounded_completely hi⟩

theorem not_hasAtelic_completely [IsOrderedAddMonoid δ] {top : δ} (hc : c.scaleMax = some top)
    (hi : i < top) :
    ¬ HasAtelic c i .completely := by
  rintro ⟨D, hD, h⟩
  simp only [readings, hc, Option.map_some, Option.getD_some, Set.mem_singleton_iff] at hD
  exact h (hD ▸ isBounded_completely hi)

/-- (25b): `completely` has no reading on an open-range base. -/
theorem readings_completely_open (hc : c.scaleMax = none) : readings c i .completely = ∅ := by
  simp [readings, hc]

/-- (23): `significantly` makes the predicate telic. -/
theorem hasTelic_significantly {s : δ} (hs : 0 < s) : HasTelic c i (.significantly s) :=
  ⟨_, rfl, isBounded_significantly hs⟩

/-- (24): `slightly` leaves the predicate atelic. -/
theorem hasAtelic_slightly [DenselyOrdered δ] {s : δ} (hs : 0 < s) :
    HasAtelic c i (.slightly s) :=
  ⟨_, rfl, not_isBounded_slightly hs⟩

theorem not_hasTelic_slightly [DenselyOrdered δ] {s : δ} (hs : 0 < s) :
    ¬ HasTelic c i (.slightly s) :=
  λ ⟨_, hD, h⟩ => not_isBounded_slightly hs (Set.mem_singleton_iff.1 hD ▸ h)

/-- (26), (28), (34a): with a salient bound, from a closed-range base or from convention, an
    unmodified degree achievement has a telic reading. -/
theorem hasTelic_of_bound [IsOrderedAddMonoid δ] {b : δ} (hb : c.bound = some b) (hi : i < b) :
    HasTelic c i .none :=
  ⟨completely b i, by simp [readings, hb], isBounded_completely hi⟩

/-- (32), (34b): the literal reading is always there, so the implicated bound can be cancelled
    and the for-adverbial is felicitous. -/
theorem hasAtelic_none [DenselyOrdered δ] : HasAtelic c i .none :=
  ⟨someAmount, by simp [readings], not_isBounded_someAmount⟩

/-- (27), (30), (31): without a salient bound, an unmodified degree achievement has only the
    atelic reading. -/
theorem not_hasTelic_none [DenselyOrdered δ] (hb : c.bound = none) : ¬ HasTelic c i .none := by
  rintro ⟨D, hD, h⟩
  simp only [readings, hb, Option.map_none, Option.getD_none, Set.union_empty,
    Set.mem_singleton_iff] at hD
  exact not_isBounded_someAmount (hD ▸ h)

/-! ### Cancellability (§3.3, (32)–(33)) -/

/-- (33): a bound supplied by overt material is not cancellable: if the rope was straightened
    completely, it is completely straight. -/
theorem completely_not_cancellable {φ : TemporalMeasure α δ T} {x : α} {top : δ}
    {t₀ t₁ : T} (h : Describes φ x (completely top (φ x t₀)) t₀ t₁) : ¬ φ x t₁ < top := by
  obtain ⟨d, hd, hinc⟩ := h
  rw [Set.mem_singleton_iff.1 hd, Increase, add_sub_cancel] at hinc
  intro hlt
  rw [← hinc] at hlt
  exact lt_irrefl _ hlt

/-- (32): a bound that is only implicated is cancellable: the literal "some amount" is
    consistent with the maximal value not having been reached. -/
theorem someAmount_cancellable [IsOrderedAddMonoid δ] [DenselyOrdered δ] {i top : δ}
    (hi : i < top) :
    ∃ φ : TemporalMeasure Unit δ Bool,
      Describes φ () someAmount false true ∧ φ () true < top := by
  obtain ⟨j, hij, hjt⟩ := exists_between hi
  exact ⟨λ _ t => if t then j else i, ⟨j - i, sub_pos.2 hij, by simp [Increase]⟩, by simpa⟩

end Semantics

/-! ### The English degree achievements (§3.2, (25)) -/

/-- The closed-range adjectives the paper names: *straight*, *empty*, *dry* ((25a)) and
    *flat*. -/
def closedRange : List String := ["straight", "empty", "dry", "flat"]

/-- The open-range adjectives the paper names: *long*, *wide*, *short* ((25b)). -/
def openRange : List String := ["long", "wide", "short"]

/-- The fragment's degree achievements agree with the paper's classification: a verb whose base
    adjective is closed-range has a scale with a maximum, and one whose base is open-range has
    not. -/
theorem fragment_range :
    ∀ v ∈ allVerbs, ∀ s ∈ v.degreeAchievementScale, ∀ a ∈ s.baseAdjective,
      (a ∈ closedRange → s.scaleBoundedness.HasMax) ∧
        (a ∈ openRange → ¬ s.scaleBoundedness.HasMax) := by
  decide +kernel

/-- The default telicity the fragment derives for a degree achievement is the telicity of the
    unmodified reading in a context whose only salient bound is the scale's maximum, when it
    has one. -/
theorem defaultTelicity_iff (s : DegreeAchievement.DegreeAchievementScale) (i top : ℚ)
    (hi : i < top) :
    s.defaultTelicity = .telic ↔
      HasTelic ⟨if s.scaleBoundedness.HasMax then some top else none, none⟩ i .none := by
  have key : s.defaultTelicity = .telic ↔ s.scaleBoundedness.HasMax := by
    rw [DegreeAchievement.DegreeAchievementScale.defaultTelicity,
      ScalarDimension.defaultTelicity_telic_iff_hasGreatest]
    exact Boundedness.hasGreatest_degreeShape_iff _
  rw [key]
  by_cases hmax : s.scaleBoundedness.HasMax
  · rw [if_pos hmax]
    exact iff_of_true hmax (hasTelic_of_bound rfl hi)
  · rw [if_neg hmax]
    exact iff_of_false hmax (not_hasTelic_none rfl)

end HayKennedyLevin1999
