import Linglib.Semantics.Aspect.DegreeAchievement
import Linglib.Semantics.Degree.Measure.Temporal
import Linglib.Semantics.Degree.Boundedness
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival
import Mathlib.Order.Max
import Mathlib.Order.Bounds.Basic

/-!
# Kennedy and Levin (2008): Measure of Change

This file formalizes the account of variable telicity in degree achievements of
[kennedy-levin-2008]. A degree achievement is the verbal positive form (26) of a measure of
change function (25), the difference function (23) of the adjective's measure function, whose
derived scale has as its minimum the degree the argument has when the event begins and inherits
a maximum from the adjective's scale exactly when that scale has one (`deltaBoundedness`,
`isLeast_derivedScale`, `isGreatest_derivedScale`). Interpretive Economy (18) then licenses two
standards on the derived scale: its minimum, true of any positive change, the comparative and
atelic reading every degree achievement has ((22), `minStandard_iff`); and, when the adjective's
scale is closed above, its maximum, true when the argument ends completely straight, dark or
full, the telic reading of Section 3.3 (`maxStandard_iff`), which entails the atelic one and is
therefore preferred (`minStandard_of_maxStandard`). Without a greatest degree, as for *widen*,
the derived scale has no maximum and so no telic reading (`not_isGreatest_derivedScale`), while
Interpretive Economy rules out the contextual standard the adjective *wide* has, so *widen*
never means *become wide*; the telic use of *cool* in (1a) rests on a conventionalized
non-scalar standard the account leaves to the lexicon.

The English fragment's degree achievements instantiate the account: each verb's Vendler class
is the one its base scale derives (`da_vendler_classes_agree`), each verb shares the boundedness
of its adjective (`adjective_verb_scales`), and the *in X* and *for X* diagnostics of (1) and
(6) follow the scale (`inX_iff_hasMax`, `diagnostics`).

## Implementation notes

Measure functions, difference functions and the measure of change are the substrate's
`Degree.TemporalMeasure`, `Degree.differenceFunction` and `Degree.measureOfChange`, and the
readings are stated on the measure of change between an event's initial and final times; scale
boundedness is `Degree.Boundedness`. The measure-phrase and degree-modifier compositions of
(28)–(34) are not formalized.

## References

* [kennedy-levin-2008]
* [hay-kennedy-levin-1999]
* [kennedy-2007]
-/

namespace KennedyLevin2008

open Degree Aspect

/-! ### The measure of change and its scale (Sections 3.2 and 3.3) -/

/-- The scale of a measure of change: closed below at the degree the argument starts with, and
closed above exactly when the adjective's scale is. -/
def deltaBoundedness : Boundedness → Boundedness
  | .open_ | .lowerBounded => .lowerBounded
  | .upperBounded | .closed => .closed

/-- The derived scale always has a minimum, the derived zero. -/
theorem deltaBoundedness_hasMin (b : Boundedness) : (deltaBoundedness b).HasMin := by
  cases b <;> decide

/-- The derived scale has a maximum exactly when the adjective's scale has one. -/
theorem deltaBoundedness_hasMax_iff (b : Boundedness) :
    (deltaBoundedness b).HasMax ↔ b.HasMax := by
  cases b <;> decide

section Readings

variable {α δ T : Type*} [LinearOrder δ] (m : TemporalMeasure α δ T) (x : α) (i f : T)

/-- The derived scale of the measure of change for an argument starting at time `i`: the
degrees from its initial degree up. -/
def derivedScale : Set δ := Set.Ici (m x i)

/-- The derived zero: the argument's initial degree is the least degree of the derived scale. -/
theorem isLeast_derivedScale : IsLeast (derivedScale m x i) (m x i) := isLeast_Ici

/-- A greatest degree of the adjective's scale is the greatest of the derived scale. -/
theorem isGreatest_derivedScale [OrderTop δ] : IsGreatest (derivedScale m x i) ⊤ :=
  ⟨le_top, λ _ _ => le_top⟩

/-- Without a greatest degree on the adjective's scale, the derived scale has none either. -/
theorem not_isGreatest_derivedScale [NoMaxOrder δ] (d : δ) :
    ¬ IsGreatest (derivedScale m x i) d := by
  rintro ⟨hd, hub⟩
  obtain ⟨d', hd'⟩ := exists_gt d
  exact absurd (hub (le_trans hd hd'.le)) hd'.not_ge

/-- The minimum-standard reading of (27): the argument changes by a non-zero degree of the
derived scale, the comparative truth conditions of (22). -/
def MinStandard : Prop := m x i < measureOfChange m x i f

/-- The maximum-standard reading of (27): the argument reaches the greatest degree. -/
def MaxStandard [OrderTop δ] : Prop := measureOfChange m x i f = ⊤

/-- The comparative reading is a positive change of the measured property. -/
theorem minStandard_iff : MinStandard m x i f ↔ m x i < m x f := by
  simp [MinStandard, measureOfChange, differenceFunction]

/-- Once the argument does not start at the maximum, the telic reading is reaching it. -/
theorem maxStandard_iff [OrderTop δ] (h : m x i < ⊤) : MaxStandard m x i f ↔ m x f = ⊤ := by
  unfold MaxStandard measureOfChange differenceFunction
  constructor
  · intro hm
    rcases max_choice (m x i) (m x f) with h' | h' <;> rw [h'] at hm
    · exact absurd hm h.ne
    · exact hm
  · intro hf
    rw [hf, max_eq_right le_top]

/-- The telic reading entails the atelic one, and so is the more informative and preferred. -/
theorem minStandard_of_maxStandard [OrderTop δ] (h : m x i < ⊤) (hmax : MaxStandard m x i f) :
    MinStandard m x i f := by
  rw [minStandard_iff, (maxStandard_iff m x i f h).mp hmax]
  exact h

end Readings

/-! ### The English degree achievements -/

/-- The fragment's degree achievements. -/
def daVerbs : List Verb :=
  [English.Predicates.Verbal.bend.toVerb, English.Predicates.Verbal.boil.toVerb,
   English.Predicates.Verbal.rust.toVerb, English.Predicates.Verbal.increase.toVerb,
   English.Predicates.Verbal.clean.toVerb, English.Predicates.Verbal.straighten.toVerb,
   English.Predicates.Verbal.flatten.toVerb, English.Predicates.Verbal.open_.toVerb,
   English.Predicates.Verbal.lengthen.toVerb, English.Predicates.Verbal.widen.toVerb,
   English.Predicates.Verbal.cool.toVerb, English.Predicates.Verbal.warm.toVerb]

/-- Every degree achievement's Vendler class is the one its base scale derives: closed above,
an accomplishment; otherwise an activity. -/
theorem da_vendler_classes_agree :
    ∀ v ∈ daVerbs, v.vendlerClass = v.degreeAchievementScale.map (·.defaultVendlerClass) := by
  decide

/-- The adjective–verb pairs of the fragment: *clean*, *straight*, *flat* and *open* with
closed scales, *long*, *wide*, *cool* and *warm* with open ones. -/
def pairs : List (English.Predicates.Adjectival.AdjectivalPredicateEntry × Verb) :=
  [(English.Predicates.Adjectival.clean, English.Predicates.Verbal.clean.toVerb),
   (English.Predicates.Adjectival.straight, English.Predicates.Verbal.straighten.toVerb),
   (English.Predicates.Adjectival.flat, English.Predicates.Verbal.flatten.toVerb),
   (English.Predicates.Adjectival.open_, English.Predicates.Verbal.open_.toVerb),
   (English.Predicates.Adjectival.long, English.Predicates.Verbal.lengthen.toVerb),
   (English.Predicates.Adjectival.wide, English.Predicates.Verbal.widen.toVerb),
   (English.Predicates.Adjectival.cool, English.Predicates.Verbal.cool.toVerb),
   (English.Predicates.Adjectival.warm, English.Predicates.Verbal.warm.toVerb)]

/-- A degree achievement measures on its adjective's scale. -/
theorem adjective_verb_scales :
    ∀ p ∈ pairs, p.2.degreeAchievementScale.map (·.scaleBoundedness) = some p.1.scaleType := by
  decide

/-- (1) and (6): a degree achievement takes *in X* exactly when its scale is closed above, and
*for X* otherwise, its Vendler class being derived from the scale. -/
theorem inX_iff_hasMax (d : Features.ScalarDimension) :
    (inXPrediction d.defaultVendlerClass = .accept ↔ d.boundedness.HasMax) ∧
      (forXPrediction d.defaultVendlerClass = .accept ↔ ¬ d.boundedness.HasMax) := by
  cases d <;> decide

/-- The diagnostics on the fragment: *bend*, *boil*, *clean*, *straighten*, *flatten* and
*open* take *in X*, *rust*, *increase*, *lengthen*, *widen*, *cool* and *warm* take *for X*. -/
theorem diagnostics :
    ∀ v ∈ daVerbs, ∀ s ∈ v.degreeAchievementScale,
      (v.vendlerClass.map inXPrediction = some .accept ↔ s.scaleBoundedness.HasMax) ∧
        (v.vendlerClass.map forXPrediction = some .accept ↔ ¬ s.scaleBoundedness.HasMax) := by
  decide

end KennedyLevin2008
