import Linglib.Data.Examples.RonderosEtAl2024
import Linglib.Processing.VisualWorld
import Linglib.Semantics.Degree.Adjective
import Mathlib.Data.Finset.Basic

/-!
# Ronderos et al. (2024): Factors affecting contrastive inferences

This file formalizes [ronderos-etal-2024]'s cross-linguistic eye-tracking study of contrastive
inference with colour, scalar, and material adjectives in the paradigm of [sedivy-etal-1999]: a
listener who interprets *the short pencil* contrastively, as distinguishing the pencil from a
longer one, identifies the referent before the noun when the display holds such a contrasting
object. The paper separates three factors by the predictions they make across adjective types.
The pragmatic account of [sedivy-2003] and [sedivy-2004] lets the interpretation be contrastive
only for adjectives rarely used descriptively, so colour, often descriptive, should show no
contrast effect and material should; the perceptual account requires the contrast to be
perceived during preview, and material contrasts are less salient than colour ones
([kursat-degen-2021], [jara-ettinger-rubio-fernandez-2022]), so colour should show the effect
and material should not. The semantic account of [aparicio-xiang-kennedy-2015] concerns the
no-contrast baseline: a relative gradable adjective ([kennedy-2007]) is interpreted against a
comparison class the listener must find in the display, so looks to the two property-matching
objects are lower for scalar adjectives than for the non-gradable colour and material ones.

`Display.contrastive` is the contrastive interpretation over a display of the paper's four
objects, and `Account.PredictsEffect` derives an account's contrast effect from whether the noun
is anticipated in each condition. `perceptual_matches` and `pragmatic_fails` compare the two
accounts with the effects found, for colour and scalar but not material adjectives, and
`baseline_higher_iff_not_relative` checks the baseline against the adjective classes, where
salience cannot explain material adjectives exceeding scalar ones. Language (English, Hindi,
Hungarian) enters the paper's models as a grouping unit only, and the rows are the pooled
findings.

## Implementation notes

* Kinds of object are named by a representative object. The perceptual factor attributes a
  property to a whole kind as soon as one member shows it, so that objects of a kind are never
  perceived as contrasting.
* Salience and informativity are the paper's premises per adjective type, with size contrasts
  taken as perceptible, as the replicated scalar effect requires.

## References

* [ronderos-etal-2024]
* [sedivy-etal-1999]
* [sedivy-2003]
* [sedivy-2004]
* [kursat-degen-2021]
* [jara-ettinger-rubio-fernandez-2022]
* [aparicio-xiang-kennedy-2015]
* [kennedy-2007]
-/

namespace RonderosEtAl2024

open Data.Examples VisualWorld

/-! ### The paradigm (Figure 1) -/

/-- The four objects of a display: the target, the object that in the contrast condition is of
the target's kind and lacks the property, the competitor of another kind sharing it, and a
distractor. -/
inductive Object where
  | target
  | contrastingObject
  | competitor
  | distractor
  deriving DecidableEq, Repr, Fintype

/-- A display as the listener takes it in: the kind of each object, named by a representative,
and the objects showing the adjective's property. -/
structure Display where
  kind : Object → Object
  has : Finset Object

namespace Display

variable (d : Display)

/-- The descriptive interpretation of the adjective: the objects with the property. -/
def descriptive : Finset Object := d.has

/-- The contrastive interpretation: the objects with the property that an object of their kind
lacks. -/
def contrastive : Finset Object :=
  d.has.filter λ o => ∃ o', d.kind o' = d.kind o ∧ o' ∉ d.has

theorem contrastive_subset_descriptive : d.contrastive ⊆ d.descriptive := Finset.filter_subset _ _

/-- The display with the property attributed to a whole kind as soon as one of its members shows
it: how a property whose contrast is not perceived is taken in. -/
def blur : Display where
  kind := d.kind
  has := Finset.univ.filter λ o => ∃ o', d.kind o' = d.kind o ∧ o' ∈ d.has

/-- A blurred display never shows a contrast within a kind. -/
theorem contrastive_blur : d.blur.contrastive = ∅ := by
  rw [contrastive, Finset.filter_eq_empty_iff]
  rintro o ho ⟨o', hk, hn⟩
  simp only [blur, Finset.mem_filter, Finset.mem_univ, true_and] at ho hn
  obtain ⟨o₁, h₁, hh⟩ := ho
  exact hn ⟨o₁, h₁.trans hk.symm, hh⟩

end Display

/-- An interpretation anticipates the noun when it already singles out the target. -/
def Anticipates (S : Finset Object) : Prop := S = {.target}

instance (S : Finset Object) : Decidable (Anticipates S) := inferInstanceAs (Decidable (_ = _))

/-- The display of the contrast condition: the contrasting object is of the target's kind and
lacks the property, the competitor has it. -/
def contrastDisplay : Display where
  kind
    | .contrastingObject => .target
    | o => o
  has := {.target, .competitor}

/-- The display of the no-contrast condition: the contrasting object is replaced by a distractor
of its own kind. -/
def noContrastDisplay : Display where
  kind o := o
  has := {.target, .competitor}

/-- The display of each condition. -/
def display : ContrastCondition → Display
  | .contrast => contrastDisplay
  | .noContrast => noContrastDisplay

/-- The contrastive interpretation of the contrast display singles out the target before the
noun: the competitor has the property but no object of its kind lacks it. -/
theorem contrastive_contrast : contrastDisplay.contrastive = {.target} := by decide

/-- The descriptive interpretation leaves the target and the competitor. -/
theorem descriptive_contrast : contrastDisplay.descriptive = {.target, .competitor} := by decide

/-- Without a contrasting object the contrastive interpretation finds nothing. -/
theorem contrastive_noContrast : noContrastDisplay.contrastive = ∅ := by decide

theorem descriptive_noContrast : noContrastDisplay.descriptive = {.target, .competitor} := by
  decide

/-! ### The three factors -/

/-- The adjective types crossed with the contrast manipulation: colour (*black*, *blue*, …),
scalar (*large*, *narrow*, *short*, …), and material (*cotton*, *glass*, *leather*, …). -/
inductive AdjType where
  | color
  | scalar
  | material
  deriving DecidableEq, Repr, Fintype

/-- Whether the contrast in the property is visually salient during preview: material contrasts
are not ([kursat-degen-2021], [jara-ettinger-rubio-fernandez-2022]), colour and size contrasts
are. -/
def Salient : AdjType → Prop
  | .material => False
  | .color | .scalar => True

instance : DecidablePred Salient
  | .material => isFalse id
  | .color | .scalar => isTrue trivial

/-- Whether the adjective type is expected to be informative, being rarely used descriptively:
colour adjectives are produced descriptively about half the time ([sedivy-2004]), material and
scalar ones rarely. -/
def Informative : AdjType → Prop
  | .color => False
  | .scalar | .material => True

instance : DecidablePred Informative
  | .color => isFalse id
  | .scalar | .material => isTrue trivial

/-- The adjective classes ([kennedy-2007]): scalar adjectives are relative gradable, colour and
material adjectives non-gradable. -/
def AdjType.adjectiveClass : AdjType → Degree.AdjectiveClass
  | .scalar => .relative
  | .color | .material => .nonGradable

/-! ### The accounts of the contrast effect -/

/-- An account fixes, per adjective type, how the display is perceived and how the adjective is
interpreted. -/
structure Account where
  perceive : AdjType → Display → Display
  interpret : AdjType → Display → Finset Object

/-- The pragmatic account ([sedivy-2003], [sedivy-2004]): perception is veridical, and the
adjective is interpreted contrastively only when it is expected to be informative. -/
def pragmatic : Account where
  perceive _ d := d
  interpret t := if Informative t then Display.contrastive else Display.descriptive

/-- The perceptual account: the adjective is always interpreted contrastively, but a contrast
that is not salient is not perceived. -/
def perceptual : Account where
  perceive t d := if Salient t then d else d.blur
  interpret _ := Display.contrastive

/-- The contrast effect an account predicts for an adjective type: the noun is anticipated in
the contrast condition and not in the no-contrast one. -/
def Account.PredictsEffect (a : Account) (t : AdjType) : Prop :=
  Anticipates (a.interpret t (a.perceive t contrastDisplay)) ∧
    ¬ Anticipates (a.interpret t (a.perceive t noContrastDisplay))

instance (a : Account) (t : AdjType) : Decidable (a.PredictsEffect t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The pragmatic account predicts a contrast effect exactly for the informative types. -/
theorem pragmatic_predictsEffect_iff (t : AdjType) :
    pragmatic.PredictsEffect t ↔ Informative t := by
  cases t <;> decide

/-- The perceptual account predicts a contrast effect exactly for the salient contrasts. -/
theorem perceptual_predictsEffect_iff (t : AdjType) :
    perceptual.PredictsEffect t ↔ Salient t := by
  cases t <;> decide

/-! ### The findings -/

/-- The row key of an adjective type. -/
def AdjType.key : AdjType → String
  | .color => "color"
  | .scalar => "scalar"
  | .material => "material"

/-- The row key of a condition. -/
def conditionKey : ContrastCondition → String
  | .contrast => "contrast"
  | .noContrast => "noContrast"

/-- A feature of the row for an adjective type in a condition. -/
def finding (t : AdjType) (c : ContrastCondition) (key : String) : Option String :=
  (Examples.all.find? λ r =>
    r.feature? "adjType" == some t.key && r.feature? "condition" == some (conditionKey c)).bind
    (·.feature? key)

/-- Whether the paper found a contrast effect for an adjective type: a cluster of condition
effects on target looks after noun onset and an effect of condition on the target-advantage
score. -/
def Effect (t : AdjType) : Prop := finding t .contrast "contrastEffect" = some "present"

instance : DecidablePred Effect := λ _ => inferInstanceAs (Decidable (_ = _))

/-- Whether looks to the target and the competitor in the no-contrast baseline were higher for
an adjective type than for scalar adjectives. -/
def BaselineHigherThanScalar (t : AdjType) : Prop :=
  finding t .noContrast "baselineVsScalar" = some "higher"

instance : DecidablePred BaselineHigherThanScalar := λ _ => inferInstanceAs (Decidable (_ = _))

/-- The perceptual account predicts the effects found: for colour and scalar adjectives, not for
material ones. -/
theorem perceptual_matches : ∀ t, perceptual.PredictsEffect t ↔ Effect t := by decide +kernel

/-- The pragmatic account predicts an effect for material and none for colour, the reverse of
what was found. -/
theorem pragmatic_fails : ¬ ∀ t, pragmatic.PredictsEffect t ↔ Effect t := by decide +kernel

/-- The baseline follows the adjective classes: looks to the property-matching objects exceed
those for scalar adjectives exactly for the non-gradable types, which need no comparison class
([aparicio-xiang-kennedy-2015]). -/
theorem baseline_higher_iff_not_relative :
    ∀ t, BaselineHigherThanScalar t ↔ ¬ t.adjectiveClass.IsRelative := by
  decide +kernel

/-- Salience does not explain the baseline: material adjectives, whose contrast is not salient,
still draw more looks than scalar ones. -/
theorem salience_not_baseline : ¬ ∀ t, BaselineHigherThanScalar t → Salient t := by
  decide +kernel

end RonderosEtAl2024
