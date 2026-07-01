import Linglib.Syntax.Adjective.Basic
import Linglib.Semantics.Gradability.Dimension
import Linglib.Semantics.Degree.Defs

/-!
# English gradable adjectives (`GradableAdjective`)

Canonical gradable adjectives typed with the `Syntax/Adjective` API, exercising the
derived Kennedy classification ([kennedy-2007], [kennedy-mcnally-2005]). Each entry
stores only its scalar `dimension` (and, for a min/max-standard adjective, the
lexicalized pole `isLowerEndpoint`, or a `standardOverride` for a mildly-positive
adjective); the scale shape, the positive standard, and the relative/absolute class
are **derived**, not stored — the fix for the old `scaleType` field that conflated
scale shape with pole and contradicted `Dimension.boundedness` (`wet`/`dry` share one
closed `.wetness` scale, differing only in pole).

This is the seed of the unified English adjective fragment; the
`Predicates/Adjectival.lean` `GradableAdjEntry` set folds in here as the migration
proceeds.
-/

open Semantics.Gradability (Dimension)
open Semantics.Degree (AdjectiveClass PositiveStandard)

namespace English.GradableAdjectives

/-! ### Entries — only the dimension + pole/override are lexical; the rest is derived -/

/-- *tall* — open height scale ⇒ relative. -/
def tall : GradableAdjective := { form := "tall", dimension := some .height }

/-- *full* — closed fullness scale, upper pole ⇒ maximum-standard. -/
def full : GradableAdjective := { form := "full", dimension := some .fullness }

/-- *empty* — closed fullness scale, lower pole ⇒ minimum-standard. -/
def empty : GradableAdjective :=
  { form := "empty", dimension := some .fullness, isLowerEndpoint := true }

/-- *wet* — closed wetness scale, lower pole ⇒ minimum-standard. -/
def wet : GradableAdjective :=
  { form := "wet", dimension := some .wetness, isLowerEndpoint := true }

/-- *dry* — closed wetness scale, upper pole ⇒ maximum-standard. -/
def dry : GradableAdjective := { form := "dry", dimension := some .wetness }

/-- *straight* — closed straightness scale, upper pole ⇒ maximum-standard. -/
def straight : GradableAdjective := { form := "straight", dimension := some .straightness }

/-- *bent* — closed straightness scale, lower pole ⇒ minimum-standard. -/
def bent : GradableAdjective :=
  { form := "bent", dimension := some .straightness, isLowerEndpoint := true }

/-- *good* — open value scale ⇒ relative. -/
def good : GradableAdjective := { form := "good", dimension := some .value }

/-- *decent* — a mildly-positive adjective: open shape but a functional standard
    ([beltrama-2025]), recorded via `standardOverride`. -/
def decent : GradableAdjective :=
  { form := "decent", dimension := some .value, standardOverride := some .functional }

/-! ### The derived classification (the API's payoff — all by `rfl`/`decide`) -/

-- scale *shape* is the dimension's; `wet`/`dry` no longer disagree on it:
theorem tall_open : tall.scaleType = .open_ := rfl
theorem wet_closed : wet.scaleType = .closed := rfl
theorem dry_closed : dry.scaleType = .closed := rfl

-- the pole the old `scaleType` conflated, now recovered:
theorem wet_min : wet.standard = .minEndpoint := rfl
theorem dry_max : dry.standard = .maxEndpoint := rfl

-- every Kennedy class, derived from (dimension, pole, override):
theorem tall_relative     : tall.adjectiveClass = .relativeGradable := rfl
theorem good_relative     : good.adjectiveClass = .relativeGradable := rfl
theorem full_absMax       : full.adjectiveClass = .absoluteMaximum := rfl
theorem straight_absMax   : straight.adjectiveClass = .absoluteMaximum := rfl
theorem dry_absMax        : dry.adjectiveClass = .absoluteMaximum := rfl
theorem empty_absMin      : empty.adjectiveClass = .absoluteMinimum := rfl
theorem wet_absMin        : wet.adjectiveClass = .absoluteMinimum := rfl
theorem bent_absMin       : bent.adjectiveClass = .absoluteMinimum := rfl
theorem decent_mildlyPos  : decent.adjectiveClass = .mildlyPositive := rfl

-- comparison-class dependence: only the open-scale relatives require one:
theorem tall_requires_cc  : tall.IsRelative := by decide
theorem good_requires_cc  : good.IsRelative := by decide
theorem wet_no_cc         : ¬ wet.IsRelative := by decide
theorem full_no_cc        : ¬ full.IsRelative := by decide
theorem decent_no_cc      : ¬ decent.IsRelative := by decide

/-- All these adjectives are gradable (carry a dimension). -/
theorem all_gradable :
    tall.IsGradable ∧ full.IsGradable ∧ wet.IsGradable ∧ good.IsGradable := by decide

end English.GradableAdjectives
