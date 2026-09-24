module

public import Linglib.Semantics.Reference.Prominence

/-!
# Turkish object marking

This file defines the differential marking of the Turkish direct object as Göksel and Kerslake
describe it. The accusative suffix *-(y)I* is obligatory on a definite direct object and on a
specific indefinite one, partitives and possessive-marked objects among them, and absent on a
non-specific indefinite, which must then stand immediately before the verb; an indefinite
object elsewhere in the clause takes the suffix. Enç's characterization of the marked
indefinites as specific is the one Aissen's typology of differential object marking adopts, so
the pattern is the definiteness scale cut off at the specific indefinites, with no animacy
dimension.

## Main definitions

* `Turkish.ObjectMarking.accusative`: the marking pattern, the definiteness scale from the
  specific indefinites up
* `Turkish.ObjectMarking.MustBePreverbal`: the definiteness levels whose objects, being
  unmarked, stand immediately before the verb

## Main results

* `Turkish.ObjectMarking.accusative_iff`: an object is marked exactly when it is at least a
  specific indefinite
* `Turkish.ObjectMarking.accusative_monotoneP`: the marked cells are an upper set of the
  prominence order
* `Turkish.ObjectMarking.mustBePreverbal_iff`: only a non-specific indefinite is confined to
  the preverbal position

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [J. Aissen, *Differential Object Marking: Iconicity vs. Economy* (2003)][aissen-2003]
-/

@[expose] public section

namespace Turkish.ObjectMarking

open Reference.Prominence

/-- The accusative marks a direct object at or above the specific indefinite on the
definiteness scale, whatever its animacy. -/
def accusative : MarkingPattern := .definitenessAtLeast .indefiniteSpecific

/-- An object is marked exactly when it is at least a specific indefinite. -/
theorem accusative_iff (a : AnimacyLevel) (d : DefinitenessLevel) :
    accusative a d = true ↔ .indefiniteSpecific ≤ d := by
  simp [accusative, MarkingPattern.definitenessAtLeast]

/-- The marked cells are an upper set of the prominence order. -/
theorem accusative_monotoneP : accusative.MonotoneP := by decide

/-- An object of a definiteness level must stand immediately before the verb when it is
unmarked. -/
def MustBePreverbal (d : DefinitenessLevel) : Prop := ∀ a, accusative a d = false

instance : DecidablePred MustBePreverbal := fun _ ↦ inferInstanceAs (Decidable (∀ _, _))

/-- Only a non-specific indefinite is confined to the preverbal position. -/
theorem mustBePreverbal_iff (d : DefinitenessLevel) : MustBePreverbal d ↔ d = .nonSpecific := by
  cases d <;> decide

end Turkish.ObjectMarking
