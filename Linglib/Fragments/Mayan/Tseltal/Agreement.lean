module

public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Syntax.Reflex
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Tseltal agreement

Tseltal marks person with two sets of affixes. Set A, the prefixes *j-*, *a-* and *s-*, before a
vowel *k-*, *aw-* and *y-*, indexes the transitive subject and the possessor and marks person
only; a plural person adds a suffix, *-tik* for the inclusive first person and *-ik* for the
second and the third, the exclusive first person varying by dialect. Set B, which indexes the
intransitive subject and the transitive object, is suffixal throughout, *-on*, *-at* and zero,
with the plurals *-otik*, *-ex* and *-ik*. The alignment is ergative in every aspect, the verbal
complex runs aspect, Set A, stem, Set B, and Tseltal has no Agent Focus form, so a transitive
subject extracts without a reflex on the verb. Polian's sketch of Tseltal and Tsotsil and
Aissen and Polian's summary of the two sets are the sources.

## Main definitions

* `Tseltal.setAExponent`, `Tseltal.setAPlural`, `Tseltal.setBExponent`: the paradigms.
* `Tseltal.template`, `Tseltal.assignCase`: the verbal complex and the ergative case function.
* `Tseltal.Extraction.realize`: no reflex for any extraction.

## References

* [polian-2017b]
* [aissen-polian-2025]
-/

@[expose] public section

namespace Tseltal

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The position classes of the verbal complex, the aspect marker and Set A before the stem and
Set B after it. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setA], [.setB]⟩

/-- Tseltal is ergative in every aspect. -/
def assignCase : UD.Aspect → ArgumentRole → Case := fun _ ↦ Alignment.ergative

/-! ### The paradigms -/

/-- The Set A markers by the following segment, the same prefix in both numbers since Set A
marks person alone. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.pn .first .singular, [.pref "j"]), (.pn .second .singular, [.pref "a"]),
     (.pn .third .singular, [.pref "s"]), (.pn .first .plural, [.pref "j"]),
     (.pn .second .plural, [.pref "a"]), (.pn .third .plural, [.pref "s"])]
  | .vowel =>
    [(.pn .first .singular, [.pref "k"]), (.pn .second .singular, [.pref "aw"]),
     (.pn .third .singular, [.pref "y"]), (.pn .first .plural, [.pref "k"]),
     (.pn .second .plural, [.pref "aw"]), (.pn .third .plural, [.pref "y"])]

/-- The plural suffix that goes with a Set A prefix, *-tik* for the inclusive first person and
*-ik* for the second and the third; the exclusive first person varies by dialect and is not
recorded. -/
def setAPlural : Person → List Morphology.Morph
  | .first | .firstInclusive => [.suff "tik"]
  | .second | .third => [.suff "ik"]
  | .firstExclusive | .zero => []

/-- The Set B suffixes, with a zero third person singular and the plural *-ik* alone in the
third person. -/
def setBExponent : ExponentTable :=
  [(.pn .first .singular, [.suff "on"]), (.pn .second .singular, [.suff "at"]),
   (.pn .third .singular, []), (.pn .first .plural, [.suff "otik"]),
   (.pn .second .plural, [.suff "ex"]), (.pn .third .plural, [.suff "ik"])]

/-! ### Extraction -/

namespace Extraction

/-- No extraction leaves a reflex on the verb, since Tseltal has no Agent Focus form. -/
def realize : ArgumentRole → Finset (Reflex Empty) := fun _ ↦ ∅

end Extraction

end Tseltal
