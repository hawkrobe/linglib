import Linglib.Fragments.Mayan.Tseltalan
import Linglib.Phonology.Segmental.Defs
import Linglib.Syntax.Reflex
import Linglib.Syntax.Clause.ArgumentRole

/-!
# Tseltal Agreement Fragment

Agreement morphology for Tseltal (Tseltalan, Mayan). Tseltal and Tsotsil are
closely related within the Tseltalan subgroup of Western Mayan, sharing most
syntactic properties relevant to possessor extraction ([aissen-polian-2025];
[polian-2013]).

## Main declarations

* `Tseltal.template`, `Tseltal.assignCase`: the verbal complex, with Set B
  after the stem, and ergative-absolutive case in every aspect.
* `Tseltal.setAExponent`, `Tseltal.setBExponent`: Oxchuc Tseltal exponent
  tables ([polian-2013]).
* `Tseltal.Extraction.realize`: unmarked extraction (no Agent Focus).

## Implementation notes

Tseltal has the same two agreement paradigms as Tsotsil: Set A (ERG/GEN)
prefixes cross-reference the transitive agent and possessor; Set B (ABS)
markers, consistently suffixal in Tseltal, cross-reference the absolutive
argument (intransitive subject and transitive patient). The key difference
from Tsotsil is Set B position — consistently suffixal in Tseltal, prefixal
or suffixal by context in Tsotsil. 3rd person singular Set B has no overt
exponent (∅). Grammatical-function classification is shared across Tseltalan
(`Mayan.Tseltalan`).

Tseltalan languages are uniformly **ergative-absolutive** with no
aspect-conditioned split (in contrast with Cholan; per [polian-2013]): Set A
indicates A, Set B indicates S and P alike.

## References

* [aissen-polian-2025]
* [kaufman-norman-1984]
* [polian-2013]
-/


namespace Tseltal

open Mayan (MarkerSet ExponentTable)
open Agreement

-- Re-export shared Tseltalan types
export Mayan.Tseltalan (GrammaticalFunction)

/-! ### The verbal complex -/

/-- The position classes of the Tseltal verbal complex: the aspect marker and Set A before
the stem, Set B, consistently suffixal, after it ([aissen-polian-2025]). -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setA], [.setB]⟩

/-- Tseltal is ergative-absolutive in every aspect, with no aspect-conditioned split
([polian-2013]). -/
def assignCase : UD.Aspect → ArgumentRole → Case := fun _ ↦ Alignment.ergative.assignCase

/-! ### Set A/B exponents (Oxchuc Tseltal) -/

/-- Set A (ERG/GEN) exponents for Oxchuc Tseltal by following-segment
    environment ([polian-2013]): prefixes on the verb or possessed noun,
    `j-`/`a-`/`s-` pre-consonantally, `k-`/`aw-`/`y-` pre-vocalically
    (person is not distinguished by number in Set A; plural is marked
    by separate suffixes not part of the person marker). -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.pn .first .singular, [.pref "j"]), (.pn .second .singular, [.pref "a"]),
     (.pn .third .singular, [.pref "s"]), (.pn .first .plural, [.pref "j"]),
     (.pn .second .plural, [.pref "a"]), (.pn .third .plural, [.pref "s"])]
  | .vowel =>
    [(.pn .first .singular, [.pref "k"]), (.pn .second .singular, [.pref "aw"]),
     (.pn .third .singular, [.pref "y"]), (.pn .first .plural, [.pref "k"]),
     (.pn .second .plural, [.pref "aw"]), (.pn .third .plural, [.pref "y"])]

/-- Set B (ABS) exponents for Oxchuc Tseltal ([polian-2013]): suffixes on
    the verb stem; 3rd person singular has zero exponence. -/
def setBExponent : ExponentTable :=
  [(.pn .first .singular, [.suff "on"]), (.pn .second .singular, [.suff "at"]),
   (.pn .third .singular, []), (.pn .first .plural, [.suff "otik"]),
   (.pn .second .plural, [.suff "ex"]), (.pn .third .plural, [.suff "ik"])]

/-- Third person singular Set B is null, as across the Mayan branches with an ergative
perfective ([kaufman-norman-1984]); San Juan Atitán Mam's default Set B surfaces there. -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .singular) = some [] := rfl

/-! ### Extraction marking -/

namespace Extraction

/-- No Agent Focus morphology is required for A-extraction, consistent
    with Tseltal being LOW-ABS. -/
def realize : ArgumentRole → Finset (Reflex Empty) :=
  fun _ ↦ ∅

end Extraction

end Tseltal
