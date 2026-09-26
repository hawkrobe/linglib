module

public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Syntax.Reflex
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Tsotsil agreement

Tsotsil marks person with two sets of affixes. Set A, the prefixes *j-*, *a-* and *s-*, before a
vowel *k-*, *av-* and *y-*, indexes the transitive subject and the possessor and marks person
only; a plural person adds a suffix, *-tik* for the inclusive first person and *-ik* for the
second and the third, the exclusive first person varying by dialect. Set B, which indexes the
intransitive subject and the transitive object, has two subsets: the suffixes *-on*, *-ot* and
zero, with the plurals *-otik*, *-oxuk* and *-ik*, and the prefixes *i-*, *a-* and zero, which
appear only after a verbal aspect prefix and never before the second person Set A, so *l-i-tal*
'I came' has the prefix and *tal-em-on* 'I have come' the suffix. The alignment is ergative in
every aspect. The verbal complex in citation order runs aspect, Set A, stem, Set B. The
extraction of a transitive subject may switch the verb to the Agent Focus form in *-on*, which
Aissen shows to be optional and governed by obviation, the form of a clause whose object
outranks its subject. Polian's sketch of Tseltal and Tsotsil, Aissen's clause-structure
monograph and her Agent Focus article are the sources.

## Main definitions

* `Tsotsil.setAExponent`, `Tsotsil.setAPlural`, `Tsotsil.setBExponent`,
  `Tsotsil.setBPrefixExponent`: the paradigms.
* `Tsotsil.template`, `Tsotsil.assignCase`: the verbal complex and the ergative case function.
* `Tsotsil.Extraction.realize`: the optional Agent Focus reflex of subject extraction.

## Implementation notes

The template records the citation order with Set B after the stem; the prefixal subset, whose
distribution is dialectally heterogeneous, is a second paradigm rather than a second template.

## References

* [polian-2017b]
* [aissen-1987]
* [aissen-1999a]
* [aissen-polian-2025]
-/

@[expose] public section

namespace Tsotsil

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The position classes of the verbal complex in citation order, the aspect marker and Set A
before the stem and Set B after it. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setA], [.setB]⟩

/-- Tsotsil is ergative in every aspect. -/
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
    [(.pn .first .singular, [.pref "k"]), (.pn .second .singular, [.pref "av"]),
     (.pn .third .singular, [.pref "y"]), (.pn .first .plural, [.pref "k"]),
     (.pn .second .plural, [.pref "av"]), (.pn .third .plural, [.pref "y"])]

/-- The plural suffix that goes with a Set A prefix, *-tik* for the inclusive first person and
*-ik* for the second and the third; the exclusive first person varies by dialect and is not
recorded. -/
def setAPlural : Person → List Morphology.Morph
  | .first | .firstInclusive => [.suff "tik"]
  | .second | .third => [.suff "ik"]
  | .firstExclusive | .zero => []

/-- The Set B suffixes, with a zero third person singular and the plural *-ik* alone in the
third person; *-on* and *-otik* have the harmonic variants *-un* and *-utik*. -/
def setBExponent : ExponentTable :=
  [(.pn .first .singular, [.suff "on"]), (.pn .second .singular, [.suff "ot"]),
   (.pn .third .singular, []), (.pn .first .plural, [.suff "otik"]),
   (.pn .second .plural, [.suff "oxuk"]), (.pn .third .plural, [.suff "ik"])]

/-- The Set B prefixes, used only after a verbal aspect prefix and never before the second
person Set A: *i-*, *a-* and zero, the inclusive first person plural *ij-*, the second plural
*a-* with *-ik*, and the third plural *-ik* alone. -/
def setBPrefixExponent : ExponentTable :=
  [(.pn .first .singular, [.pref "i"]), (.pn .second .singular, [.pref "a"]),
   (.pn .third .singular, []), (.pn .first .plural, [.pref "ij"]),
   (.pn .second .plural, [.pref "a", .suff "ik"]), (.pn .third .plural, [.suff "ik"])]

/-! ### Extraction -/

namespace Extraction

/-- The host of the extraction reflex. -/
inductive Host where
  | verb
  deriving DecidableEq, Repr

/-- The Agent Focus suffix *-on*. -/
def agentFocusSuffix : Morphology.Morph := .suff "on"

/-- The extraction of a transitive subject may switch the verb to the Agent Focus form, which
is optional and used when the object outranks the subject in obviation; no other extraction is
marked. -/
def realize : ArgumentRole → Finset (Reflex Host)
  | .A => {.morpheme .verb [agentFocusSuffix]}
  | _ => ∅

end Extraction

end Tsotsil
