import Linglib.Syntax.Reciprocal
import Linglib.Fragments.Swahili.Verbs

/-!
# Swahili reciprocals

Swahili marks reciprocity with the verbal suffix *-an-*, which derives an intransitive verb whose
plural subject names the reciprocants (*Juma na Halima wa-li-tekeny-an-a* 'Juma and Halima
tickled each other', [nordlinger-2023] ex. 12); with a singular subject and a comitative *na*
phrase it forms the discontinuous reciprocal (exx. 37, 40). The suffix is distinct from the
reflexive prefix *ji-*, so Swahili is the non-reflexive type of [maslova-nedjalkov-2013]. Some
*-an-* verbs have lexicalized reciprocal entries, paired with their binary bases
([palmieri-2024], Appendix C).

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [E. Maslova and V. P. Nedjalkov, *Reciprocal Constructions* (2013)][maslova-nedjalkov-2013]
* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
-/

namespace Swahili.Reciprocals

open Reciprocal

def anSuffix : Marker :=
  { form := "-an-", strategy := .verbalAffix }

/-- Marker inventory. -/
def markers : Finset Marker := {anSuffix}

/-- The inventory computes the WALS value of Swahili ([maslova-nedjalkov-2013]). -/
theorem ofInventory_markers_eq_wals :
    some (ofInventory markers) = (Data.WALS.F106A.lookupISO "swh").map (·.value) := by
  decide +kernel

/-- The *-an-* verbs with lexicalized reciprocal entries ([palmieri-2024],
    Appendix C), referenced as ordinary verb entries. -/
def lexicalReciprocals : List Verb :=
  [Verbs.achana, Verbs.gawana, Verbs.gombana,
   Verbs.gongana, Verbs.jibizana, Verbs.pambana,
   Verbs.patana, Verbs.pigana, Verbs.shindana]

/-- Derivational pairing of each lexical reciprocal with its binary base
    ([palmieri-2024], Appendix C). *jibizana* is absent: it has no
    binary base (\**jibiza*). -/
def derivedFrom : List (Verb × Verb) :=
  [(Verbs.achana, Verbs.acha), (Verbs.gawana, Verbs.gawa),
   (Verbs.gombana, Verbs.gomba), (Verbs.gongana, Verbs.gonga),
   (Verbs.pambana, Verbs.pamba), (Verbs.patana, Verbs.pata),
   (Verbs.pigana, Verbs.piga), (Verbs.shindana, Verbs.shinda)]

end Swahili.Reciprocals
