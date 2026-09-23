module

public import Linglib.Syntax.Reciprocal
public import Linglib.Fragments.Swahili.Verbs

/-!
# Swahili reciprocals

Swahili marks reciprocity with the verbal suffix *-an-*, which derives an intransitive verb whose
plural subject names the reciprocants (*Juma na Halima wa-li-tekeny-an-a* 'Juma and Halima tickled
each other', [nordlinger-2023] ex. 12); with a singular subject and a comitative *na* phrase it
forms the discontinuous reciprocal (exx. 37, 40). The suffix is distinct from the reflexive prefix
*ji-*. Some *-an-* verbs have lexicalized reciprocal entries, paired with their binary bases
([palmieri-2024], Appendix C).

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
-/

@[expose] public section

namespace Swahili.Reciprocals

open Reciprocal

def anSuffix : Marker :=
  { form := "-an-", strategy := .verbalAffix }

/-- Marker inventory. -/
def markers : Finset Marker := {anSuffix}

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
