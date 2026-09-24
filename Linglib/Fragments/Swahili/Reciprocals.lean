module

public import Linglib.Syntax.Reciprocal
public import Linglib.Fragments.Swahili.Verbs

/-!
# Swahili reciprocals

This file defines the Swahili reciprocal marker and the verbs it has lexicalized in. Swahili
marks reciprocity with the verbal suffix *-an-*, which derives an intransitive verb whose plural
subject names the reciprocants, *Juma na Halima wa-li-tekeny-an-a* 'Juma and Halima tickled
each other'; with a singular subject and a comitative *na* phrase it forms the discontinuous
reciprocal, *Juma a-li-tekeny-an-a na Halima*, which Nordlinger reviews. The suffix is distinct
from the reflexive prefix *ji-*. Palmieri's appendix pairs the *-an-* verbs with a lexicalized
reciprocal entry with their binary bases, each the base with the suffix before its final vowel.

## Main definitions

* `Swahili.Reciprocals.anSuffix`, `markers`: the marker and the inventory
* `Swahili.Reciprocals.lexicalReciprocals`, `derivedFrom`: the lexical reciprocals and their
  pairing with a binary base

## Main results

* `Swahili.Reciprocals.derivedFrom_form`: each lexical reciprocal is its base with *-an-*
  before the final vowel

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
-/

@[expose] public section

namespace Swahili.Reciprocals

open Reciprocal

/-- The reciprocal suffix *-an-*. -/
def anSuffix : Marker :=
  { form := "-an-", strategy := .verbalAffix }

/-- The marker inventory. -/
def markers : Finset Marker := {anSuffix}

/-- The *-an-* verbs with a lexicalized reciprocal entry. -/
def lexicalReciprocals : List Verb :=
  [Verbs.achana, Verbs.gawana, Verbs.gombana, Verbs.gongana, Verbs.jibizana, Verbs.pambana,
    Verbs.patana, Verbs.pigana, Verbs.shindana]

/-- Each lexical reciprocal with its binary base; *jibizana* has none. -/
def derivedFrom : List (Verb × Verb) :=
  [(Verbs.achana, Verbs.acha), (Verbs.gawana, Verbs.gawa), (Verbs.gombana, Verbs.gomba),
    (Verbs.gongana, Verbs.gonga), (Verbs.pambana, Verbs.pamba), (Verbs.patana, Verbs.pata),
    (Verbs.pigana, Verbs.piga), (Verbs.shindana, Verbs.shinda)]

/-- Each lexical reciprocal is its base with *-an-* before the final vowel. -/
theorem derivedFrom_form :
    ∀ p ∈ derivedFrom, p.1.form.toList = p.2.form.toList.dropLast ++ ['a', 'n', 'a'] := by
  decide

end Swahili.Reciprocals
