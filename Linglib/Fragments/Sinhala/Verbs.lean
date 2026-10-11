module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Sinhala verbs

A Colloquial Sinhala verb root occurs in a volitive stem, an involitive stem, or both. Involitive
stems have front root vowels and the thematic vowel *-e-* in the present tense, while volitive
stems take *-a-* or *-i-*. Subjects of volitives tend to be read as volitional, and involitives
always convey non-volitionality, unexpectedness to the speaker or ironic denial. A root that
requires volition, as *minimarannə* 'murder' does, has no involitive stem, and a psych verb such
as *ridennə* 'ache' has no volitive one. Some causative roots also have an intransitive
inchoative, which is always involitive, as *gilannə* 'drown' has *Nimal giluna* 'Nimal drowned'.

The entries are the roots whose anticausatives Beavers and Zubair analyze. An entry is cited by
its volitive infinitive, records its involitive infinitive where it has one, and has an
intransitive diathesis with the patient as subject when the root has an inchoative.

## Implementation notes

Forms are transliterated as printed in Beavers and Zubair, whose PDF text layer drops *ə*. They
give the involitives of *kapannə* 'cut' and *vinaashə-kərannə* 'destroy' only in the past,
*kæpuna* and *vinaashə-wuna*. The infinitives *kæpennə* and *vinaashə-wennə* follow their stem
formation, in which a compound's volitive *-kərə-* 'do' pairs with the involitive *-we-*.

## References

* [J. Beavers and C. Zubair, *Anticausatives in Sinhala: Involitivity and causer suppression*
  (2013)][beavers-zubair-2013]
-/

@[expose] public section

namespace Sinhala

/-- A Sinhala verb is cited by its volitive infinitive and records its involitive infinitive
when the root has an involitive stem. -/
structure Verb extends _root_.Verb where
  /-- The involitive infinitive, if the root has an involitive stem. -/
  involitive : Option String := none

/-- A verb has an involitive stem when it records an involitive infinitive. -/
def Verb.HasInvolitive (v : Verb) : Prop := v.involitive.isSome

instance : DecidablePred Verb.HasInvolitive := fun v ↦
  inferInstanceAs (Decidable (v.involitive.isSome = true))

/-- *kadannə* 'break' has the involitive *kædennə* and an inchoative, as in
*Eewa okkomə ibeemə kædenəwa* 'They all just break by themselves'. -/
def kadann : Verb where
  morphs := [.root "kadannə"]
  involitive := some "kædennə"
  valency := .of [(.np, [0, 1]), (.intransitive, [1])]

/-- *gilannə* 'drown' has the involitive *gilennə* and an inchoative, as in *Nimal giluna*
'Nimal drowned'. -/
def gilann : Verb where
  morphs := [.root "gilannə"]
  involitive := some "gilennə"
  valency := .of [(.np, [0, 1]), (.intransitive, [1])]

/-- *marannə* 'kill' has the involitive *mærennə* 'die', which occurs only intransitively, as in
*Nimal mæruna* 'Nimal died'. -/
def marann : Verb where
  morphs := [.root "marannə"]
  involitive := some "mærennə"
  valency := .of [(.np, [0, 1]), (.intransitive, [1])]

/-- *minimarannə* 'murder' requires volition and so has neither an involitive stem nor an
inchoative. -/
def minimarann : Verb where
  morphs := [.root "minimarannə"]
  valency := .ofFrame .np

/-- *kapannə* 'cut' has an involitive stem, as in *Joon atiŋ pan kæpuna* 'John cut the bread
(accidentally)', but no inchoative. -/
def kapann : Verb where
  morphs := [.root "kapannə"]
  involitive := some "kæpennə"
  valency := .ofFrame .np

/-- *vinaashə-kərannə* 'destroy' has the involitive *vinaashə-wennə* and, unlike English
*destroy*, an inchoative. -/
def vinaashKarann : Verb where
  morphs := [.root "vinaashə-kərannə"]
  involitive := some "vinaashə-wennə"
  valency := .of [(.np, [0, 1]), (.intransitive, [1])]

/-- The verbs of this file. -/
def verbs : List Verb := [kadann, gilann, marann, minimarann, kapann, vinaashKarann]

end Sinhala
