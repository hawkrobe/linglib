import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# German indefinite pronouns

German has indefinite pronouns of two morphological kinds: *jemand* 'someone' and *etwas*
'something', built on generic nouns (*jemand* from *je-man* 'ever-person'), and the *irgend-*
series, *irgendwer*, *irgendwas*, built with a dedicated indefinite prefix. *Jemand* and *etwas*
are used for a referent the speaker has in mind or presupposes; *irgend-* is used for one the
speaker presupposes but cannot identify and for irrealis non-specific reference, a distribution
it reached from an earlier non-specific use, as Aloni and Port describe. Kratzer and Shimoyama's
domain-widening analysis of *irgendein* is the matter of `German.ModalIndefinites`.

## References

* [aloni-port-2015]
* [haspelmath-1997]
* [kratzer-shimoyama-2002]
-/

namespace German.Indefinites

open Indefinite

/-- The *irgend-* series: built with a dedicated prefix, used for a referent the speaker cannot
identify and for irrealis non-specific reference. -/
def irgendEntry : IndefinitePronoun where
  form := "irgend-"
  ontology := .person
  basis := .special
  functions := {.specificUnknown, .irrealis}

/-- *Jemand* 'someone' and *etwas* 'something': built on generic nouns, used for a referent the
speaker has in mind or presupposes. -/
def jemandEntry : IndefinitePronoun where
  form := "jemand/etwas"
  ontology := .person
  basis := .genericNoun
  functions := {.specificKnown, .specificUnknown}

/-- The German paradigm: the dedicated prefix and the generic-noun forms. -/
def paradigm : List IndefinitePronoun := [irgendEntry, jemandEntry]

end German.Indefinites
