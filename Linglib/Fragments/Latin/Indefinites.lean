import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Latin indefinite pronouns

Latin builds its indefinite pronouns on the interrogative *quis*: *aliquis*, with the prefix
*ali-*, is used for a referent the speaker presupposes but cannot identify and for irrealis
non-specific reference, and *quidam*, with the suffix *-dam*, for a referent the speaker has in
mind.

## References

* [bubnov-2026]
* [haspelmath-1997]
-/

namespace Latin.Indefinites

open Indefinite

/-- *Aliquis*: the prefix *ali-* on the interrogative, for a referent the speaker cannot identify
and for irrealis non-specific reference. -/
def aliEntry : IndefinitePronoun where
  form := "aliquis"
  ontology := .person
  basis := .interrogative
  functions := {.specificUnknown, .irrealis}

/-- *Quidam*: the suffix *-dam* on the interrogative, for a referent the speaker has in mind. -/
def damEntry : IndefinitePronoun where
  form := "quidam"
  ontology := .person
  basis := .interrogative
  functions := {.specificKnown}

/-- The Latin paradigm: *aliquis* and *quidam*. -/
def paradigm : IndefiniteParadigm := [aliEntry, damEntry]

end Latin.Indefinites
