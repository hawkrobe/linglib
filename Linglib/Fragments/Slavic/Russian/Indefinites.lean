import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Russian indefinite pronouns

Russian builds three indefinite series on the interrogative pronouns *kto* 'who' and *čto*
'what': *koe-kto*, with the prefix *koe-*, for a referent the speaker has in mind ("Koe-kto
prišël" 'someone, I know who, came'); *kto-to*, with the suffix *-to*, for one the speaker
presupposes but cannot identify ("Kto-to prišël" 'someone came'); and *kto-nibud'*, with the
suffix *-nibud'*, for irrealis non-specific reference in imperatives, questions and other
irrealis clauses ("Kupi čto-nibud'" 'buy something, anything'). Each series has a function of
its own.

## References

* [bubnov-2026]
* [degano-aloni-2025]
* [haspelmath-1997]
-/

namespace Russian.Indefinites

open Indefinite

/-- *Kto-nibud'*: the suffix *-nibud'* on the interrogative, for irrealis non-specific
reference. -/
def nibudEntry : IndefinitePronoun where
  form := "kto-nibud'"
  ontology := .person
  basis := .interrogative
  functions := {.irrealis}

/-- *Kto-to*: the suffix *-to* on the interrogative, for a referent the speaker presupposes but
cannot identify. -/
def toEntry : IndefinitePronoun where
  form := "kto-to"
  ontology := .person
  basis := .interrogative
  functions := {.specificUnknown}

/-- *Koe-kto*: the prefix *koe-* on the interrogative, for a referent the speaker has in mind. -/
def koeEntry : IndefinitePronoun where
  form := "koe-kto"
  ontology := .person
  basis := .interrogative
  functions := {.specificKnown}

/-- The Russian paradigm: three series for the three specific functions. -/
def paradigm : List IndefinitePronoun := [nibudEntry, toEntry, koeEntry]

end Russian.Indefinites
