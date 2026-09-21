import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Russian indefinite pronouns

Russian builds its indefinite series on the interrogative pronouns *kto* 'who' and *čto*
'what'. Three of them divide the specific functions: *koe-kto*, with the prefix *koe-*, for a
referent the speaker has in mind ("Koe-kto prišël" 'someone, I know who, came'); *kto-to*, with
the suffix *-to*, for one the speaker presupposes but cannot identify ("Kto-to prišël" 'someone
came'); and *kto-nibud'*, with *-nibud'*, for irrealis non-specific reference, in questions and
in conditionals ("Kupi čto-nibud'" 'buy something, anything'). The *-libo* series shares the
functions of *-nibud'* and replaces it under indirect negation and in comparatives, where *kto
by to ni bylo* also occurs; *nikto* is confined to direct negation and *kto ugodno* to free
choice.

## References

* [bubnov-2026]
* [degano-aloni-2025]
* [haspelmath-1997]
-/

namespace Russian.Indefinites

/-- *Koe-kto*: the prefix *koe-* on the interrogative, for a referent the speaker has in mind. -/
def koeEntry : IndefinitePronoun where
  form := "koe-kto"
  ontology := .person
  basis := .interrogative

/-- *Kto-to*: the suffix *-to* on the interrogative, for a referent the speaker presupposes but
cannot identify. -/
def toEntry : IndefinitePronoun where
  form := "kto-to"
  ontology := .person
  basis := .interrogative

/-- *Kto-nibud'*: the suffix *-nibud'* on the interrogative, for irrealis non-specific
reference and in questions and conditionals. -/
def nibudEntry : IndefinitePronoun where
  form := "kto-nibud'"
  ontology := .person
  basis := .interrogative

/-- *Kto-libo*: the functions of *-nibud'*, with indirect negation and the comparative. -/
def liboEntry : IndefinitePronoun where
  form := "kto-libo"
  ontology := .person
  basis := .interrogative

/-- *Kto by to ni bylo*: conditionals, indirect negation and the comparative. -/
def byToNiByloEntry : IndefinitePronoun where
  form := "kto by to ni bylo"
  ontology := .person
  basis := .interrogative

/-- *Nikto* 'nobody': the negative prefix *ni-* on the interrogative, direct negation. -/
def niEntry : IndefinitePronoun where
  form := "nikto"
  ontology := .person
  basis := .interrogative

/-- *Kto ugodno* 'anyone': the interrogative with *ugodno* 'pleasing', free choice. -/
def ugodnoEntry : IndefinitePronoun where
  form := "kto ugodno"
  ontology := .person
  basis := .interrogative

/-- The Russian paradigm. -/
def paradigm : List IndefinitePronoun :=
  [koeEntry, toEntry, nibudEntry, liboEntry, byToNiByloEntry, niEntry, ugodnoEntry]

end Russian.Indefinites
