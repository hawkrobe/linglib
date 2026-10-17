module

public import Linglib.Fragments.Slavic.Russian.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Russian indefinite pronouns

Russian builds its indefinite series on the interrogative pronouns *kto* 'who' and *čto* 'what' of
`Russian.Pronouns`: a marker maps each interrogative to an indefinite, and a series collects the
indefinites one marker builds. A series marks the interrogative with a prefix, *koe-* or *ni-*, with
a suffix, *-to*, *-nibud'* or *-libo*, or with a following phrase, *by to ni bylo* or *ugodno*. The
free-choice determiner *ljuboj* 'any' forms a series of its own.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Russian.Indefinites

open Pronouns

/-! ### The markers -/

/-- The *koe-* marker attaches the prefix *koe-* to the interrogative. -/
def koe : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("koe-" ++ ·)

/-- The *-to* marker attaches the suffix *-to* to the interrogative. -/
def to_ : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-to")

/-- The *-nibud'* marker attaches the suffix *-nibud'* to the interrogative. -/
def nibud : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-nibud'")

/-- The *-libo* marker attaches the suffix *-libo* to the interrogative. -/
def libo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-libo")

/-- The *by to ni bylo* marker follows the interrogative with *by to ni bylo*. -/
def byToNiBylo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ " by to ni bylo")

/-- The negative marker attaches the prefix *ni-* to the interrogative. -/
def ni : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("ni" ++ ·)

/-- The *ugodno* marker follows the interrogative with *ugodno* 'pleasing'. -/
def ugodno : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ " ugodno")

/-! ### The person row -/

/-- *koe-kto* 'someone'. -/
def koeKto : IndefinitePronoun := koe kto

/-- *kto-to* 'someone'. -/
def ktoTo : IndefinitePronoun := to_ kto

/-- *kto-nibud'* 'someone, anyone'. -/
def ktoNibud : IndefinitePronoun := nibud kto

/-- *kto-libo* 'anyone'. -/
def ktoLibo : IndefinitePronoun := libo kto

/-- *kto by to ni bylo* 'anyone at all'. -/
def ktoByToNiBylo : IndefinitePronoun := byToNiBylo kto

/-- *nikto* 'nobody'. -/
def nikto : IndefinitePronoun := ni kto

/-- *kto ugodno* 'anyone'. -/
def ktoUgodno : IndefinitePronoun := ugodno kto

/-- *ljuboj* 'any', a free-choice determiner. -/
def ljuboj : IndefinitePronoun := { form := "ljuboj", ontology := .determiner, basis := .special }

/-! ### The series -/

/-- The *koe-* series, *koe-kto* 'someone' and *koe-čto* 'something'. -/
def koeSeries : IndefinitePronoun.Series := ⟨"koe-", [kto, čto].map koe⟩

/-- The *-to* series, *kto-to* 'someone' and *čto-to* 'something'. -/
def toSeries : IndefinitePronoun.Series := ⟨"-to", [kto, čto].map to_⟩

/-- The *-nibud'* series, *kto-nibud'* and *čto-nibud'*. -/
def nibudSeries : IndefinitePronoun.Series := ⟨"-nibud'", [kto, čto].map nibud⟩

/-- The *-libo* series, *kto-libo* and *čto-libo*. -/
def liboSeries : IndefinitePronoun.Series := ⟨"-libo", [kto, čto].map libo⟩

/-- The *by to ni bylo* series, *kto by to ni bylo* and *čto by to ni bylo*. -/
def byToNiByloSeries : IndefinitePronoun.Series :=
  ⟨"by to ni bylo", [kto, čto].map byToNiBylo⟩

/-- The negative series, *nikto* 'nobody' and *ničto* 'nothing'. -/
def niSeries : IndefinitePronoun.Series := ⟨"ni-", [kto, čto].map ni⟩

/-- The *ugodno* series, *kto ugodno* and *čto ugodno*. -/
def ugodnoSeries : IndefinitePronoun.Series := ⟨"ugodno", [kto, čto].map ugodno⟩

/-- The series of the determiner *ljuboj*. -/
def ljubojSeries : IndefinitePronoun.Series := ⟨"ljuboj", [ljuboj]⟩

end Russian.Indefinites
