module

public import Linglib.Fragments.Slavic.Russian.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Russian indefinite pronouns

Russian builds its indefinite series on the interrogative pronouns *kto* 'who' and *čto* 'what'
of `Russian.Pronouns`, and each series is here a map from the interrogatives to the indefinites.
A series marks the interrogative with a prefix, *koe-* or *ni-*, with a suffix, *-to*, *-nibud'*
or *-libo*, or with a following phrase, *by to ni bylo* or *ugodno*. The person row gives the
member of each series built on *kto*.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Russian.Indefinites

open Pronouns

/-! ### The series -/

/-- The *koe-* series attaches the prefix *koe-* to the interrogative. -/
def koe : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("koe-" ++ ·)

/-- The *-to* series attaches the suffix *-to* to the interrogative. -/
def to_ : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-to")

/-- The *-nibud'* series attaches the suffix *-nibud'* to the interrogative. -/
def nibud : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-nibud'")

/-- The *-libo* series attaches the suffix *-libo* to the interrogative. -/
def libo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-libo")

/-- The *by to ni bylo* series follows the interrogative with *by to ni bylo*. -/
def byToNiBylo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ " by to ni bylo")

/-- The negative series attaches the prefix *ni-* to the interrogative. -/
def ni : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("ni" ++ ·)

/-- The *ugodno* series follows the interrogative with *ugodno* 'pleasing'. -/
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

end Russian.Indefinites
