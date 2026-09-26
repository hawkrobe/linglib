module

public import Linglib.Fragments.Slavic.Russian.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Russian indefinite pronouns

Russian builds its indefinite series on the interrogative pronouns *kto* 'who' and *čto*
'what' of `Russian.Pronouns`, and each series is here a map from the interrogatives to the
indefinites. Three of them divide the specific functions: *koe-kto*, with the prefix *koe-*, for a
referent the speaker has in mind ("Koe-kto prišël" 'someone, I know who, came'); *kto-to*, with
the suffix *-to*, mainly for one the speaker presupposes but cannot identify ("Kto-to prišël"
'someone came'), though not excluded from non-specific uses; and *kto-nibud'*, with *-nibud'*,
for irrealis non-specific reference, in questions and in conditionals ("Kupi čto-nibud'" 'buy
something, anything'). The *-libo* series shares the functions of *-nibud'* and replaces it
under indirect negation and in comparatives, where *kto by to ni bylo* also occurs; *nikto* is
confined to direct negation and *kto ugodno* to free choice.

## References

* [bubnov-2026]
* [degano-aloni-2025]
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

/-- *koe-kto* 'someone', for a referent the speaker has in mind. -/
def koeKto : IndefinitePronoun := koe kto

/-- *kto-to* 'someone', mainly for a referent the speaker presupposes but cannot identify. -/
def ktoTo : IndefinitePronoun := to_ kto

/-- *kto-nibud'* 'someone, anyone', for irrealis non-specific reference and in questions and
conditionals. -/
def ktoNibud : IndefinitePronoun := nibud kto

/-- *kto-libo* 'anyone', with the functions of *kto-nibud'* and under indirect negation and in
comparatives. -/
def ktoLibo : IndefinitePronoun := libo kto

/-- *kto by to ni bylo* 'anyone at all', in conditionals, under indirect negation and in
comparatives. -/
def ktoByToNiBylo : IndefinitePronoun := byToNiBylo kto

/-- *nikto* 'nobody', under direct negation. -/
def nikto : IndefinitePronoun := ni kto

/-- *kto ugodno* 'anyone', of free choice. -/
def ktoUgodno : IndefinitePronoun := ugodno kto

/-- The person row of the series. -/
def paradigm : List IndefinitePronoun :=
  [koeKto, ktoTo, ktoNibud, ktoLibo, ktoByToNiBylo, nikto, ktoUgodno]

end Russian.Indefinites
