module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# German indefinite pronouns

German has indefinite pronouns of two morphological kinds. *Jemand* 'someone', *etwas*
'something' and negative *niemand*, *nichts* are built on generic nouns (*jemand* from *je-man*
'ever-person'); the *irgend-* series, *irgendwer*, *irgendwas*, temporal *je* 'ever' and
*jeder* 'any, every' are built with dedicated markers. *Jemand* runs from the specific
functions to indirect negation. *Irgend-* is excluded where the speaker has the referent in
mind and under direct negation and covers the rest of the map, a distribution it reached from
an earlier non-specific use, as Aloni and Port describe; the two series overlap from specific
unknown to indirect negation. The determiner *irgendein* is `German.PolarityItems.irgendein`.
Each series is entered with its person member, *je* with its temporal one, and named as
Haspelmath names it.

## References

* [aloni-port-2015]
* [haspelmath-1997]
* [kratzer-shimoyama-2002]
-/

@[expose] public section

namespace German.Indefinites

/-- *jemand* 'someone', built on a generic noun. -/
def jemand : IndefinitePronoun where
  form := "jemand"
  ontology := .person
  basis := .genericNoun

/-- *irgendwer*, built with the dedicated prefix *irgend-*. -/
def irgendwer : IndefinitePronoun where
  form := "irgendwer"
  ontology := .person
  basis := .special

/-- Temporal *je* 'ever'. -/
def je : IndefinitePronoun where
  form := "je"
  ontology := .time
  basis := .special

/-- *jeder* 'any, every'. -/
def jeder : IndefinitePronoun where
  form := "jeder"
  ontology := .person
  basis := .special

/-- *niemand* 'nobody', built on a generic noun. -/
def niemand : IndefinitePronoun where
  form := "niemand"
  ontology := .person
  basis := .genericNoun

/-! ### The series -/

/-- The series of *jemand* and *etwas*, which Haspelmath names the *etwas-* series. -/
def etwasSeries : IndefinitePronoun.Series := ⟨"etwas-", [jemand]⟩

/-- The *irgend-* series. -/
def irgendSeries : IndefinitePronoun.Series := ⟨"irgend-", [irgendwer]⟩

/-- The series of temporal *je*. -/
def jeSeries : IndefinitePronoun.Series := ⟨"je", [je]⟩

/-- The series of *jeder*. -/
def jederSeries : IndefinitePronoun.Series := ⟨"jeder", [jeder]⟩

/-- The negative *n-* series of *niemand* and *nichts*. -/
def nSeries : IndefinitePronoun.Series := ⟨"n-", [niemand]⟩

end German.Indefinites
