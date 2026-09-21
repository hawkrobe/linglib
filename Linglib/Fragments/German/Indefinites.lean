import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# German indefinite pronouns

German has indefinite pronouns of two morphological kinds. *Jemand* 'someone', *etwas*
'something' and negative *niemand*, *nichts* are built on generic nouns (*jemand* from *je-man*
'ever-person'); the *irgend-* series, *irgendwer*, *irgendwas*, temporal *je* 'ever' and
*jeder* 'any, every' are built with dedicated markers. *Jemand* runs from the specific
functions to indirect negation. *Irgend-* is excluded where the speaker has the referent in
mind and under direct negation and covers the rest of the map, a distribution it reached from
an earlier non-specific use, as Aloni and Port describe; the two series overlap from specific
unknown to indirect negation. Kratzer and Shimoyama's domain-widening analysis of *irgendein*
is the matter of `German.ModalIndefinites`.

## References

* [aloni-port-2015]
* [haspelmath-1997]
* [kratzer-shimoyama-2002]
-/

namespace German.Indefinites

/-- *Jemand* 'someone', with *etwas* 'something': built on generic nouns, from the specific
functions through questions and conditionals to indirect negation. -/
def jemandEntry : IndefinitePronoun where
  form := "jemand"
  ontology := .person
  basis := .genericNoun

/-- The *irgend-* series, *irgendwer*: built with a dedicated prefix, everywhere on the map but
for a referent the speaker has in mind and under direct negation. -/
def irgendEntry : IndefinitePronoun where
  form := "irgendwer"
  ontology := .person
  basis := .special

/-- Temporal *je* 'ever': questions, conditionals, indirect negation and the comparative. -/
def jeEntry : IndefinitePronoun where
  form := "je"
  ontology := .time
  basis := .special

/-- *Jeder* 'any, every': indirect negation, the comparative and free choice. -/
def jederEntry : IndefinitePronoun where
  form := "jeder"
  ontology := .person
  basis := .special

/-- *Niemand* 'nobody', with *nichts* 'nothing': direct negation. -/
def niemandEntry : IndefinitePronoun where
  form := "niemand"
  ontology := .person
  basis := .genericNoun

/-- The German paradigm. -/
def paradigm : List IndefinitePronoun :=
  [jemandEntry, irgendEntry, jeEntry, jederEntry, niemandEntry]

end German.Indefinites
