import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Latin indefinite pronouns

Latin builds most of its indefinite pronouns on the interrogative *quis*: *quidam*, with the
suffix *-dam*, for a referent the speaker has in mind; *aliquis*, with the prefix *ali-*, for
one the speaker cannot identify, for irrealis non-specific reference and in questions and
conditionals; *quisquam*, with *-quam*, in the negative-polarity functions short of direct
negation; and *quivis*, with *-vis* 'you want' (and *quilibet*, with *-libet* 'it pleases'),
for free choice. The negative series, *nemo* 'nobody' from *ne* and *homo* 'man', is built on
generic nouns and confined to direct negation. In questions and conditionals the bare
interrogative is commoner than *aliquis* where it can lean on *si* or *num*.

## References

* [haspelmath-1997]
-/

namespace Latin.Indefinites

/-- *Quidam*: the suffix *-dam* on the interrogative, for a referent the speaker has in mind. -/
def damEntry : IndefinitePronoun where
  form := "quidam"
  ontology := .person
  basis := .interrogative

/-- *Aliquis*: the prefix *ali-* on the interrogative, for a referent the speaker cannot
identify, for irrealis non-specific reference and in questions and conditionals. -/
def aliEntry : IndefinitePronoun where
  form := "aliquis"
  ontology := .person
  basis := .interrogative

/-- *Quisquam*: the suffix *-quam* on the interrogative, in questions, conditionals and
comparatives and under indirect negation. -/
def quamEntry : IndefinitePronoun where
  form := "quisquam"
  ontology := .person
  basis := .interrogative

/-- *Nemo* 'nobody', with *nihil* 'nothing': the negator on a generic noun, direct negation. -/
def nemoEntry : IndefinitePronoun where
  form := "nemo"
  ontology := .person
  basis := .genericNoun

/-- *Quivis*, with *quilibet*: the interrogative with *-vis* 'you want', free choice. -/
def visEntry : IndefinitePronoun where
  form := "quivis"
  ontology := .person
  basis := .interrogative

/-- The Latin paradigm. -/
def paradigm : List IndefinitePronoun := [damEntry, aliEntry, quamEntry, nemoEntry, visEntry]

end Latin.Indefinites
