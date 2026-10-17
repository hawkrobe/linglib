module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Latin indefinite pronouns

Latin builds most of its indefinite pronouns on the interrogative *quis*: *quidam*, with the
suffix *-dam*, for a referent the speaker has in mind; *aliquis*, with the prefix *ali-*, for
one the speaker cannot identify, for irrealis non-specific reference and in questions and
conditionals; *quisquam*, with *-quam*, in the negative-polarity functions short of direct
negation; and *quivis*, with *-vis* 'you want' (and *quilibet*, with *-libet* 'it pleases'),
for free choice. The negative series, *nemo* 'nobody' from *ne* and *homo* 'man', is built on
generic nouns and confined to direct negation. In questions and conditionals the bare
interrogative is commoner than *aliquis* where it can lean on *si* or *num*. Each series is
entered with its person member.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Latin.Indefinites

/-- *quidam*, the suffix *-dam* on the interrogative. -/
def quidam : IndefinitePronoun where
  form := "quidam"
  ontology := .person
  basis := .interrogative

/-- *aliquis*, the prefix *ali-* on the interrogative. -/
def aliquis : IndefinitePronoun where
  form := "aliquis"
  ontology := .person
  basis := .interrogative

/-- *quisquam*, the suffix *-quam* on the interrogative. -/
def quisquam : IndefinitePronoun where
  form := "quisquam"
  ontology := .person
  basis := .interrogative

/-- *nemo* 'nobody', the negator on a generic noun. -/
def nemo : IndefinitePronoun where
  form := "nemo"
  ontology := .person
  basis := .genericNoun

/-- *quivis*, the interrogative with *-vis* 'you want'. -/
def quivis : IndefinitePronoun where
  form := "quivis"
  ontology := .person
  basis := .interrogative

/-! ### The series -/

/-- The *-dam* series. -/
def damSeries : IndefinitePronoun.Series := ⟨"-dam", [quidam]⟩

/-- The *ali-* series. -/
def aliSeries : IndefinitePronoun.Series := ⟨"ali-", [aliquis]⟩

/-- The *-quam* series. -/
def quamSeries : IndefinitePronoun.Series := ⟨"-quam", [quisquam]⟩

/-- The negative series of *nemo* and *nihil*. -/
def nSeries : IndefinitePronoun.Series := ⟨"n-", [nemo]⟩

/-- The *-vis* series. -/
def visSeries : IndefinitePronoun.Series := ⟨"-vis", [quivis]⟩

end Latin.Indefinites
