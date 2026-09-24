module

public import Linglib.Fragments.Latvian.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Latvian indefinite pronouns

Latvian builds its three indefinite series on the interrogative pronouns: the general
*kaut*-series with the particle *kaut* 'at least, even' (*kaut kas* 'something'), the negative
*ne*-series with the prefix *ne-*, apparently that of verbal negation, with which the series
co-occurs (*Viņu nekas neinteresē* 'Nothing interests him'), and the free-choice *jeb*-series
with *jeb* 'or' (*jebkas* 'anything'). The person row departs from the pattern:
*neviens* 'nobody' is built on the numeral *viens* 'one' and *jebkāds* 'anybody' on the
determiner *kāds*, which is also used bare for 'somebody'. The manner row has no member of the
*jeb*-series.

## Implementation notes

Forms are orthographic: the prefixes are written together with the interrogative (*nekas*),
*kaut* apart from it (*kaut kas*); [haspelmath-1997] hyphenates the prefixes (*ne-kas*). A
member is its series applied to an interrogative of `Latvian.Pronouns`, which derives its form,
category and basis. In the person row *kāds* and *jebkāds* take the person category over the
determiner they are built on, and *neviens*, built on no interrogative, is stated whole.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Latvian.Indefinites

/-! ### The series -/

/-- The *kaut*-series: the particle *kaut* before the interrogative. -/
def kaut : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("kaut " ++ ·)

/-- The *ne*-series: the negative prefix *ne-* on the interrogative. -/
def ne : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("ne" ++ ·)

/-- The *jeb*-series: the prefix *jeb-* on the interrogative. -/
def jeb : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative ("jeb" ++ ·)

/-! ### The person row -/

/-- *kaut kas* 'someone': the *kaut*-series on *kas* 'who'. -/
def kautKas : IndefinitePronoun := kaut Pronouns.kasPerson

/-- *kāds* 'somebody': the interrogative determiner used bare as a person indefinite. -/
def kāds : IndefinitePronoun :=
  { IndefinitePronoun.ofInterrogative id Pronouns.kāds with ontology := .person }

/-- *neviens* 'nobody': *ne-* on the numeral *viens* 'one', in a series otherwise built on the
interrogatives ([haspelmath-1997], §7.5.2). -/
def neviens : IndefinitePronoun :=
  { form := "neviens", ontology := .person, basis := .interrogative }

/-- *jebkāds* 'anybody': the *jeb*-series on the determiner *kāds*. -/
def jebkāds : IndefinitePronoun := { jeb Pronouns.kāds with ontology := .person }

/-! ### The paradigm -/

/-- The *kaut*-series, person to determiner. -/
def kautSeries : List IndefinitePronoun :=
  [kautKas, kāds, kaut Pronouns.kasThing, kaut Pronouns.kur, kaut Pronouns.kad, kaut Pronouns.kā,
    kaut Pronouns.kāds]

/-- The *ne*-series, person to determiner. -/
def neSeries : List IndefinitePronoun :=
  [neviens, ne Pronouns.kasThing, ne Pronouns.kur, ne Pronouns.kad, ne Pronouns.kā,
    ne Pronouns.kāds]

/-- The *jeb*-series, person to determiner. -/
def jebSeries : List IndefinitePronoun :=
  [jebkāds, jeb Pronouns.kasThing, jeb Pronouns.kur, jeb Pronouns.kad, jeb Pronouns.kāds,
    jeb Pronouns.kurš]

end Latvian.Indefinites
