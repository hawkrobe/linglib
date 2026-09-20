import Linglib.Syntax.Agreement.Allocutive
import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Korean pronouns and speech-style particles

Korean is discourse-oriented: pronouns are omitted whenever they are recoverable, and reference
to a third party is a demonstrative with a noun for a person, *geu bun* 'that person', *geu ai*
'that child', graded by the deference the noun carries. The overt pronouns are chosen by the
addressee's or referent's age and status relative to the speaker, as Sohn tabulates them: the
first person has the neutral *na* and the humble *jeo*, with the plurals *uri* and *jeohui*;
the second has the plain *neo* for a child or intimate, the familiar *jane*, the blunt
*dangsin*, used to an adult equal or inferior and affectionately between spouses, and the
deferential *taek* to an adult stranger, kinship terms and titles serving a superior; in the
third person *geu* 'he' and *geunyeo* 'she', with the plural *geudeul*, are recent innovations
of written narrative used anaphorically, while the colloquial *gyae*, contracted from *geu ai*,
is neutral for gender and implies familiarity with the referent, as Kwon and Lee describe.
Before the nominative particle *na*, *jeo* and *neo* become *nae*, *je* and *ne*. The
sentence-final speech-style particles *-yo* and *-(seu)mnida* occur in root clauses only. Both
present the addressee as above the speaker, and they differ in the formality of the discourse:
*-yo* is the polite particle of informal speech and *-(seu)mnida* that of formal speech. Forms
are in the Revised Romanization; Sohn writes *na*, *ce*, *wuli*, *ce-huy*, *ne*, *caney*,
*tangsin*, *tayk*, *ku*, *ku nye* and *ku-tul*.

## Main definitions

* `Korean.Pronouns.pronouns` — the personal pronouns
* `Korean.Pronouns.allocutiveParticles` — the speech-style particles

## Implementation notes

The humble first person is chosen by the standing of the addressee. That is neither the
formality of the situation, which a pronoun's register records, nor the level at which a
pronoun presents its own referent, so *jeo* and *jeohui* carry neither value and differ from
*na* and *uri* in form alone.

## References

* [alok-bhalla-2026]
* [kwon-lee-2026]
* [sohn-1994]
* [sohn-1999]
-/

namespace Korean.Pronouns

/-- The neutral first person *na*. -/
def na : PersonalPronoun :=
  { form := "na", script := some "나", person := some .first, number := some .singular }

/-- The humble first person *jeo*, used to a senior or an adult equal where the plain *na* is
used to a child or a younger adult ([sohn-1999]). -/
def jeo : PersonalPronoun :=
  { form := "jeo", script := some "저", person := some .first, number := some .singular }

/-- The neutral first person plural *uri*. -/
def uri : PersonalPronoun :=
  { form := "uri", script := some "우리", person := some .first, number := some .plural }

/-- The humble first person plural *jeohui*. -/
def jeohui : PersonalPronoun :=
  { form := "jeohui", script := some "저희", person := some .first, number := some .plural }

/-- The plain second person *neo*, to a child or an intimate. -/
def neo : PersonalPronoun :=
  { form := "neo", script := some "너", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- The familiar second person *jane*, to an adult or pre-adult inferior. -/
def jane : PersonalPronoun :=
  { form := "jane", script := some "자네", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- The blunt second person *dangsin*, to an adult equal or inferior and between spouses. -/
def dangsin : PersonalPronoun :=
  { form := "dangsin", script := some "당신", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- The deferential second person *taek*, to an adult stranger. -/
def taek : PersonalPronoun :=
  { form := "taek", script := some "댁", person := some .second, number := some .singular,
    honorific := some .honorific }

/-- The written-narrative masculine third person *geu*. -/
def geu : PersonalPronoun :=
  { form := "geu", script := some "그", person := some .third, number := some .singular,
    gender := some .masculine, register := .formal }

/-- The written-narrative feminine third person *geunyeo*. -/
def geunyeo : PersonalPronoun :=
  { form := "geunyeo", script := some "그녀", person := some .third, number := some .singular,
    gender := some .feminine, register := .formal }

/-- The colloquial third person *gyae*, neutral for gender. -/
def gyae : PersonalPronoun :=
  { form := "gyae", script := some "걔", person := some .third, number := some .singular,
    register := .informal }

/-- The written-narrative third person plural *geudeul*. -/
def geudeul : PersonalPronoun :=
  { form := "geudeul", script := some "그들", person := some .third, number := some .plural,
    register := .formal }

/-- The personal pronouns. -/
def pronouns : Finset PersonalPronoun :=
  {na, jeo, uri, jeohui, neo, jane, dangsin, taek, geu, geunyeo, gyae, geudeul}

/-- The polite speech-style particle *-yo*, of informal discourse. -/
def yo : AllocutiveMarker := { form := "-yo", honorific := .honorific, register := .informal }

/-- The speech-style particle *-(seu)mnida*, of formal discourse. -/
def supnida : AllocutiveMarker :=
  { form := "-(seu)mnida", honorific := .honorific, register := .formal }

/-- The speech-style particles. -/
def allocutiveParticles : List AllocutiveMarker := [yo, supnida]

end Korean.Pronouns
