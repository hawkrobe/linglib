import Linglib.Syntax.Category.Pronoun.Basic

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
sentence-final speech-style particles *-yo* and *-(seu)mnida* encode the formality of the
speaker's relation to the addressee and occur in root clauses only. Forms are in the Revised
Romanization; Sohn writes *na*, *ce*, *wuli*, *ce-huy*, *ne*, *caney*, *tangsin*, *tayk*, *ku*,
*ku nye* and *ku-tul*.

## Main definitions

* `Korean.Pronouns.pronouns` — the personal pronouns
* `Korean.Pronouns.allocutiveParticles` — the speech-style particles

## References

* [alok-bhalla-2026]
* [kwon-lee-2026]
* [sohn-1994]
-/

namespace Korean.Pronouns

open Pronoun

/-- The neutral first person *na*. -/
def na : PersonalPronoun :=
  { form := "na", script := some "나", person := some .first, number := some .singular }

/-- The humble first person *jeo*. -/
def jeo : PersonalPronoun :=
  { form := "jeo", script := some "저", person := some .first, number := some .singular,
    register := .formal }

/-- The neutral first person plural *uri*. -/
def uri : PersonalPronoun :=
  { form := "uri", script := some "우리", person := some .first, number := some .plural }

/-- The humble first person plural *jeohui*. -/
def jeohui : PersonalPronoun :=
  { form := "jeohui", script := some "저희", person := some .first, number := some .plural,
    register := .formal }

/-- The plain second person *neo*, to a child or an intimate. -/
def neo : PersonalPronoun :=
  { form := "neo", script := some "너", person := some .second, number := some .singular,
    register := .informal }

/-- The familiar second person *jane*, to an adult or pre-adult inferior. -/
def jane : PersonalPronoun :=
  { form := "jane", script := some "자네", person := some .second, number := some .singular,
    register := .informal }

/-- The blunt second person *dangsin*, to an adult equal or inferior and between spouses. -/
def dangsin : PersonalPronoun :=
  { form := "dangsin", script := some "당신", person := some .second, number := some .singular }

/-- The deferential second person *taek*, to an adult stranger. -/
def taek : PersonalPronoun :=
  { form := "taek", script := some "댁", person := some .second, number := some .singular,
    register := .formal }

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

/-- The polite speech-style particle *-yo*. -/
def yo : AllocutiveEntry := { form := "-yo", register := .neutral, gloss := "POL" }

/-- The formal speech-style particle *-(seu)mnida*. -/
def supnida : AllocutiveEntry := { form := "-(seu)mnida", register := .formal, gloss := "FORM" }

/-- The speech-style particles. -/
def allocutiveParticles : List AllocutiveEntry := [yo, supnida]

end Korean.Pronouns
