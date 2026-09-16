import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Korean pronouns and speech-style particles

Korean is discourse-oriented, and the unmarked reference to a third party is a null pronoun,
a demonstrative or a full noun phrase such as *geu chingu* 'that friend'. The overt pronouns
divide by register: the first person has the plain *na* and the humble *jeo*, the second the
plain *neo* and the polite *dangsin*; in the third person *geu*, *geunyeo* and the plural
*geudeul* belong to the written language, *geunyeo* a compound of *geu* 'that' and *nyeo*
'female' formed under Western influence, while the colloquial *gyae*, contracted from *geu ai*
'that child', is neutral for gender and implies familiarity with the referent, as Kwon and Lee
describe. The sentence-final speech-style particles *-yo* and *-(su)pnida* encode the
formality of the speaker's relation to the addressee and occur in root clauses only. Forms are
in the Revised Romanization; the Yale forms *ku*, *kunye*, *kyay* appear in the literature.

## Main definitions

* `Korean.Pronouns.pronouns` — the personal pronouns
* `Korean.Pronouns.allocutiveParticles` — the speech-style particles

## References

* [alok-bhalla-2026]
* [kwon-lee-2026]
* [sohn-1999]
-/

namespace Korean.Pronouns

open Pronoun

/-- The plain first person *na*. -/
def na : PersonalPronoun :=
  { form := "na", script := some "나", person := some .first, number := some .singular,
    register := .informal }

/-- The humble first person *jeo*. -/
def jeo : PersonalPronoun :=
  { form := "jeo", script := some "저", person := some .first, number := some .singular,
    register := .formal }

/-- The first person plural *uri*. -/
def uri : PersonalPronoun :=
  { form := "uri", script := some "우리", person := some .first, number := some .plural }

/-- The plain second person *neo*. -/
def neo : PersonalPronoun :=
  { form := "neo", script := some "너", person := some .second, number := some .singular,
    register := .informal }

/-- The polite second person *dangsin*. -/
def dangsin : PersonalPronoun :=
  { form := "dangsin", script := some "당신", person := some .second, number := some .singular,
    register := .formal }

/-- The written-language masculine third person *geu*. -/
def geu : PersonalPronoun :=
  { form := "geu", script := some "그", person := some .third, number := some .singular,
    gender := some .masculine, register := .formal }

/-- The written-language feminine third person *geunyeo*. -/
def geunyeo : PersonalPronoun :=
  { form := "geunyeo", script := some "그녀", person := some .third, number := some .singular,
    gender := some .feminine, register := .formal }

/-- The colloquial third person *gyae*, neutral for gender. -/
def gyae : PersonalPronoun :=
  { form := "gyae", script := some "걔", person := some .third, number := some .singular,
    register := .informal }

/-- The written-language third person plural *geudeul*. -/
def geudeul : PersonalPronoun :=
  { form := "geudeul", script := some "그들", person := some .third, number := some .plural,
    register := .formal }

/-- The personal pronouns. -/
def pronouns : Finset PersonalPronoun :=
  {na, jeo, uri, neo, dangsin, geu, geunyeo, gyae, geudeul}

/-- The polite speech-style particle *-yo*. -/
def yo : AllocutiveEntry := { form := "-yo", register := .neutral, gloss := "POL" }

/-- The formal speech-style particle *-(su)pnida*. -/
def supnida : AllocutiveEntry := { form := "-(su)pnida", register := .formal, gloss := "FORM" }

/-- The speech-style particles. -/
def allocutiveParticles : List AllocutiveEntry := [yo, supnida]

end Korean.Pronouns
