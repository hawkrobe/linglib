import Linglib.Syntax.Agreement.Allocutive
import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Basque pronouns and allocutive markers

Basque has two pronouns for a single addressee, the familiar *hi* and the ordinary *zu*. *Zu*
was once the second person plural and still agrees as one: the verb takes the same plural
marking with *zu* as with *gu* 'we'. The newer plural *zuek* is built on it. The Souletin
dialect has allocutive suffixes on the auxiliary, *-k* and *-n* for a familiar male and female
addressee and *-zü* for an addressee spoken to with respect. The same suffixes serve as ordinary
agreement with a second person subject.

## References

* [laka-1996]
* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

namespace Basque.Pronouns

/-- *ni* — 1sg. -/
def ni : PersonalPronoun := { form := "ni", person := some .first, number := some .singular }

/-- *gu* — 1pl. -/
def gu : PersonalPronoun := { form := "gu", person := some .first, number := some .plural }

/-- *hi* — 2sg familiar. -/
def hi : PersonalPronoun :=
  { form := "hi", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- *Zu* addresses one person and agrees as a second person plural. -/
def zu : PersonalPronoun :=
  { form := "zu", person := some .second, number := some .plural, honorific := some .honorific,
    referential := {.addressee} }

/-- *zuek* — 2pl. -/
def zuek : PersonalPronoun :=
  { form := "zuek", person := some .second, number := some .plural }

/-- *hura* — 3sg. -/
def hura : PersonalPronoun :=
  { form := "hura", person := some .third, number := some .singular }

/-- *haiek* — 3pl. -/
def haiek : PersonalPronoun :=
  { form := "haiek", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun := {ni, gu, hi, zu, zuek, hura, haiek}

/-- *Zu* bears the agreement features of the plural *zuek*. -/
theorem phi_zu : HasPhi.phi zu = HasPhi.phi zuek := by decide

/-- *Zu* denotes a single addressee, as the familiar *hi* does. -/
theorem referential_zu : zu.referential = hi.referential := by decide

/-- *-k* — nonhonorific male addressee. -/
def allocM : AllocutiveMarker :=
  { form := "-k", honorific := .nonhonorific, gender := some .masculine }

/-- *-n* — nonhonorific female addressee. -/
def allocF : AllocutiveMarker :=
  { form := "-n", honorific := .nonhonorific, gender := some .feminine }

/-- *-zü* — honorific addressee. -/
def allocH : AllocutiveMarker := { form := "-zü", honorific := .honorific }

/-- The Souletin allocutive markers. -/
def allocutiveMarkers : List AllocutiveMarker := [allocM, allocF, allocH]

end Basque.Pronouns
