module

public import Linglib.Syntax.Agreement.Allocutive
public import Linglib.Syntax.Category.Pronoun.Personal

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

@[expose] public section

namespace Basque

/-- The honorific grades of Basque pronouns and allocutive markers, lowest first. -/
inductive Grade where
  /-- The familiar grade, *hi*. -/
  | familiar
  /-- The polite grade, *zu*. -/
  | polite
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *ni* — 1sg. -/
def ni : PersonalPronoun Grade :=
  { form := "ni", person := some .first, number := some .singular }

/-- *gu* — 1pl. -/
def gu : PersonalPronoun Grade :=
  { form := "gu", person := some .first, number := some .plural }

/-- *hi* — 2sg familiar. -/
def hi : PersonalPronoun Grade :=
  { form := "hi", person := some .second, number := some .singular,
    grades := {.familiar} }

/-- *Zu* addresses one person and agrees as a second person plural. -/
def zu : PersonalPronoun Grade :=
  { form := "zu", person := some .second, number := some .plural, grades := {.polite},
    referential := {.addressee} }

/-- *zuek* — 2pl. -/
def zuek : PersonalPronoun Grade :=
  { form := "zuek", person := some .second, number := some .plural }

/-- *hura* — 3sg. -/
def hura : PersonalPronoun Grade :=
  { form := "hura", person := some .third, number := some .singular }

/-- *haiek* — 3pl. -/
def haiek : PersonalPronoun Grade :=
  { form := "haiek", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : Finset (PersonalPronoun Grade) := {ni, gu, hi, zu, zuek, hura, haiek}

/-- *Zu* bears the agreement features of the plural *zuek*. -/
theorem phi_zu : HasPhi.phi zu = HasPhi.phi zuek := by decide

/-- *Zu* denotes a single addressee, as the familiar *hi* does. -/
theorem referential_zu : zu.referential = hi.referential := by decide

/-- *-k* — nonhonorific male addressee. -/
def allocM : AllocutiveMarker Grade :=
  { form := "-k", grade := .familiar, gender := some .masculine }

/-- *-n* — nonhonorific female addressee. -/
def allocF : AllocutiveMarker Grade :=
  { form := "-n", grade := .familiar, gender := some .feminine }

/-- *-zü* — honorific addressee. -/
def allocH : AllocutiveMarker Grade := { form := "-zü", grade := .polite }

/-- The Souletin allocutive markers. -/
def allocutiveMarkers : List (AllocutiveMarker Grade) := [allocM, allocF, allocH]

end Pronouns

end Basque
