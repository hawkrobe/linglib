import Linglib.Syntax.Agreement.Allocutive
import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Magahi pronouns and allocutive markers

Personal pronouns of Magahi, with a three-level honorific contrast in the
second person (*tõ* / *tũ* / *apne*) and a two-level one in the third
(*okraa* / *unkaa*), and the allocutive agreement suffixes of
[alok-bhalla-2026]'s (2)–(6): composites of the subject's and the
addressee's honorific level (`allocutive`). Allocutive agreement is sourced
from the finiteness phrase and occurs in every finite embedded clause.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

namespace Magahi.Pronouns

/-- *hum* — 1sg. -/
def hum : PersonalPronoun := { form := "hum", person := some .first, number := some .singular }

/-- *hum sab* — 1pl. -/
def humSab : PersonalPronoun :=
  { form := "hum sab", person := some .first, number := some .plural }

/-- *tõ* — 2sg nonhonorific. -/
def toN : PersonalPronoun :=
  { form := "tõ", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- *tũ* — 2sg honorific. -/
def tuN : PersonalPronoun :=
  { form := "tũ", person := some .second, number := some .singular, honorific := some .honorific }

/-- *apne* — 2sg high honorific. -/
def apne : PersonalPronoun :=
  { form := "apne", person := some .second, number := some .singular,
    honorific := some .highHonorific }

/-- *toraa* — 2sg nonhonorific accusative ([alok-bhalla-2026] (39)). -/
def toraa : PersonalPronoun :=
  { form := "toraa", person := some .second, number := some .singular, case_ := some .acc,
    honorific := some .nonhonorific }

/-- *tor* — 2sg nonhonorific genitive ([alok-bhalla-2026] (41)). -/
def tor : PersonalPronoun :=
  { form := "tor", person := some .second, number := some .singular, case_ := some .gen,
    honorific := some .nonhonorific }

/-- *apne-ke* — 2sg high honorific accusative/dative ([alok-bhalla-2026] (40)). -/
def apneKe : PersonalPronoun :=
  { form := "apne-ke", person := some .second, number := some .singular, case_ := some .acc,
    honorific := some .highHonorific }

/-- *i* — 3sg proximal. -/
def iProx : PersonalPronoun := { form := "i", person := some .third, number := some .singular }

/-- *ũ* — 3sg distal. -/
def uN : PersonalPronoun := { form := "ũ", person := some .third, number := some .singular }

/-- *ũ sab* — 3pl distal. -/
def uNSab : PersonalPronoun := { form := "ũ sab", person := some .third, number := some .plural }

/-- *okraa* — 3sg nonhonorific accusative ([alok-bhalla-2026] (44a)). -/
def okraa : PersonalPronoun :=
  { form := "okraa", person := some .third, number := some .singular, case_ := some .acc,
    honorific := some .nonhonorific }

/-- *okar* — 3sg nonhonorific genitive ([alok-bhalla-2026] (45)). -/
def okar : PersonalPronoun :=
  { form := "okar", person := some .third, number := some .singular, case_ := some .gen,
    honorific := some .nonhonorific }

/-- *unkaa* — 3sg honorific accusative/dative ([alok-bhalla-2026] (44b)). -/
def unkaa : PersonalPronoun :=
  { form := "unkaa", person := some .third, number := some .singular, case_ := some .acc,
    honorific := some .honorific }

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {hum, humSab, toN, tuN, apne, toraa, tor, apneKe, iProx, uN, uNSab, okraa, okar, unkaa}

/-- The fused subject/addressee agreement suffix by the subject's and the
    addressee's honorific level; `none` where no form is attested. -/
def allocutive : SocialMeaning.HonorificLevel → SocialMeaning.HonorificLevel → Option String
  | .nonhonorific, .nonhonorific => some "-au"
  | .nonhonorific, .honorific => some "-o"
  | .nonhonorific, .highHonorific => some "-ain"
  | .honorific, .nonhonorific => some "-thu(n)"
  | .highHonorific, .highHonorific => some "-thi(n)"
  | _, _ => none

/-- The allocutive markers of a nonhonorific subject, *-au*, *-o* and *-ain*: one for each
    honorific level of the addressee, read off `allocutive`. -/
def allocutiveMarkers : List AllocutiveMarker :=
  [.nonhonorific, .honorific, .highHonorific].filterMap fun a ↦
    (allocutive .nonhonorific a).map fun form ↦ { form, honorific := a }

end Magahi.Pronouns
