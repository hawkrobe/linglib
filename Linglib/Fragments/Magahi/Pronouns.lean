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
  { form := "tõ", person := some .second, number := some .singular, register := .informal }

/-- *tũ* — 2sg honorific. -/
def tuN : PersonalPronoun :=
  { form := "tũ", person := some .second, number := some .singular, register := .neutral }

/-- *apne* — 2sg high honorific. -/
def apne : PersonalPronoun :=
  { form := "apne", person := some .second, number := some .singular, register := .formal }

/-- *toraa* — 2sg nonhonorific accusative ([alok-bhalla-2026] (39)). -/
def toraa : PersonalPronoun :=
  { form := "toraa", person := some .second, number := some .singular, case_ := some .acc,
    register := .informal }

/-- *tor* — 2sg nonhonorific genitive ([alok-bhalla-2026] (41)). -/
def tor : PersonalPronoun :=
  { form := "tor", person := some .second, number := some .singular, case_ := some .gen,
    register := .informal }

/-- *apne-ke* — 2sg high honorific accusative/dative ([alok-bhalla-2026] (40)). -/
def apneKe : PersonalPronoun :=
  { form := "apne-ke", person := some .second, number := some .singular, case_ := some .acc,
    register := .formal }

/-- *i* — 3sg proximal. -/
def iProx : PersonalPronoun := { form := "i", person := some .third, number := some .singular }

/-- *ũ* — 3sg distal. -/
def uN : PersonalPronoun := { form := "ũ", person := some .third, number := some .singular }

/-- *ũ sab* — 3pl distal. -/
def uNSab : PersonalPronoun := { form := "ũ sab", person := some .third, number := some .plural }

/-- *okraa* — 3sg nonhonorific accusative ([alok-bhalla-2026] (44a)). -/
def okraa : PersonalPronoun :=
  { form := "okraa", person := some .third, number := some .singular, case_ := some .acc,
    register := .informal }

/-- *okar* — 3sg nonhonorific genitive ([alok-bhalla-2026] (45)). -/
def okar : PersonalPronoun :=
  { form := "okar", person := some .third, number := some .singular, case_ := some .gen,
    register := .informal }

/-- *unkaa* — 3sg honorific accusative/dative ([alok-bhalla-2026] (44b)). -/
def unkaa : PersonalPronoun :=
  { form := "unkaa", person := some .third, number := some .singular, case_ := some .acc,
    register := .neutral }

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {hum, humSab, toN, tuN, apne, toraa, tor, apneKe, iProx, uN, uNSab, okraa, okar, unkaa}

/-- The fused subject/addressee agreement suffix by the subject's and the
    addressee's honorific level; `none` where no form is attested. -/
def allocutive : SocialMeaning.Register.Level → SocialMeaning.Register.Level → Option String
  | .informal, .informal => some "-au"
  | .informal, .neutral => some "-o"
  | .informal, .formal => some "-ain"
  | .neutral, .informal => some "-thu(n)"
  | .formal, .formal => some "-thi(n)"
  | _, _ => none

/-- The allocutive markers of a nonhonorific subject, *-au*, *-o* and *-ain*: one for each
    honorific level of the addressee, read off `allocutive`. -/
def allocutiveMarkers : List AllocutiveMarker :=
  [.informal, .neutral, .formal].filterMap fun a ↦
    (allocutive .informal a).map fun form ↦ { form, register := a }

end Magahi.Pronouns
