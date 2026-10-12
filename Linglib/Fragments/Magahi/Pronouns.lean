module

public import Linglib.Syntax.Agreement.Allocutive
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Magahi pronouns and allocutive markers

Personal pronouns of Magahi, with three honorific grades in the second person (*tõ* / *tũ* /
*apne*) and two in the third (*okraa* / *unkaa*), and the allocutive agreement suffixes of Alok
and Bhalla's (2)–(6): composites of the subject's and the addressee's honorific grade
(`allocutive`). Allocutive agreement is sourced from the finiteness phrase and occurs in every
finite embedded clause.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

@[expose] public section

namespace Magahi

/-- The honorific grades of Magahi, lowest first. -/
inductive Grade where
  /-- The nonhonorific grade, *tõ*. -/
  | nonhonorific
  /-- The honorific grade, *tũ*. -/
  | honorific
  /-- The high honorific grade, *apne*. -/
  | highHonorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *hum* — 1sg. -/
def hum : PersonalPronoun Grade :=
  { form := "hum", person := some .first, number := some .singular }

/-- *hum sab* — 1pl. -/
def humSab : PersonalPronoun Grade :=
  { form := "hum sab", person := some .first, number := some .plural }

/-- *tõ* — 2sg nonhonorific. -/
def toN : PersonalPronoun Grade :=
  { form := "tõ", person := some .second, number := some .singular,
    grades := {.nonhonorific} }

/-- *tũ* — 2sg honorific. -/
def tuN : PersonalPronoun Grade :=
  { form := "tũ", person := some .second, number := some .singular, grades := {.honorific} }

/-- *apne* — 2sg high honorific. -/
def apne : PersonalPronoun Grade :=
  { form := "apne", person := some .second, number := some .singular,
    grades := {.highHonorific} }

/-- *toraa* — 2sg nonhonorific accusative ([alok-bhalla-2026] (39)). -/
def toraa : PersonalPronoun Grade :=
  { form := "toraa", person := some .second, number := some .singular, case_ := some .acc,
    grades := {.nonhonorific} }

/-- *tor* — 2sg nonhonorific genitive ([alok-bhalla-2026] (41)). -/
def tor : PersonalPronoun Grade :=
  { form := "tor", person := some .second, number := some .singular, case_ := some .gen,
    grades := {.nonhonorific} }

/-- *apne-ke* — 2sg high honorific accusative/dative ([alok-bhalla-2026] (40)). -/
def apneKe : PersonalPronoun Grade :=
  { form := "apne-ke", person := some .second, number := some .singular, case_ := some .acc,
    grades := {.highHonorific} }

/-- *i* — 3sg proximal. -/
def iProx : PersonalPronoun Grade :=
  { form := "i", person := some .third, number := some .singular }

/-- *ũ* — 3sg distal. -/
def uN : PersonalPronoun Grade := { form := "ũ", person := some .third, number := some .singular }

/-- *ũ sab* — 3pl distal. -/
def uNSab : PersonalPronoun Grade :=
  { form := "ũ sab", person := some .third, number := some .plural }

/-- *okraa* — 3sg nonhonorific accusative ([alok-bhalla-2026] (44a)). -/
def okraa : PersonalPronoun Grade :=
  { form := "okraa", person := some .third, number := some .singular, case_ := some .acc,
    grades := {.nonhonorific} }

/-- *okar* — 3sg nonhonorific genitive ([alok-bhalla-2026] (45)). -/
def okar : PersonalPronoun Grade :=
  { form := "okar", person := some .third, number := some .singular, case_ := some .gen,
    grades := {.nonhonorific} }

/-- *unkaa* — 3sg honorific accusative/dative ([alok-bhalla-2026] (44b)). -/
def unkaa : PersonalPronoun Grade :=
  { form := "unkaa", person := some .third, number := some .singular, case_ := some .acc,
    grades := {.honorific} }

/-- The pronoun inventory. -/
def pronouns : Finset (PersonalPronoun Grade) :=
  {hum, humSab, toN, tuN, apne, toraa, tor, apneKe, iProx, uN, uNSab, okraa, okar, unkaa}

/-- The fused subject/addressee agreement suffix by the subject's and the
    addressee's honorific grade; `none` where no form is attested. -/
def allocutive : Grade → Grade → Option String
  | .nonhonorific, .nonhonorific => some "-au"
  | .nonhonorific, .honorific => some "-o"
  | .nonhonorific, .highHonorific => some "-ain"
  | .honorific, .nonhonorific => some "-thu(n)"
  | .highHonorific, .highHonorific => some "-thi(n)"
  | _, _ => none

/-- The allocutive markers of a nonhonorific subject, *-au*, *-o* and *-ain*: one for each
    honorific grade of the addressee, read off `allocutive`. -/
def allocutiveMarkers : List (AllocutiveMarker Grade) :=
  [.nonhonorific, .honorific, .highHonorific].filterMap fun a ↦
    (allocutive .nonhonorific a).map fun form ↦ { form, grade := a }

end Pronouns

end Magahi
