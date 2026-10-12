module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Punjabi pronouns

Personal pronouns of Punjabi: a two-level honorific contrast in the second
person (*tũ* / *tusii*, the latter also the plural) and the demonstrative
*uh* for both third-person numbers. Punjabi has allocutive agreement with
third-person subjects only ([alok-bhalla-2026], after Kaur 2020); its marker
forms are not recorded here.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

@[expose] public section

namespace Punjabi

/-- The honorific grades of Punjabi pronouns, lowest first. -/
inductive Grade where
  /-- The nonhonorific grade, *tũ*. -/
  | nonhonorific
  /-- The honorific grade, *tusii*. -/
  | honorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- *maiṃ* — 1sg. -/
def maiN : PersonalPronoun := { form := "maiṃ", person := some .first, number := some .singular }

/-- *asiiṃ* — 1pl. -/
def asiiN : PersonalPronoun := { form := "asiiṃ", person := some .first, number := some .plural }

/-- *tũ* — 2sg nonhonorific. -/
def tuN : PersonalPronoun := { form := "tũ", person := some .second, number := some .singular }

/-- *tusii* — 2sg honorific, also 2pl. -/
def tusii : PersonalPronoun := { form := "tusii", person := some .second, number := some .singular }

/-- *uh* — 3sg, the distal demonstrative. -/
def uhSg : PersonalPronoun := { form := "uh", person := some .third, number := some .singular }

/-- *uh* — 3pl, the same form. -/
def uhPl : PersonalPronoun := { form := "uh", person := some .third, number := some .plural }

/-- The second person singular at each grade. -/
def addressee : Grade → PersonalPronoun
  | .nonhonorific => tuN
  | .honorific => tusii

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun := {maiN, asiiN, tuN, tusii, uhSg, uhPl}

end Pronouns

end Punjabi
