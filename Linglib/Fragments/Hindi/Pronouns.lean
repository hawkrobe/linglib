import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Hindi pronouns

Personal pronouns of Hindi: a three-level honorific contrast in the second
person (*tuu* / *tum* / *aap*) and demonstrative-based third-person forms
(*vah* / *ve*). Hindi has no allocutive agreement; an honorific subject
co-opts plural verb agreement ([alok-bhalla-2026] (48)).
-/

namespace Hindi.Pronouns

open Pronoun

/-- *maiṃ* — 1sg. -/
def maiN : PersonalPronoun := { form := "maiṃ", person := some .first, number := some .singular }

/-- *ham* — 1pl. -/
def ham : PersonalPronoun := { form := "ham", person := some .first, number := some .plural }

/-- *tuu* — 2sg nonhonorific. -/
def tuu : PersonalPronoun :=
  { form := "tuu", person := some .second, number := some .singular, register := .informal }

/-- *tum* — 2sg honorific. -/
def tum : PersonalPronoun :=
  { form := "tum", person := some .second, number := some .singular, register := .neutral }

/-- *aap* — 2sg high honorific. -/
def aap : PersonalPronoun :=
  { form := "aap", person := some .second, number := some .singular, register := .formal }

/-- *vah* — 3sg, the distal demonstrative. -/
def vah : PersonalPronoun := { form := "vah", person := some .third, number := some .singular }

/-- *ve* — 3pl, the distal demonstrative plural. -/
def ve : PersonalPronoun := { form := "ve", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : List PersonalPronoun := [maiN, ham, tuu, tum, aap, vah, ve]

end Hindi.Pronouns
