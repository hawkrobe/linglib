import Linglib.Typology.UniversalQuantifier
import Linglib.Fragments.English.Determiners

/-!
# English universal-quantifier inventory

[haslinger-etal-2025-nllt]

English is a **2-form** language: distinct [+dist] (`every`, `each`) and [−dist]
(`all`) universal quantifiers. The exponents are derived from the existing
determiner Fragment (`Fragments/English/Determiners.lean`) rather than restated.
-/

namespace English

open Typology.UniversalQuantifier

/-- English UQ inventory: 2-form. `distForm` and `nonDistForm` are read off the
determiner Fragment entries (`every`, `all`); the further [+dist] item `each`
adds an atomicity presupposition (see `Fragments/English/Distributives.lean`). -/
def universalQuantifier : UQProfile :=
  { language := "English"
  , family := "Indo-European (Germanic)"
  , systemType := .twoForm
  , distForm := English.Determiners.every.form
  , nonDistForm := English.Determiners.all.form
  , source := "[haslinger-etal-2025-nllt] Table 1" }

/-- The [+dist] exponent is `every`, derived from the determiner Fragment. -/
theorem universalQuantifier_distForm : universalQuantifier.distForm = "every" := rfl

/-- The [−dist] exponent is `all`, derived from the determiner Fragment. -/
theorem universalQuantifier_nonDistForm : universalQuantifier.nonDistForm = "all" := rfl

end English
