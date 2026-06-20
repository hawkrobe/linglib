import Linglib.Typology.UniversalQuantifier
import Linglib.Fragments.German.Distributives

/-!
# German universal-quantifier inventory

[haslinger-etal-2025-nllt]

German is a **2-form** language: a [+dist] form `jeder` (`jed-`) and a [−dist]
form `alle` (`all-`). The exponents are derived from the existing distributive
Fragment (`Fragments/German/Distributives.lean`) rather than restated.
-/

namespace German

open Typology.UniversalQuantifier

/-- German UQ inventory: 2-form. `distForm`/`nonDistForm` are read off the
distributive Fragment entries (`jederEntry`, `alleEntry`). The survey cites the
forms by their stems `jed-`/`all-`; the Fragment stores the citation forms. -/
def universalQuantifier : UQProfile :=
  { language := "German"
  , family := "Indo-European (Germanic)"
  , systemType := .twoForm
  , distForm := German.Distributives.jederEntry.form
  , nonDistForm := German.Distributives.alleEntry.form
  , source := "[haslinger-etal-2025-nllt] Table 1 (author elicitation)" }

/-- The [+dist] exponent is `jeder`, derived from the distributive Fragment. -/
theorem universalQuantifier_distForm : universalQuantifier.distForm = "jeder" := rfl

/-- The [−dist] exponent is `alle`, derived from the distributive Fragment. -/
theorem universalQuantifier_nonDistForm : universalQuantifier.nonDistForm = "alle" := rfl

end German
