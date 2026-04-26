import Linglib.Core.Typology.LanguageProfile

/-!
# Russian typological profile

Aggregate WALS-style typological profile for Russian (ISO 639-3 `rus`).
-/

namespace Fragments.Slavic.Russian

open Core.Typology in
/-- Russian: SVO, prepositional, declined relative pronoun *kotoryj*. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "rus" "Russian"
    |>.withRelativization
        { subjStrategy := .relativePronoun
        , oblStrategy := .relativePronoun
        , rcPosition := .postNominal
        , lowestRelativizable := .objComparison
        , notes := "Rel pronoun kotoryj (declines); all AH positions" }

end Fragments.Slavic.Russian
