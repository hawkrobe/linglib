import Linglib.Typology.LanguageProfile

/-!
# Finnish typological profile

Aggregate WALS-style typological profile for Finnish (ISO 639-3 `fin`).
-/

namespace Fragments.Finnish

open Typology in
/-- Finnish: SVO, postpositional, agglutinative; declined relative pronoun. -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "fin" "Finnish"
    |>.withRelativization
        { subjStrategy := .relativePronoun
        , oblStrategy := .relativePronoun
        , rcPosition := .postNominal
        , lowestRelativizable := .oblique
        , notes := "Rel pronoun joka (declines for case); post-nominal RC" }

end Fragments.Finnish
