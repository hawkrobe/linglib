import Linglib.Core.Typology.LanguageProfile
import Linglib.Fragments.German.Morph

/-!
# German typological profile

Aggregate WALS-style typological profile for German (ISO 639-3 `deu`).
-/

namespace Fragments.German

open Core.Typology in
/-- German: V2 in main clauses, SOV in embedded; WALS codes Ch 81 as
    `noDominantOrder`. Prepositional. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "deu" "German"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile
    |>.withRelativization
        { subjStrategy := .relativePronoun
        , oblStrategy := .relativePronoun
        , rcPosition := .postNominal
        , lowestRelativizable := .objComparison
        , notes := "Relative pronoun der/die/das; all AH positions relativizable" }

end Fragments.German
