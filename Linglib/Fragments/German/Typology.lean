import Linglib.Typology.LanguageProfile
import Linglib.Fragments.German.Morph
import Linglib.Fragments.German.Indefinites

/-!
# German typological profile

Aggregate WALS-style typological profile for German (ISO 639-3 `deu`).
-/

namespace Fragments.German

open Typology in
/-- German: V2 in main clauses, SOV in embedded; WALS codes Ch 81 as
    `noDominantOrder`. Prepositional. Mixed indefinite bases
    (special *irgend-* + generic-noun *jemand* / *etwas*). -/
def typology : LanguageProfile :=
  LanguageProfile.empty "deu" "German"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile
    |>.withIndefinites Indefinites.paradigm
    |>.withRelativization
        { subjStrategy := .relativePronoun
        , oblStrategy := .relativePronoun
        , rcPosition := .postNominal
        , lowestRelativizable := .objComparison
        , notes := "Relative pronoun der/die/das; all AH positions relativizable" }

end Fragments.German
