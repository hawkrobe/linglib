import Linglib.Typology.LanguageProfile
import Linglib.Fragments.English.Morph
import Linglib.Fragments.English.Indefinites

/-!
# English typological profile

Aggregate WALS-style typological profile for English (ISO 639-3 `eng`).
WALS-derivable fields (word order Ch 81/82/83, adposition Ch 85) are
pulled via `withWordOrderFromWALS`/`withAdpositionFromWALS`; morphology
is supplied from the Fragment's `morphProfile` (which itself overrides
WALS with hand-coded fallbacks); indefinite-pronoun paradigm is supplied
from the Fragment's `Indefinites.paradigm`.
-/

namespace Fragments.English

open Typology in
/-- English: SVO, prepositional, concatenative + nonflexive morphology,
    generic-noun-based indefinites (someone, somebody, …). -/
def typology : LanguageProfile :=
  LanguageProfile.empty "eng" "English"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile
    |>.withIndefinites Indefinites.paradigm
    |>.withRelativization
        { subjStrategy := .mixed
        , oblStrategy := .mixed
        , rcPosition := .postNominal
        , lowestRelativizable := .objComparison
        , notes := "Gap + relative pronoun; P-stranding allows gap on obliques; "
                ++ "can relativize all AH positions" }

end Fragments.English
