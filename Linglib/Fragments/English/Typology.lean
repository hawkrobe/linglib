import Linglib.Core.Typology.LanguageProfile
import Linglib.Fragments.English.Morph

/-!
# English typological profile

Aggregate WALS-style typological profile for English (ISO 639-3 `eng`).
WALS-derivable fields (word order Ch 81/82/83, adposition Ch 85) are
pulled via `withWordOrderFromWALS`/`withAdpositionFromWALS`; morphology
is supplied from the Fragment's `morphProfile` (which itself overrides
WALS with hand-coded fallbacks).
-/

namespace Fragments.English

open Core.Typology in
/-- English: SVO, prepositional, concatenative + nonflexive morphology. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "eng" "English"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile

end Fragments.English
