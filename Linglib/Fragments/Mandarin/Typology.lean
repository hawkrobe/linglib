import Linglib.Core.Typology.LanguageProfile
import Linglib.Fragments.Mandarin.Morph

/-!
# Mandarin typological profile

Aggregate WALS-style typological profile for Mandarin (ISO 639-3 `cmn`).
-/

namespace Fragments.Mandarin

open Core.Typology in
/-- Mandarin: SVO, mixed adpositions, mixed headedness. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "cmn" "Mandarin"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile

end Fragments.Mandarin
