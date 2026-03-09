import Linglib.Core.Morphology.MorphProfile

/-!
# Quechua (Cusco) Morphological Profile

WALS-derived morphological profile for Quechua (Cusco).
Quechua (Cusco): all fallback (iso=quz absent from morphology chapters). Values based on Quechuan typology — cf. Quechua (Imbabura) in WALS.
-/

namespace Fragments.Quechua

open Core.Morphology in
/-- Quechua (Cusco): all fallback (iso=quz absent from morphology chapters). Values based on Quechuan typology — cf. Quechua (Imbabura) in WALS. -/
def morphProfile : MorphProfile :=
  { language := "Quechua (Cusco)"
  , iso := "quz"
  , fusion := (walsFusion "quz").getD .concatenative
  , exponence := (walsExponence "quz").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "quz").getD .high
  , locus := (walsLocus "quz").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "quz").getD .stronglySuffixing
  , reduplication := (walsReduplication "quz").getD .noProductive
  }

end Fragments.Quechua
