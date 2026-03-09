import Linglib.Core.Morphology.MorphProfile

/-!
# Swahili Morphological Profile

WALS-derived morphological profile for Swahili.
Swahili: F20A: exclusivelyConcatenative; F21A: noCase (fallback monoexponential); F22A: 4-5 (moderate); F23A: headMarking; F26A: weaklyPrefixing; F27A: productiveFull.
-/

namespace Fragments.Swahili

open Core.Morphology in
/-- Swahili: F20A: exclusivelyConcatenative; F21A: noCase (fallback monoexponential); F22A: 4-5 (moderate); F23A: headMarking; F26A: weaklyPrefixing; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Swahili"
  , iso := "swh"
  , fusion := (walsFusion "swh").getD .concatenative
  , exponence := (walsExponence "swh").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "swh").getD .moderate
  , locus := (walsLocus "swh").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "swh").getD .stronglySuffixing
  , reduplication := (walsReduplication "swh").getD .noProductive
  , locusClause := walsLocusClause "swh"
  , locusPossessive := walsLocusPossessive "swh"
  , wholeLanguageMarking := walsWholeLanguageMarking "swh"
  , zeroMarkingAP := walsZeroMarkingAP "swh"
  , caseSyncretism := walsCaseSyncretism "swh"
  , verbalSyncretism := walsVerbalSyncretism "swh"
  , tamExponence := walsTAMExponence "swh"
  , actionNominal := walsActionNominal "swh"
  , suppletionTA := walsSuppletionTA "swh"
  , suppletionImperative := walsSuppletionImperative "swh"
  , verbalNumber := walsVerbalNumber "swh"
  }

end Fragments.Swahili
