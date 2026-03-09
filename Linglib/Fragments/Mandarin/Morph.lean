import Linglib.Core.Morphology.MorphProfile

/-!
# Mandarin Chinese Morphological Profile

WALS-derived morphological profile for Mandarin Chinese.
Mandarin Chinese: F20A: isolatingConcatenative (fallback isolating); F21A: monoexponentialCase; F22A: 0-1; F23A: dependentMarking; F26A: stronglySuffixing; F27A: productiveFull.
-/

namespace Fragments.Mandarin

open Core.Morphology in
/-- Mandarin Chinese: F20A: isolatingConcatenative (fallback isolating); F21A: monoexponentialCase; F22A: 0-1; F23A: dependentMarking; F26A: stronglySuffixing; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , fusion := (walsFusion "cmn").getD .isolating
  , exponence := (walsExponence "cmn").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "cmn").getD .moderate
  , locus := (walsLocus "cmn").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "cmn").getD .stronglySuffixing
  , reduplication := (walsReduplication "cmn").getD .noProductive
  , locusClause := walsLocusClause "cmn"
  , locusPossessive := walsLocusPossessive "cmn"
  , wholeLanguageMarking := walsWholeLanguageMarking "cmn"
  , zeroMarkingAP := walsZeroMarkingAP "cmn"
  , caseSyncretism := walsCaseSyncretism "cmn"
  , verbalSyncretism := walsVerbalSyncretism "cmn"
  , tamExponence := walsTAMExponence "cmn"
  , actionNominal := walsActionNominal "cmn"
  , suppletionTA := walsSuppletionTA "cmn"
  , suppletionImperative := walsSuppletionImperative "cmn"
  , verbalNumber := walsVerbalNumber "cmn"
  }

end Fragments.Mandarin
