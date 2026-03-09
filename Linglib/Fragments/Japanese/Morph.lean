import Linglib.Core.Morphology.MorphProfile

/-!
# Japanese Morphological Profile

WALS-derived morphological profile for Japanese.
Japanese: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 4-5; F23A: dependentMarking; F26A: stronglySuffixing; F27A: fullReduplicationOnly.
-/

namespace Fragments.Japanese

open Core.Morphology in
/-- Japanese: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 4-5; F23A: dependentMarking; F26A: stronglySuffixing; F27A: fullReduplicationOnly. -/
def morphProfile : MorphProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , fusion := (walsFusion "jpn").getD .concatenative
  , exponence := (walsExponence "jpn").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "jpn").getD .moderate
  , locus := (walsLocus "jpn").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "jpn").getD .stronglySuffixing
  , reduplication := (walsReduplication "jpn").getD .noProductive
  , locusClause := walsLocusClause "jpn"
  , locusPossessive := walsLocusPossessive "jpn"
  , wholeLanguageMarking := walsWholeLanguageMarking "jpn"
  , zeroMarkingAP := walsZeroMarkingAP "jpn"
  , caseSyncretism := walsCaseSyncretism "jpn"
  , verbalSyncretism := walsVerbalSyncretism "jpn"
  , tamExponence := walsTAMExponence "jpn"
  , actionNominal := walsActionNominal "jpn"
  , suppletionTA := walsSuppletionTA "jpn"
  , suppletionImperative := walsSuppletionImperative "jpn"
  , verbalNumber := walsVerbalNumber "jpn"
  }

end Fragments.Japanese
