import Linglib.Core.Morphology.MorphProfile

/-!
# Indonesian Morphological Profile

WALS-derived morphological profile for Indonesian.
Indonesian: F20A: exclusivelyIsolating; F21A: noCase (fallback monoexponential); F22A: 4-5; F23A: noMarking (zeroMarking); F26A: stronglySuffixing; F27A: fullReduplicationOnly.
-/

namespace Fragments.Indonesian

open Core.Morphology in
/-- Indonesian: F20A: exclusivelyIsolating; F21A: noCase (fallback monoexponential); F22A: 4-5; F23A: noMarking (zeroMarking); F26A: stronglySuffixing; F27A: fullReduplicationOnly. -/
def morphProfile : MorphProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , fusion := (walsFusion "ind").getD .concatenative
  , exponence := (walsExponence "ind").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "ind").getD .moderate
  , locus := (walsLocus "ind").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "ind").getD .stronglySuffixing
  , reduplication := (walsReduplication "ind").getD .noProductive
  , locusClause := walsLocusClause "ind"
  , locusPossessive := walsLocusPossessive "ind"
  , wholeLanguageMarking := walsWholeLanguageMarking "ind"
  , zeroMarkingAP := walsZeroMarkingAP "ind"
  , caseSyncretism := walsCaseSyncretism "ind"
  , verbalSyncretism := walsVerbalSyncretism "ind"
  , tamExponence := walsTAMExponence "ind"
  , actionNominal := walsActionNominal "ind"
  , suppletionTA := walsSuppletionTA "ind"
  , suppletionImperative := walsSuppletionImperative "ind"
  , verbalNumber := walsVerbalNumber "ind"
  , flexivity := some .nonflexive
  , bnExponence := some .separative
  }

end Fragments.Indonesian
