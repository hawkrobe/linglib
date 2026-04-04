import Linglib.Core.Morphology.MorphProfile

/-!
# English Morphological Profile

WALS-derived morphological profile for English.
English: F20A: exclusivelyConcatenative; F21A: noCase (fallback monoexponential); F22A: 2-3; F23A: dependentMarking; F26A: stronglySuffixing; F27A: noProductive.
-/

namespace Fragments.English

open Core.Morphology in
/-- English: F20A: exclusivelyConcatenative; F21A: noCase (fallback monoexponential); F22A: 2-3; F23A: dependentMarking; F26A: stronglySuffixing; F27A: noProductive. -/
def morphProfile : MorphProfile :=
  { language := "English"
  , iso := "eng"
  , fusion := (walsFusion "eng").getD .concatenative
  , exponence := (walsExponence "eng").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "eng").getD .moderate
  , locus := (walsLocus "eng").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "eng").getD .stronglySuffixing
  , reduplication := (walsReduplication "eng").getD .noProductive
  , locusClause := walsLocusClause "eng"
  , locusPossessive := walsLocusPossessive "eng"
  , wholeLanguageMarking := walsWholeLanguageMarking "eng"
  , zeroMarkingAP := walsZeroMarkingAP "eng"
  , caseSyncretism := walsCaseSyncretism "eng"
  , verbalSyncretism := walsVerbalSyncretism "eng"
  , tamExponence := walsTAMExponence "eng"
  , actionNominal := walsActionNominal "eng"
  , suppletionTA := walsSuppletionTA "eng"
  , suppletionImperative := walsSuppletionImperative "eng"
  , verbalNumber := walsVerbalNumber "eng"
  , flexivity := some .nonflexive
  , bnExponence := some .separative
  }

end Fragments.English
