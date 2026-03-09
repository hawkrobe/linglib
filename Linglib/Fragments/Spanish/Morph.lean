import Linglib.Core.Morphology.MorphProfile

/-!
# Spanish Morphological Profile

WALS-derived morphological profile for Spanish.
Spanish: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 4-5; F23A: doubleMarking; F26A: stronglySuffixing; F27A: noProductive.
-/

namespace Fragments.Spanish

open Core.Morphology in
/-- Spanish: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 4-5; F23A: doubleMarking; F26A: stronglySuffixing; F27A: noProductive. -/
def morphProfile : MorphProfile :=
  { language := "Spanish"
  , iso := "spa"
  , fusion := (walsFusion "spa").getD .concatenative
  , exponence := (walsExponence "spa").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "spa").getD .moderate
  , locus := (walsLocus "spa").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "spa").getD .stronglySuffixing
  , reduplication := (walsReduplication "spa").getD .noProductive
  , locusClause := walsLocusClause "spa"
  , locusPossessive := walsLocusPossessive "spa"
  , wholeLanguageMarking := walsWholeLanguageMarking "spa"
  , zeroMarkingAP := walsZeroMarkingAP "spa"
  , caseSyncretism := walsCaseSyncretism "spa"
  , verbalSyncretism := walsVerbalSyncretism "spa"
  , tamExponence := walsTAMExponence "spa"
  , actionNominal := walsActionNominal "spa"
  , suppletionTA := walsSuppletionTA "spa"
  , suppletionImperative := walsSuppletionImperative "spa"
  , verbalNumber := walsVerbalNumber "spa"
  }

end Fragments.Spanish
