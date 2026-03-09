import Linglib.Core.Morphology.MorphProfile

/-!
# Finnish Morphological Profile

WALS-derived morphological profile for Finnish.
Finnish: F20A: exclusivelyConcatenative; F21A: caseNumber (polyexponential); F22A: 2-3 (low); F23A: dependentMarking; F26A: stronglySuffixing; F27A: noProductive.
-/

namespace Fragments.Finnish

open Core.Morphology in
/-- Finnish: F20A: exclusivelyConcatenative; F21A: caseNumber (polyexponential); F22A: 2-3 (low); F23A: dependentMarking; F26A: stronglySuffixing; F27A: noProductive. -/
def morphProfile : MorphProfile :=
  { language := "Finnish"
  , iso := "fin"
  , fusion := (walsFusion "fin").getD .concatenative
  , exponence := (walsExponence "fin").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "fin").getD .moderate
  , locus := (walsLocus "fin").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "fin").getD .stronglySuffixing
  , reduplication := (walsReduplication "fin").getD .noProductive
  , locusClause := walsLocusClause "fin"
  , locusPossessive := walsLocusPossessive "fin"
  , wholeLanguageMarking := walsWholeLanguageMarking "fin"
  , zeroMarkingAP := walsZeroMarkingAP "fin"
  , caseSyncretism := walsCaseSyncretism "fin"
  , verbalSyncretism := walsVerbalSyncretism "fin"
  , tamExponence := walsTAMExponence "fin"
  , actionNominal := walsActionNominal "fin"
  , suppletionTA := walsSuppletionTA "fin"
  , suppletionImperative := walsSuppletionImperative "fin"
  , verbalNumber := walsVerbalNumber "fin"
  }

end Fragments.Finnish
