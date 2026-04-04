import Linglib.Core.Morphology.MorphProfile

/-!
# Russian Morphological Profile

WALS-derived morphological profile for Russian.
Russian: F20A: exclusivelyConcatenative (WALS evaluates selected formatives); F21A: caseNumber (polyexponential); F22A: 4-5; F23A: dependentMarking; F26A: stronglySuffixing; F27A: noProductive.
-/

namespace Fragments.Russian

open Core.Morphology in
/-- Russian: F20A: exclusivelyConcatenative (WALS evaluates selected formatives); F21A: caseNumber (polyexponential); F22A: 4-5; F23A: dependentMarking; F26A: stronglySuffixing; F27A: noProductive. -/
def morphProfile : MorphProfile :=
  { language := "Russian"
  , iso := "rus"
  , fusion := (walsFusion "rus").getD .concatenative
  , exponence := (walsExponence "rus").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "rus").getD .moderate
  , locus := (walsLocus "rus").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "rus").getD .stronglySuffixing
  , reduplication := (walsReduplication "rus").getD .noProductive
  , locusClause := walsLocusClause "rus"
  , locusPossessive := walsLocusPossessive "rus"
  , wholeLanguageMarking := walsWholeLanguageMarking "rus"
  , zeroMarkingAP := walsZeroMarkingAP "rus"
  , caseSyncretism := walsCaseSyncretism "rus"
  , verbalSyncretism := walsVerbalSyncretism "rus"
  , tamExponence := walsTAMExponence "rus"
  , actionNominal := walsActionNominal "rus"
  , suppletionTA := walsSuppletionTA "rus"
  , suppletionImperative := walsSuppletionImperative "rus"
  , verbalNumber := walsVerbalNumber "rus"
  , flexivity := some .flexive
  , bnExponence := some .cumulative
  }

end Fragments.Russian
