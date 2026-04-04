import Linglib.Core.Morphology.MorphProfile

/-!
# Hungarian Morphological Profile

WALS-derived morphological profile for Hungarian.
Hungarian: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 4-5; F23A: dependentMarking; F26A: stronglySuffixing; F27A: productiveFull.
-/

namespace Fragments.Hungarian

open Core.Morphology in
/-- Hungarian: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 4-5; F23A: dependentMarking; F26A: stronglySuffixing; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , fusion := (walsFusion "hun").getD .concatenative
  , exponence := (walsExponence "hun").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "hun").getD .moderate
  , locus := (walsLocus "hun").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "hun").getD .stronglySuffixing
  , reduplication := (walsReduplication "hun").getD .noProductive
  , locusClause := walsLocusClause "hun"
  , locusPossessive := walsLocusPossessive "hun"
  , wholeLanguageMarking := walsWholeLanguageMarking "hun"
  , zeroMarkingAP := walsZeroMarkingAP "hun"
  , caseSyncretism := walsCaseSyncretism "hun"
  , verbalSyncretism := walsVerbalSyncretism "hun"
  , tamExponence := walsTAMExponence "hun"
  , actionNominal := walsActionNominal "hun"
  , suppletionTA := walsSuppletionTA "hun"
  , suppletionImperative := walsSuppletionImperative "hun"
  , verbalNumber := walsVerbalNumber "hun"
  , flexivity := some .nonflexive
  , bnExponence := some .separative
  }

end Fragments.Hungarian
