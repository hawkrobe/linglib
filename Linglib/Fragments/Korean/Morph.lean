import Linglib.Core.Morphology.MorphProfile

/-!
# Korean Morphological Profile

WALS-derived morphological profile for Korean.
Korean: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 4-5; F23A: dependentMarking; F26A: stronglySuffixing; F27A: productiveFull.
-/

namespace Fragments.Korean

open Core.Morphology in
/-- Korean: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 4-5; F23A: dependentMarking; F26A: stronglySuffixing; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Korean"
  , iso := "kor"
  , fusion := (walsFusion "kor").getD .concatenative
  , exponence := (walsExponence "kor").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "kor").getD .moderate
  , locus := (walsLocus "kor").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "kor").getD .stronglySuffixing
  , reduplication := (walsReduplication "kor").getD .noProductive
  , locusClause := walsLocusClause "kor"
  , locusPossessive := walsLocusPossessive "kor"
  , wholeLanguageMarking := walsWholeLanguageMarking "kor"
  , zeroMarkingAP := walsZeroMarkingAP "kor"
  , caseSyncretism := walsCaseSyncretism "kor"
  , verbalSyncretism := walsVerbalSyncretism "kor"
  , tamExponence := walsTAMExponence "kor"
  , actionNominal := walsActionNominal "kor"
  , suppletionTA := walsSuppletionTA "kor"
  , suppletionImperative := walsSuppletionImperative "kor"
  , verbalNumber := walsVerbalNumber "kor"
  , flexivity := some .nonflexive
  , bnExponence := some .separative
  }

end Fragments.Korean
