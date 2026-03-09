import Linglib.Core.Morphology.MorphProfile

/-!
# Thai Morphological Profile

WALS-derived morphological profile for Thai.
Thai: F20A: isolatingConcatenative (fallback isolating); F21A: noCase (fallback noCase); F22A: 2-3 (low); F23A: noMarking (zeroMarking); F26A: littleAffixation; F27A: productiveFull.
-/

namespace Fragments.Thai

open Core.Morphology in
/-- Thai: F20A: isolatingConcatenative (fallback isolating); F21A: noCase (fallback noCase); F22A: 2-3 (low); F23A: noMarking (zeroMarking); F26A: littleAffixation; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Thai"
  , iso := "tha"
  , fusion := (walsFusion "tha").getD .isolating
  , exponence := (walsExponence "tha").getD .noCase
  , verbSynthesis := (walsVerbSynthesis "tha").getD .moderate
  , locus := (walsLocus "tha").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "tha").getD .stronglySuffixing
  , reduplication := (walsReduplication "tha").getD .noProductive
  , locusClause := walsLocusClause "tha"
  , locusPossessive := walsLocusPossessive "tha"
  , wholeLanguageMarking := walsWholeLanguageMarking "tha"
  , zeroMarkingAP := walsZeroMarkingAP "tha"
  , caseSyncretism := walsCaseSyncretism "tha"
  , verbalSyncretism := walsVerbalSyncretism "tha"
  , tamExponence := walsTAMExponence "tha"
  , actionNominal := walsActionNominal "tha"
  , suppletionTA := walsSuppletionTA "tha"
  , suppletionImperative := walsSuppletionImperative "tha"
  , verbalNumber := walsVerbalNumber "tha"
  }

end Fragments.Thai
