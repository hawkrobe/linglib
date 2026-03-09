import Linglib.Core.Morphology.MorphProfile

/-!
# Turkish Morphological Profile

WALS-derived morphological profile for Turkish.
Turkish: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 6-7; F23A: dependentMarking; F26A: stronglySuffixing; F27A: productiveFull.
-/

namespace Fragments.Turkish

open Core.Morphology in
/-- Turkish: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 6-7; F23A: dependentMarking; F26A: stronglySuffixing; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Turkish"
  , iso := "tur"
  , fusion := (walsFusion "tur").getD .concatenative
  , exponence := (walsExponence "tur").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "tur").getD .moderate
  , locus := (walsLocus "tur").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "tur").getD .stronglySuffixing
  , reduplication := (walsReduplication "tur").getD .noProductive
  , locusClause := walsLocusClause "tur"
  , locusPossessive := walsLocusPossessive "tur"
  , wholeLanguageMarking := walsWholeLanguageMarking "tur"
  , zeroMarkingAP := walsZeroMarkingAP "tur"
  , caseSyncretism := walsCaseSyncretism "tur"
  , verbalSyncretism := walsVerbalSyncretism "tur"
  , tamExponence := walsTAMExponence "tur"
  , actionNominal := walsActionNominal "tur"
  , suppletionTA := walsSuppletionTA "tur"
  , suppletionImperative := walsSuppletionImperative "tur"
  , verbalNumber := walsVerbalNumber "tur"
  }

end Fragments.Turkish
