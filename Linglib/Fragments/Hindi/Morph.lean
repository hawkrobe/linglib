import Linglib.Core.Morphology.MorphProfile

/-!
# Hindi-Urdu Morphological Profile

WALS-derived morphological profile for Hindi-Urdu.
Hindi-Urdu: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 2-3 (low); F23A: doubleMarking; F26A: stronglySuffixing; F27A: productiveFull.
-/

namespace Fragments.Hindi

open Core.Morphology in
/-- Hindi-Urdu: F20A: exclusivelyConcatenative; F21A: monoexponentialCase; F22A: 2-3 (low); F23A: doubleMarking; F26A: stronglySuffixing; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , fusion := (walsFusion "hin").getD .concatenative
  , exponence := (walsExponence "hin").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "hin").getD .moderate
  , locus := (walsLocus "hin").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "hin").getD .stronglySuffixing
  , reduplication := (walsReduplication "hin").getD .noProductive
  , locusClause := walsLocusClause "hin"
  , locusPossessive := walsLocusPossessive "hin"
  , wholeLanguageMarking := walsWholeLanguageMarking "hin"
  , zeroMarkingAP := walsZeroMarkingAP "hin"
  , caseSyncretism := walsCaseSyncretism "hin"
  , verbalSyncretism := walsVerbalSyncretism "hin"
  , tamExponence := walsTAMExponence "hin"
  , actionNominal := walsActionNominal "hin"
  , suppletionTA := walsSuppletionTA "hin"
  , suppletionImperative := walsSuppletionImperative "hin"
  , verbalNumber := walsVerbalNumber "hin"
  , flexivity := some .flexive
  , bnExponence := some .cumulative
  }

end Fragments.Hindi
