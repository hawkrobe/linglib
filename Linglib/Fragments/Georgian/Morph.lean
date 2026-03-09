import Linglib.Core.Morphology.MorphProfile

/-!
# Georgian Morphological Profile

WALS-derived morphological profile for Georgian.
Georgian: F20A: exclusivelyConcatenative (WALS evaluates selected formatives); F21A: monoexponentialCase; F22A: 8-9 (high); F23A: doubleMarking; F26A: weaklySuffixing; F27A: productiveFull.
-/

namespace Fragments.Georgian

open Core.Morphology in
/-- Georgian: F20A: exclusivelyConcatenative (WALS evaluates selected formatives); F21A: monoexponentialCase; F22A: 8-9 (high); F23A: doubleMarking; F26A: weaklySuffixing; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Georgian"
  , iso := "kat"
  , fusion := (walsFusion "kat").getD .concatenative
  , exponence := (walsExponence "kat").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "kat").getD .moderate
  , locus := (walsLocus "kat").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "kat").getD .stronglySuffixing
  , reduplication := (walsReduplication "kat").getD .noProductive
  , locusClause := walsLocusClause "kat"
  , locusPossessive := walsLocusPossessive "kat"
  , wholeLanguageMarking := walsWholeLanguageMarking "kat"
  , zeroMarkingAP := walsZeroMarkingAP "kat"
  , caseSyncretism := walsCaseSyncretism "kat"
  , verbalSyncretism := walsVerbalSyncretism "kat"
  , tamExponence := walsTAMExponence "kat"
  , actionNominal := walsActionNominal "kat"
  , suppletionTA := walsSuppletionTA "kat"
  , suppletionImperative := walsSuppletionImperative "kat"
  , verbalNumber := walsVerbalNumber "kat"
  }

end Fragments.Georgian
