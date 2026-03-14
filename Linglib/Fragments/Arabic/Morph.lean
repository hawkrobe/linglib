import Linglib.Core.Morphology.MorphProfile

/-!
# Arabic (Egyptian) Morphological Profile

WALS-derived morphological profile for Arabic (Egyptian).
WALS uses Egyptian Arabic (ISO arz, WALS code aeg) as the representative
Arabic variety for most morphology chapters.
-/

namespace Fragments.Arabic

open Core.Morphology in
/-- Arabic (Egyptian): F20A nonlinear; F22A moderate; F23A noMarking;
    F25A inconsistentOrOther; F26A weaklySuffixing; F27A productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Arabic (Egyptian)"
  , iso := "arz"
  , fusion := (walsFusion "arz").getD .nonlinear
  , exponence := (walsExponence "arz").getD .polyexponential
  , verbSynthesis := (walsVerbSynthesis "arz").getD .moderate
  , locus := (walsLocus "arz").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "arz").getD .weaklySuffixing
  , reduplication := (walsReduplication "arz").getD .productiveFull
  , locusClause := walsLocusClause "arz"
  , locusPossessive := walsLocusPossessive "arz"
  , wholeLanguageMarking := walsWholeLanguageMarking "arz"
  , zeroMarkingAP := walsZeroMarkingAP "arz"
  , caseSyncretism := walsCaseSyncretism "arz"
  , verbalSyncretism := walsVerbalSyncretism "arz"
  , tamExponence := walsTAMExponence "arz"
  , actionNominal := walsActionNominal "arz"
  , suppletionTA := walsSuppletionTA "arz"
  , suppletionImperative := walsSuppletionImperative "arz"
  , verbalNumber := walsVerbalNumber "arz"
  }

end Fragments.Arabic
