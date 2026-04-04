import Linglib.Core.Morphology.MorphProfile

/-!
# Tagalog Morphological Profile

WALS-derived morphological profile for Tagalog.
Tagalog: F20A: exclusivelyConcatenative; F21A: caseReferentiality (polyexponential); F22A: 2-3 (low); F23A: doubleMarking; F26A: littleAffixation; F27A: productiveFull.
-/

namespace Fragments.Tagalog

open Core.Morphology in
/-- Tagalog: F20A: exclusivelyConcatenative; F21A: caseReferentiality (polyexponential); F22A: 2-3 (low); F23A: doubleMarking; F26A: littleAffixation; F27A: productiveFull. -/
def morphProfile : MorphProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , fusion := (walsFusion "tgl").getD .concatenative
  , exponence := (walsExponence "tgl").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "tgl").getD .moderate
  , locus := (walsLocus "tgl").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "tgl").getD .stronglySuffixing
  , reduplication := (walsReduplication "tgl").getD .noProductive
  , locusClause := walsLocusClause "tgl"
  , locusPossessive := walsLocusPossessive "tgl"
  , wholeLanguageMarking := walsWholeLanguageMarking "tgl"
  , zeroMarkingAP := walsZeroMarkingAP "tgl"
  , caseSyncretism := walsCaseSyncretism "tgl"
  , verbalSyncretism := walsVerbalSyncretism "tgl"
  , tamExponence := walsTAMExponence "tgl"
  , actionNominal := walsActionNominal "tgl"
  , suppletionTA := walsSuppletionTA "tgl"
  , suppletionImperative := walsSuppletionImperative "tgl"
  , verbalNumber := walsVerbalNumber "tgl"
  , flexivity := some .nonflexive
  , bnExponence := some .separative
  }

end Fragments.Tagalog
