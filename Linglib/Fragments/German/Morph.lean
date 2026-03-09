import Linglib.Core.Morphology.MorphProfile

/-!
# German Morphological Profile

WALS-derived morphological profile for German.
German: F20A: exclusivelyConcatenative (WALS evaluates selected formatives); F21A: caseNumber (polyexponential); F22A: 2-3 (low); F23A: dependentMarking; F26A: stronglySuffixing; F27A: noProductive.
-/

namespace Fragments.German

open Core.Morphology in
/-- German: F20A: exclusivelyConcatenative (WALS evaluates selected formatives); F21A: caseNumber (polyexponential); F22A: 2-3 (low); F23A: dependentMarking; F26A: stronglySuffixing; F27A: noProductive. -/
def morphProfile : MorphProfile :=
  { language := "German"
  , iso := "deu"
  , fusion := (walsFusion "deu").getD .concatenative
  , exponence := (walsExponence "deu").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "deu").getD .moderate
  , locus := (walsLocus "deu").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "deu").getD .stronglySuffixing
  , reduplication := (walsReduplication "deu").getD .noProductive
  , locusClause := walsLocusClause "deu"
  , locusPossessive := walsLocusPossessive "deu"
  , wholeLanguageMarking := walsWholeLanguageMarking "deu"
  , zeroMarkingAP := walsZeroMarkingAP "deu"
  , caseSyncretism := walsCaseSyncretism "deu"
  , verbalSyncretism := walsVerbalSyncretism "deu"
  , tamExponence := walsTAMExponence "deu"
  , actionNominal := walsActionNominal "deu"
  , suppletionTA := walsSuppletionTA "deu"
  , suppletionImperative := walsSuppletionImperative "deu"
  , verbalNumber := walsVerbalNumber "deu"
  }

end Fragments.German
