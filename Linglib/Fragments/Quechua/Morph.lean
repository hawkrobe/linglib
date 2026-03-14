import Linglib.Core.Morphology.MorphProfile

/-!
# Quechua (Imbabura) Morphological Profile

WALS-derived morphological profile for Imbabura Quechua (ISO qvi).
Consistent with the Imbabura data used in the Negation and PolarityItems
fragments in this directory.
-/

namespace Fragments.Quechua

open Core.Morphology in
/-- Quechua (Imbabura): F20A concatenative; F21A monoexponential; F22A high;
    F23A dependentMarking; F25A dependentMarking; F26A stronglySuffixing;
    F27A fullOnly. -/
def morphProfile : MorphProfile :=
  { language := "Quechua (Imbabura)"
  , iso := "qvi"
  , fusion := (walsFusion "qvi").getD .concatenative
  , exponence := (walsExponence "qvi").getD .monoexponential
  , verbSynthesis := (walsVerbSynthesis "qvi").getD .high
  , locus := (walsLocus "qvi").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "qvi").getD .stronglySuffixing
  , reduplication := (walsReduplication "qvi").getD .fullOnly
  , locusClause := walsLocusClause "qvi"
  , locusPossessive := walsLocusPossessive "qvi"
  , wholeLanguageMarking := walsWholeLanguageMarking "qvi"
  , zeroMarkingAP := walsZeroMarkingAP "qvi"
  , caseSyncretism := walsCaseSyncretism "qvi"
  , verbalSyncretism := walsVerbalSyncretism "qvi"
  , tamExponence := walsTAMExponence "qvi"
  , actionNominal := walsActionNominal "qvi"
  , suppletionTA := walsSuppletionTA "qvi"
  , suppletionImperative := walsSuppletionImperative "qvi"
  , verbalNumber := walsVerbalNumber "qvi"
  }

end Fragments.Quechua
