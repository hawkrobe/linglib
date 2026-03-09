import Linglib.Core.Morphology.MorphProfile

/-!
# Arabic (MSA) Morphological Profile

WALS-derived morphological profile for Arabic (MSA).
Arabic (MSA): mostly fallback (MSA absent from most WALS chapters; only F26A has iso=arb). Linguistically: nonlinear, polyexponential, moderate synthesis, dependent-marking.
-/

namespace Fragments.Arabic

open Core.Morphology in
/-- Arabic (MSA): mostly fallback (MSA absent from most WALS chapters; only F26A has iso=arb). Linguistically: nonlinear, polyexponential, moderate synthesis, dependent-marking. -/
def morphProfile : MorphProfile :=
  { language := "Arabic (MSA)"
  , iso := "arb"
  , fusion := (walsFusion "arb").getD .nonlinear
  , exponence := (walsExponence "arb").getD .polyexponential
  , verbSynthesis := (walsVerbSynthesis "arb").getD .moderate
  , locus := (walsLocus "arb").getD .dependentMarking
  , prefixSuffix := (walsPrefixSuffix "arb").getD .stronglySuffixing
  , reduplication := (walsReduplication "arb").getD .noProductive
  }

end Fragments.Arabic
