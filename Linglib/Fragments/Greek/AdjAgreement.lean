import Linglib.Theories.Syntax.Minimalism.Modification
import Linglib.Fragments.Greek.Case

/-!
# Greek Adjective Agreement
@cite{alexeyenko-zeijlstra-2025}

Modern Greek adjectives are fully inflected for gender, number, and case
in both predicative and attributive use (37). The agreement paradigm is
identical across positions — the same form appears predicatively and
attributively.

This is the key fact that makes Greek an HFF-violating language under
the MAG: MAG condition (a) is satisfied because pred = attr featurally
and agreement covers all φ/κ-features in the DP.
-/

namespace Fragments.Greek.AdjAgreement

open Minimalism.Modification

/-- φ-features realized on Greek adjectives: number and gender. -/
private def phiFeatures : List MAGFeatureType :=
  [ .phi (.number .pl), .phi (.number .sg)
  , .phi (.gender 0), .phi (.gender 1), .phi (.gender 2) ]

/-- κ-features realized on Greek adjectives: full 3-case system
    (nom, acc, gen — matching `Case.caseInventory`). -/
private def kappaFeatures : List MAGFeatureType :=
  [.kappa .nom, .kappa .acc, .kappa .gen]

/-- All φ/κ-features present in the Greek DP. -/
def dpFeatures : List MAGFeatureType := phiFeatures ++ kappaFeatures

/-- Greek adjective agreement entry: identical pred and attr features,
    covering all DP features. -/
def entry : AdjAgreementEntry where
  predFeatures := phiFeatures ++ kappaFeatures
  attrFeatures := phiFeatures ++ kappaFeatures
  dpFeatures   := dpFeatures

/-- Greek pred = attr agreement. -/
theorem same_agreement : entry.sameAgreement = true := by native_decide

/-- Greek adjectives cover all DP φ/κ-features. -/
theorem phi_kappa_complete : entry.phiKappaComplete = true := by native_decide

end Fragments.Greek.AdjAgreement
