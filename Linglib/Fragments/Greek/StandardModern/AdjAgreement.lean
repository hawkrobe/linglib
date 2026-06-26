import Linglib.Syntax.Agreement.AdjAgreement
import Linglib.Fragments.Greek.Case

/-!
# Greek Adjective Agreement
[alexeyenko-zeijlstra-2025]

Modern Greek adjectives are fully inflected for gender, number, and case
in both predicative and attributive use (37). The agreement paradigm is
identical across positions — the same form appears predicatively and
attributively.

This is the key fact that makes Greek an HFF-violating language under
the MAG: MAG condition (a) is satisfied because pred = attr featurally
and agreement covers all φ/κ-features in the DP.
-/

namespace Greek.StandardModern.AdjAgreement

open Agreement

/-- φ-features realized on Greek adjectives: number and gender. -/
private def phiFeatures : List AgrFeature :=
  [ .number .plural, .number .singular
  , .gender 0, .gender 1, .gender 2 ]

/-- κ-features realized on Greek adjectives: full 3-case system
    (nom, acc, gen — matching `Case.caseInventory`). -/
private def kappaFeatures : List AgrFeature :=
  [.kappa .nom, .kappa .acc, .kappa .gen]

/-- All φ/κ-features present in the Greek DP. -/
def dpFeatures : List AgrFeature := phiFeatures ++ kappaFeatures

/-- Greek adjective agreement entry: identical pred and attr features,
    covering all DP features. -/
def entry : AdjAgreementEntry where
  predFeatures := phiFeatures ++ kappaFeatures
  attrFeatures := phiFeatures ++ kappaFeatures
  dpFeatures   := dpFeatures

/-- Greek pred = attr agreement. -/
theorem same_agreement : entry.sameAgreement = true := by decide

/-- Greek adjectives cover all DP φ/κ-features. -/
theorem phi_kappa_complete : entry.phiKappaComplete = true := by decide

end Greek.StandardModern.AdjAgreement
