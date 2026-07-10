import Linglib.Syntax.Agreement.AdjAgreement
import Linglib.Fragments.Greek.Case

/-!
# Greek Adjective Agreement
[alexeyenko-zeijlstra-2025]

Modern Greek adjectives are fully inflected for gender, number, and case
in both predicative and attributive use (37). The agreement paradigm is
identical across positions — the same form appears predicatively and
attributively — and covers all φ/κ-features in the DP, so MAG condition
(a) is satisfied and Greek violates the HFF.
-/

namespace Greek.StandardModern.AdjAgreement

open Agreement

/-- φ-features realized on Greek adjectives: number and gender. -/
private def phiFeatures : Finset AgrFeature :=
  { .number .singular, .number .plural
  , .gender .masculine, .gender .feminine, .gender .neuter }

/-- κ-features realized on Greek adjectives, derived from the 3-case
    `Greek.Case.caseInventory`. -/
private def kappaFeatures : Finset AgrFeature :=
  Greek.Case.caseInventory.image .kappa

/-- Greek adjective agreement entry: identical pred and attr features,
    covering all DP features. -/
def entry : AdjAgreementEntry where
  predFeatures := phiFeatures ∪ kappaFeatures
  attrFeatures := phiFeatures ∪ kappaFeatures
  dpFeatures   := phiFeatures ∪ kappaFeatures

/-- Greek pred = attr agreement. -/
theorem same_agreement : entry.SameAgreement := rfl

/-- Greek adjectives cover all DP φ/κ-features. -/
theorem phi_kappa_complete : entry.PhiKappaComplete := Finset.Subset.refl _

end Greek.StandardModern.AdjAgreement
