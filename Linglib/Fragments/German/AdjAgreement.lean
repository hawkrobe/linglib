import Linglib.Syntax.Agreement.AdjAgreement
import Linglib.Fragments.German.Case

/-!
# German Adjective Agreement
[alexeyenko-zeijlstra-2025]

German predicative adjectives are bare (uninflected): *Er ist stolz*
'He is proud.' Attributive adjectives carry strong/weak/mixed agreement
endings inflected for gender, number, and case: *stolzer Vater* 'proud
father' (38), (60). Because the predicative form realizes no agreement,
pred ≠ attr, and German obeys the HFF.
-/

namespace German.AdjAgreement

open Agreement

/-- Attributive φ-features: number and gender. -/
private def phiFeatures : Finset AgrFeature :=
  { .number .singular, .number .plural
  , .gender .masculine, .gender .feminine, .gender .neuter }

/-- Attributive κ-features, derived from the 4-case `German.Case.caseInventory`. -/
private def kappaFeatures : Finset AgrFeature :=
  German.Case.caseInventory.image .kappa

/-- German entry: bare predicative forms, fully inflected attributive forms. -/
def entry : AdjAgreementEntry where
  predFeatures := ∅
  attrFeatures := phiFeatures ∪ kappaFeatures
  dpFeatures   := phiFeatures ∪ kappaFeatures

/-- German pred ≠ attr: predicative adjectives are bare. -/
theorem not_same_agreement : ¬ entry.SameAgreement := by decide

end German.AdjAgreement
