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

/-- The attributive paradigm: number, gender, and the 4-case inventory. -/
private def attrForm : FeatureSpec where
  numbers := {.singular, .plural}
  genders := {.masculine, .feminine, .neuter}
  cases   := German.Case.caseInventory

/-- German entry: bare predicative forms, fully inflected attributive forms. -/
def entry : AdjAgreementEntry := ⟨{}, attrForm, attrForm⟩

/-- German pred ≠ attr: predicative adjectives are bare. -/
theorem not_same_agreement : ¬ entry.SameAgreement := by decide

end German.AdjAgreement
