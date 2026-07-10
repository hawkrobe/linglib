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

/-- The adjectival paradigm: number, gender, and the 3-case inventory. -/
private def adjForm : FeatureSpec where
  numbers := {.singular, .plural}
  genders := {.masculine, .feminine, .neuter}
  cases   := Greek.Case.caseInventory

/-- Greek adjective agreement entry: identical pred and attr specifications,
    covering all DP features. -/
def entry : AdjAgreementEntry := ⟨adjForm, adjForm, adjForm⟩

/-- Greek pred = attr agreement. -/
theorem same_agreement : entry.SameAgreement := rfl

/-- Greek adjectives cover all DP φ/κ-features. -/
theorem phi_kappa_complete : entry.PhiKappaComplete := by decide

end Greek.StandardModern.AdjAgreement
