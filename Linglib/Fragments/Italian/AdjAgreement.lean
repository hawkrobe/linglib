import Linglib.Syntax.Agreement.AdjAgreement

/-!
# Italian Adjective Agreement
[alexeyenko-zeijlstra-2025]

Italian adjectives are inflected for gender and number (φ-features) in
both predicative and attributive use, but NOT for case (κ-features).
The agreement forms are identical across positions (36). Because the
DP carries case even when adjectives never realize it (fn 17), Italian
adjectives are not φ/κ-complete, and Italian obeys the HFF (72).
-/

namespace Italian.AdjAgreement

open Agreement

/-- The adjectival paradigm: number and gender only — no case. -/
private def adjForm : FeatureSpec where
  numbers := {.singular, .plural}
  genders := {.masculine, .feminine}

/-- Italian entry: identical pred and attr φ-specifications; the DP
    additionally carries κ (case is always a DP feature per fn 17, even
    when not morphologically realized on adjectives). -/
def entry : AdjAgreementEntry where
  predFeatures := adjForm
  attrFeatures := adjForm
  dpFeatures   := { adjForm with cases := {.nom, .acc} }

/-- Italian pred = attr (both carry φ). -/
theorem same_agreement : entry.SameAgreement := rfl

/-- Italian is NOT φ/κ-complete: adjectives lack case. -/
theorem not_phi_kappa_complete : ¬ entry.PhiKappaComplete := by decide

end Italian.AdjAgreement
