import Linglib.Syntax.Agreement.AdjAgreement
import Linglib.Fragments.Slavic.Russian.Case

/-!
# Russian Adjective Agreement
[alexeyenko-zeijlstra-2025]

Russian has long and short adjective forms. Long forms are fully inflected
for gender, number, and case; they appear in BOTH predicative and
attributive positions. Short forms retain the full φ-set but lack κ
entirely and are predicative-only ((39), Table 4). Since only the long
form can appear attributively, it alone bears on MAG (34a): the long form
is identical in pred and attr use and fully φ/κ-specified, so Russian
correctly violates the HFF — A–XP–N is attested (24).

The spec records the long-form paradigm's marker inventory, not positional
value distributions: predicative long forms canonically surface in NOM or
INST, but carry the same fully case-inflected agreement marker; gender is
distinguished in the singular only (the plural neutralizes it across the
agreement system).
-/

namespace Russian.AdjAgreement

open Agreement

/-- The long-form paradigm: number, gender, and the full 6-case inventory. -/
private def longForm : FeatureSpec where
  numbers := {.singular, .plural}
  genders := {.masculine, .feminine, .neuter}
  cases   := Russian.Case.caseInventory

/-- Russian long-form entry: identical pred and attr specifications covering
    the whole DP. -/
def entry : AdjAgreementEntry := ⟨longForm, longForm, longForm⟩

/-- Russian long forms agree identically in predicative and attributive use. -/
theorem same_agreement : entry.SameAgreement := rfl

/-- Russian long forms realize every DP φ/κ-feature. -/
theorem phi_kappa_complete : entry.PhiKappaComplete := by decide

end Russian.AdjAgreement
