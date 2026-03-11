import Linglib.Theories.Syntax.Minimalism.Core.Modification

/-!
# Russian Adjective Agreement
@cite{alexeyenko-zeijlstra-2025}

Russian has long and short adjective forms. Long forms are fully inflected
for gender, number, and case; they appear in BOTH predicative and
attributive positions. Short forms are pred-only and lack case marking
(39), Table 4.

For the MAG, only the form that CAN appear attributively matters — the
long form. Since the long form is identical in pred and attr use and is
fully φ/κ-specified, MAG(a) is satisfied. Russian correctly violates
the HFF: A–XP–N is attested (24).
-/

namespace Fragments.Russian.AdjAgreement

open Minimalism.Modification

/-- Russian long-form features: φ (number, gender) + κ (6-case). -/
def longFormFeatures : List MAGFeatureType :=
  [ .phi (.number true), .phi (.number false)
  , .phi (.gender 0), .phi (.gender 1), .phi (.gender 2)
  , .kappa .nom, .kappa .acc, .kappa .dat
  , .kappa .gen, .kappa .abl, .kappa .obl ]

def dpFeatures : List MAGFeatureType := longFormFeatures

/-- Russian: long forms are identical in pred and attr. -/
def entry : AdjAgreementEntry where
  predFeatures := longFormFeatures
  attrFeatures := longFormFeatures
  dpFeatures   := dpFeatures

theorem same_agreement : entry.sameAgreement = true := by native_decide
theorem phi_kappa_complete : entry.phiKappaComplete = true := by native_decide

end Fragments.Russian.AdjAgreement
