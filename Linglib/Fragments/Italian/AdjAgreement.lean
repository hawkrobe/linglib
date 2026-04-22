import Linglib.Theories.Syntax.Minimalism.Modification

/-!
# Italian Adjective Agreement
@cite{alexeyenko-zeijlstra-2025}

Italian adjectives are inflected for gender and number (φ-features) in
both predicative and attributive use, but NOT for case (κ-features).
The agreement forms are identical across positions (36).

Under the MAG, Italian fails condition (a) because φ/κ-completeness
requires case marking: `agreementPhiKappaComplete = false`. Since the
Attr head is null and affixal (carrying κ-features), the ICP forces
adjacency. Italian prenominal adjectives therefore obey the HFF. The
analysis is given in (72).
-/

namespace Fragments.Italian.AdjAgreement

open Minimalism.Modification

/-- Italian adjective φ-features: number and gender only. -/
def phiFeatures : List MAGFeatureType :=
  [ .phi (.number .pl), .phi (.number .sg)
  , .phi (.gender 0), .phi (.gender 1) ]

/-- Italian DP features include κ (case is always a DP feature per fn 17,
    even when not morphologically realized on adjectives). -/
def dpFeatures : List MAGFeatureType :=
  phiFeatures ++ [.kappa .nom, .kappa .acc]

def entry : AdjAgreementEntry where
  predFeatures := phiFeatures
  attrFeatures := phiFeatures
  dpFeatures   := dpFeatures

/-- Italian pred = attr (both carry φ). -/
theorem same_agreement : entry.sameAgreement = true := by native_decide

/-- Italian is NOT φ/κ-complete: adjectives lack case. -/
theorem not_phi_kappa_complete : entry.phiKappaComplete = false := by native_decide

end Fragments.Italian.AdjAgreement
