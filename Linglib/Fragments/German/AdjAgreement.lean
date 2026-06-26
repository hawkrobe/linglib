import Linglib.Syntax.Agreement.AdjAgreement

/-!
# German Adjective Agreement
[alexeyenko-zeijlstra-2025]

German predicative adjectives are bare (uninflected): *Er ist stolz*
'He is proud.' Attributive adjectives carry strong/weak/mixed agreement
endings inflected for gender, number, and case: *stolzer Vater* 'proud
father' (38), (60).

Because predicative and attributive forms differ, `predAttrSameAgreement`
is false, and the MAG correctly predicts that German obeys the HFF.
The attributivizer is affixal (the agreement ending itself is the
spellout of Attr), so the ICP forces adjacency.
-/

namespace German.AdjAgreement

open Agreement

/-- German predicative adjectives carry NO agreement features (bare). -/
def predFeatures : List AgrFeature := []

/-- German attributive adjectives carry φ + κ (strong endings). -/
def attrFeatures : List AgrFeature :=
  [ .number .plural, .number .singular
  , .gender 0, .gender 1, .gender 2
  , .kappa .nom, .kappa .acc, .kappa .dat, .kappa .gen ]

/-- All φ/κ-features available in the German DP. -/
def dpFeatures : List AgrFeature := attrFeatures

def entry : AdjAgreementEntry where
  predFeatures := predFeatures
  attrFeatures := attrFeatures
  dpFeatures   := dpFeatures

/-- German pred ≠ attr: predicative is bare. -/
theorem not_same_agreement : entry.sameAgreement = false := by decide

end German.AdjAgreement
