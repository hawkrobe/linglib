import Linglib.Features.Possession

/-!
# Korean possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Korean (ISO `kor`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Korean.Possession

open _root_.Possession

/-- Korean possession profile. -/
def possession : PossessionProfile :=
  { language := "Korean"
  , family := "Koreanic"
  , iso := "kor"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .locational
  , adnominalStrategy := .dependentMarking
  , affixPosition := Option.none
  , examples := ["na-ege chaek-i iss-da", "Yeonghui-ui chaek"]
  , notes := "Dative possessor + existential iss-da; genitive -ui for adnominal possession" }

end Korean.Possession
