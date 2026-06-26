import Linglib.Features.Possession

/-!
# Georgian possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Georgian (ISO `kat`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Georgian.Possession

open _root_.Possession

/-- Georgian possession profile. -/
def possession : PossessionProfile :=
  { language := "Georgian"
  , family := "Kartvelian"
  , iso := "kat"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .locational
  , adnominalStrategy := .doubleMarking
  , affixPosition := some .none
  , examples := ["me m-akvs cigni", "kac-is saxl-i"]
  , notes := "Dative experiencer + verb agreeing with possessum; genitive on possessor in adnominal constructions" }

end Georgian.Possession
