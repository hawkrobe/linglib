import Linglib.Features.Possession

/-!
# Japanese possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Japanese (ISO `jpn`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Japanese.Possession

open _root_.Possession

/-- Japanese possession profile. -/
def possession : PossessionProfile :=
  { language := "Japanese"
  , family := "Japonic"
  , iso := "jpn"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .topic
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .noAffix
  , examples := ["watashi-ni-wa hon-ga aru", "Tanaka-no hon"]
  , notes := "Topic-comment: possessor-DAT-TOP possessum-NOM aru/iru; genitive no for adnominal" }

end Japanese.Possession
