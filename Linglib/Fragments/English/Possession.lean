import Linglib.Features.Possession

/-!
# English possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for English (ISO `eng`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace English.Possession

open _root_.Possession

/-- English possession profile. -/
def possession : PossessionProfile :=
  { language := "English"
  , family := "Indo-European"
  , iso := "eng"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .haveVerb
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .none
  , examples := ["I have a book", "John's book", "the book of John"]
  , notes := "Genitive clitic -'s on possessor; of-phrase alternative" }

end English.Possession
