import Linglib.Features.Possession

/-!
# Arabic possession profile
[stassen-2009] [nichols-1986] [heine-1997] 

PossessionProfile bundle for Arabic (ISO `arb`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativeStrategy`, `AdnominalMarking`,
…) live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Arabic.ModernStandard.Possession

open _root_.Possession

/-- Arabic possession profile. -/
def possession : PossessionProfile :=
  { language := "Arabic"
  , family := "Afro-Asiatic"
  , iso := "arb"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .genitiveDative
  , adnominalStrategy := .juxtaposition
  , affixPosition := some .suffixes
  , examples := ["ʿindii kitaab-un", "kitaab-u l-walad-i"]
  , notes := "Preposition ʿinda for predicative possession (lit. 'at me [there is] a book'); construct state (iḍāfa) for adnominal possession — juxtaposition with the head noun in construct state (no nunation, no definite article) and the possessor in the genitive" }

end Arabic.ModernStandard.Possession
