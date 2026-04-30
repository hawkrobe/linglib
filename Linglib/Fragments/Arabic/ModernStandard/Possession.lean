import Linglib.Typology.Possession

/-!
# Arabic possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997} 

PossessionProfile bundle for Arabic (ISO `arb`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Phenomena/Possession/Studies/NicholsBickel2013.lean`.
-/

set_option autoImplicit false

namespace Fragments.Arabic.ModernStandard.Possession

open _root_.Typology.Possession

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

end Fragments.Arabic.ModernStandard.Possession
