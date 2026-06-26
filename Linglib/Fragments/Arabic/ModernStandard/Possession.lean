import Linglib.Features.Possession

/-!
# Arabic possession profile
[stassen-2009] [nichols-1986] [heine-1997]

Bare per-language possession `def`s for Arabic (Afro-Asiatic, ISO `arb`),
per the project's "per-language data flows through Fragments" rule.
Substrate types (`PredicativeStrategy`, `AdnominalMarking`, …) live in
`Linglib/Features/Possession.lean`. Cross-linguistic theorems consuming
these values live in `Studies/NicholsBickel2013.lean`.

Examples: ʿindii kitaab-un; kitaab-u l-walad-i. Preposition ʿinda for
predicative possession (lit. 'at me [there is] a book'); construct state
(iḍāfa) for adnominal possession — juxtaposition with the head noun in
construct state (no nunation, no definite article) and the possessor in
the genitive.
-/

set_option autoImplicit false

namespace Arabic.ModernStandard.Possession

open _root_.Possession

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .locational
def adnominalStrategy : AdnominalMarking := .zeroMarking
def affixPosition : Option AffixPosition := some .suffixes

end Arabic.ModernStandard.Possession
