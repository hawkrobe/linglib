import Linglib.Typology.Possession

/-!
# Hungarian possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997}
@cite{kenesei-vago-fenyvesi-1998} @cite{rounds-2001}

PossessionProfile bundle for Hungarian (ISO `hun`), per the
project's "per-language data flows through Fragments" rule. Substrate
types (`PossessionProfile`, `PredicativePossession`, `AdnominalPossession`,
…) live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consuming this profile live in
`Phenomena/Possession/Studies/NicholsBickel2013.lean`.

The `adnominalStrategy := .headMarking` choice is consistent with both
standard reference grammars: @cite{kenesei-vago-fenyvesi-1998} §1.10
analyzes possession via the possessive suffix on the possessum
(*Péter vers-e* 'Peter's poem' = "Peter poem-POSS"), with the optional
*dative* possessor (*Péter-nek a vers-e* "Peter-DAT the poem-POSS")
when extracted for specificity reasons (per Szabolcsi 1986/1992, 1994,
as cited there). Both KVF and @cite{rounds-2001} treat the
possessor-marker as **dative**, not genitive — Hungarian has no
morphological GEN, and `Fragments/Hungarian/Case.lean` reflects this
by omitting `.gen` from its `caseInventory`.
-/

set_option autoImplicit false

namespace Fragments.Hungarian.Possession

open _root_.Typology.Possession

/-- Hungarian possession profile. -/
def possession : PossessionProfile :=
  { language := "Hungarian"
  , family := "Uralic"
  , iso := "hun"
  , obligatoryPossession := .exists_
  , possessiveClassification := .noClassification
  , predicativeStrategy := .locational
  , adnominalStrategy := .headMarking
  , affixPosition := some .suffixes
  , examples := ["nekem van konyvem", "Janos kalap-ja"]
  , notes := "Dative possessor + van 'exists' + head-marked possessum; possessive suffixes obligatory on relational nouns" }

end Fragments.Hungarian.Possession
