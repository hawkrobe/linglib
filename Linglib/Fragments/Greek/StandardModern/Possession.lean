import Linglib.Typology.Possession

/-!
# Standard Modern Greek possession profile
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997}
@cite{holton-mackridge-philippaki-warburton-spyropoulos-2012}
@cite{kampanarou-alexiadou-2026}

`PossessionProfile` bundle for Standard Modern Greek (SMG; ISO `ell`), per
the project's per-language data flows through Fragments rule. Substrate
types live in `Linglib/Typology/Possession.lean`. Cross-linguistic theorems
consume this profile from `Phenomena/Possession/Studies/NicholsBickel2013.lean`.

Greek is the canonical case of a language that **morphologically** has a
single adnominal possession class (no alienable/inalienable split is marked
on the noun) yet **structurally** distinguishes the two via the position of
the possessor (per @cite{kampanarou-alexiadou-2026} §7, citing
@cite{alexiadou-2003}: inalienable possessors are introduced as complements
of the possessee NP, alienable possessors in the specifier of a dedicated
PossP). The structural distinction is not visible on `PossessionProfile`,
which is a typological-surface bundle; it lives in
`Theories/Morphology/DM/NominalStructure.lean::PossessionType`.

The `apo`-PP variant of the genitive (e.g., *to vivlio apo ton ðimarxo*
'the book of the mayor') is a partitive-coerced alternative to inflectional
genitive (per @cite{kampanarou-alexiadou-2026} §5). Felicity is gated by
the relation type (part-whole and source: free; ownership and kinship:
degraded) and by whether the possessor can be construed as a set (modified
or pluralised possessors are felicitous). The licensing apparatus lives in
`Phenomena/Possession/Studies/KampanarouAlexiadou2026.lean`.

For the dialect contrast, see `Fragments/Greek/Grevena/Possession.lean`
(genitive-loss endpoint per @cite{michelioudakis-chatzikyriakidis-spathas-2024})
and `Fragments/Greek/Smyrna/Possession.lean` (over-extended genitive per
@cite{kampanarou-alexiadou-2026} fn 7, citing @cite{liosis-2016}).
-/

set_option autoImplicit false

namespace Fragments.Greek.StandardModern.Possession

open _root_.Typology.Possession

/-- Heine notions expressible by SMG inflectional genitive (broad coverage:
    ownership, kinship, body parts, part-whole, abstract). -/
def genNotions : List PossessiveNotion :=
  [.physical, .temporary, .permanent, .inalienable, .abstract,
   .inanimateInalienable, .inanimateAlienable]

/-- Heine notions naturally expressible by the SMG `apo`-PP variant.
    Restricted set per @cite{kampanarou-alexiadou-2026} (5)–(11): part-whole
    and source-like readings; ownership and kinship are degraded
    (the `apo`-PP coerces a partitive interpretation). -/
def apoNotions : List PossessiveNotion :=
  [.inanimateInalienable, .inanimateAlienable]

/-- Standard Modern Greek possession profile. -/
def possession : PossessionProfile :=
  { language := "Greek"
  , family := "Indo-European"
  , iso := "ell"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .haveVerb
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .none
  , examples :=
      [ "to vivlio tu Jani"        -- 'John's book' (inflectional GEN)
      , "to pomolo apo tin porta"  -- 'the door's handle' (apo-PP, part-whole)
      , "to nero apo tin piji"     -- 'the spring's water' (apo-PP, source)
      , "exi pola vivlia"          -- 'has many books' (predicative haveVerb)
      ]
  , notes := "Inflectional genitive (head-suffix on possessor) is the broad-coverage strategy;\
 apo-PP alternates only in part-whole and source-like contexts and is degraded with animate possessors,\
 pronouns, and proper names (per Kampanarou & Alexiadou 2026)." }

end Fragments.Greek.StandardModern.Possession
