import Linglib.Features.Possession

/-!
# Standard Modern Greek possession profile
[stassen-2009] [nichols-1986] [heine-1997]
[holton-mackridge-philippaki-warburton-spyropoulos-2012]
[kampanarou-alexiadou-2026]

`PossessionProfile` bundle for Standard Modern Greek (SMG; ISO `ell`), per
the project's per-language data flows through Fragments rule. Substrate
types live in `Linglib/Features/Possession.lean`. Cross-linguistic theorems
consume this profile from `Studies/NicholsBickel2013.lean`.

Greek is the canonical case of a language that **morphologically** has a
single adnominal possession class (no alienable/inalienable split is marked
on the noun) yet **structurally** distinguishes the two via the position of
the possessor (per [kampanarou-alexiadou-2026] §7, citing
[alexiadou-2003]: inalienable possessors are introduced as complements
of the possessee NP, alienable possessors in the specifier of a dedicated
PossP). The structural distinction is not visible on `PossessionProfile`,
which is a typological-surface bundle; it lives in
`Morphology/DM/NominalStructure.lean::PossessionType`.

The `apo`-PP variant of the genitive (e.g., *to vivlio apo ton ðimarxo*
'the book of the mayor') is a partitive-coerced alternative to inflectional
genitive (per [kampanarou-alexiadou-2026] §5). Felicity is gated by
the relation type (part-whole and source: free; ownership and kinship:
degraded) and by whether the possessor can be construed as a set (modified
or pluralised possessors are felicitous). The licensing apparatus lives in
`Studies/KampanarouAlexiadou2026.lean`.

For the dialect contrast, see `Fragments/Greek/Grevena/Possession.lean`
(genitive-loss endpoint per [michelioudakis-chatzikyriakidis-spathas-2024])
and `Fragments/Greek/Smyrna/Possession.lean` (over-extended genitive per
[kampanarou-alexiadou-2026] fn 7, citing [liosis-2016]).
-/

set_option autoImplicit false

namespace Greek.StandardModern.Possession

open _root_.Possession

/-- Heine notions expressible by SMG inflectional genitive (broad coverage:
    ownership, kinship, body parts, part-whole, abstract). -/
def genNotions : List Notion :=
  [.physical, .temporary, .permanent, .inalienable, .abstract,
   .inanimateInalienable, .inanimateAlienable]

/-- Heine notions naturally expressible by the SMG `apo`-PP variant.
    Restricted set per [kampanarou-alexiadou-2026] (5)–(11): part-whole
    and source-like readings; ownership and kinship are degraded
    (the `apo`-PP coerces a partitive interpretation). -/
def apoNotions : List Notion :=
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

end Greek.StandardModern.Possession
