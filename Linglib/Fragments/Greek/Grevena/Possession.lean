import Linglib.Features.Possession

/-!
# Grevena Greek possession profile
[stassen-2009] [nichols-1986] [heine-1997]
[michelioudakis-chatzikyriakidis-spathas-2024]
[kampanarou-alexiadou-2026]

Per-language possession data for Grevena Greek (GG; Northern Greek dialect;
Indo-European; ISO `ell`, shared macro-language code with SMG), as bare
field-by-field `def`s — the genitive-loss endpoint within the Modern Greek
dialect continuum.

Examples: *tu vivliu ap tun ðimarxu* 'the book of the mayor' (apo-PP, no GEN
on noun), *i piriγrafi ap tun ðimarxu ap ta piðja* (iterated apo-PPs,
impossible in SMG), *tu spiti m* 'my house' (cliticised pronoun retains
GEN). Inflectional genitive lost on common nouns; apo-PPs cover all genitive
functions and can stack, front, and sub-extract (cf. Romance de/di).

## What makes GG different from SMG

In GG, **inflectional genitive has been entirely lost on common nouns**
([michelioudakis-chatzikyriakidis-spathas-2024]); its functions are
served by `apo`-PPs across the board. GG `apo`-PPs differ from SMG
`apo`-PPs (per [kampanarou-alexiadou-2026] §4, Table 3): they can
stack/iterate, can be fronted, can be sub-extracted, and express the full
range of pragmatically implied relations — paralleling Romance *de/di*
genitives. Michelioudakis et al. analyse them as **reduced relative
clauses** adjoining within the DP. This is exactly the structure SMG
`apo`-PPs *cannot* be — see Kampanarou & Alexiadou 2026 §4 for the
contrast.

The only inflectional genitives surviving in GG are on pronominal clitics
and proper names (or proper-name-like nouns including kinship terms in
some sub-varieties), echoing other Indo-European languages where genitive
relics persist with proper names (German *Hans' Buch*).

## Cross-dialectal contrast

Together with `Fragments/Greek/Possession.lean` (SMG, transitional) and
`Fragments/Greek/Smyrna/Possession.lean` (over-extended, opposite
direction), GG is one of three sibling profiles needed to support
Kampanarou & Alexiadou's bidirectional cross-dialectal argument: SMG sits
on a continuum between Smyrna's over-extension and GG's complete loss.
-/

set_option autoImplicit false

namespace Greek.Grevena.Possession

open _root_.Possession

/-- Heine notions expressible by GG `apo`-PPs. Unlike SMG (where `apoNotions`
    is restricted to inanimate part-whole/source readings), GG `apo`-PPs
    cover the full range that SMG inflectional genitive covers
    (per [michelioudakis-chatzikyriakidis-spathas-2024] (19), discussed
    by [kampanarou-alexiadou-2026] §4 ex. 16a). -/
def apoNotions : List Notion :=
  [.physical, .temporary, .permanent, .inalienable, .abstract,
   .inanimateInalienable, .inanimateAlienable]

/-- Heine notions still expressible by GG inflectional genitive — only on
    pronominal clitics and proper names (and some kinship terms in some
    sub-varieties), per [michelioudakis-chatzikyriakidis-spathas-2024]
    discussed in [kampanarou-alexiadou-2026] §4. The empty common-noun
    coverage is the dialect's defining feature. -/
def genNotions : List Notion := []

def obligatoryPossession : Obligatoriness := .noObligatory
def possessiveClassification : Classification := .noClassification
def predicativeStrategy : PredicativeStrategy := .haveVerb

/-- `.zeroMarking` reflects the loss of inflectional GEN on common nouns;
    the `apo`-PP variant carries the load. The label is approximate —
    `juxtaposition` is the closest WALS-mapped category for "no morphological
    possessor marking on the noun, possession encoded by phrasal means" — but
    the genuine analysis (per [michelioudakis-chatzikyriakidis-spathas-2024])
    is *reduced relative clause adjunction*, which the substrate doesn't
    distinguish from juxtaposition (a structure SMG apo-PPs do NOT support,
    see [kampanarou-alexiadou-2026] §4). -/
def adnominalStrategy : AdnominalMarking := .zeroMarking
def affixPosition : Option AffixPosition := some .noAffix

end Greek.Grevena.Possession
