/-!
# Dutch Adjective Lexicon Fragment
@cite{mcnally-deswart-2011} @cite{broekhuis-keizer-2011}

Dutch adjective entries with morphological alternation: each adjective
typically has three lexical forms — uninflected (`rood`), inflected with
`-e` (`rode`), and derived nominalisation in `-heid` (`roodheid`). A small
class of adjectives (forms ending in /ə/, `-a`, or `-en`) does not
participate in the alternation; this is recorded as `inflectionAlternation
= false`.

The schema records *consensus* Dutch grammatical metadata — distinctions
that any theory of Dutch adjective semantics could consume. Theory- and
paper-specific apparatus (the `Pasp` relational denotation, trope vs kind
classification, Chierchia ∩ in `het`-as-nominaliser) lives in the relevant
study files (currently `Phenomena/Morphology/Studies/McNallyDeSwart2011.lean`).

## Inflection alternation

The Dutch adjective takes the suffix `-e` in:
* definite DPs containing neuter nouns (`het groene boek`),
* both definite and indefinite DPs containing non-neuter nouns
  (`een/de groene tafel`),
* plural DPs.

It appears in its uninflected form only with indefinite singular neuter
nouns (`een groen boek`). Adjectives ending in /ə/ (`roze`, `mauve`),
`-a` (`lila`), or `-en` (`gouden`) do not show the alternation.

## -heid derivation

The suffix `-heid` derives a non-neuter noun from an adjective base:
`rood → roodheid`, `bitter → bitterheid`, `dicht → dichtheid`. Not all
adjectives admit `-heid` derivation; concrete adjectives (`dicht` 'closed')
admit it less productively than abstract ones.
-/

namespace Fragments.Dutch.Adjectives

/-- Semantic domain of a Dutch adjective entry. The distinction between
    abstract and concrete domains tracks the differential availability of
    the inflected nominalisation construction discussed in
    @cite{mcnally-deswart-2011} §1: abstract adjectives (`vreemd`,
    `gezond`, `leuk`) admit it freely, concrete adjectives (`dicht`)
    rarely or not at all. -/
inductive Domain where
  /-- Color terms (rood, wit, groen, ...). -/
  | color
  /-- Taste terms (bitter, zoet, zuur, zout). -/
  | taste
  /-- Abstract evaluative/quality adjectives (vreemd, gezond, leuk). -/
  | abstract
  /-- Concrete physical-property adjectives (dicht, zwaar). -/
  | concrete
  deriving DecidableEq, Repr, BEq

/-- A lexical entry for a Dutch adjective.

    Records the three morphological forms and the semantic domain. The
    `inflectionAlternation` flag distinguishes the productive alternation
    pattern (most adjectives) from the small exceptional class that does
    not show the alternation (forms in /ə/, -a, -en per
    @cite{mcnally-deswart-2011} §1). -/
structure AdjEntry where
  /-- Uninflected form (lemma; also predicative + indef-neuter use). -/
  form : String
  /-- Inflected form with -e suffix; `none` for the exceptional class. -/
  formInfl : Option String := none
  /-- Derived nominalisation in -heid; `none` if no -heid form attested. -/
  nominalHeid : Option String := none
  /-- Semantic domain. -/
  domain : Domain
  /-- Whether the adjective shows the +e vs uninflected alternation. -/
  inflectionAlternation : Bool := true
  deriving DecidableEq, Repr, BEq

/-! ## Color terms

Examples drawn from @cite{mcnally-deswart-2011} (3), (6), (7) and standard
Dutch dictionaries. -/

/-- `rood` 'red' (paper §1, §3.1; ex (3)). -/
def rood : AdjEntry :=
  { form := "rood", formInfl := some "rode",
    nominalHeid := some "roodheid", domain := .color }

/-- `wit` 'white' (paper §3.1; ex (3b)). -/
def wit : AdjEntry :=
  { form := "wit", formInfl := some "witte",
    nominalHeid := some "witheid", domain := .color }

/-- `groen` 'green' (paper §1; ex (1), (2), (3b)). -/
def groen : AdjEntry :=
  { form := "groen", formInfl := some "groene",
    nominalHeid := some "groenheid", domain := .color }

/-- `geel` 'yellow' (paper §2.1; ex (6a), (7a)). -/
def geel : AdjEntry :=
  { form := "geel", formInfl := some "gele",
    nominalHeid := some "geelheid", domain := .color }

/-- `blauw` 'blue'. -/
def blauw : AdjEntry :=
  { form := "blauw", formInfl := some "blauwe",
    nominalHeid := some "blauwheid", domain := .color }

/-- `zwart` 'black' (paper §1; cf. Spanish *negros* in (5b)). -/
def zwart : AdjEntry :=
  { form := "zwart", formInfl := some "zwarte",
    nominalHeid := some "zwartheid", domain := .color }

/-! ### Color exceptions to the inflection alternation

Per @cite{mcnally-deswart-2011} §1: forms ending in /ə/ (`roze`, `mauve`),
`-a` (`lila`), or `-en` (`gouden`) do not show the +e alternation. -/

/-- `roze` 'pink' — exception to inflection alternation (final schwa). -/
def roze : AdjEntry :=
  { form := "roze", domain := .color, inflectionAlternation := false }

/-- `mauve` 'mauve' — exception to inflection alternation (final schwa). -/
def mauve : AdjEntry :=
  { form := "mauve", domain := .color, inflectionAlternation := false }

/-- `lila` 'lilac' — exception to inflection alternation (-a-final). -/
def lila : AdjEntry :=
  { form := "lila", domain := .color, inflectionAlternation := false }

/-- `gouden` 'golden' — exception to inflection alternation (-en-final). -/
def gouden : AdjEntry :=
  { form := "gouden", domain := .color, inflectionAlternation := false }

/-! ## Taste terms

Examples from @cite{mcnally-deswart-2011} (4), (7c). -/

/-- `bitter` 'bitter' (paper §1, §3.1; ex (4)). -/
def bitter : AdjEntry :=
  { form := "bitter", formInfl := some "bittere",
    nominalHeid := some "bitterheid", domain := .taste }

/-- `zoet` 'sweet' (paper §3.1; ex (4b)). -/
def zoet : AdjEntry :=
  { form := "zoet", formInfl := some "zoete",
    nominalHeid := some "zoetheid", domain := .taste }

/-- `zuur` 'sour' (paper §3.1; ex (4a) for the lemma, (13c) for the
    inflected `zure`). -/
def zuur : AdjEntry :=
  { form := "zuur", formInfl := some "zure",
    nominalHeid := some "zuurheid", domain := .taste }

/-- `zout` 'salty/salt' (paper §3.1; ex (4a)). -/
def zout : AdjEntry :=
  { form := "zout", formInfl := some "zoute",
    nominalHeid := some "zoutheid", domain := .taste }

/-! ## Abstract and concrete contrasts

@cite{mcnally-deswart-2011} §1 notes the inflected-nominalised use is
frequent with abstract adjectives but rare with concrete ones. -/

/-- `vreemd` 'strange' — abstract; freely takes inflected nominalisation. -/
def vreemd : AdjEntry :=
  { form := "vreemd", formInfl := some "vreemde",
    nominalHeid := some "vreemdheid", domain := .abstract }

/-- `gezond` 'healthy' — abstract; cited in (§3.4) for *het gezonde van X*. -/
def gezond : AdjEntry :=
  { form := "gezond", formInfl := some "gezonde",
    nominalHeid := some "gezondheid", domain := .abstract }

/-- `leuk` 'nice/fun' — abstract (§3.4). -/
def leuk : AdjEntry :=
  { form := "leuk", formInfl := some "leuke",
    nominalHeid := some "leukheid", domain := .abstract }

/-- `bijzonder` 'special' — abstract (§3.4). -/
def bijzonder : AdjEntry :=
  { form := "bijzonder", formInfl := some "bijzondere",
    nominalHeid := some "bijzonderheid", domain := .abstract }

/-- `dicht` 'closed' — concrete; nominalised inflected use marginal/odd
    (paper §1: `?*het dichte van deze doos`). -/
def dicht : AdjEntry :=
  { form := "dicht", formInfl := some "dichte",
    nominalHeid := some "dichtheid", domain := .concrete }

/-! ## Bundles -/

/-- All Dutch color adjectives in this fragment, including exceptions. -/
def colorAdjectives : List AdjEntry :=
  [rood, wit, groen, geel, blauw, zwart, roze, mauve, lila, gouden]

/-- Color adjectives that participate in the +e alternation. -/
def colorAdjectivesAlternating : List AdjEntry :=
  [rood, wit, groen, geel, blauw, zwart]

/-- All Dutch taste adjectives in this fragment. -/
def tasteAdjectives : List AdjEntry :=
  [bitter, zoet, zuur, zout]

/-- Abstract adjectives illustrated in @cite{mcnally-deswart-2011}. -/
def abstractAdjectives : List AdjEntry :=
  [vreemd, gezond, leuk, bijzonder]

/-- All Dutch adjectives in this fragment. -/
def all : List AdjEntry :=
  colorAdjectives ++ tasteAdjectives ++ abstractAdjectives ++ [dicht]

end Fragments.Dutch.Adjectives
