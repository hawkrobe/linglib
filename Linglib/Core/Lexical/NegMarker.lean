import Linglib.Datasets.WALS.Datapoint
import Linglib.Datasets.WALS.Features.F112A
import Linglib.Datasets.WALS.Features.F143A
import Linglib.Datasets.WALS.Features.F144A

/-!
# Negation Marker Substrate
@cite{dryer-2013-wals} @cite{haspelmath-2013} @cite{miestamo-2005}

Cross-linguistic data structure for the standard sentential negation
marker of a language: form, morphological status, and position relative
to the verb. The morpheme typology is anchored on WALS Ch 112A; position
is a coarsening of WALS Ch 143A and 144A.

This file provides the substrate that `Fragments/{Lang}/Negation.lean`
files use to encode their language's negation marker (e.g., Italian *non*,
French *ne...pas*, Japanese *-nai*, Finnish *e-*). Cross-linguistic
typological generalizations (Miestamo's symmetry dimensions, Haspelmath's
WALS Ch 115 NPI typology) live in `Phenomena/Negation/Typology.lean` and
consume the same `NegMorphemeType`.

Polarity-sensitive items (n-words, NPIs, FCIs) are NOT marker-side data;
they live in `Core.Lexical.PolarityItem.PolarityItemEntry` and in each
language's `Fragments/{Lang}/PolarityItems.lean`.
-/

namespace Core.Lexical.NegMarker

/-- Type of the standard negation morpheme @cite{dryer-2013-wals}.

    Six categories anchored on WALS Ch 112A (negative morpheme classification).
    Originally declared in `Phenomena.Negation.Typology` and promoted here
    for use by `Fragments/{Lang}/Negation.lean` files. -/
inductive NegMorphemeType where
  /-- Negative affix on the verb (e.g., Kolyma Yukaghir `el-jaqa-te-je`
      'NEG-achieve-FUT-1SG'). -/
  | affix
  /-- Free negative particle, no verbal inflection (e.g., English `not`,
      Italian `non`). -/
  | particle
  /-- Negative auxiliary verb inflecting for verbal categories (e.g.,
      Finnish `e-n` 'NEG-1SG'). -/
  | auxVerb
  /-- Negative word whose status as verb or particle is unclear, typically
      in isolating languages (e.g., Maori `kaahore`). -/
  | wordUnclear
  /-- Language uses both negative word and negative affix in different
      constructions (e.g., Rama). -/
  | variation
  /-- Bipartite negation: two co-occurring morphemes flanking the verb
      (e.g., French `ne...pas`, Izi `to-...-du`). -/
  | doubleNeg
  deriving DecidableEq, BEq, Repr

/-- Position of the negation morpheme relative to the verb.

    Coarser than WALS Ch 144A's full S/O/V grid; the `wals144A` field on
    `NegMarkerEntry` preserves the precise WALS classification for callers
    that need it. -/
inductive NegMarkerPosition where
  /-- Marker precedes the verb (e.g., Italian `non V`, English `do not V`). -/
  | preverbal
  /-- Marker follows the verb (e.g., Japanese `V-nai`, Turkish `V-mE-`). -/
  | postverbal
  /-- Bipartite: one element preverbal, one postverbal (e.g., French
      `ne V pas`). -/
  | discontinuous
  /-- Marker is a morphological process on the verb (infix, tone change,
      stem change) rather than a positionable element. -/
  | morphological
  /-- None of the above; consult `wals144A` for the precise classification. -/
  | other
  deriving DecidableEq, BEq, Repr

/-- One language's standard sentential negation marker. -/
structure NegMarkerEntry where
  /-- Surface form. For affixal negation this is an abstract citation form
      (e.g., Turkish `-mE-` for the harmony-conditioned `-ma-` / `-me-`
      alternants). For tonal/morphological negation use `position :=
      .morphological` and document the realization in the `def` docstring. -/
  form : String
  /-- Standard interlinear gloss. Defaults to the WALS-style "NEG". -/
  gloss : String := "NEG"
  /-- Morphological status: affix, free particle, auxiliary, etc. -/
  morphemeType : NegMorphemeType
  /-- Coarse position relative to the verb. -/
  position : NegMarkerPosition
  deriving Repr

/-- Convert a WALS Ch 112A morpheme classification to the Core enum.
    The forward direction of the bridge declared (and made private) in
    `Phenomena.Negation.Typology`; promoted here so Fragment files can use it. -/
def ofWALS112A : Datasets.WALS.F112A.NegativeMorphemeType → NegMorphemeType
  | .negativeAffix => .affix
  | .negativeParticle => .particle
  | .negativeAuxiliaryVerb => .auxVerb
  | .negativeWordUnclearIfVerbOrParticle => .wordUnclear
  | .variationBetweenNegativeWordAndAffix => .variation
  | .doubleNegation => .doubleNeg

/-- A language's standard negation system.

    The Fragment-side joint: every `Fragments/{Lang}/Negation.lean` exposes
    `def negationSystem : NegationSystem`. Bundled (rather than just
    `markers : List NegMarkerEntry` per language) so that future
    typological fields can land without changing the joint contract.

    Multiple markers handle languages with mood/aspect/lexical-class
    alternation: Greek *δεν* (indicative) vs *μη(ν)* (subjunctive),
    Mandarin *bù* (general) vs *méi* (perfective/existential),
    Korean long *an V* vs short *V-ji anh-*. Length-1 for most languages
    (Italian, Spanish, English, German).

    WALS datapoints are bundled at the system level — in WALS coding, F112A
    / F143A / F144A take one value per language regardless of how many
    markers the language has, so they belong to the system, not to
    individual markers. Richer typological properties (symmetry,
    NCI behavior, Miestamo dimensions) live in
    `Phenomena/Negation/Typology.lean::NegationProfile`. -/
structure NegationSystem where
  /-- Standard negation marker(s). Order is editorial; Fragment files
      should put the unmarked / default-context marker first. -/
  markers : List NegMarkerEntry
  /-- WALS Ch 112A: morpheme classification. Should not be hand-encoded
      in Fragment files — use `NegationSystem.ofISO` to populate from the
      `Datasets.WALS` data, which is the single source of truth. -/
  wals112A : Option Datasets.WALS.F112A.NegativeMorphemeType := none
  /-- WALS Ch 143A: NegV / VNeg / double-negation pattern. Populated by
      `NegationSystem.ofISO`. -/
  wals143A : Option Datasets.WALS.F143A.NegVerbOrder := none
  /-- WALS Ch 144A: full S/O/V positional classification. Populated by
      `NegationSystem.ofISO`. -/
  wals144A : Option Datasets.WALS.F144A.PositionOfNegativeWordWithRespectToSubjectObjectAndVerb := none
  deriving Repr

/-- Build a `NegationSystem` for a language identified by ISO 639-3 code,
    pulling F112A / F143A / F144A values from the `Datasets.WALS` data.

    This is the canonical Fragment-side constructor — it ensures the
    WALS classification stays in sync with the dataset rather than being
    hand-stipulated per Fragment. Fields default to `none` for languages
    absent from a particular WALS chapter. Mirrors the
    `LanguageProfile.withWordOrderFromWALS`-style builder convention. -/
def NegationSystem.ofISO (iso : String) (markers : List NegMarkerEntry) :
    NegationSystem :=
  { markers
  , wals112A := (Datasets.WALS.F112A.lookupISO iso).map (·.value)
  , wals143A := (Datasets.WALS.F143A.lookupISO iso).map (·.value)
  , wals144A := (Datasets.WALS.F144A.lookupISO iso).map (·.value)
  }

end Core.Lexical.NegMarker
