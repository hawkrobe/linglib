import Linglib.Data.WALS.Datapoint
import Linglib.Data.WALS.Features.F112A
import Linglib.Data.WALS.Features.F113A
import Linglib.Data.WALS.Features.F114A
import Linglib.Data.WALS.Features.F115A
import Linglib.Data.WALS.Features.F143A
import Linglib.Data.WALS.Features.F144A
import Linglib.Typology.NegativeConcord

/-!
# Typology.Negation
@cite{dryer-2013-wals} @cite{haspelmath-2013} @cite{miestamo-2005}

Per-language typological substrate for the standard sentential negation
marker of a language: form, morphological status, position, symmetric/
asymmetric status, asymmetry subtype, and negative-indefinite strategy.

Mirrors the `Linglib/Typology/Possession.lean` (Possession), `Question.lean`
(Question), and `Case.lean` (Case) substrate-extension pattern: the
substrate carries (a) per-paradigm-entry schema (`NegMarkerEntry`,
`NegationSystem`), (b) the WALS-bundled per-language `NegationProfile`,
(c) WALS converters and sample-counting helpers.

## What lives here

- `NegMorphemeType` — direct projection from WALS Ch 112A's 6-way
  classification (`negativeAffix`, `negativeParticle`, `negativeAuxiliaryVerb`,
  `negativeWordUnclearIfVerbOrParticle`, `variationBetweenNegativeWordAndAffix`,
  `doubleNegation`). This is **Dryer's WALS Ch 112 morpheme typology**, NOT
  @cite{miestamo-2005}'s construction-level typology — Miestamo classifies
  *constructions*, not morphemes. The substrate carries Dryer's classification
  for cross-linguistic indexing; Miestamo's framework lives in
  `Studies/Miestamo2005.lean`.
- `NegMarkerPosition` — coarsening of WALS Ch 144A.
- `NegMarkerEntry` — one language's standard sentential negation marker.
- `NegationSystem` — bundles markers + WALS Ch 112A/143A/144A datapoints.
  The Fragment-side joint: every `Fragments/{Lang}/Negation.lean` exposes
  `def negationSystem : NegationSystem`.
- `NegSymmetry`, `AsymmetrySubtype`, `NegIndefiniteStrategy`,
  `NegVerbPosition`, `NegMorphemePosition` — WALS Ch 113-115/143A
  feature enums.
- `NegationProfile` — sibling per-language schema bundling Ch 112-115 +
  Greco's `negIsHead` + JinKoenig's `enAttested`. Each Fragment exposes
  `def negationProfile : NegationProfile` alongside `def negationSystem`.
  Sibling pattern (mirrors `Typology/Possession.lean::PossessionProfile`):
  the marker-side joint is independent from the typology-feature joint.
- `ofWALS112A`/`fromWALS113A`/`114A`/`115A`/`143A` converters.
- `countByMorphemeType`/`countBySymmetry` sample-counting helpers (consumed by
  `Studies/Dryer2013Negation.lean`) and the `NegIndefiniteStrategy.admits`
  negative-concord bridge.

## Theory-laden caveats

`NegSymmetry` and `AsymmetrySubtype` are **WALS Ch 113/114** values
(@cite{dryer-haspelmath-2013}). @cite{miestamo-2005}'s richer
two-dimension framework (constructional vs paradigmatic asymmetry,
derived vs independent source) lives in `Studies/Miestamo2005.lean`
because it goes beyond what WALS encodes.

## Out of scope

Polarity-sensitive items (n-words, NPIs, FCIs) are NOT marker-side data;
they live in `Typology/PolarityItem.lean` and in each language's
`Fragments/{Lang}/PolarityItems.lean`. Cross-linguistic theorems consuming
Fragment per-language data live in
`Studies/Dryer2013Negation.lean` (Ch 112/143A/144A grounding)
and `Studies/Miestamo2005.lean` (Ch 113-115 grounding).
-/

set_option autoImplicit false

namespace Typology.Negation

/-! ### Substrate enums -/

/-- Type of the standard negation morpheme @cite{dryer-2013-wals}.

    Six categories anchored on WALS Ch 112A (negative morpheme classification).
    Direct projection from `Data.WALS.F112A.NegativeMorphemeType` via
    `ofWALS112A`; the substrate enum exists for ergonomic pattern-matching
    in Fragment files. -/
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

    One-way coarsening of WALS Ch 144A's full S/O/V grid. The `wals144A`
    field on `NegationSystem` preserves the precise WALS classification
    for callers that need decoarsening. -/
inductive NegMarkerPosition where
  | preverbal
  | postverbal
  | discontinuous
  | morphological
  | other
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 113A: whether negation changes clause structure beyond adding
    the negative marker. Symmetric: no structural change. Asymmetric: changes
    in finiteness, verb paradigm, or TAM marking. -/
inductive NegSymmetry where
  | symmetric
  | asymmetric
  /-- Both symmetric and asymmetric (Type SymAsy): some constructions
      symmetric, others asymmetric. -/
  | both
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 114A: which grammatical domain is affected by asymmetric
    negation. The four primary subtypes correspond to @cite{miestamo-2005}'s
    A/Fin (finiteness), A/NonReal (reality status), A/Emph (emphasis),
    A/Cat (other categories) plus combined codings.

    Note: WALS Ch 114 does not encode A/Emph as a separate value
    (@cite{miestamo-2005} Table 2 distinguishes it; WALS collapses it). -/
inductive AsymmetrySubtype where
  | finiteness
  | realityStatus
  | emphasis
  | otherCategories
  | finAndNonReal
  | finAndEmph
  | finAndCat
  | nonRealAndCat
  | emphAndCat
  /-- Non-assignable: language has only symmetric negation. -/
  | nonAssignable
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 115A: how negative indefinites interact with predicate negation. -/
inductive NegIndefiniteStrategy where
  /-- Negative indefinites co-occur with predicate negation (negative concord).
      Dominant pattern worldwide. -/
  | cooccur
  /-- Negative indefinites preclude predicate negation. -/
  | preclude
  /-- Mixed (position-dependent or different indefinite series). -/
  | mixed
  /-- Negative existential construction. -/
  | negExistential
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 143A: position of negative morpheme relative to verb.
    Single-negation types (`NegV`/`VNeg`/`[Neg-V]`/`[V-Neg]`) plus
    multi-negation types (obligatory/optional double, optional triple). -/
inductive NegVerbPosition where
  /-- Preverbal negative particle: `NegV`. -/
  | preverbalParticle
  /-- Postverbal negative particle: `VNeg`. -/
  | postverbalParticle
  /-- Preverbal negative affix: `[Neg-V]`. -/
  | preverbalAffix
  /-- Postverbal negative affix: `[V-Neg]`. -/
  | postverbalAffix
  | negativeTone
  | mixedSingle
  | obligDoublNeg
  | optDoubleNeg
  | tripleNeg
  | optSingleNeg
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 143E/F: whether a language has preverbal and/or postverbal
    negative morphemes. -/
inductive NegMorphemePosition where
  | preverbalOnly
  | postverbalOnly
  | preverbalAffixOnly
  | postverbalAffixOnly
  | both
  | none
  deriving DecidableEq, BEq, Repr

/-! ### NegMarkerEntry / NegationSystem (Fragment marker-side joint) -/

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

/-- A language's standard negation system.

    The Fragment-side joint: every `Fragments/{Lang}/Negation.lean` exposes
    `def negationSystem : NegationSystem`. Multiple markers handle languages
    with mood/aspect/lexical-class alternation (Greek, Mandarin, Korean).
    Length-1 for most languages.

    WALS datapoints are bundled at the system level — in WALS coding,
    F112A/F143A/F144A take one value per language regardless of how many
    markers the language has. -/
structure NegationSystem where
  /-- Standard negation marker(s). Order is editorial; Fragment files
      should put the unmarked / default-context marker first. -/
  markers : List NegMarkerEntry
  /-- WALS Ch 112A: morpheme classification. Should not be hand-encoded
      in Fragment files — use `NegationSystem.ofISO` to populate from the
      `Data.WALS` data, which is the single source of truth. -/
  wals112A : Option Data.WALS.F112A.NegativeMorphemeType := none
  /-- WALS Ch 143A: NegV / VNeg / double-negation pattern. Populated by
      `NegationSystem.ofISO`. -/
  wals143A : Option Data.WALS.F143A.NegVerbOrder := none
  /-- WALS Ch 144A: full S/O/V positional classification. Populated by
      `NegationSystem.ofISO`. -/
  wals144A :
    Option Data.WALS.F144A.PositionOfNegativeWordWithRespectToSubjectObjectAndVerb
    := none
  deriving Repr

/-! ### NegationProfile (Fragment typology-feature joint) -/

/-- A language's negation profile across WALS Chapters 112-115, plus
    fields from @cite{greco-2020} (`negIsHead`) and @cite{jin-koenig-2021}
    (`enAttested`).

    Sibling Fragment-side joint to `NegationSystem`: every
    `Fragments/{Lang}/Negation.lean` exposes `def negationProfile :
    NegationProfile`. The two joints are independent because the data
    partition is real: `negationSystem.markers` is consumed by lexical
    code; `negationProfile` is consumed by typology studies. Mirrors
    `Typology/Possession.lean::PossessionProfile`. -/
structure NegationProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Ch 112: how standard negation is expressed. -/
  morphemeType : NegMorphemeType
  /-- Ch 113: symmetric, asymmetric, or both. -/
  symmetry : NegSymmetry
  /-- Ch 114: asymmetry subtype (`nonAssignable` if symmetric only). -/
  asymmetrySubtype : AsymmetrySubtype
  /-- Ch 115: strategy for negative indefinites, if attested. -/
  negIndefinite : Option NegIndefiniteStrategy := none
  /-- Illustrative negative marker form(s). -/
  negMarkers : List String := []
  /-- Is the negation marker a syntactic head (X°) rather than a phrase (XP)?
      Relevant for @cite{greco-2020}: only head-status markers can merge in
      CP to produce surprise negation. -/
  negIsHead : Option Bool := none
  /-- Is expletive negation attested in this language?
      @cite{jin-koenig-2021} (722-language survey: EN in 74 languages)
      and @cite{rett-2026}. -/
  enAttested : Option Bool := none
  deriving Repr

/-! ### WALS converters -/

/-- WALS Ch 112A → `NegMorphemeType`. -/
def ofWALS112A : Data.WALS.F112A.NegativeMorphemeType → NegMorphemeType
  | .negativeAffix => .affix
  | .negativeParticle => .particle
  | .negativeAuxiliaryVerb => .auxVerb
  | .negativeWordUnclearIfVerbOrParticle => .wordUnclear
  | .variationBetweenNegativeWordAndAffix => .variation
  | .doubleNegation => .doubleNeg

/-- WALS Ch 113A → `NegSymmetry`. -/
def fromWALS113A : Data.WALS.F113A.NegationSymmetry → NegSymmetry
  | .symmetric  => .symmetric
  | .asymmetric => .asymmetric
  | .both       => .both

/-- WALS Ch 114A → `AsymmetrySubtype`. -/
def fromWALS114A :
    Data.WALS.F114A.AsymmetricNegationSubtype → AsymmetrySubtype
  | .aFin           => .finiteness
  | .aNonreal       => .realityStatus
  | .aCat           => .otherCategories
  | .aFinAndANonreal => .finAndNonReal
  | .aFinAndACat    => .finAndCat
  | .aNonrealAndACat => .nonRealAndCat
  | .nonAssignable  => .nonAssignable

/-- WALS Ch 115A → `NegIndefiniteStrategy`. -/
def fromWALS115A :
    Data.WALS.F115A.NegativeIndefiniteType → NegIndefiniteStrategy
  | .predicateNegationAlsoPresent      => .cooccur
  | .noPredicateNegation               => .preclude
  | .mixedBehaviour                    => .mixed
  | .negativeExistentialConstruction   => .negExistential

/-- WALS Ch 143A → `NegVerbPosition`. -/
def fromWALS143A : Data.WALS.F143A.NegVerbOrder → NegVerbPosition
  | .negv => .preverbalParticle
  | .vneg => .postverbalParticle
  | .negV => .preverbalAffix
  | .vNeg => .postverbalAffix
  | .negativeTone => .negativeTone
  | .type1Type2 => .mixedSingle
  | .type1Type3 => .mixedSingle
  | .type1Type4 => .mixedSingle
  | .type2Type3 => .mixedSingle
  | .type2Type4 => .mixedSingle
  | .type3Type4 => .mixedSingle
  | .type3NegativeInfix => .mixedSingle
  | .optsingleneg => .optSingleNeg
  | .obligdoubleneg => .obligDoublNeg
  | .optdoubleneg => .optDoubleNeg
  | .opttriplenegObligdoubleneg => .tripleNeg
  | .opttriplenegOptdoubleneg => .tripleNeg

/-- Build a `NegationSystem` for a language identified by ISO 639-3 code,
    pulling F112A / F143A / F144A values from the `Data.WALS` data. -/
def NegationSystem.ofISO (iso : String) (markers : List NegMarkerEntry) :
    NegationSystem :=
  { markers
  , wals112A := (Data.WALS.F112A.lookupISO iso).map (·.value)
  , wals143A := (Data.WALS.F143A.lookupISO iso).map (·.value)
  , wals144A := (Data.WALS.F144A.lookupISO iso).map (·.value)
  }

/-! ### NegationProfile helpers (Fragment-consumed) -/

/-- Does a language use a given morpheme type? -/
def NegationProfile.hasMorphemeType (p : NegationProfile)
    (t : NegMorphemeType) : Bool :=
  p.morphemeType == t

/-- Does a language have symmetric negation (either symmetric only or both)? -/
def NegationProfile.hasSymmetric (p : NegationProfile) : Bool :=
  p.symmetry == .symmetric || p.symmetry == .both

/-- Does a language have asymmetric negation (either asymmetric only or both)? -/
def NegationProfile.hasAsymmetric (p : NegationProfile) : Bool :=
  p.symmetry == .asymmetric || p.symmetry == .both

/-- Does a language show negative concord? -/
def NegationProfile.hasNegConcord (p : NegationProfile) : Bool :=
  p.negIndefinite == some .cooccur

/-- Count of languages in a sample with a given morpheme type. -/
def countByMorphemeType (langs : List NegationProfile)
    (t : NegMorphemeType) : Nat :=
  (langs.filter (·.hasMorphemeType t)).length

/-- Count of languages in a sample with a given symmetry type. -/
def countBySymmetry (langs : List NegationProfile) (s : NegSymmetry) : Nat :=
  (langs.filter (·.symmetry == s)).length

/-! ### Negative concord: WALS 115A strategy ↔ item-level n-word status -/

open Typology.NegativeConcord (NWordStatus)

/-- Whether the negative-indefinite system shows negative concord
    (@cite{van-der-auwera-van-alsenoy-2016}): WALS 115A `cooccur` (concord) and `mixed`
    (position-dependent) do; `preclude` (double negation) and `negExistential` do not.
    Broader than `NegationProfile.hasNegConcord`, which tests `cooccur` only. -/
def NegIndefiniteStrategy.hasNegativeConcord : NegIndefiniteStrategy → Bool
  | .cooccur | .mixed => true
  | .preclude | .negExistential => false

/-- Whether an item-level n-word status is consistent with a language's WALS 115A
    negative-indefinite strategy: an n-word needs a concord system, an inherently
    negative quantifier a non-concord (double-negation / neg-existential) one, an NPI
    any (@cite{van-der-auwera-van-alsenoy-2016}). -/
def NegIndefiniteStrategy.admits : NegIndefiniteStrategy → NWordStatus → Bool
  | strat, .nWord => strat.hasNegativeConcord
  | strat, .negQuantifier => !strat.hasNegativeConcord
  | _, .npi => true

/-- N-words live in negative-concord systems, inherently negative quantifiers in
    double-negation ones (@cite{van-der-auwera-van-alsenoy-2016}). -/
theorem nWord_vs_negQuantifier :
    (NegIndefiniteStrategy.cooccur).admits .nWord = true ∧
    (NegIndefiniteStrategy.preclude).admits .nWord = false ∧
    (NegIndefiniteStrategy.preclude).admits .negQuantifier = true := by decide

end Typology.Negation
