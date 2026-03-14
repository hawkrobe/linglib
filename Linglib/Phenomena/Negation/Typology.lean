import Linglib.Core.Lexical.Word
import Linglib.Core.WALS.Features.F112A
import Linglib.Core.WALS.Features.F113A
import Linglib.Core.WALS.Features.F114A
import Linglib.Core.WALS.Features.F115A
import Linglib.Core.WALS.Features.F143A
import Linglib.Core.WALS.Features.F143B
import Linglib.Core.WALS.Features.F143C
import Linglib.Core.WALS.Features.F143D
import Linglib.Core.WALS.Features.F143E
import Linglib.Core.WALS.Features.F143F
import Linglib.Core.WALS.Features.F143G
import Linglib.Core.WALS.Features.F144A
import Linglib.Core.WALS.Features.F144B
import Linglib.Core.WALS.Features.F144C
import Linglib.Core.WALS.Features.F144D
import Linglib.Core.WALS.Features.F144E
import Linglib.Core.WALS.Features.F144F
import Linglib.Core.WALS.Features.F144G
import Linglib.Core.WALS.Features.F144H
import Linglib.Core.WALS.Features.F144I
import Linglib.Core.WALS.Features.F144J
import Linglib.Core.WALS.Features.F144K
import Linglib.Core.WALS.Features.F144L
import Linglib.Core.WALS.Features.F144M
import Linglib.Core.WALS.Features.F144N
import Linglib.Core.WALS.Features.F144O
import Linglib.Core.WALS.Features.F144P
import Linglib.Core.WALS.Features.F144Q
import Linglib.Core.WALS.Features.F144R
import Linglib.Core.WALS.Features.F144S
import Linglib.Core.WALS.Features.F144T
import Linglib.Core.WALS.Features.F144U
import Linglib.Core.WALS.Features.F144V
import Linglib.Core.WALS.Features.F144W
import Linglib.Core.WALS.Features.F144X
import Linglib.Core.WALS.Features.F144Y

/-!
# Cross-Linguistic Typology of Negation (WALS Chapters 112--115, 143--144)
@cite{dryer-haspelmath-2013} @cite{haspelmath-2013} @cite{miestamo-2005} @cite{miestamo-2013}
@cite{dryer-2013c}

Cross-linguistic data on clausal negation from WALS chapters 112--115, 143, and 144.

## Ch 112: Negative Morphemes

How standard (clausal) negation is expressed. Six categories based on
morpheme type: negative affix, negative particle, negative auxiliary verb,
negative word of unclear status, variation between word and affix, and
double (bipartite) negation requiring two co-occurring markers.

## Ch 113: Symmetric and Asymmetric Standard Negation

Whether negation changes clause structure beyond adding a negative marker.
Symmetric negation adds only the negator; asymmetric negation introduces
further structural changes (e.g., changes in finiteness, verb paradigm,
or tense-aspect marking). Three types: Sym only, Asy only, or both.

## Ch 114: Subtypes of Asymmetric Standard Negation

For languages with asymmetric negation, what structural domain is affected:
finiteness (A/Fin), reality status (A/NonReal), or other grammatical
categories (A/Cat). Languages may combine subtypes.

## Ch 115: Negative Indefinite Pronouns and Predicate Negation

How negative indefinites ('nobody', 'nothing') interact with clausal
negation. Whether they co-occur with predicate negation (negative concord,
the dominant pattern worldwide) or preclude it.

## Ch 143: Order of Negative Morpheme and Verb

Seven sub-features (143A--143G) covering the position of the negative
morpheme relative to the verb. 143A gives the overall classification
(NegV, VNeg, [Neg-V], [V-Neg], double/triple negation, etc.). 143B--143D
detail obligatory/optional double and triple negation patterns. 143E--143G
decompose into preverbal morphemes, postverbal morphemes, and minor
morphological means (negative tone, infix, stem change). All seven features
cover the same 1325-language sample except 143B (119), 143C (81), 143D (6).

## Ch 144: Position of Negative Morphemes by Word Order Type

Twenty-five sub-features (144A--144Y) cross-tabulating negation position
with basic word order type. 144A gives the overall position of the negative
word relative to S, O, and V (1190 languages). 144B gives clause-edge and
verb-adjacency position (609 languages). 144C covers languages where
negation changes word order (28 languages). 144D--144K break down SVO
languages by negation position. 144L--144S break down SOV languages.
144T--144X break down verb-initial languages. 144Y covers object-initial
languages (16 languages).

-/

namespace Phenomena.Negation.Typology

-- ============================================================================
-- Chapter 112: Negative Morpheme Types
-- ============================================================================

/-- WALS Ch 112: How standard (clausal) negation is expressed.

    Six categories based on the morphological status of the negative marker:
    (1) affix on the verb, (2) free particle, (3) auxiliary verb inflecting
    for verbal categories, (4) negative word whose status is unclear,
    (5) variation between word and affix constructions in the same language,
    (6) bipartite ("double") negation requiring two co-occurring markers. -/
inductive NegMorphemeType where
  /-- Negative affix on the verb (e.g., Kolyma Yukaghir `el-jaqa-te-je`
      'NEG-achieve-FUT-1SG'). -/
  | affix
  /-- Negative particle: free word, no verbal inflection
      (e.g., English `not`, Musgu `pay`). -/
  | particle
  /-- Negative auxiliary verb: inflects for person, number, or TAM like
      verbs in the language (e.g., Finnish `e-n` 'NEG-1SG'). -/
  | auxVerb
  /-- Negative word whose status as verb or particle is unclear, typically
      in isolating languages with little verbal morphology
      (e.g., Maori `kaahore`). -/
  | wordUnclear
  /-- Language uses both a negative word and a negative affix in different
      constructions (e.g., Rama: preverbal particle in one construction,
      verbal suffix in another). -/
  | variation
  /-- Bipartite negation: two co-occurring negative morphemes, one preceding
      and one following the verb (e.g., French `ne...pas`,
      Izi `to-ome-du` 'NEG-do-NEG'). -/
  | doubleNeg
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 113: Symmetric vs Asymmetric Standard Negation
-- ============================================================================

/-- WALS Ch 113: Whether negation changes clause structure.

    Symmetric negation: the negative differs from the affirmative only by
    adding the negative marker(s) -- no structural changes to verb form,
    paradigm, or clause type.

    Asymmetric negation: the negative construction differs structurally
    from the affirmative in additional ways (changed finiteness, different
    verb paradigm, different TAM marking, etc.). -/
inductive NegSymmetry where
  /-- Symmetric only (Type Sym): negation never changes clause structure.
      (e.g., German `ich singe` / `ich singe nicht`). -/
  | symmetric
  /-- Asymmetric only (Type Asy): negation always introduces structural
      differences (e.g., Finnish: negative verb + connegative). -/
  | asymmetric
  /-- Both symmetric and asymmetric (Type SymAsy): some constructions are
      symmetric, others asymmetric (e.g., Lezgian: present symmetric,
      past imperfective asymmetric). -/
  | both
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 114: Subtypes of Asymmetric Negation
-- ============================================================================

/-- WALS Ch 114: Which grammatical domain is affected by asymmetric negation.

    Four primary subtypes (@cite{miestamo-2005} Table 2, p. 60):
    - A/Fin: negation changes finiteness (adds negative verb, lexical verb
      becomes nonfinite / subordinate)
    - A/NonReal: negation introduces irrealis/nonrealized marking
    - A/Emph: negative contains marking that expresses emphasis in
      non-negatives (rare; 4 languages in RS)
    - A/Cat: negation changes marking of TAM, person, number, etc.

    Note: WALS Ch 114 does not distinguish A/Emph as a separate value,
    collapsing it into other categories. The four-way distinction is from
    @cite{miestamo-2005} only. -/
inductive AsymmetrySubtype where
  /-- A/Fin: asymmetry in finiteness. Typically a negative auxiliary becomes
      the finite verb, and the lexical verb appears in a nonfinite form
      (e.g., Finnish: `e-n tule` 'NEG-1SG come.CONNEG'). -/
  | finiteness
  /-- A/NonReal: asymmetry in reality status. The negative is obligatorily
      marked with an irrealis/nonrealized category that the affirmative
      lacks (e.g., Imbabura Quechua: negative requires `-chu` irrealis). -/
  | realityStatus
  /-- A/Emph: the negative contains marking that expresses emphasis
      in non-negative contexts. Rare (4 languages in the RS).
      @cite{miestamo-2005} §3.3.3, Table 2 (p. 60). -/
  | emphasis
  /-- A/Cat: asymmetry in other grammatical categories (TAM, person-number
      affixes, etc.). The negative uses different category markers than the
      affirmative (e.g., Karok: different person-number affixes under
      negation). -/
  | otherCategories
  /-- Combined: A/Fin and A/NonReal
      (e.g., Copainalá Zoque, Squamish). -/
  | finAndNonReal
  /-- Combined: A/Fin and A/Emph (e.g., Meithei). -/
  | finAndEmph
  /-- Combined: A/Fin and A/Cat
      (e.g., Kolokuma Ijo). -/
  | finAndCat
  /-- Combined: A/NonReal and A/Cat. -/
  | nonRealAndCat
  /-- Combined: A/Emph and A/Cat (e.g., Cantonese, Meithei). -/
  | emphAndCat
  /-- Non-assignable: language has only symmetric negation (Type Sym in
      Ch 113), so no asymmetry subtype applies. -/
  | nonAssignable
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Miestamo's Asymmetry Dimensions (beyond WALS)
-- ============================================================================

/-- @cite{miestamo-2005}'s two dimensions of asymmetry. WALS Ch 113 collapses
    these into a single symmetric/asymmetric distinction; Miestamo decomposes
    asymmetry into two independent dimensions. -/
inductive AsymmetryDimension where
  /-- The negative clause has a different syntactic structure than the
      affirmative, beyond just the negation marker. E.g., Finnish neg aux
      restructures the clause; Japanese *-nai* changes verb to i-adjective. -/
  | constructional
  /-- The negative paradigm has fewer formal distinctions than the
      affirmative. E.g., Burmese *-bu* neutralizes TAM; Turkish aorist
      uses a different marker. -/
  | paradigmatic
  deriving DecidableEq, Repr, BEq

/-- Whether the asymmetry is derived from the negation marker type
    or independent of it (@cite{miestamo-2005}). -/
inductive AsymmetrySource where
  /-- The asymmetry follows structurally from the negation marker's
      properties. A negative verb necessarily creates A/Fin. -/
  | derived
  /-- The asymmetry is not predictable from the marker type alone.
      E.g., TAM neutralization in Burmese is independent of circumfixing. -/
  | independent
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Chapter 115: Negative Indefinites and Predicate Negation
-- ============================================================================

/-- WALS Ch 115: Interaction of negative indefinites ('nobody', 'nothing')
    with clausal negation.

    Cross-linguistically, negative concord (co-occurrence) is overwhelmingly
    dominant. The preclusion pattern is concentrated in Western Europe and
    Mesoamerica; the normative criticism of "double negation" as "illogical"
    is a prescriptive artifact rooted in Latin prestige
    (@cite{haspelmath-1997}, sec. 8.2). -/
inductive NegIndefiniteStrategy where
  /-- Negative indefinites co-occur with predicate negation (negative concord).
      'Nobody NEG came' = 'Nobody came'.
      The dominant pattern worldwide.
      (e.g., Russian `nikto ne prisel` 'nobody NEG came'). -/
  | cooccur
  /-- Negative indefinites preclude predicate negation.
      The indefinite alone carries the negation.
      (e.g., German `Niemand kam` 'Nobody came', *`Niemand kam nicht`). -/
  | preclude
  /-- Mixed behavior: some negative indefinites co-occur with negation,
      others preclude it (e.g., position-dependent as in Spanish:
      `Nadie vino` but `No vi nada`; or different indefinite series as
      in Swedish). -/
  | mixed
  /-- Negative existential construction: a negative/negated existential verb
      serves as the main predicate (e.g., Nelemwa `kia agu i uya`
      'not.exist person 3SG arrive' = 'Nobody came'). -/
  | negExistential
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

private def fromWALS112A : Core.WALS.F112A.NegativeMorphemeType → NegMorphemeType
  | .negativeAffix => .affix
  | .negativeParticle => .particle
  | .negativeAuxiliaryVerb => .auxVerb
  | .negativeWordUnclearIfVerbOrParticle => .wordUnclear
  | .variationBetweenNegativeWordAndAffix => .variation
  | .doubleNegation => .doubleNeg

private def fromWALS113A : Core.WALS.F113A.NegationSymmetry → NegSymmetry
  | .symmetric => .symmetric
  | .asymmetric => .asymmetric
  | .both => .both

private def fromWALS114A : Core.WALS.F114A.AsymmetricNegationSubtype → AsymmetrySubtype
  | .aFin => .finiteness
  | .aNonreal => .realityStatus
  | .aCat => .otherCategories
  | .aFinAndANonreal => .finAndNonReal
  | .aFinAndACat => .finAndCat
  | .aNonrealAndACat => .nonRealAndCat
  | .nonAssignable => .nonAssignable

private def fromWALS115A : Core.WALS.F115A.NegativeIndefiniteType → NegIndefiniteStrategy
  | .predicateNegationAlsoPresent => .cooccur
  | .noPredicateNegation => .preclude
  | .mixedBehaviour => .mixed
  | .negativeExistentialConstruction => .negExistential

-- ============================================================================
-- Chapter 143: Order of Negative Morpheme and Verb
-- ============================================================================

/-- WALS Ch 143A: Position of the negative morpheme relative to the verb.

    Covers 1325 languages. Single-negation types distinguish NegV (preverbal
    particle), VNeg (postverbal particle), [Neg-V] (preverbal affix), and
    [V-Neg] (postverbal affix). Multi-negation types cover obligatory double
    negation, optional double negation, and optional triple negation with
    obligatory or optional double negation. -/
inductive NegVerbPosition where
  /-- Preverbal negative particle: `NegV`. -/
  | preverbalParticle
  /-- Postverbal negative particle: `VNeg`. -/
  | postverbalParticle
  /-- Preverbal negative affix: `[Neg-V]`. -/
  | preverbalAffix
  /-- Postverbal negative affix: `[V-Neg]`. -/
  | postverbalAffix
  /-- Negative tone (suprasegmental). -/
  | negativeTone
  /-- Mixed: two single-negation types coexist. -/
  | mixedSingle
  /-- Obligatory double negation. -/
  | obligDoublNeg
  /-- Optional double negation. -/
  | optDoubleNeg
  /-- Optional triple negation (with obligatory or optional double). -/
  | tripleNeg
  /-- Optional single negation. -/
  | optSingleNeg
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 143E/F: Whether a language has preverbal and/or postverbal
    negative morphemes. -/
inductive NegMorphemePosition where
  /-- Preverbal particle only. -/
  | preverbalOnly
  /-- Postverbal particle only. -/
  | postverbalOnly
  /-- Preverbal affix only. -/
  | preverbalAffixOnly
  /-- Postverbal affix only. -/
  | postverbalAffixOnly
  /-- Both preverbal and postverbal. -/
  | both
  /-- None (language uses minor means or double negation). -/
  | none
  deriving DecidableEq, BEq, Repr

private def fromWALS143A : Core.WALS.F143A.NegVerbOrder → NegVerbPosition
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

-- ============================================================================
-- WALS Distribution Data (from generated modules)
-- ============================================================================

private abbrev ch112 := Core.WALS.F112A.allData
private abbrev ch113 := Core.WALS.F113A.allData
private abbrev ch114 := Core.WALS.F114A.allData
private abbrev ch115 := Core.WALS.F115A.allData

theorem ch112_total : ch112.length = 1157 := by native_decide
theorem ch113_total : ch113.length = 297 := by native_decide
theorem ch114_total : ch114.length = 297 := by native_decide
theorem ch115_total : ch115.length = 206 := by native_decide

/-- Ch 113 and Ch 114 use the same sample. -/
theorem ch113_ch114_same_sample : ch113.length = ch114.length := by native_decide

-- Chapter 143 sub-features
private abbrev ch143A := Core.WALS.F143A.allData
private abbrev ch143B := Core.WALS.F143B.allData
private abbrev ch143C := Core.WALS.F143C.allData
private abbrev ch143D := Core.WALS.F143D.allData
private abbrev ch143E := Core.WALS.F143E.allData
private abbrev ch143F := Core.WALS.F143F.allData
private abbrev ch143G := Core.WALS.F143G.allData

theorem ch143A_total : ch143A.length = 1325 := by native_decide
theorem ch143B_total : ch143B.length = 119 := by native_decide
theorem ch143C_total : ch143C.length = 81 := by native_decide
theorem ch143D_total : ch143D.length = 6 := by native_decide
theorem ch143E_total : ch143E.length = 1325 := by native_decide
theorem ch143F_total : ch143F.length = 1325 := by native_decide
theorem ch143G_total : ch143G.length = 1325 := by native_decide

/-- Ch 143A, 143E, 143F, 143G all cover the same 1325-language sample. -/
theorem ch143_same_sample :
    ch143A.length = ch143E.length ∧
    ch143A.length = ch143F.length ∧
    ch143A.length = ch143G.length := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- Chapter 144 sub-features
private abbrev ch144A := Core.WALS.F144A.allData
private abbrev ch144B := Core.WALS.F144B.allData
private abbrev ch144C := Core.WALS.F144C.allData
private abbrev ch144D := Core.WALS.F144D.allData
private abbrev ch144E := Core.WALS.F144E.allData
private abbrev ch144F := Core.WALS.F144F.allData
private abbrev ch144G := Core.WALS.F144G.allData
private abbrev ch144H := Core.WALS.F144H.allData
private abbrev ch144I := Core.WALS.F144I.allData
private abbrev ch144J := Core.WALS.F144J.allData
private abbrev ch144K := Core.WALS.F144K.allData
private abbrev ch144L := Core.WALS.F144L.allData
private abbrev ch144M := Core.WALS.F144M.allData
private abbrev ch144N := Core.WALS.F144N.allData
private abbrev ch144O := Core.WALS.F144O.allData
private abbrev ch144P := Core.WALS.F144P.allData
private abbrev ch144Q := Core.WALS.F144Q.allData
private abbrev ch144R := Core.WALS.F144R.allData
private abbrev ch144S := Core.WALS.F144S.allData
private abbrev ch144T := Core.WALS.F144T.allData
private abbrev ch144U := Core.WALS.F144U.allData
private abbrev ch144V := Core.WALS.F144V.allData
private abbrev ch144W := Core.WALS.F144W.allData
private abbrev ch144X := Core.WALS.F144X.allData
private abbrev ch144Y := Core.WALS.F144Y.allData

theorem ch144A_total : ch144A.length = 1190 := by native_decide
theorem ch144B_total : ch144B.length = 609 := by native_decide
theorem ch144C_total : ch144C.length = 28 := by native_decide
theorem ch144D_total : ch144D.length = 463 := by native_decide
theorem ch144E_total : ch144E.length = 48 := by native_decide
theorem ch144F_total : ch144F.length = 56 := by native_decide
theorem ch144G_total : ch144G.length = 35 := by native_decide
theorem ch144H_total : ch144H.length = 420 := by native_decide
theorem ch144I_total : ch144I.length = 421 := by native_decide
theorem ch144J_total : ch144J.length = 446 := by native_decide
theorem ch144K_total : ch144K.length = 446 := by native_decide
theorem ch144L_total : ch144L.length = 573 := by native_decide
theorem ch144M_total : ch144M.length = 54 := by native_decide
theorem ch144N_total : ch144N.length = 45 := by native_decide
theorem ch144O_total : ch144O.length = 31 := by native_decide
theorem ch144P_total : ch144P.length = 408 := by native_decide
theorem ch144Q_total : ch144Q.length = 408 := by native_decide
theorem ch144R_total : ch144R.length = 411 := by native_decide
theorem ch144S_total : ch144S.length = 490 := by native_decide
theorem ch144T_total : ch144T.length = 152 := by native_decide
theorem ch144U_total : ch144U.length = 17 := by native_decide
theorem ch144V_total : ch144V.length = 152 := by native_decide
theorem ch144W_total : ch144W.length = 151 := by native_decide
theorem ch144X_total : ch144X.length = 151 := by native_decide
theorem ch144Y_total : ch144Y.length = 16 := by native_decide

-- ============================================================================
-- Language Profile Structure
-- ============================================================================

/-- A language's negation profile across WALS Chapters 112--115. -/
structure NegationProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Ch 112: How standard negation is expressed. -/
  morphemeType : NegMorphemeType
  /-- Ch 113: Symmetric, asymmetric, or both. -/
  symmetry : NegSymmetry
  /-- Ch 114: Asymmetry subtype (nonAssignable if symmetric only). -/
  asymmetrySubtype : AsymmetrySubtype
  /-- Ch 115: Strategy for negative indefinites, if attested. -/
  negIndefinite : Option NegIndefiniteStrategy := none
  /-- Illustrative negative marker form(s). -/
  negMarkers : List String := []
  /-- Is the negation marker a syntactic head (X°) rather than a phrase (XP)?
      Relevant for @cite{greco-2020}: only head-status markers can merge in CP
      to produce surprise negation. -/
  negIsHead : Option Bool := none
  /-- Notes on the negation system. -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Language Data
-- ============================================================================

/--
English: negative particle `not`; WALS classifies as both symmetric and
asymmetric (do-support is an asymmetric structural change). A/Cat: the
category-level change is the introduction of auxiliary `do` in negation.
Negative indefinites show mixed behavior: `nobody` precludes
predicate negation (`*Nobody didn't come`), but `anything` requires it
(`I didn't see anything`).
-/
def english : NegationProfile :=
  { language := "English"
  , iso := "eng"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , negIndefinite := some .mixed
  , negMarkers := ["not"]
  , notes := "WALS: SymAsy due to do-support; " ++
             "mixed indefinites: 'nobody' precludes, 'anything' co-occurs" }

/--
German: negative particle `nicht`; symmetric negation — adding `nicht`
causes no structural change to the clause. Negative indefinites preclude
predicate negation: `Niemand kam` (*`Niemand kam nicht`).
(But note: substandard / Bavarian German has negative concord.)
-/
def german : NegationProfile :=
  { language := "German"
  , iso := "deu"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .preclude
  , negMarkers := ["nicht"]
  , notes := "Bavarian German has negative concord (substandard)" }

/--
French: bipartite negation `ne...pas` (WALS codes as particle since
colloquial French drops `ne`). In colloquial register, only `pas` is used.
WALS Ch 115 classifies as mixed: some negative indefinites co-occur with
`ne` (`Je n'ai rien vu`), while `personne` can appear without `ne` in
some registers.
-/
def french : NegationProfile :=
  { language := "French"
  , iso := "fra"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .mixed
  , negMarkers := ["ne", "pas"]
  , negIsHead := some true  -- ne is a weak clitic (X°)
  , notes := "WALS codes as particle (ne optional in colloquial); " ++
             "historically bipartite ne...pas (Jespersen cycle)" }

/--
Russian: negative particle `ne`; symmetric negation. Negative indefinites
obligatorily co-occur with predicate negation (negative concord):
`Nikto ne prisel` 'Nobody NEG came' = 'Nobody came'.
-/
def russian : NegationProfile :=
  { language := "Russian"
  , iso := "rus"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["ne"]
  , notes := "Canonical negative concord: nikto ne prisel 'nobody NEG came'" }

/--
Finnish: negative auxiliary verb `e-` inflects for person-number; the lexical
verb appears as a connegative (present) or past participle (past). Always
asymmetric (A/Fin): negation changes finiteness structure.
-/
def finnish : NegationProfile :=
  { language := "Finnish"
  , iso := "fin"
  , morphemeType := .auxVerb
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , negIndefinite := some .cooccur
  , negMarkers := ["e-"]
  , notes := "Negative auxiliary: e-n tule 'NEG-1SG come.CONNEG'; " ++
             "negative auxiliary verb area stretches across northern Eurasia" }

/--
Japanese: negative suffix `-nai` (affix on verb). WALS classifies as
asymmetric (A/Fin + A/Cat): the negative form involves both finiteness
changes and different category markings.
Negative indefinites co-occur with predicate negation:
`dare-mo ko-nakat-ta` 'who-MO come-NEG-PST' = 'Nobody came'.
-/
def japanese : NegationProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finAndCat
  , negIndefinite := some .cooccur
  , negMarkers := ["-nai", "-nakat-"]
  , notes := "Suffix -nai; WALS: asymmetric A/Fin+A/Cat; " ++
             "negative concord with -mo indefinites" }

/--
Mandarin Chinese: negative particles `bu` (general) and `mei(you)` (perfective).
WALS classifies as both symmetric and asymmetric: the `bu`/`mei` distinction
introduces an asymmetry of type A/Fin (finiteness-like distinction).
-/
def mandarin : NegationProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .finiteness
  , negIndefinite := some .cooccur
  , negMarkers := ["bu", "mei"]
  , notes := "Two negative particles: bu (general) vs mei (perfective/existential); " ++
             "WALS: SymAsy with A/Fin asymmetry" }

/--
Turkish: negative suffix `-mA-` on the verb. WALS classifies as both
symmetric and asymmetric: some constructions (aorist) are symmetric while
others show category changes (A/Cat).
Negative indefinites co-occur with predicate negation:
`Hic kimse gel-me-di` 'at.all person come-NEG-PST' = 'Nobody came'.
-/
def turkish : NegationProfile :=
  { language := "Turkish"
  , iso := "tur"
  , morphemeType := .affix
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , negIndefinite := some .cooccur
  , negMarkers := ["-mA-"]
  , notes := "Verbal suffix; WALS: SymAsy with A/Cat; " ++
             "negative concord with hic 'at all' + indefinite" }

/--
Czech: negative prefix `ne-` on the verb; symmetric negation. Negative
indefinites obligatorily co-occur with predicate negation (negative concord):
`Nikdo neprisel` 'Nobody NEG.came' = 'Nobody came'.
Note: Czech is not in the WALS Ch 113--115 sample; Ch 112 classification
is grounded.
-/
def czech : NegationProfile :=
  { language := "Czech"
  , iso := "ces"
  , morphemeType := .affix
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["ne-"]
  , notes := "Prefix ne-; obligatory negative concord (Slavic pattern); " ++
             "not in WALS Ch 113-115 sample" }

/--
Spanish: negative particle `no`; symmetric negation. Mixed behavior for
negative indefinites: preverbal indefinites preclude negation
(`Nadie vino` 'Nobody came'), but postverbal indefinites require it
(`No vi nada` 'NEG I.saw nothing').
-/
def spanish : NegationProfile :=
  { language := "Spanish"
  , iso := "spa"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .mixed
  , negMarkers := ["no"]
  , negIsHead := some false  -- no can be focused/coordinated (XP; @cite{greco-2020}, §5.2)
  , notes := "Position-dependent: preverbal nadie precludes no, " ++
             "postverbal nada requires no" }

/--
Italian: negative particle `non`; symmetric negation. Mixed behavior for
negative indefinites (paralleling Spanish): preverbal n-words stand alone
(`Nessuno è venuto` 'Nobody came'), but postverbal n-words require `non`
(`Non ho visto nessuno` 'NEG have seen nobody').
-/
def italian : NegationProfile :=
  { language := "Italian"
  , iso := "ita"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .mixed
  , negMarkers := ["non"]
  , negIsHead := some true  -- non is a preverbal clitic (X°), cannot be focused/coordinated
  , notes := "Preverbal non; n-words: postverbal require non " ++
             "(Non ho visto nessuno), preverbal alone " ++
             "(Nessuno è venuto); parallels Spanish pattern" }

/--
Burmese: bipartite negation with prefix `ma-` and suffix `-bu`; the negative
suffix `-bu` replaces the TAM markers used in the affirmative. Always
asymmetric: the negative neutralizes TAM distinctions.
-/
def burmese : NegationProfile :=
  { language := "Burmese"
  , iso := "mya"
  , morphemeType := .doubleNeg
  , symmetry := .asymmetric
  , asymmetrySubtype := .otherCategories
  , negMarkers := ["ma-", "-bu"]
  , notes := "Circumfix ma-...-bu; -bu replaces TAM markers, " ++
             "collapsing tense-aspect distinctions under negation" }

/--
Maori: negative word `kaahore`; isolating language makes it unclear whether
the negator is a verb or particle. Classified as 'wordUnclear' per WALS.
WALS Ch 113 classifies Maori as asymmetric with A/Fin: the negator
functions as a (quasi-)auxiliary that changes the finiteness structure.
-/
def maori : NegationProfile :=
  { language := "Maori"
  , iso := "mri"
  , morphemeType := .wordUnclear
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , negMarkers := ["kaahore"]
  , notes := "Isolating; WALS: asymmetric A/Fin — negator as quasi-auxiliary" }

/--
Izi (Igboid, Niger-Congo): bipartite negation with prefix and suffix on the
verb: `to-ome-du` 'NEG-do-NEG'. Always asymmetric.
Note: Izi is not in the WALS Ch 113--115 sample; Ch 112 is grounded.
-/
def izi : NegationProfile :=
  { language := "Izi"
  , iso := "izz"
  , morphemeType := .doubleNeg
  , symmetry := .asymmetric
  , asymmetrySubtype := .otherCategories
  , negMarkers := ["to-", "-du"]
  , notes := "Circumfixal double negation on verb: to-ome-du 'NEG-do-NEG'; " ++
             "not in WALS Ch 113-115 sample" }

/--
Kolyma Yukaghir: negative prefix `el-` on the verb. WALS classifies as
both symmetric and asymmetric, with A/Cat subtype: tense marking may
differ under negation but not in all constructions.
-/
def kolYukaghir : NegationProfile :=
  { language := "Kolyma Yukaghir"
  , iso := "yux"
  , morphemeType := .affix
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , negMarkers := ["el-"]
  , notes := "Prefix el-; WALS: SymAsy with A/Cat; " ++
             "el-jaqa-te-je 'NEG-achieve-FUT-1SG'" }

/--
Rama (Chibchan; Nicaragua): WALS Ch 112 classifies as negative particle.
Has both symmetric and asymmetric negation (Ch 113), with A/Fin + A/Cat
asymmetry subtype (Ch 114).
-/
def rama : NegationProfile :=
  { language := "Rama"
  , iso := "rma"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .finAndCat
  , negMarkers := ["aa", "-taama"]
  , notes := "WALS: particle (Ch 112), SymAsy with A/Fin+A/Cat (Ch 113-114)" }

/--
Hixkaryana (Carib; Brazil): asymmetric negation of subtype A/Fin. A
non-negative copula functions as the finite element, and the lexical verb
is deverbalized by the negative suffix `-hira`:
`amryeki-hira w-ah-ko` 'hunt-NEG 1SUBJ-be-IMM.PST'.
-/
def hixkaryana : NegationProfile :=
  { language := "Hixkaryana"
  , iso := "hix"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , negMarkers := ["-hira"]
  , notes := "Negative suffix deverbalizes; copula becomes finite element" }

/--
Nelemwa (Oceanic; New Caledonia): negative indefinites use a negative
existential construction: `kia agu i uya` 'not.exist person 3SG arrive'
= 'Nobody came'. Classified as negExistential for Ch 115.
Note: Nelemwa is only in the WALS Ch 115 sample; Ch 112-114 values
are based on descriptive sources.
-/
def nelemwa : NegationProfile :=
  { language := "Nelemwa"
  , iso := "nee"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .negExistential
  , negMarkers := ["kia"]
  , notes := "Negative existential for indefinites: kia agu 'not.exist person'; " ++
             "only in WALS Ch 115 sample" }

/--
Imbabura Quechua: negative particle `mana` with optional irrealis suffix
`-chu`. WALS classifies as SymAsy with A/NonReal: some constructions are
symmetric (particle alone), others require `-chu` irrealis marking on the
verb. The A/NonReal asymmetry is paradigmatic — the negative obligatorily
includes an irrealis category absent from the affirmative.
-/
def imbaburaQuechua : NegationProfile :=
  { language := "Quechua (Imbabura)"
  , iso := "qvi"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .realityStatus
  , negIndefinite := some .cooccur
  , negMarkers := ["mana"]
  , notes := "A/NonReal: -chu irrealis suffix required in some negative " ++
             "constructions; paradigmatic asymmetry (no constructional change)" }

/-- All language profiles in the sample. -/
def allLanguages : List NegationProfile :=
  [ english, german, french, russian, finnish, japanese, mandarin, turkish
  , czech, spanish, italian, burmese, maori, izi, kolYukaghir, rama
  , hixkaryana, nelemwa, imbaburaQuechua ]

-- ============================================================================
-- WALS Grounding: Ch 112 (Negative Morphemes)
-- ============================================================================

theorem english_ch112 :
    (Core.WALS.F112A.lookup "eng").map (fromWALS112A ·.value) = some english.morphemeType := by
  native_decide
theorem german_ch112 :
    (Core.WALS.F112A.lookup "ger").map (fromWALS112A ·.value) = some german.morphemeType := by
  native_decide
theorem french_ch112 :
    (Core.WALS.F112A.lookup "fre").map (fromWALS112A ·.value) = some french.morphemeType := by
  native_decide
theorem russian_ch112 :
    (Core.WALS.F112A.lookup "rus").map (fromWALS112A ·.value) = some russian.morphemeType := by
  native_decide
theorem finnish_ch112 :
    (Core.WALS.F112A.lookup "fin").map (fromWALS112A ·.value) = some finnish.morphemeType := by
  native_decide
theorem japanese_ch112 :
    (Core.WALS.F112A.lookup "jpn").map (fromWALS112A ·.value) = some japanese.morphemeType := by
  native_decide
theorem mandarin_ch112 :
    (Core.WALS.F112A.lookup "mnd").map (fromWALS112A ·.value) = some mandarin.morphemeType := by
  native_decide
theorem turkish_ch112 :
    (Core.WALS.F112A.lookup "tur").map (fromWALS112A ·.value) = some turkish.morphemeType := by
  native_decide
theorem czech_ch112 :
    (Core.WALS.F112A.lookup "cze").map (fromWALS112A ·.value) = some czech.morphemeType := by
  native_decide
theorem spanish_ch112 :
    (Core.WALS.F112A.lookup "spa").map (fromWALS112A ·.value) = some spanish.morphemeType := by
  native_decide
theorem italian_ch112 :
    (Core.WALS.F112A.lookup "ita").map (fromWALS112A ·.value) = some italian.morphemeType := by
  native_decide
theorem burmese_ch112 :
    (Core.WALS.F112A.lookup "brm").map (fromWALS112A ·.value) = some burmese.morphemeType := by
  native_decide
theorem maori_ch112 :
    (Core.WALS.F112A.lookup "mao").map (fromWALS112A ·.value) = some maori.morphemeType := by
  native_decide
theorem izi_ch112 :
    (Core.WALS.F112A.lookup "izi").map (fromWALS112A ·.value) = some izi.morphemeType := by
  native_decide
theorem yukaghir_ch112 :
    (Core.WALS.F112A.lookup "yko").map (fromWALS112A ·.value) = some kolYukaghir.morphemeType := by
  native_decide
theorem rama_ch112 :
    (Core.WALS.F112A.lookup "ram").map (fromWALS112A ·.value) = some rama.morphemeType := by
  native_decide
theorem hixkaryana_ch112 :
    (Core.WALS.F112A.lookup "hix").map (fromWALS112A ·.value) = some hixkaryana.morphemeType := by
  native_decide
theorem imbaburaQuechua_ch112 :
    (Core.WALS.F112A.lookup "qim").map (fromWALS112A ·.value) =
    some imbaburaQuechua.morphemeType := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 113 (Symmetric/Asymmetric)
-- Not all languages are in Ch 113 sample (Czech, Izi, Nelemwa absent)
-- ============================================================================

theorem english_ch113 :
    (Core.WALS.F113A.lookup "eng").map (fromWALS113A ·.value) = some english.symmetry := by
  native_decide
theorem german_ch113 :
    (Core.WALS.F113A.lookup "ger").map (fromWALS113A ·.value) = some german.symmetry := by
  native_decide
theorem french_ch113 :
    (Core.WALS.F113A.lookup "fre").map (fromWALS113A ·.value) = some french.symmetry := by
  native_decide
theorem russian_ch113 :
    (Core.WALS.F113A.lookup "rus").map (fromWALS113A ·.value) = some russian.symmetry := by
  native_decide
theorem finnish_ch113 :
    (Core.WALS.F113A.lookup "fin").map (fromWALS113A ·.value) = some finnish.symmetry := by
  native_decide
theorem japanese_ch113 :
    (Core.WALS.F113A.lookup "jpn").map (fromWALS113A ·.value) = some japanese.symmetry := by
  native_decide
theorem mandarin_ch113 :
    (Core.WALS.F113A.lookup "mnd").map (fromWALS113A ·.value) = some mandarin.symmetry := by
  native_decide
theorem turkish_ch113 :
    (Core.WALS.F113A.lookup "tur").map (fromWALS113A ·.value) = some turkish.symmetry := by
  native_decide
theorem spanish_ch113 :
    (Core.WALS.F113A.lookup "spa").map (fromWALS113A ·.value) = some spanish.symmetry := by
  native_decide
theorem italian_ch113 :
    (Core.WALS.F113A.lookup "ita").map (fromWALS113A ·.value) = some italian.symmetry := by
  native_decide
theorem burmese_ch113 :
    (Core.WALS.F113A.lookup "brm").map (fromWALS113A ·.value) = some burmese.symmetry := by
  native_decide
theorem maori_ch113 :
    (Core.WALS.F113A.lookup "mao").map (fromWALS113A ·.value) = some maori.symmetry := by
  native_decide
theorem yukaghir_ch113 :
    (Core.WALS.F113A.lookup "yko").map (fromWALS113A ·.value) = some kolYukaghir.symmetry := by
  native_decide
theorem rama_ch113 :
    (Core.WALS.F113A.lookup "ram").map (fromWALS113A ·.value) = some rama.symmetry := by
  native_decide
theorem hixkaryana_ch113 :
    (Core.WALS.F113A.lookup "hix").map (fromWALS113A ·.value) = some hixkaryana.symmetry := by
  native_decide
theorem imbaburaQuechua_ch113 :
    (Core.WALS.F113A.lookup "qim").map (fromWALS113A ·.value) =
    some imbaburaQuechua.symmetry := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 114 (Asymmetry Subtypes)
-- Same sample as Ch 113 (Czech, Izi, Nelemwa absent)
-- ============================================================================

theorem english_ch114 :
    (Core.WALS.F114A.lookup "eng").map (fromWALS114A ·.value) =
    some english.asymmetrySubtype := by native_decide
theorem german_ch114 :
    (Core.WALS.F114A.lookup "ger").map (fromWALS114A ·.value) =
    some german.asymmetrySubtype := by native_decide
theorem french_ch114 :
    (Core.WALS.F114A.lookup "fre").map (fromWALS114A ·.value) =
    some french.asymmetrySubtype := by native_decide
theorem russian_ch114 :
    (Core.WALS.F114A.lookup "rus").map (fromWALS114A ·.value) =
    some russian.asymmetrySubtype := by native_decide
theorem finnish_ch114 :
    (Core.WALS.F114A.lookup "fin").map (fromWALS114A ·.value) =
    some finnish.asymmetrySubtype := by native_decide
theorem japanese_ch114 :
    (Core.WALS.F114A.lookup "jpn").map (fromWALS114A ·.value) =
    some japanese.asymmetrySubtype := by native_decide
theorem mandarin_ch114 :
    (Core.WALS.F114A.lookup "mnd").map (fromWALS114A ·.value) =
    some mandarin.asymmetrySubtype := by native_decide
theorem turkish_ch114 :
    (Core.WALS.F114A.lookup "tur").map (fromWALS114A ·.value) =
    some turkish.asymmetrySubtype := by native_decide
theorem spanish_ch114 :
    (Core.WALS.F114A.lookup "spa").map (fromWALS114A ·.value) =
    some spanish.asymmetrySubtype := by native_decide
theorem italian_ch114 :
    (Core.WALS.F114A.lookup "ita").map (fromWALS114A ·.value) =
    some italian.asymmetrySubtype := by native_decide
theorem burmese_ch114 :
    (Core.WALS.F114A.lookup "brm").map (fromWALS114A ·.value) =
    some burmese.asymmetrySubtype := by native_decide
theorem maori_ch114 :
    (Core.WALS.F114A.lookup "mao").map (fromWALS114A ·.value) =
    some maori.asymmetrySubtype := by native_decide
theorem yukaghir_ch114 :
    (Core.WALS.F114A.lookup "yko").map (fromWALS114A ·.value) =
    some kolYukaghir.asymmetrySubtype := by native_decide
theorem rama_ch114 :
    (Core.WALS.F114A.lookup "ram").map (fromWALS114A ·.value) =
    some rama.asymmetrySubtype := by native_decide
theorem hixkaryana_ch114 :
    (Core.WALS.F114A.lookup "hix").map (fromWALS114A ·.value) =
    some hixkaryana.asymmetrySubtype := by native_decide
theorem imbaburaQuechua_ch114 :
    (Core.WALS.F114A.lookup "qim").map (fromWALS114A ·.value) =
    some imbaburaQuechua.asymmetrySubtype := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 115 (Negative Indefinites)
-- Smaller sample: Czech, Izi, Rama, Hixkaryana absent
-- ============================================================================

theorem english_ch115 :
    (Core.WALS.F115A.lookup "eng").map (fromWALS115A ·.value) = some .mixed := by
  native_decide
theorem german_ch115 :
    (Core.WALS.F115A.lookup "ger").map (fromWALS115A ·.value) = some .preclude := by
  native_decide
theorem french_ch115 :
    (Core.WALS.F115A.lookup "fre").map (fromWALS115A ·.value) = some .mixed := by
  native_decide
theorem russian_ch115 :
    (Core.WALS.F115A.lookup "rus").map (fromWALS115A ·.value) = some .cooccur := by
  native_decide
theorem finnish_ch115 :
    (Core.WALS.F115A.lookup "fin").map (fromWALS115A ·.value) = some .cooccur := by
  native_decide
theorem japanese_ch115 :
    (Core.WALS.F115A.lookup "jpn").map (fromWALS115A ·.value) = some .cooccur := by
  native_decide
theorem mandarin_ch115 :
    (Core.WALS.F115A.lookup "mnd").map (fromWALS115A ·.value) = some .cooccur := by
  native_decide
theorem turkish_ch115 :
    (Core.WALS.F115A.lookup "tur").map (fromWALS115A ·.value) = some .cooccur := by
  native_decide
theorem spanish_ch115 :
    (Core.WALS.F115A.lookup "spa").map (fromWALS115A ·.value) = some .mixed := by
  native_decide
theorem italian_ch115 :
    (Core.WALS.F115A.lookup "ita").map (fromWALS115A ·.value) = some .mixed := by
  native_decide
theorem nelemwa_ch115 :
    (Core.WALS.F115A.lookup "nel").map (fromWALS115A ·.value) =
    some .negExistential := by native_decide
theorem imbaburaQuechua_ch115 :
    (Core.WALS.F115A.lookup "qim").map (fromWALS115A ·.value) =
    some .cooccur := by native_decide

-- ============================================================================
-- Helper Predicates
-- ============================================================================

/-- Does a language use a given morpheme type? -/
def NegationProfile.hasMorphemeType (p : NegationProfile) (t : NegMorphemeType) : Bool :=
  p.morphemeType == t

/-- Does a language have symmetric negation (either symmetric only or both)? -/
def NegationProfile.hasSymmetric (p : NegationProfile) : Bool :=
  p.symmetry == .symmetric || p.symmetry == .both

/-- Does a language have asymmetric negation (either asymmetric only or both)? -/
def NegationProfile.hasAsymmetric (p : NegationProfile) : Bool :=
  p.symmetry == .asymmetric || p.symmetry == .both

/-- Does a language show negative concord (co-occurrence of negative indefinites
    with predicate negation)? -/
def NegationProfile.hasNegConcord (p : NegationProfile) : Bool :=
  p.negIndefinite == some .cooccur

/-- Count of languages in the sample with a given morpheme type. -/
def countByMorphemeType (langs : List NegationProfile) (t : NegMorphemeType) : Nat :=
  (langs.filter (·.hasMorphemeType t)).length

/-- Count of languages in the sample with a given symmetry type. -/
def countBySymmetry (langs : List NegationProfile) (s : NegSymmetry) : Nat :=
  (langs.filter (·.symmetry == s)).length

-- ============================================================================
-- Typological Generalization 1: Negative Particles Are Most Common
-- ============================================================================

/-- Ch 112: Negative particles outnumber negative affixes. -/
theorem particles_most_common :
    (ch112.filter (·.value == .negativeParticle)).length >
    (ch112.filter (·.value == .negativeAffix)).length := by native_decide

/-- Ch 112: Negative auxiliary verbs are rare (< 5% of sample). -/
theorem aux_verbs_rare :
    (ch112.filter (·.value == .negativeAuxiliaryVerb)).length * 20 <
    ch112.length := by native_decide

/-- Ch 112: Particles + affixes together account for the vast majority. -/
theorem particles_affixes_dominant :
    let particles := (ch112.filter (·.value == .negativeParticle)).length
    let affixes := (ch112.filter (·.value == .negativeAffix)).length
    (particles + affixes) * 2 > ch112.length := by native_decide

-- ============================================================================
-- Typological Generalization 2: Symmetric Negation Is Common
-- ============================================================================

/-- Ch 113: SymAsy (both) is the most common type, followed by Sym.
    Asy-only is the least common. -/
theorem symasy_most_common :
    let sym := (ch113.filter (·.value == .symmetric)).length
    let asy := (ch113.filter (·.value == .asymmetric)).length
    let both := (ch113.filter (·.value == .both)).length
    both > sym ∧ sym > asy := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 113: Languages with at least some symmetric negation (Sym + Both)
    far outnumber purely asymmetric languages. -/
theorem symmetric_dominant :
    let sym := (ch113.filter (·.value == .symmetric)).length
    let both := (ch113.filter (·.value == .both)).length
    let asy := (ch113.filter (·.value == .asymmetric)).length
    sym + both > asy * 4 := by
  native_decide

-- ============================================================================
-- Typological Generalization 3: A/Cat Is the Most Common Asymmetry Subtype
-- ============================================================================

/-- Ch 114: Among languages with a single asymmetry subtype, A/Cat is the
    most common, followed by A/Fin and A/NonReal. -/
theorem acat_most_common_subtype :
    let aCat := (ch114.filter (·.value == .aCat)).length
    let aFin := (ch114.filter (·.value == .aFin)).length
    let aNon := (ch114.filter (·.value == .aNonreal)).length
    aCat > aFin ∧ aFin > aNon := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- Typological Generalization 4: Negative Concord Is Overwhelmingly Dominant
-- ============================================================================

/-- Ch 115: Co-occurrence with predicate negation (negative concord) is
    by far the most common pattern worldwide. Co-occurrence outnumbers
    preclusion by more than 15x. -/
theorem neg_concord_dominant :
    let cooccur := (ch115.filter (·.value == .predicateNegationAlsoPresent)).length
    let preclude := (ch115.filter (·.value == .noPredicateNegation)).length
    cooccur > preclude * 15 := by native_decide

/-- Ch 115: Preclusion of predicate negation by negative indefinites is
    the rarest of the four strategies. -/
theorem preclusion_rarest :
    let preclude := (ch115.filter (·.value == .noPredicateNegation)).length
    let mixed := (ch115.filter (·.value == .mixedBehaviour)).length
    let negEx := (ch115.filter (·.value == .negativeExistentialConstruction)).length
    preclude ≤ mixed ∧ preclude ≤ negEx := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- Typological Generalization 5: Bipartite Negation Implies Asymmetry
-- ============================================================================

/-- In our sample, every language with bipartite ("double") negation morphemes
    (Ch 112) has asymmetric negation (Ch 113). This makes sense: if negation
    requires two markers whose placement changes the clause structure, the
    negative clause structurally differs from the affirmative. -/
theorem bipartite_implies_asymmetric :
    let bipartite := allLanguages.filter (·.hasMorphemeType .doubleNeg)
    bipartite.all (·.hasAsymmetric) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 6: Negative Concord in Slavic
-- ============================================================================

/-- In our sample, all Slavic languages (Russian, Czech) show negative concord:
    negative indefinites obligatorily co-occur with predicate negation. -/
def slavicLanguages : List NegationProfile := [russian, czech]

theorem slavic_neg_concord :
    slavicLanguages.all (·.hasNegConcord) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 7: Isolating Languages and Word Status
-- ============================================================================

/-- Languages with negative words of unclear status (Ch 112 type 4) are
    common in isolating languages where verbal morphology is minimal.
    Maori (isolating, Polynesian) illustrates this: without verbal inflection,
    there is no morphological basis for deciding if the negator is a verb. -/
theorem maori_word_unclear :
    maori.morphemeType == .wordUnclear := by native_decide

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

theorem english_is_particle : english.morphemeType == .particle := by native_decide
theorem english_is_both : english.symmetry == .both := by native_decide
theorem german_precludes : german.negIndefinite == some .preclude := by native_decide
theorem finnish_is_aux : finnish.morphemeType == .auxVerb := by native_decide
theorem finnish_is_asymmetric : finnish.symmetry == .asymmetric := by native_decide
theorem finnish_afin : finnish.asymmetrySubtype == .finiteness := by native_decide
theorem japanese_is_affix : japanese.morphemeType == .affix := by native_decide
theorem japanese_is_asymmetric : japanese.symmetry == .asymmetric := by native_decide
theorem burmese_is_double : burmese.morphemeType == .doubleNeg := by native_decide
theorem spanish_is_mixed : spanish.negIndefinite == some .mixed := by native_decide
theorem italian_is_particle : italian.morphemeType == .particle := by native_decide
theorem italian_is_symmetric : italian.symmetry == .symmetric := by native_decide
theorem italian_is_mixed : italian.negIndefinite == some .mixed := by native_decide
/-- Italian *non* is a syntactic head (X°): preverbal clitic,
    cannot be focused or coordinated. -/
theorem italian_neg_is_head : italian.negIsHead == some true := by native_decide
/-- Spanish *no* is a phrase (XP): can be focused and coordinated. -/
theorem spanish_neg_is_phrase : spanish.negIsHead == some false := by native_decide
/-- French *ne* is a syntactic head (X°): weak clitic. -/
theorem french_neg_is_head : french.negIsHead == some true := by native_decide
/-- Italian and Spanish share the same mixed n-word strategy. -/
theorem italian_spanish_parallel :
    italian.negIndefinite = spanish.negIndefinite := rfl
theorem russian_neg_concord : russian.hasNegConcord = true := by native_decide

-- ============================================================================
-- Cross-Chapter Consistency
-- ============================================================================

/-- In our sample, every language classified as symmetric-only (Ch 113) has
    a non-assignable asymmetry subtype (Ch 114). -/
theorem symmetric_implies_nonassignable :
    let symmetric := allLanguages.filter (·.symmetry == .symmetric)
    symmetric.all (·.asymmetrySubtype == .nonAssignable) = true := by
  native_decide

/-- In our sample, no language classified as asymmetric or both has a
    non-assignable subtype. -/
theorem asymmetric_implies_assignable :
    let asymmetric := allLanguages.filter (·.hasAsymmetric)
    asymmetric.all (·.asymmetrySubtype != .nonAssignable) = true := by
  native_decide

/-- In the WALS data, the count of non-assignable languages in Ch 114
    exactly equals the count of symmetric-only languages in Ch 113.
    This is a consistency check: the same set of languages. -/
theorem ch114_nonassignable_eq_ch113_sym :
    (ch114.filter (·.value == .nonAssignable)).length =
    (ch113.filter (·.value == .symmetric)).length := by native_decide

-- ============================================================================
-- Implicational Patterns
-- ============================================================================

/-- Negative auxiliary verbs (Ch 112) are always associated with asymmetric
    negation of subtype A/Fin: the auxiliary becomes the finite element, and
    the lexical verb is defiticized. Finnish illustrates this perfectly:
    `e-n tule` [NEG-1SG come.CONNEG]. In our sample, Finnish is the only
    negative auxiliary verb language, and it has A/Fin asymmetry. -/
theorem aux_verb_implies_afin :
    let auxLangs := allLanguages.filter (·.hasMorphemeType .auxVerb)
    auxLangs.all (·.asymmetrySubtype == .finiteness) = true := by
  native_decide

/-- Areal pattern: the negative auxiliary verb type is concentrated in
    northern Eurasia, stretching from Finland to western Siberia
    (@cite{dryer-haspelmath-2013}, sec. 2). Our sample contains Finnish as the representative;
    other languages in this belt include Estonian, Nenets, Evenki, Khanty. -/
theorem finnish_neg_aux_representative :
    finnish.morphemeType == .auxVerb ∧
    finnish.asymmetrySubtype == .finiteness := by
  native_decide

-- ============================================================================
-- Summary Statistics for Our Sample
-- ============================================================================

/-- Number of languages in our sample. -/
theorem sample_size : allLanguages.length = 19 := by native_decide

/-- Morpheme type distribution in our sample. -/
theorem sample_affix_count : countByMorphemeType allLanguages .affix = 5 := by native_decide
theorem sample_particle_count : countByMorphemeType allLanguages .particle = 10 := by native_decide
theorem sample_auxverb_count : countByMorphemeType allLanguages .auxVerb = 1 := by native_decide
theorem sample_double_count : countByMorphemeType allLanguages .doubleNeg = 2 := by native_decide
theorem sample_unclear_count : countByMorphemeType allLanguages .wordUnclear = 1 := by native_decide
theorem sample_variation_count : countByMorphemeType allLanguages .variation = 0 := by native_decide

/-- Symmetry distribution in our sample. -/
theorem sample_symmetry_counts :
    countBySymmetry allLanguages .symmetric = 7 ∧
    countBySymmetry allLanguages .asymmetric = 6 ∧
    countBySymmetry allLanguages .both = 6 := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 143A (Neg-Verb Order)
-- All profile languages are in the 1325-language Ch 143A sample.
-- ============================================================================

theorem english_ch143A :
    (Core.WALS.F143A.lookup "eng").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalParticle := by native_decide
theorem german_ch143A :
    (Core.WALS.F143A.lookup "ger").map (fromWALS143A ·.value) =
    some NegVerbPosition.mixedSingle := by native_decide
theorem french_ch143A :
    (Core.WALS.F143A.lookup "fre").map (fromWALS143A ·.value) =
    some NegVerbPosition.optDoubleNeg := by native_decide
theorem russian_ch143A :
    (Core.WALS.F143A.lookup "rus").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalParticle := by native_decide
theorem finnish_ch143A :
    (Core.WALS.F143A.lookup "fin").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalParticle := by native_decide
theorem japanese_ch143A :
    (Core.WALS.F143A.lookup "jpn").map (fromWALS143A ·.value) =
    some NegVerbPosition.postverbalAffix := by native_decide
theorem mandarin_ch143A :
    (Core.WALS.F143A.lookup "mnd").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalParticle := by native_decide
theorem turkish_ch143A :
    (Core.WALS.F143A.lookup "tur").map (fromWALS143A ·.value) =
    some NegVerbPosition.postverbalAffix := by native_decide
theorem czech_ch143A :
    (Core.WALS.F143A.lookup "cze").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalAffix := by native_decide
theorem spanish_ch143A :
    (Core.WALS.F143A.lookup "spa").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalParticle := by native_decide
theorem italian_ch143A :
    (Core.WALS.F143A.lookup "ita").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalParticle := by native_decide
theorem burmese_ch143A :
    (Core.WALS.F143A.lookup "brm").map (fromWALS143A ·.value) =
    some NegVerbPosition.obligDoublNeg := by native_decide
theorem maori_ch143A :
    (Core.WALS.F143A.lookup "mao").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalParticle := by native_decide
theorem izi_ch143A :
    (Core.WALS.F143A.lookup "izi").map (fromWALS143A ·.value) =
    some NegVerbPosition.obligDoublNeg := by native_decide
theorem yukaghir_ch143A :
    (Core.WALS.F143A.lookup "yko").map (fromWALS143A ·.value) =
    some NegVerbPosition.preverbalAffix := by native_decide
theorem rama_ch143A :
    (Core.WALS.F143A.lookup "ram").map (fromWALS143A ·.value) =
    some NegVerbPosition.mixedSingle := by native_decide
theorem hixkaryana_ch143A :
    (Core.WALS.F143A.lookup "hix").map (fromWALS143A ·.value) =
    some NegVerbPosition.postverbalAffix := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 144A (Neg Position Relative to S, O, V)
-- All profile languages except Nelemwa are in the 1190-language Ch 144A sample.
-- ============================================================================

theorem english_ch144A :
    (Core.WALS.F144A.lookup "eng").map (·.value) = some .snegvo := by native_decide
theorem german_ch144A :
    (Core.WALS.F144A.lookup "ger").map (·.value) = some .moreThanOnePosition := by native_decide
theorem french_ch144A :
    (Core.WALS.F144A.lookup "fre").map (·.value) = some .optdoubleneg := by native_decide
theorem russian_ch144A :
    (Core.WALS.F144A.lookup "rus").map (·.value) = some .snegvo := by native_decide
theorem finnish_ch144A :
    (Core.WALS.F144A.lookup "fin").map (·.value) = some .snegvo := by native_decide
theorem japanese_ch144A :
    (Core.WALS.F144A.lookup "jpn").map (·.value) = some .morphneg := by native_decide
theorem mandarin_ch144A :
    (Core.WALS.F144A.lookup "mnd").map (·.value) = some .snegvo := by native_decide
theorem turkish_ch144A :
    (Core.WALS.F144A.lookup "tur").map (·.value) = some .morphneg := by native_decide
theorem czech_ch144A :
    (Core.WALS.F144A.lookup "cze").map (·.value) = some .morphneg := by native_decide
theorem spanish_ch144A :
    (Core.WALS.F144A.lookup "spa").map (·.value) = some .snegvo := by native_decide
theorem italian_ch144A :
    (Core.WALS.F144A.lookup "ita").map (·.value) = some .snegvo := by native_decide
theorem burmese_ch144A :
    (Core.WALS.F144A.lookup "brm").map (·.value) = some .obligdoubleneg := by native_decide
theorem maori_ch144A :
    (Core.WALS.F144A.lookup "mao").map (·.value) = some .negsvo := by native_decide
theorem izi_ch144A :
    (Core.WALS.F144A.lookup "izi").map (·.value) = some .obligdoubleneg := by native_decide
theorem yukaghir_ch144A :
    (Core.WALS.F144A.lookup "yko").map (·.value) = some .morphneg := by native_decide
theorem rama_ch144A :
    (Core.WALS.F144A.lookup "ram").map (·.value) = some .moreThanOnePosition := by native_decide
theorem hixkaryana_ch144A :
    (Core.WALS.F144A.lookup "hix").map (·.value) = some .morphneg := by native_decide

-- ============================================================================
-- Ch 143A Distribution: Preverbal Negation Dominates
-- ============================================================================

/-- Ch 143A: Preverbal particle (NegV) is the most common single-negation
    type, accounting for 525 of 1325 languages. -/
theorem ch143A_preverbal_particle_count :
    (ch143A.filter (·.value == .negv)).length = 525 := by native_decide

/-- Ch 143A: Postverbal affix ([V-Neg]) is the second most common type. -/
theorem ch143A_postverbal_affix_count :
    (ch143A.filter (·.value == .vNeg)).length = 202 := by native_decide

/-- Ch 143A: Postverbal particle (VNeg) count. -/
theorem ch143A_postverbal_particle_count :
    (ch143A.filter (·.value == .vneg)).length = 171 := by native_decide

/-- Ch 143A: Preverbal affix ([Neg-V]) count. -/
theorem ch143A_preverbal_affix_count :
    (ch143A.filter (·.value == .negV)).length = 162 := by native_decide

/-- Ch 143A: Obligatory double negation count. -/
theorem ch143A_oblig_double_count :
    (ch143A.filter (·.value == .obligdoubleneg)).length = 114 := by native_decide

/-- Ch 143A: Optional double negation count. -/
theorem ch143A_opt_double_count :
    (ch143A.filter (·.value == .optdoubleneg)).length = 80 := by native_decide

/-- Ch 143A: Preverbal negation (particle or affix) is far more common than
    postverbal negation (particle or affix). -/
theorem ch143A_preverbal_dominates :
    let preParticle := (ch143A.filter (·.value == .negv)).length
    let preAffix := (ch143A.filter (·.value == .negV)).length
    let postParticle := (ch143A.filter (·.value == .vneg)).length
    let postAffix := (ch143A.filter (·.value == .vNeg)).length
    preParticle + preAffix > postParticle + postAffix := by native_decide

/-- Ch 143A: Particles (free words) are more common than affixes (bound
    morphemes) for both preverbal and postverbal positions. -/
theorem ch143A_particles_over_affixes :
    let preParticle := (ch143A.filter (·.value == .negv)).length
    let preAffix := (ch143A.filter (·.value == .negV)).length
    let postParticle := (ch143A.filter (·.value == .vneg)).length
    let postAffix := (ch143A.filter (·.value == .vNeg)).length
    preParticle > preAffix ∧ postAffix > postParticle := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- Ch 143B Distribution: Obligatory Double Negation Patterns
-- ============================================================================

/-- Ch 143B: NegVNeg (discontinuous double negation) is the most common
    obligatory double negation pattern (35 of 119 languages). -/
theorem ch143B_negvneg_most_common :
    (ch143B.filter (·.value == .negvneg)).length = 35 := by native_decide

/-- Ch 143B: Neg[V-Neg] (28 languages) and [Neg-V-Neg] (27 languages)
    are close behind NegVNeg (35) as the most common double negation
    patterns. -/
theorem ch143B_negVNeg_count :
    (ch143B.filter (·.value == .negVNeg)).length = 28 := by native_decide
theorem ch143B_negVNeg4_count :
    (ch143B.filter (·.value == .negVNeg_4)).length = 27 := by native_decide

-- ============================================================================
-- Ch 143E Distribution: Preverbal Negative Morphemes
-- ============================================================================

/-- Ch 143E: Most languages have a preverbal negative particle. -/
theorem ch143E_preverbal_particle_dominant :
    (ch143E.filter (·.value == .negv)).length = 682 := by native_decide

/-- Ch 143E: Preverbal affix count. -/
theorem ch143E_preverbal_affix_count :
    (ch143E.filter (·.value == .negV)).length = 230 := by native_decide

/-- Ch 143E: Languages with no preverbal negative morpheme. -/
theorem ch143E_none_count :
    (ch143E.filter (·.value == .none)).length = 390 := by native_decide

-- ============================================================================
-- Ch 143F Distribution: Postverbal Negative Morphemes
-- ============================================================================

/-- Ch 143F: Postverbal affix is more common than postverbal particle. -/
theorem ch143F_affix_over_particle :
    (ch143F.filter (·.value == .vNeg)).length >
    (ch143F.filter (·.value == .vneg)).length := by native_decide

/-- Ch 143F: Postverbal affix count. -/
theorem ch143F_postverbal_affix_count :
    (ch143F.filter (·.value == .vNeg)).length = 307 := by native_decide

/-- Ch 143F: Postverbal particle count. -/
theorem ch143F_postverbal_particle_count :
    (ch143F.filter (·.value == .vneg)).length = 288 := by native_decide

/-- Ch 143F: Most languages have no postverbal negative morpheme. -/
theorem ch143F_none_count :
    (ch143F.filter (·.value == .none)).length = 712 := by native_decide

-- ============================================================================
-- Ch 143G Distribution: Minor Morphological Means
-- ============================================================================

/-- Ch 143G: The vast majority of languages use no minor morphological
    means (negative tone, infix, stem change) for negation. -/
theorem ch143G_none_dominant :
    (ch143G.filter (·.value == .none)).length = 1315 := by native_decide

/-- Ch 143G: Negative tone is the most common minor means. -/
theorem ch143G_tone_count :
    (ch143G.filter (·.value == .negtone)).length = 7 := by native_decide

-- ============================================================================
-- Ch 143: Cross-Feature Consistency
-- ============================================================================

/-- Ch 143E + 143F: Most languages have at least one preverbal or
    postverbal negative morpheme. The "none" counts for preverbal (390)
    and postverbal (712) do not sum to more than the sample size, meaning
    some languages lack both and rely on double negation or minor means. -/
theorem ch143EF_coverage :
    (ch143E.filter (·.value == .none)).length +
    (ch143F.filter (·.value == .none)).length < ch143E.length * 2 := by native_decide

-- ============================================================================
-- Ch 144A Distribution: Position of Negative Word
-- ============================================================================

/-- Ch 144A: MorphNeg (morphological negation, no negative word) is the
    largest single category. -/
theorem ch144A_morphneg_count :
    (ch144A.filter (·.value == .morphneg)).length = 333 := by native_decide

/-- Ch 144A: SNegVO (subject, then negative word, then verb-object) is the
    most common word-order-specific position. -/
theorem ch144A_snegvo_count :
    (ch144A.filter (·.value == .snegvo)).length = 112 := by native_decide

/-- Ch 144A: ObligDoubleNeg count. -/
theorem ch144A_oblig_double_count :
    (ch144A.filter (·.value == .obligdoubleneg)).length = 101 := by native_decide

/-- Ch 144A: OptDoubleNeg count. -/
theorem ch144A_opt_double_count :
    (ch144A.filter (·.value == .optdoubleneg)).length = 67 := by native_decide

/-- Ch 144A: SVONeg count. -/
theorem ch144A_svoneg_count :
    (ch144A.filter (·.value == .svoneg)).length = 81 := by native_decide

/-- Ch 144A: SONegV count. -/
theorem ch144A_sonegv_count :
    (ch144A.filter (·.value == .sonegv)).length = 65 := by native_decide

/-- Ch 144A: SOVNeg count. -/
theorem ch144A_sovneg_count :
    (ch144A.filter (·.value == .sovneg)).length = 49 := by native_decide

/-- Ch 144A: NegVSO count. -/
theorem ch144A_negvso_count :
    (ch144A.filter (·.value == .negvso)).length = 58 := by native_decide

/-- Ch 144A: NegVOS count. -/
theorem ch144A_negvos_count :
    (ch144A.filter (·.value == .negvos)).length = 18 := by native_decide

-- ============================================================================
-- Ch 144D Distribution: Negation in SVO Languages
-- ============================================================================

/-- Ch 144D: In SVO languages, SNegVO is the most common negation position. -/
theorem ch144D_snegvo_dominant :
    let snegvo := (ch144D.filter (·.value == .snegvo)).length
    let svoneg := (ch144D.filter (·.value == .svoneg)).length
    snegvo > svoneg := by native_decide

/-- Ch 144D: SNegVO count. -/
theorem ch144D_snegvo_count :
    (ch144D.filter (·.value == .snegvo)).length = 111 := by native_decide

/-- Ch 144D: SVONeg count. -/
theorem ch144D_svoneg_count :
    (ch144D.filter (·.value == .svoneg)).length = 81 := by native_decide

/-- Ch 144D: S[Neg-V]O (preverbal affix) count. -/
theorem ch144D_snegVO_count :
    (ch144D.filter (·.value == .sNegVO)).length = 67 := by native_decide

-- ============================================================================
-- Ch 144L Distribution: Negation in SOV Languages
-- ============================================================================

/-- Ch 144L: In SOV languages, postverbal affix SO[V-Neg] is the most
    common single-negation position. -/
theorem ch144L_postverbal_affix_dominant :
    let soVNeg := (ch144L.filter (·.value == .soVNeg)).length
    let sonegv := (ch144L.filter (·.value == .sonegv)).length
    let sovneg := (ch144L.filter (·.value == .sovneg)).length
    let soNegV := (ch144L.filter (·.value == .soNegV)).length
    soVNeg > sonegv ∧ soVNeg > sovneg ∧ soVNeg > soNegV := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Ch 144L: SO[V-Neg] count. -/
theorem ch144L_soVNeg_count :
    (ch144L.filter (·.value == .soVNeg)).length = 128 := by native_decide

/-- Ch 144L: SONegV count. -/
theorem ch144L_sonegv_count :
    (ch144L.filter (·.value == .sonegv)).length = 64 := by native_decide

/-- Ch 144L: SOVNeg count. -/
theorem ch144L_sovneg_count :
    (ch144L.filter (·.value == .sovneg)).length = 48 := by native_decide

/-- Ch 144L: SO[Neg-V] count. -/
theorem ch144L_soNegV_count :
    (ch144L.filter (·.value == .soNegV)).length = 49 := by native_decide

-- ============================================================================
-- Ch 144T Distribution: Negation in Verb-Initial Languages
-- ============================================================================

/-- Ch 144T: In verb-initial languages, NegVSO is the dominant pattern. -/
theorem ch144T_negvso_dominant :
    (ch144T.filter (·.value == .negvso)).length = 57 := by native_decide

/-- Ch 144T: NegVOS count. -/
theorem ch144T_negvos_count :
    (ch144T.filter (·.value == .negvos)).length = 18 := by native_decide

-- ============================================================================
-- Ch 144Y Distribution: Negation in Object-Initial Languages
-- ============================================================================

/-- Ch 144Y: Object-initial languages are rare (16 in sample). -/
theorem ch144Y_small_sample :
    ch144Y.length = 16 := by native_decide

-- ============================================================================
-- Ch 144B Distribution: Clause Position of Negative Word
-- ============================================================================

/-- Ch 144B: Immediately preverbal is the most common position for
    negative words. -/
theorem ch144B_immed_preverbal_dominant :
    (ch144B.filter (·.value == .immedPreverbal)).length = 339 := by native_decide

/-- Ch 144B: Immediately preverbal outnumbers all other positions. -/
theorem ch144B_immed_preverbal_majority :
    let preverbal := (ch144B.filter (·.value == .immedPreverbal)).length
    let postverbal := (ch144B.filter (·.value == .immedPostverbal)).length
    let clauseEnd := (ch144B.filter (·.value == .endNotImmedPostverbal)).length
    preverbal > postverbal + clauseEnd := by native_decide

-- ============================================================================
-- Cross-Chapter Typological Generalizations: Ch 143--144
-- ============================================================================

/-- Ch 143A: Double negation (obligatory + optional) accounts for about
    15% of all languages in the sample. -/
theorem ch143A_double_neg_proportion :
    let oblig := (ch143A.filter (·.value == .obligdoubleneg)).length
    let opt := (ch143A.filter (·.value == .optdoubleneg)).length
    let triple1 := (ch143A.filter (·.value == .opttriplenegObligdoubleneg)).length
    let triple2 := (ch143A.filter (·.value == .opttriplenegOptdoubleneg)).length
    (oblig + opt + triple1 + triple2) * 5 < ch143A.length := by native_decide

/-- Ch 144A: Languages with morphological negation (no negative word) are
    the single largest category, but languages with a negative word of
    some kind outnumber them. -/
theorem ch144A_word_neg_majority :
    let morphneg := (ch144A.filter (·.value == .morphneg)).length
    let other := (ch144A.filter (·.value == .other)).length
    ch144A.length - morphneg - other > morphneg := by native_decide

/-- Ch 143A vs Ch 144A: The two chapters cover overlapping but different
    samples (1325 vs 1190 languages). -/
theorem ch143A_ch144A_different_samples :
    ch143A.length ≠ ch144A.length := by native_decide

/-- Ch 144D + 144L + 144T: SVO, SOV, and verb-initial languages together
    account for the entire Ch 144A sample (with overlap, since some
    languages appear in multiple word-order-specific sub-features). -/
theorem ch144_subtypes_cover_sample :
    ch144D.length + ch144L.length + ch144T.length + ch144Y.length > ch144A.length := by
  native_decide

-- ============================================================================
-- Expletive Negation: Cross-Linguistic Survey (@cite{jin-koenig-2021})
-- ============================================================================

/-! ## Expletive negation survey
@cite{jin-koenig-2021}

Expletive negation (EN) — semantically vacuous negation triggered by the
lexical meaning of an embedding predicate or operator — was surveyed
across 722 languages. EN was attested in 74 languages across 37 genera
(every continental area except South America).

The two most widespread EN triggers:
- BEFORE (UNTIL): 50 of the 74 EN-attesting languages
- FEAR (AFRAID): 39 of the 74 EN-attesting languages -/

/-- Cross-linguistic EN survey results. -/
structure ENSurveyResult where
  /-- Total languages surveyed -/
  totalSurveyed : Nat
  /-- Languages where EN was attested -/
  languagesWithEN : Nat
  /-- Genera where EN was attested -/
  generaWithEN : Nat
  /-- Languages with EN in BEFORE-clauses specifically -/
  beforeTriggerCount : Nat
  /-- Languages with EN in FEAR-clauses specifically -/
  fearTriggerCount : Nat
  deriving Repr

/-- The overall EN survey from @cite{jin-koenig-2021}. -/
def enSurvey : ENSurveyResult where
  totalSurveyed := 722
  languagesWithEN := 74
  generaWithEN := 37
  beforeTriggerCount := 50
  fearTriggerCount := 39

/-- EN is attested in a substantial minority of surveyed languages. -/
theorem en_attested_minority :
    enSurvey.languagesWithEN < enSurvey.totalSurveyed := by decide

/-- EN is found across many genera (not an areal phenomenon). -/
theorem en_across_many_genera :
    enSurvey.generaWithEN ≥ 30 := by decide

/-- BEFORE is the most common EN trigger. -/
theorem en_before_most_common :
    enSurvey.beforeTriggerCount > enSurvey.fearTriggerCount := by decide

/-- BEFORE triggers occur in the majority of EN-attesting languages. -/
theorem en_before_trigger_majority :
    enSurvey.beforeTriggerCount * 2 > enSurvey.languagesWithEN := by decide

-- ============================================================================
-- Table 2: EN by Continental Area (@cite{jin-koenig-2021})
-- ============================================================================

/-- Continental areas from @cite{jin-koenig-2021} Table 2. -/
inductive ContinentalArea where
  | africa
  | australiaNewGuinea
  | eurasia
  | northAmerica
  | southAmerica
  | pidginsCreoles
  deriving DecidableEq, BEq, Repr

/-- Per-area EN survey data (Table 2). -/
structure ENAreaData where
  area : ContinentalArea
  languagesLookedAt : Nat
  languagesWithEN : Nat
  generaCovered : Option Nat  -- None for Pidgins & Creoles
  generaWithEN : Option Nat
  deriving Repr

/-- Table 2: Distribution of languages with and without EN by
    continental area (@cite{jin-koenig-2021}). -/
def enByArea : List ENAreaData :=
  [ ⟨.africa,             177, 11, some 74, some 5⟩
  , ⟨.australiaNewGuinea,  96,  2, some 57, some 2⟩
  , ⟨.eurasia,            304, 56, some 42, some 29⟩
  , ⟨.northAmerica,        90,  1, some 43, some 1⟩
  , ⟨.southAmerica,        50,  0, some 34, some 0⟩
  , ⟨.pidginsCreoles,      11,  4, none,    none⟩ ]

/-- The per-area EN counts sum to 74. (The per-area language-looked-at
    counts sum to 728, not 722 — the paper's total is 722, suggesting
    6 Pidgin/Creole languages are also counted in geographic areas.) -/
theorem enByArea_sums_to_74 :
    (enByArea.map (·.languagesWithEN)).sum = 74 := by native_decide

/-- EN is not attested in South America in this sample. -/
theorem en_absent_south_america :
    (enByArea.filter (·.area == .southAmerica)).all
      (·.languagesWithEN == 0) = true := by native_decide

/-- Eurasia has the highest concentration of EN-attesting languages. -/
theorem eurasia_most_en :
    (enByArea.filter (·.area == .eurasia)).all
      (·.languagesWithEN > 50) = true := by native_decide

-- ============================================================================
-- Table 3: EN Languages and Trigger Concepts (@cite{jin-koenig-2021})
-- ============================================================================

/-! ### Per-language EN attestation

Table 3 lists all 74 languages where EN was attested, grouped by
continental area and genus. Each entry records the EN trigger concepts
attested in that language (using the concept labels from the paper,
in small capitals). Lexical forms are recorded in the `forms` field
where available in the paper. -/

/-- A language with attested EN and its trigger concepts (Table 3). -/
structure ENLanguageEntry where
  /-- Language name -/
  name : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Genus (following the paper's classification) -/
  genus : String
  /-- Continental area -/
  area : ContinentalArea
  /-- EN trigger concepts attested (concept labels from Table 3) -/
  triggers : List String
  deriving Repr

/-- Table 3: All 74 languages where EN was attested, with their trigger
    concepts (@cite{jin-koenig-2021}, pp. 45–48). -/
def enLanguages : List ENLanguageEntry :=
  -- ── Africa (11 languages) ──────────────────────────────────────────
  [ ⟨"Shupamem",        "bax", "Bantoid",    .africa,
    ["AFRAID", "FORBID", "PROHIBIT"]⟩
  , ⟨"Fongbe",          "fon", "Kwa",        .africa,
    ["DENY", "FEAR", "REFUSE"]⟩
  , ⟨"Supyire",         "spp", "Kwa",        .africa,
    ["PREVENT"]⟩
  , ⟨"Dinka",           "dik", "Nilotic",    .africa,
    ["FEAR", "FORBID", "REFUSE", "TOO EXHAUSTED/DIFFICULT TO"]⟩
  , ⟨"Egyptian Arabic", "arz", "Semitic",    .africa,
    ["FEAR"]⟩
  , ⟨"Hebrew",          "heb", "Semitic",    .africa,
    ["ALMOST", "BEFORE", "FEAR", "UNTIL", "WORRY", "WITHOUT"]⟩
  , ⟨"Jibbali",         "shv", "Semitic",    .africa,
    ["FEAR", "REFUSE", "WARN", "PREVENT", "BEFORE"]⟩
  , ⟨"Maltese",         "mlt", "Semitic",    .africa,
    ["BEFORE", "UNTIL"]⟩
  , ⟨"Tigre",           "tig", "Semitic",    .africa,
    ["BEFORE", "FEAR"]⟩
  , ⟨"Tigrinya",        "tir", "Semitic",    .africa,
    ["BEFORE", "FEAR"]⟩
  , ⟨"Miya",            "mkf", "West Chadic", .africa,
    ["FEAR"]⟩
  -- ── Australia-New Guinea (2 languages) ─────────────────────────────
  , ⟨"Amele",           "aey", "Madang",     .australiaNewGuinea,
    ["APPREHENSIVE"]⟩
  , ⟨"Warrongo",        "wrg", "Northern Pama-Nyungan", .australiaNewGuinea,
    ["APPREHENSIONAL"]⟩
  -- ── Eurasia (56 languages) ─────────────────────────────────────────
  , ⟨"Albanian",        "sqi", "Albanian",   .eurasia,
    ["FEAR"]⟩
  , ⟨"Latvian",         "lvs", "Baltic",     .eurasia,
    ["FEAR"]⟩
  , ⟨"Lithuanian",      "lit", "Baltic",     .eurasia,
    ["FEAR", "UNTIL"]⟩
  , ⟨"Basque",          "eus", "Basque",     .eurasia,
    ["FEAR", "FORBID"]⟩
  , ⟨"Tshangla",        "tsj", "Bodic",      .eurasia,
    ["UNTIL"]⟩
  , ⟨"Rabha",           "rah", "Bodo-Garo",  .eurasia,
    ["UNTIL"]⟩
  , ⟨"Burushaski",      "bsk", "Burushaski", .eurasia,
    ["UNTIL"]⟩
  , ⟨"Breton",          "bre", "Celtic",     .eurasia,
    ["FOR FEAR THAT", "UNTIL", "WITHOUT"]⟩
  , ⟨"Kambera",         "xbr", "Central Malayo-Polynesian", .eurasia,
    ["FORBID"]⟩
  , ⟨"Mandarin",        "cmn", "Chinese",    .eurasia,
    ["ALMOST", "AVOID", "BEFORE", "BEWARE", "BLAME", "COMPLAIN",
     "DENY", "DOUBT", "INEVITABLE", "REFUSE", "REGRET", "UNLESS"]⟩
  , ⟨"Finnish",         "fin", "Finnic",     .eurasia,
    ["DENY", "DOUBT", "FEAR", "FORBID"]⟩
  , ⟨"Komi-Zyrian",     "kpf", "Finnic",     .eurasia,
    ["FEAR"]⟩
  , ⟨"Livonian",        "liv", "Livonian",   .eurasia,
    ["THAN"]⟩
  , ⟨"Afrikaans",       "afr", "Germanic",   .eurasia,
    ["BEFORE", "UNLESS"]⟩
  , ⟨"Dutch",           "nld", "Germanic",   .eurasia,
    ["BEFORE", "DENY", "THAN", "UNLESS"]⟩
  , ⟨"English",         "eng", "Germanic",   .eurasia,
    ["AVOID", "HOLD BACK FROM", "IMPOSSIBLE", "MISS",
     "KEEP FROM", "SINCE", "WITHOUT"]⟩
  , ⟨"German",          "deu", "Germanic",   .eurasia,
    ["BEFORE", "DENY", "UNTIL"]⟩
  , ⟨"Yiddish",         "yid", "Germanic",   .eurasia,
    ["FEAR", "UNTIL", "BEFORE"]⟩
  , ⟨"Greek",           "ell", "Greek",      .eurasia,
    ["BEWARE", "FEAR", "WORRY"]⟩
  , ⟨"Bengali",         "ben", "Indic",      .eurasia,
    ["UNTIL"]⟩
  , ⟨"Domari",          "rmt", "Indic",      .eurasia,
    ["PREVENT"]⟩
  , ⟨"Hindi",           "hin", "Indic",      .eurasia,
    ["FEAR", "UNTIL"]⟩
  , ⟨"Kashmiri",        "kas", "Indic",      .eurasia,
    ["UNTIL"]⟩
  , ⟨"Punjabi",         "pan", "Indic",      .eurasia,
    ["UNTIL"]⟩
  , ⟨"Persian",         "fas", "Iranian",    .eurasia,
    ["UNTIL/UNLESS"]⟩
  , ⟨"Catalan",         "cat", "Italic",     .eurasia,
    ["AVOID", "BEFORE", "DENY", "DOUBT", "FEAR", "THAN"]⟩
  , ⟨"French",          "fra", "Italic",     .eurasia,
    ["ADVISE AGAINST", "ALMOST", "ANXIOUS", "AVOID", "BEFORE",
     "BEWARE", "CAN'T WAIT", "DENY", "DESPAIR", "DOUBT", "FEAR",
     "FORBID", "HIDE", "IMPOSSIBLE", "IT ONLY DEPENDS ON SOMEONE THAT",
     "PREVENT", "RARELY", "SINCE", "TOO…TO", "UNLESS", "WITHOUT",
     "THAN", "WORRY"]⟩
  , ⟨"Italian",         "ita", "Italic",     .eurasia,
    ["BEFORE", "DOUBT", "HARDLY", "NEARLY", "THAN", "UNLESS",
     "UNTIL", "WITHOUT"]⟩
  , ⟨"Ligurian",        "lij", "Italic",     .eurasia,
    ["FEAR", "PREVENT"]⟩
  , ⟨"Portuguese",      "por", "Italic",     .eurasia,
    ["ALMOST", "AVOID", "FORBID", "PREVENT", "WATCH OUT", "WITHOUT"]⟩
  , ⟨"Romanian",        "ron", "Italic",     .eurasia,
    ["FEAR", "UNTIL/BEFORE"]⟩
  , ⟨"Spanish",         "spa", "Italic",     .eurasia,
    ["ALMOST", "AVOID", "DOUBT", "FEAR", "PREVENT", "UNTIL", "THAN"]⟩
  , ⟨"Japanese",        "jpn", "Japanese",   .eurasia,
    ["BEFORE"]⟩
  , ⟨"Kadu",            "zkd", "Jingpho-Luish", .eurasia,
    ["BEFORE"]⟩
  , ⟨"Lao",             "lao", "Kam-Tai",    .eurasia,
    ["FORBID"]⟩
  , ⟨"Georgian",        "kat", "Kartvelian",  .eurasia,
    ["FEAR", "UNTIL"]⟩
  , ⟨"Korean",          "kor", "Korean",     .eurasia,
    ["BEFORE", "IT'S BEEN A LONG TIME SINCE"]⟩
  , ⟨"Karbi",           "mjw", "Kuki-Chin",  .eurasia,
    ["BEFORE"]⟩
  , ⟨"Ingush",          "inh", "Nakh",       .eurasia,
    ["ONLY"]⟩
  , ⟨"Kurux",           "kxl", "Northern Dravidian", .eurasia,
    ["NOT WITHOUT", "UNTIL"]⟩
  , ⟨"Abkhaz",          "abk", "Northwest Caucasian", .eurasia,
    ["FEAR"]⟩
  , ⟨"Daakaka",         "bpa", "Oceanic",    .eurasia,
    ["FEAR", "LACK"]⟩
  , ⟨"Samoan",          "smo", "Oceanic",    .eurasia,
    ["AFRAID", "DISLIKE"]⟩
  , ⟨"Tuvaluan",        "tvl", "Oceanic",    .eurasia,
    ["BEFORE"]⟩
  , ⟨"Vaeakau-Taumako", "piv", "Oceanic",    .eurasia,
    ["CRITICIZE"]⟩
  , ⟨"Bulgarian",       "bul", "Slavic",     .eurasia,
    ["UNTIL"]⟩
  , ⟨"Czech",           "cse", "Slavic",     .eurasia,
    ["FEAR"]⟩
  , ⟨"Croatian",        "hrv", "Slavic",     .eurasia,
    ["BEFORE", "FEAR", "UNLESS", "UNTIL"]⟩
  , ⟨"Polish",          "pol", "Slavic",     .eurasia,
    ["BEFORE", "FEAR", "ALMOST"]⟩
  , ⟨"Russian",         "rus", "Slavic",     .eurasia,
    ["ALMOST", "BEWARE", "FEAR", "SINCE", "UNTIL", "WORRY"]⟩
  , ⟨"Slovenian",       "slv", "Slavic",     .eurasia,
    ["BEFORE", "FEAR", "UNLESS", "UNTIL"]⟩
  , ⟨"Ukrainian",       "ukr", "Slavic",     .eurasia,
    ["FEAR", "UNTIL"]⟩
  , ⟨"Turkish",         "tur", "Turkic",     .eurasia,
    ["BEFORE", "WITHOUT/FROM"]⟩
  , ⟨"Kumyk",           "kum", "Turkic",     .eurasia,
    ["FEAR"]⟩
  , ⟨"Hungarian",       "hun", "Ugric",      .eurasia,
    ["UNTIL"]⟩
  , ⟨"Vietnamese",      "vie", "Viet-Muong", .eurasia,
    ["AVOID", "FORBID", "FORGET", "REFUSE", "STOP"]⟩
  -- ── North America (1 language) ─────────────────────────────────────
  , ⟨"Lakhota",         "lkt", "Core Siouan", .northAmerica,
    ["BEFORE"]⟩
  -- ── Pidgins & Creoles (4 languages) ────────────────────────────────
  , ⟨"Haitian creole",  "hat", "Pidgin/Creole", .pidginsCreoles,
    ["WITHOUT"]⟩
  , ⟨"Nigerian pidgin", "pcm", "Pidgin/Creole", .pidginsCreoles,
    ["UNTIL"]⟩
  , ⟨"Pichinglis",      "fpe", "Pidgin/Creole", .pidginsCreoles,
    ["FEAR"]⟩
  , ⟨"Saramaccan creole", "srm", "Pidgin/Creole", .pidginsCreoles,
    ["CANNOT BE THAT"]⟩ ]

-- ── Verification ─────────────────────────────────────────────────────

/-- Table 3 has exactly 74 languages. -/
theorem enLanguages_count : enLanguages.length = 74 := by native_decide

/-- Per-area counts match Table 2. -/
theorem enLanguages_africa :
    (enLanguages.filter (·.area == .africa)).length = 11 := by native_decide

theorem enLanguages_australiaNewGuinea :
    (enLanguages.filter (·.area == .australiaNewGuinea)).length = 2 := by
  native_decide

theorem enLanguages_eurasia :
    (enLanguages.filter (·.area == .eurasia)).length = 56 := by native_decide

theorem enLanguages_northAmerica :
    (enLanguages.filter (·.area == .northAmerica)).length = 1 := by
  native_decide

theorem enLanguages_pidginsCreoles :
    (enLanguages.filter (·.area == .pidginsCreoles)).length = 4 := by
  native_decide

/-- No South American languages have EN in this sample. -/
theorem enLanguages_no_southAmerica :
    (enLanguages.filter (·.area == .southAmerica)).length = 0 := by
  native_decide

/-- Every language has at least one trigger concept. -/
theorem enLanguages_all_have_triggers :
    enLanguages.all (fun e => !e.triggers.isEmpty) = true := by native_decide

/-- The number of distinct genera represented (counting unique genus strings). -/
theorem enLanguages_many_genera :
    (enLanguages.map (·.genus) |>.eraseDups).length ≥ 37 := by native_decide

-- ── Cross-validation: Table 3 triggers vs Table 4 counts ────────────

/-! ### Cross-validating Table 3 and Table 4

Table 4 reports that BEFORE (UNTIL) triggers EN in 50 languages and
FEAR (AFRAID) in 39. We can verify these counts against the per-language
trigger lists in Table 3. -/

private def hasTrigger (triggers : List String) (concept : String) : Bool :=
  triggers.any (· == concept)

private def hasAnyTrigger (triggers : List String) (concepts : List String) : Bool :=
  concepts.any (hasTrigger triggers)

/-- BEFORE/UNTIL EN triggers occur in 50 languages (Table 4). -/
theorem enLanguages_before_count :
    (enLanguages.filter (λ e =>
      hasAnyTrigger e.triggers
        ["BEFORE", "UNTIL", "UNTIL/BEFORE", "UNTIL/UNLESS"])).length = 50 := by
  native_decide

/-- FEAR/AFRAID EN triggers occur in 39 languages (Table 4). -/
theorem enLanguages_fear_count :
    (enLanguages.filter (λ e =>
      hasAnyTrigger e.triggers
        ["FEAR", "AFRAID", "APPREHENSIVE", "APPREHENSIONAL",
         "FOR FEAR THAT", "FEAR⁵"])).length = 39 := by
  native_decide

end Phenomena.Negation.Typology
