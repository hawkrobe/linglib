import Linglib.Core.Lexical.Word
import Linglib.Core.WALS.Features.F112A
import Linglib.Core.WALS.Features.F113A
import Linglib.Core.WALS.Features.F114A
import Linglib.Core.WALS.Features.F115A

/-!
# Cross-Linguistic Typology of Negation (WALS Chapters 112--115)
@cite{dryer-haspelmath-2013} @cite{haspelmath-2013} @cite{miestamo-2005} @cite{miestamo-2013}

Cross-linguistic data on clausal negation from four WALS chapters:

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

    Three primary subtypes:
    - A/Fin: negation changes finiteness (adds negative verb, lexical verb
      becomes nonfinite / subordinate)
    - A/NonReal: negation introduces irrealis/nonrealized marking
    - A/Cat: negation changes marking of TAM, person, number, etc. -/
inductive AsymmetrySubtype where
  /-- A/Fin: asymmetry in finiteness. Typically a negative auxiliary becomes
      the finite verb, and the lexical verb appears in a nonfinite form
      (e.g., Finnish: `e-n tule` 'NEG-1SG come.CONNEG'). -/
  | finiteness
  /-- A/NonReal: asymmetry in reality status. The negative is obligatorily
      marked with an irrealis/nonrealized category that the affirmative
      lacks (e.g., Imbabura Quechua: negative requires `-chu` irrealis). -/
  | realityStatus
  /-- A/Cat: asymmetry in other grammatical categories (TAM, person-number
      affixes, etc.). The negative uses different category markers than the
      affirmative (e.g., Karok: different person-number affixes under
      negation). -/
  | otherCategories
  /-- Combined: A/Fin and A/NonReal
      (e.g., Copainalá Zoque, Squamish). -/
  | finAndNonReal
  /-- Combined: A/Fin and A/Cat
      (e.g., Kolokuma Ijo). -/
  | finAndCat
  /-- Combined: A/NonReal and A/Cat. -/
  | nonRealAndCat
  /-- Non-assignable: language has only symmetric negation (Type Sym in
      Ch 113), so no asymmetry subtype applies. -/
  | nonAssignable
  deriving DecidableEq, BEq, Repr

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

/-- All language profiles in the sample. -/
def allLanguages : List NegationProfile :=
  [ english, german, french, russian, finnish, japanese, mandarin, turkish
  , czech, spanish, italian, burmese, maori, izi, kolYukaghir, rama
  , hixkaryana, nelemwa ]

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
theorem sample_size : allLanguages.length = 18 := by native_decide

/-- Morpheme type distribution in our sample. -/
theorem sample_affix_count : countByMorphemeType allLanguages .affix = 5 := by native_decide
theorem sample_particle_count : countByMorphemeType allLanguages .particle = 9 := by native_decide
theorem sample_auxverb_count : countByMorphemeType allLanguages .auxVerb = 1 := by native_decide
theorem sample_double_count : countByMorphemeType allLanguages .doubleNeg = 2 := by native_decide
theorem sample_unclear_count : countByMorphemeType allLanguages .wordUnclear = 1 := by native_decide
theorem sample_variation_count : countByMorphemeType allLanguages .variation = 0 := by native_decide

/-- Symmetry distribution in our sample. -/
theorem sample_symmetry_counts :
    countBySymmetry allLanguages .symmetric = 7 ∧
    countBySymmetry allLanguages .asymmetric = 6 ∧
    countBySymmetry allLanguages .both = 5 := by
  native_decide

end Phenomena.Negation.Typology
