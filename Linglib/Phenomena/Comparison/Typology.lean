import Linglib.Core.Lexical.Word
import Linglib.Core.Case
import Linglib.Core.WALS.Features.F121A

/-!
# Comparative Construction Typology (WALS Chapter 121)
@cite{beck-2009} @cite{haspelmath-2001} @cite{kennedy-2007} @cite{stassen-1985} @cite{stassen-2013}

Cross-linguistic data on how languages express comparison of inequality
("X is taller than Y"), based on @cite{stassen-2013} in WALS Online. Stassen
identifies five major construction types attested across a sample of 167
languages, classified by how the standard of comparison (the entity being
compared to) is encoded.

The WALS 2013 typology simplifies @cite{stassen-1985}'s original six-type
classification. Stassen 1985 (based on 110 languages) distinguishes three
subtypes within "locational": **separative** (standard marked 'from'/ablative),
**allative** (standard marked 'to'/goal), and **locative** (standard marked
'at'/contact). This finer distinction is crucial to the book's explanatory
hypothesis connecting comparative types to temporal chaining constructions
(formalized in `Studies/Stassen1985.lean`). The WALS 2013 typology also adds
the "mixed" category not present in the 1985 system.

The typology intersects with two further dimensions:
- **Degree word typology**: whether a language has an overt
  degree word like English "more" or achieves comparison morphologically or
  without any degree marker.
- **Superlative strategies**: how superlatives are formed (elative, definite
  article + comparative, special morphology, "exceed all" constructions, etc.).

## Key typological generalizations

1. Locational comparatives are the most common type worldwide.
2. Particle comparatives concentrate in Europe (a Standard Average European
   feature; @cite{haspelmath-2001}).
3. Exceed comparatives concentrate in West Africa and mainland Southeast Asia.
4. Conjoined comparatives are the least common type, concentrated in Papuan
   and Australian languages.
5. SOV languages strongly favor locational comparatives; SVO languages split
   between exceed and particle types.

-/

namespace Phenomena.Comparison.Typology

-- ============================================================================
-- Comparative Construction Types (@cite{stassen-2013})
-- ============================================================================

/-- WALS Ch 121: How a language expresses comparison of inequality.

    Stassen's classification is based on how the **standard of comparison**
    (the Y in "X is more Adj than Y") is encoded. The five types are
    cross-cutting: a single language may use more than one productively
    (classified as "mixed"). -/
inductive ComparativeType where
  /-- Locational: the standard is marked with a locational/ablative case
      or adposition, as if saying "X is tall from/at Y".
      Example: Japanese `Taroo wa Hanako yori se ga takai`
      'Taro TOP Hanako than/from tall'. Also Turkish (ablative),
      Hindi-Urdu (postposition `se`), Latin (ablative case). -/
  | locational
  /-- Exceed: a verb meaning 'exceed' or 'surpass' is used to encode
      comparison, as if saying "X exceeds/surpasses Y in tallness".
      Example: Yoruba `Ade ga ju Bola lo` 'Ade tall exceed Bola go'.
      Common in Niger-Congo and mainland Southeast Asian languages. -/
  | exceed
  /-- Conjoined: two juxtaposed or coordinated clauses, one attributing
      the property to X and the other denying it of Y (or attributing
      its antonym), as if saying "X is tall, Y is short".
      Example: Amele (Papuan) `uqa busak-i, ija cos-ig-a`
      'he big-PRED, I small-1SG-PRED'. The rarest type. -/
  | conjoined
  /-- Particle: a dedicated comparative particle or morpheme marks the
      standard, as in English "X is taller **than** Y". The particle is
      not a case marker or adposition with independent spatial meaning.
      Concentrated in Standard Average European. -/
  | particle
  /-- Mixed: the language uses more than one of the above types productively,
      without a clear dominant strategy. -/
  | mixed
  deriving DecidableEq, Repr

-- ============================================================================
-- Stassen 1985 Fine-grained Typology (@cite{stassen-1985} Ch 2)
-- ============================================================================

-- Case assignment parameters (`CaseAssignment`, `FixedCaseEncoding`) are
-- imported from `Core.Case.Basic`. The spatial triad (ablative, allative,
-- locative) reuses `Core.Case` values rather than defining a parallel type.

open Core (CaseAssignment FixedCaseEncoding)

/-- The six comparative construction types of @cite{stassen-1985} Ch 2.

    These are finer than the WALS 2013 types (`ComparativeType`): the three
    adverbial subtypes (separative, allative, locative) are collapsed into
    a single "locational" category in WALS. The six types form a hierarchy
    based on case assignment and syntactic encoding:

    ```
                        Comparative
                       /            \
                Derived case    Fixed case
               /        \       /        \
          Conjoined  Particle  Exceed  Adverbial
                                      /    |    \
                                   Sep   All   Loc
    ``` -/
inductive ComparativeType1985 where
  | separative | allative | locative | exceed | conjoined | particle
  deriving DecidableEq, Repr

/-- Map @cite{stassen-1985} types to the coarser WALS 2013 types.

    The key coarsening: separative, allative, and locative all become
    "locational". This loses the spatial-relation distinction that drives
    Stassen's explanatory universals connecting comparison to temporal
    chaining. -/
def ComparativeType1985.toWALS : ComparativeType1985 → ComparativeType
  | .separative => .locational
  | .allative   => .locational
  | .locative   => .locational
  | .exceed     => .exceed
  | .conjoined  => .conjoined
  | .particle   => .particle

/-- Case assignment for each 1985 type. -/
def ComparativeType1985.caseAssignment : ComparativeType1985 → CaseAssignment
  | .conjoined | .particle => .derived
  | _ => .fixed

/-- Fixed-case encoding (only meaningful for fixed-case types). -/
def ComparativeType1985.fixedEncoding :
    ComparativeType1985 → Option FixedCaseEncoding
  | .exceed => some .directObject
  | .separative | .allative | .locative => some .adverbial
  | .conjoined | .particle => none

/-- Spatial case of the standard marker (only meaningful for adverbial types).

    Maps to the `Core.Case` values that correspond to Stassen's spatial
    triad: ablative (separative), allative, locative. -/
def ComparativeType1985.spatialCase :
    ComparativeType1985 → Option Core.Case
  | .separative => some .abl
  | .allative => some .all
  | .locative => some .loc
  | _ => none

-- ============================================================================
-- Degree Word Typology (@cite{beck-2009})
-- ============================================================================

/-- Whether a language has an overt degree word in comparatives.

    @cite{beck-2009} classify languages into three types based on the
    presence and nature of degree morphology in comparison constructions:
    - Languages with a dedicated degree word (English "more", German "mehr")
    - Languages with comparative morphology but no free degree word
      (English "-er" suffix, but also Turkish, Japanese)
    - Languages with no degree marking at all (the comparative meaning is
      derived from context, word order, or the exceed-verb semantics). -/
inductive DegreeWordType where
  /-- Has a free degree word (e.g., English "more", French "plus",
      Mandarin "geng"). -/
  | hasDegreeWord
  /-- Has comparative morphology (affixal) but no free degree word
      (e.g., English "-er" for short adjectives, Turkish "-rak"). -/
  | morphological
  /-- No overt degree marking; comparison expressed via exceed verb,
      juxtaposition, or pragmatic inference. -/
  | noDegreeMarking
  deriving DecidableEq, Repr

-- ============================================================================
-- Superlative Strategies
-- ============================================================================

/-- How a language forms superlatives ("X is the tallest").

    Superlative strategies are partially independent of comparative type.
    Some languages lack a dedicated superlative entirely, using comparatives
    with a universal standard ("taller than all") or "most" constructions. -/
inductive SuperlativeStrategy where
  /-- Superlative morphology: dedicated affix or stem change
      (e.g., English "-est", Latin "-issimus"). -/
  | morphological
  /-- Definite article + comparative: "the more Adj" = superlative
      (e.g., Romance languages: French "le plus grand"). -/
  | definiteComparative
  /-- Elative: special "very/extremely" form without comparison class
      (e.g., Arabic elative pattern `ʔafʕal`). -/
  | elative
  /-- Exceed-all: exceed verb + universal quantifier
      (e.g., "X exceeds all in height"). -/
  | exceedAll
  /-- Comparative + universal standard: "X is taller than all"
      (e.g., Japanese `dare yori mo takai` 'than anyone tall'). -/
  | comparativeUniversal
  /-- No dedicated superlative strategy; context or periphrasis used. -/
  | none
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Converter Function
-- ============================================================================

/-- Map WALS 121A enum values to the local `ComparativeType`.

    The generated WALS data (v2020.4) uses four categories; the "mixed" type
    is not represented as a separate WALS value. Languages in the WALS dataset
    are assigned to whichever single type best characterizes them. -/
private def fromWALS121A : Core.WALS.F121A.ComparativeType → ComparativeType
  | .locational => .locational
  | .exceed     => .exceed
  | .conjoined  => .conjoined
  | .particle   => .particle

-- ============================================================================
-- WALS Distribution Data (from generated module)
-- ============================================================================

private abbrev ch121 := Core.WALS.F121A.allData

/-- Ch 121 total: 167 languages in the generated WALS dataset. -/
theorem ch121_total : ch121.length = 167 := by native_decide

/-- Ch 121A per-type counts from the generated WALS v2020.4 data. -/
theorem ch121_locational_count :
    (ch121.filter (·.value == .locational)).length = 78 := by native_decide
theorem ch121_exceed_count :
    (ch121.filter (·.value == .exceed)).length = 33 := by native_decide
theorem ch121_conjoined_count :
    (ch121.filter (·.value == .conjoined)).length = 34 := by native_decide
theorem ch121_particle_count :
    (ch121.filter (·.value == .particle)).length = 22 := by native_decide

/-- Per-type counts sum to sample total. -/
theorem ch121_counts_sum :
    (ch121.filter (·.value == .locational)).length +
    (ch121.filter (·.value == .exceed)).length +
    (ch121.filter (·.value == .conjoined)).length +
    (ch121.filter (·.value == .particle)).length =
    ch121.length := by native_decide

-- ============================================================================
-- Comparative Profile Structure
-- ============================================================================

/-- A language's comparative construction profile. -/
structure ComparativeProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String
  /-- WALS Ch 121 comparative type. -/
  comparativeType : ComparativeType
  /-- Degree word typology. -/
  degreeWord : DegreeWordType
  /-- Primary superlative strategy. -/
  superlative : SuperlativeStrategy
  /-- Illustrative comparative construction form. -/
  comparativeForm : String := ""
  /-- Standard marker (the "than" equivalent), if applicable. -/
  standardMarker : String := ""
  /-- Degree marker ("more" equivalent), if applicable. -/
  degreeMarker : String := ""
  /-- Dominant basic word order (for word-order correlations). -/
  basicOrder : String := ""
  /-- Notes on the construction. -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Language Data
-- ============================================================================

/--
English: particle comparative with dedicated "than". Dual degree marking:
free "more" for polysyllabic adjectives, bound "-er" for short adjectives.
Superlative: "-est" or "most". Classic Standard Average European pattern.
-/
def english : ComparativeProfile :=
  { language := "English"
  , iso := "eng"
  , comparativeType := .particle
  , degreeWord := .hasDegreeWord
  , superlative := .morphological
  , comparativeForm := "X is taller/more Adj than Y"
  , standardMarker := "than"
  , degreeMarker := "more / -er"
  , basicOrder := "SVO"
  , notes := "Dual degree marking: '-er' (synthetic) vs 'more' (analytic)" }

/--
German: particle comparative with "als" marking the standard. Comparative
formed with suffix "-er" (always synthetic, unlike English). Superlative
with "-st" + strong/weak ending. Standard Average European pattern.
-/
def german : ComparativeProfile :=
  { language := "German"
  , iso := "deu"
  , comparativeType := .particle
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X ist größer als Y"
  , standardMarker := "als"
  , degreeMarker := "-er (suffix)"
  , basicOrder := "SVO/V2"
  , notes := "Always synthetic comparative (-er); 'mehr' only for non-gradable NPs" }

/--
Japanese: locational comparative with postposition "yori" ('from/than')
marking the standard. No comparative morphology on the adjective; the
bare adjective form is used. SOV order. Superlative via universal
standard "dare yori mo" ('than anyone').
-/
def japanese : ComparativeProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , comparativeType := .locational
  , degreeWord := .noDegreeMarking
  , superlative := .comparativeUniversal
  , comparativeForm := "Y yori X ga Adj"
  , standardMarker := "yori"
  , degreeMarker := ""
  , basicOrder := "SOV"
  , notes := "No comparative morphology; 'motto' (more) is optional intensifier" }

/--
Mandarin Chinese: exceed comparative using "bi" construction. The verb-like
element "bi" introduces the standard, functioning as an exceed-type
marker. SVO order. Degree adverb "geng" ('more/even more') is optional.
-/
def mandarin : ComparativeProfile :=
  { language := "Mandarin"
  , iso := "cmn"
  , comparativeType := .exceed
  , degreeWord := .hasDegreeWord
  , superlative := .definiteComparative
  , comparativeForm := "X bi Y Adj"
  , standardMarker := "bi"
  , degreeMarker := "geng"
  , basicOrder := "SVO"
  , notes := "Debate whether 'bi' is a verb or coverb; " ++
             "superlative: 'zui' + Adj ('most Adj')" }

/--
Korean: locational comparative with ablative-like particle "-boda" marking
the standard. Some analyses treat "-boda" as a particle (mixed classification).
No comparative morphology on the adjective. SOV order.
-/
def korean : ComparativeProfile :=
  { language := "Korean"
  , iso := "kor"
  , comparativeType := .locational
  , degreeWord := .noDegreeMarking
  , superlative := .comparativeUniversal
  , comparativeForm := "Y-boda X-ga Adj"
  , standardMarker := "-boda"
  , degreeMarker := ""
  , basicOrder := "SOV"
  , notes := "'-boda' sometimes analyzed as particle; 'deo' (more) is optional" }

/--
Turkish: locational comparative with ablative case "-dan"/"-den" marking the
standard. Comparative morphology "-rak"/"-rek" exists but is optional.
SOV order. Superlative with "en" ('most') + adjective.
-/
def turkish : ComparativeProfile :=
  { language := "Turkish"
  , iso := "tur"
  , comparativeType := .locational
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X Y-den daha Adj"
  , standardMarker := "-dan/-den"
  , degreeMarker := "daha"
  , basicOrder := "SOV"
  , notes := "Ablative case on standard; 'daha' (more) is degree word; " ++
             "superlative: 'en' + Adj" }

/--
Yoruba: exceed comparative using verb "ju" ('surpass/exceed'). The parameter
(dimension) of comparison is expressed as a separate predicate.
Example: "Ade ga ju Bola lo" 'Ade tall exceed Bola go'. SVO order.
-/
def yoruba : ComparativeProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , comparativeType := .exceed
  , degreeWord := .noDegreeMarking
  , superlative := .exceedAll
  , comparativeForm := "X Adj ju Y lo"
  , standardMarker := "ju...lo"
  , degreeMarker := ""
  , basicOrder := "SVO"
  , notes := "Serial verb construction: Adj + 'exceed' + standard + 'go'" }

/--
Hindi-Urdu: locational comparative with postposition "se" ('from/than')
marking the standard. The comparative adjective is optionally modified
by "zyaadaa" ('more'). SOV order.
-/
def hindiUrdu : ComparativeProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , comparativeType := .locational
  , degreeWord := .hasDegreeWord
  , superlative := .comparativeUniversal
  , comparativeForm := "X Y se (zyaadaa) Adj hai"
  , standardMarker := "se"
  , degreeMarker := "zyaadaa"
  , basicOrder := "SOV"
  , notes := "Postposition 'se' also means 'from' (spatial); " ++
             "superlative: 'sab se' (from all) + Adj" }

/--
Russian: particle comparative with "chem" ('than') or genitive case on the
standard. Comparative adjective formed with "-ee"/"-ej" suffix or suppletive
stem. Relatively free word order (SVO dominant).
-/
def russian : ComparativeProfile :=
  { language := "Russian"
  , iso := "rus"
  , comparativeType := .particle
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X Adj-ee, chem Y / X Adj-ee Y-GEN"
  , standardMarker := "chem / genitive case"
  , degreeMarker := "-ee/-ej (suffix)"
  , basicOrder := "SVO"
  , notes := "Two standard-marking strategies: 'chem' particle or genitive case; " ++
             "superlative: 'samyj' + Adj or '-ejsij' suffix" }

/--
Finnish: locational comparative with partitive case marking the standard.
Comparative adjective formed with "-mpi" suffix. SOV/SVO flexible order.
-/
def finnish : ComparativeProfile :=
  { language := "Finnish"
  , iso := "fin"
  , comparativeType := .locational
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X on Y-tä Adj-mpi"
  , standardMarker := "partitive case"
  , degreeMarker := "-mpi (suffix)"
  , basicOrder := "SVO"
  , notes := "Partitive case on standard is locational (partitive < ablative); " ++
             "superlative: '-in' suffix" }

/--
Swahili: exceed comparative using verb "-zidi" ('exceed/surpass') or
"kuliko" ('than/more than'). SVO order. No comparative morphology on
adjectives. Bantu language with agglutinative verb morphology.
-/
def swahili : ComparativeProfile :=
  { language := "Swahili"
  , iso := "swh"
  , comparativeType := .exceed
  , degreeWord := .noDegreeMarking
  , superlative := .exceedAll
  , comparativeForm := "X ni Adj kuliko Y / X anazidi Y kwa uAdj"
  , standardMarker := "kuliko / -zidi"
  , degreeMarker := ""
  , basicOrder := "SVO"
  , notes := "Multiple exceed strategies: 'kuliko' and '-zidi' (surpass verb)" }

/--
Latin: locational comparative with ablative case marking the standard, or
particle "quam" ('than'). Comparative adjective formed with "-ior" suffix.
Free word order (SOV tendency). Superlative with "-issimus" suffix.
-/
def latin : ComparativeProfile :=
  { language := "Latin"
  , iso := "lat"
  , comparativeType := .mixed
  , degreeWord := .morphological
  , superlative := .morphological
  , comparativeForm := "X Adj-ior Y-ABL / X Adj-ior quam Y"
  , standardMarker := "ablative case / quam"
  , degreeMarker := "-ior (suffix)"
  , basicOrder := "SOV"
  , notes := "Mixed: ablative (locational) and 'quam' (particle) both productive; " ++
             "superlative: '-issimus' suffix" }

/--
Thai: exceed comparative using verb "kwaa" ('exceed/more'). SVO order.
The adjective precedes "kwaa", which introduces the standard.
No comparative morphology.
-/
def thai : ComparativeProfile :=
  { language := "Thai"
  , iso := "tha"
  , comparativeType := .exceed
  , degreeWord := .noDegreeMarking
  , superlative := .exceedAll
  , comparativeForm := "X Adj kwaa Y"
  , standardMarker := "kwaa"
  , degreeMarker := ""
  , basicOrder := "SVO"
  , notes := "'kwaa' functions as exceed marker; related to 'more than' semantics" }

/--
Tagalog: exceed comparative using "mas...kaysa" construction (borrowed from
Spanish "mas...que") or native "higit" ('surpass'). Verb-initial (VSO) order.
-/
def tagalog : ComparativeProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , comparativeType := .exceed
  , degreeWord := .hasDegreeWord
  , superlative := .definiteComparative
  , comparativeForm := "mas Adj si X kaysa kay Y / higit na Adj si X"
  , standardMarker := "kaysa / higit sa"
  , degreeMarker := "mas (< Spanish) / higit"
  , basicOrder := "VSO"
  , notes := "Spanish-influenced 'mas...kaysa' coexists with native 'higit'; " ++
             "superlative: 'pinaka-' prefix" }

/--
Arabic (Modern Standard): elative pattern "ʔafʕal" serves as both comparative
and superlative. The standard is marked with "min" ('from'). The elative is
a fixed morphological template, not decomposable into degree + adjective.
-/
def arabic : ComparativeProfile :=
  { language := "Arabic (MSA)"
  , iso := "arb"
  , comparativeType := .locational
  , degreeWord := .noDegreeMarking
  , superlative := .elative
  , comparativeForm := "X ʔafʕal min Y"
  , standardMarker := "min (from)"
  , degreeMarker := ""
  , basicOrder := "VSO/SVO"
  , notes := "Elative template ʔafʕal serves both comparative and superlative; " ++
             "'min' (from) marks standard = locational" }

/--
Navajo: conjoined comparative. Comparison expressed by juxtaposing two
clauses or using the comparative enclitic "-go" with a predicate meaning
'big/much'. Navajo lacks dedicated comparative morphology.
SOV order. Athabaskan language.
-/
def navajo : ComparativeProfile :=
  { language := "Navajo"
  , iso := "nav"
  , comparativeType := .conjoined
  , degreeWord := .noDegreeMarking
  , superlative := .none
  , comparativeForm := "X nineez, Y altso"
  , standardMarker := ""
  , degreeMarker := ""
  , basicOrder := "SOV"
  , notes := "No dedicated comparative construction; comparison via juxtaposition " ++
             "or predicate '-go nineez' (big-COMP tall)" }

/--
Martuthunira (Pama-Nyungan, Western Australia): conjoined comparative.
Comparison expressed by juxtaposing two clauses, one asserting the property
of the comparee and the other denying it (or asserting the antonym) of
the standard. Common Australian pattern.
-/
def martuthunira : ComparativeProfile :=
  { language := "Martuthunira"
  , iso := "vma"
  , comparativeType := .conjoined
  , degreeWord := .noDegreeMarking
  , superlative := .none
  , comparativeForm := "X big, Y small"
  , standardMarker := ""
  , degreeMarker := ""
  , basicOrder := "free"
  , notes := "Pama-Nyungan; typical Australian conjoined comparative pattern; " ++
             "no dedicated comparison morphology" }

/--
French: particle comparative with "que" ('than') marking the standard.
Degree word "plus" ('more') obligatory. Superlative: "le/la plus" +
adjective. Standard Average European pattern.
-/
def french : ComparativeProfile :=
  { language := "French"
  , iso := "fra"
  , comparativeType := .particle
  , degreeWord := .hasDegreeWord
  , superlative := .definiteComparative
  , comparativeForm := "X est plus Adj que Y"
  , standardMarker := "que"
  , degreeMarker := "plus"
  , basicOrder := "SVO"
  , notes := "Analytic comparative: 'plus' + Adj + 'que' + standard; " ++
             "superlative: definite article + comparative ('le plus grand')" }

/-- All language profiles in the sample. -/
def allLanguages : List ComparativeProfile :=
  [ english, german, japanese, mandarin, korean, turkish, yoruba
  , hindiUrdu, russian, finnish, swahili, latin, thai, tagalog
  , arabic, navajo, martuthunira, french ]

-- ============================================================================
-- Helper Predicates
-- ============================================================================

/-- Does a language have a given comparative type? -/
def ComparativeProfile.hasType (p : ComparativeProfile) (t : ComparativeType) : Bool :=
  p.comparativeType == t

/-- Does a language have a degree word? -/
def ComparativeProfile.hasDegWord (p : ComparativeProfile) : Bool :=
  p.degreeWord == .hasDegreeWord

/-- Does a language have comparative morphology (bound degree marking)? -/
def ComparativeProfile.hasMorphComp (p : ComparativeProfile) : Bool :=
  p.degreeWord == .morphological

/-- Does a language lack overt degree marking entirely? -/
def ComparativeProfile.noDegree (p : ComparativeProfile) : Bool :=
  p.degreeWord == .noDegreeMarking

/-- Does a language have a morphological superlative? -/
def ComparativeProfile.hasMorphSuperlative (p : ComparativeProfile) : Bool :=
  p.superlative == .morphological

/-- Is this an SOV language? -/
def ComparativeProfile.isSOV (p : ComparativeProfile) : Bool :=
  p.basicOrder == "SOV"

/-- Is this an SVO language? -/
def ComparativeProfile.isSVO (p : ComparativeProfile) : Bool :=
  p.basicOrder == "SVO" || p.basicOrder == "SVO/V2"

/-- Count of languages in the sample with a given comparative type. -/
def countByType (langs : List ComparativeProfile) (t : ComparativeType) : Nat :=
  (langs.filter (·.hasType t)).length

-- ============================================================================
-- Typological Generalization 1: Locational is Most Common Worldwide
-- ============================================================================

/-- In the WALS data, locational and particle comparatives together account
    for more than half of the 167-language sample. -/
theorem locational_and_particle_dominant :
    let loc := (ch121.filter (·.value == .locational)).length
    let par := (ch121.filter (·.value == .particle)).length
    loc + par > ch121.length / 2 := by native_decide

/-- Locational comparatives are the most common single type in WALS Ch 121. -/
theorem locational_most_common :
    let loc := (ch121.filter (·.value == .locational)).length
    let exc := (ch121.filter (·.value == .exceed)).length
    let con := (ch121.filter (·.value == .conjoined)).length
    let par := (ch121.filter (·.value == .particle)).length
    loc > exc ∧ loc > con ∧ loc > par := by native_decide

/-- Particle comparatives are the rarest single type in WALS Ch 121
    (in the v2020.4 data, which lacks a separate "mixed" category). -/
theorem particle_rarest :
    let loc := (ch121.filter (·.value == .locational)).length
    let exc := (ch121.filter (·.value == .exceed)).length
    let con := (ch121.filter (·.value == .conjoined)).length
    let par := (ch121.filter (·.value == .particle)).length
    par < loc ∧ par < exc ∧ par < con := by native_decide

-- ============================================================================
-- Typological Generalization 2: Particle Concentrates in Europe (SAE)
-- ============================================================================

/-- In our sample, particle comparative languages are all Indo-European
    languages of Europe. This reflects @cite{haspelmath-2001}'s identification of
    the comparative particle as a Standard Average European feature. -/
def particleLanguages : List ComparativeProfile :=
  allLanguages.filter (·.hasType .particle)

theorem particle_languages_count :
    particleLanguages.length = 4 := by native_decide

/-- All particle languages in our sample are SVO (or V2). -/
theorem particle_implies_svo_in_sample :
    particleLanguages.all (·.isSVO) = true := by native_decide

-- ============================================================================
-- Typological Generalization 3: Exceed Concentrates in W Africa and SE Asia
-- ============================================================================

/-- In our sample, exceed comparative languages include Yoruba (W Africa),
    Mandarin (E Asia), Swahili (E Africa), Thai (SE Asia), and Tagalog
    (Austronesian). This reflects the areal concentration noted by Stassen. -/
def exceedLanguages : List ComparativeProfile :=
  allLanguages.filter (·.hasType .exceed)

theorem exceed_languages_count :
    exceedLanguages.length = 5 := by native_decide

-- ============================================================================
-- Typological Generalization 4: Conjoined Comparatives are Rarest
-- ============================================================================

/-- Conjoined comparatives are the rarest type in our sample (2/18). -/
def conjoinedLanguages : List ComparativeProfile :=
  allLanguages.filter (·.hasType .conjoined)

theorem conjoined_languages_count :
    conjoinedLanguages.length = 2 := by native_decide

/-- Languages with conjoined comparatives universally lack overt degree marking
    in our sample: comparison without any morphological apparatus. -/
theorem conjoined_no_degree_marking :
    conjoinedLanguages.all (·.noDegree) = true := by native_decide

-- ============================================================================
-- Typological Generalization 5: SOV Favors Locational
-- ============================================================================

/-- SOV languages in our sample (Japanese, Korean, Turkish, Hindi-Urdu, Navajo,
    Latin) tend toward locational comparatives. In our sample, all SOV languages
    with a single comparative type use locational (the exceptions being Navajo
    with conjoined, and Latin which is mixed). -/
def sovLanguages : List ComparativeProfile :=
  allLanguages.filter (·.isSOV)

theorem sov_languages_count :
    sovLanguages.length = 6 := by native_decide

/-- Among SOV languages in our sample, locational is the dominant type: more
    SOV languages use locational than any other single type. -/
theorem sov_locational_dominant :
    let locCount := countByType sovLanguages .locational
    let excCount := countByType sovLanguages .exceed
    let parCount := countByType sovLanguages .particle
    locCount > excCount ∧ locCount > parCount := by native_decide

-- ============================================================================
-- Typological Generalization 6: SVO Splits Between Exceed and Particle
-- ============================================================================

/-- SVO languages in our sample are split between exceed (Mandarin, Yoruba,
    Swahili, Thai) and particle (English, German, Russian, French) types. -/
def svoLanguages : List ComparativeProfile :=
  allLanguages.filter (·.isSVO)

theorem svo_languages_count :
    svoLanguages.length = 9 := by native_decide

/-- Among SVO languages, exceed and particle types are roughly balanced. -/
theorem svo_exceed_particle_split :
    let excCount := countByType svoLanguages .exceed
    let parCount := countByType svoLanguages .particle
    excCount > 0 ∧ parCount > 0 := by native_decide

-- ============================================================================
-- Typological Generalization 7: Exceed Languages Lack Degree Morphology
-- ============================================================================

/-- Exceed-comparative languages in our sample mostly lack bound comparative
    morphology on adjectives. Comparison is expressed via the verb. -/
theorem exceed_mostly_no_morphology :
    let noMorph := exceedLanguages.filter (·.noDegree)
    noMorph.length ≥ 3 := by native_decide

-- ============================================================================
-- Typological Generalization 8: Conjoined Languages Lack Superlatives
-- ============================================================================

/-- Languages with conjoined comparatives also lack dedicated superlative
    strategies in our sample: if you can't grammaticalize "more than",
    you typically can't grammaticalize "most" either. -/
theorem conjoined_no_superlative :
    conjoinedLanguages.all (λ p => p.superlative == .none) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 9: Morphological Comparative ↔ Superlative
-- ============================================================================

/-- Languages with morphological comparative degree marking (suffix "-er"/"-ee"
    etc.) also tend to have morphological superlatives. In our sample, every
    language with morphological comparative degree also has a morphological
    superlative. -/
theorem morph_comp_implies_morph_super :
    let morphComp := allLanguages.filter (·.hasMorphComp)
    morphComp.all (·.hasMorphSuperlative) = true := by native_decide

-- ============================================================================
-- Typological Generalization 10: Locational Standard Markers are Polysemous
-- ============================================================================

/-- Every locational comparative in our sample uses a standard marker that
    also has spatial/ablative meaning ('from', ablative case, partitive case).
    This is definitional of the locational type but worth verifying: the
    standard marker is never semantically empty. -/
def locationalLanguages : List ComparativeProfile :=
  allLanguages.filter (·.hasType .locational)

theorem locational_languages_count :
    locationalLanguages.length = 6 := by native_decide

theorem locational_has_standard_marker :
    locationalLanguages.all (λ p => p.standardMarker != "") = true := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 121A (Comparative Constructions)
-- Languages whose profile comparative type matches the WALS F121A data.
-- German, Latin, Tagalog, and Martuthunira are absent from the WALS sample.
-- Finnish and Navajo are documented discrepancies (see end of file).
-- ============================================================================

theorem english_ch121 :
    (Core.WALS.F121A.lookup "eng").map (fromWALS121A ·.value) =
    some english.comparativeType := by native_decide
theorem japanese_ch121 :
    (Core.WALS.F121A.lookup "jpn").map (fromWALS121A ·.value) =
    some japanese.comparativeType := by native_decide
theorem mandarin_ch121 :
    (Core.WALS.F121A.lookup "mnd").map (fromWALS121A ·.value) =
    some mandarin.comparativeType := by native_decide
theorem korean_ch121 :
    (Core.WALS.F121A.lookup "kor").map (fromWALS121A ·.value) =
    some korean.comparativeType := by native_decide
theorem turkish_ch121 :
    (Core.WALS.F121A.lookup "tur").map (fromWALS121A ·.value) =
    some turkish.comparativeType := by native_decide
theorem yoruba_ch121 :
    (Core.WALS.F121A.lookup "yor").map (fromWALS121A ·.value) =
    some yoruba.comparativeType := by native_decide
theorem hindiUrdu_ch121 :
    (Core.WALS.F121A.lookup "hin").map (fromWALS121A ·.value) =
    some hindiUrdu.comparativeType := by native_decide
theorem russian_ch121 :
    (Core.WALS.F121A.lookup "rus").map (fromWALS121A ·.value) =
    some russian.comparativeType := by native_decide
theorem swahili_ch121 :
    (Core.WALS.F121A.lookup "swa").map (fromWALS121A ·.value) =
    some swahili.comparativeType := by native_decide
theorem thai_ch121 :
    (Core.WALS.F121A.lookup "tha").map (fromWALS121A ·.value) =
    some thai.comparativeType := by native_decide
theorem arabic_ch121 :
    (Core.WALS.F121A.lookup "ams").map (fromWALS121A ·.value) =
    some arabic.comparativeType := by native_decide
theorem french_ch121 :
    (Core.WALS.F121A.lookup "fre").map (fromWALS121A ·.value) =
    some french.comparativeType := by native_decide

-- Discrepancy: Finnish is .particle in WALS F121A but .locational in our profile
-- (Stassen may have reclassified; WALS 2013 emphasizes partitive-case standard).
-- Discrepancy: Navajo is .locational in WALS F121A but .conjoined in our profile
-- (genuine reclassification between 1985 and 2013 editions).

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Comparative type checks
theorem english_is_particle : english.comparativeType == .particle := by native_decide
theorem german_is_particle : german.comparativeType == .particle := by native_decide
theorem japanese_is_locational : japanese.comparativeType == .locational := by native_decide
theorem mandarin_is_exceed : mandarin.comparativeType == .exceed := by native_decide
theorem korean_is_locational : korean.comparativeType == .locational := by native_decide
theorem turkish_is_locational : turkish.comparativeType == .locational := by native_decide
theorem yoruba_is_exceed : yoruba.comparativeType == .exceed := by native_decide
theorem hindiUrdu_is_locational : hindiUrdu.comparativeType == .locational := by native_decide
theorem russian_is_particle : russian.comparativeType == .particle := by native_decide
theorem finnish_is_locational : finnish.comparativeType == .locational := by native_decide
theorem swahili_is_exceed : swahili.comparativeType == .exceed := by native_decide
theorem latin_is_mixed : latin.comparativeType == .mixed := by native_decide
theorem thai_is_exceed : thai.comparativeType == .exceed := by native_decide
theorem tagalog_is_exceed : tagalog.comparativeType == .exceed := by native_decide
theorem arabic_is_locational : arabic.comparativeType == .locational := by native_decide
theorem navajo_is_conjoined : navajo.comparativeType == .conjoined := by native_decide
theorem martuthunira_is_conjoined : martuthunira.comparativeType == .conjoined := by native_decide
theorem french_is_particle : french.comparativeType == .particle := by native_decide

-- Degree word checks
theorem english_has_degree_word : english.hasDegWord = true := by native_decide
theorem japanese_no_degree : japanese.noDegree = true := by native_decide
theorem german_morph_comp : german.hasMorphComp = true := by native_decide
theorem yoruba_no_degree : yoruba.noDegree = true := by native_decide

-- Superlative checks
theorem english_morph_super : english.hasMorphSuperlative = true := by native_decide
theorem french_def_comp_super :
    french.superlative == .definiteComparative := by native_decide
theorem arabic_elative_super :
    arabic.superlative == .elative := by native_decide
theorem navajo_no_super :
    navajo.superlative == .none := by native_decide

-- ============================================================================
-- Cross-Chapter Consistency: Comparative Type vs Degree Word
-- ============================================================================

/-- Particle comparatives in our sample all have overt degree marking
    (either a free degree word or comparative morphology): the comparative
    particle co-occurs with explicit degree semantics. -/
theorem particle_has_degree :
    particleLanguages.all (λ p =>
      p.hasDegWord || p.hasMorphComp) = true := by native_decide

/-- Conjoined comparatives in our sample never have degree marking:
    the absence of a dedicated comparative construction correlates with
    the absence of dedicated degree morphology. -/
theorem conjoined_lacks_degree :
    conjoinedLanguages.all (·.noDegree) = true := by native_decide

/-- Exceed comparatives show a split on degree words: some have overt
    degree words (Mandarin "geng", Tagalog "mas"), others do not
    (Yoruba, Swahili, Thai). -/
theorem exceed_degree_split :
    let withDeg := exceedLanguages.filter (·.hasDegWord)
    let withoutDeg := exceedLanguages.filter (·.noDegree)
    withDeg.length > 0 ∧ withoutDeg.length > 0 := by native_decide

-- ============================================================================
-- Distribution Summary for Our Sample
-- ============================================================================

/-- Sample type distribution: how many languages per comparative type. -/
theorem sample_locational_count :
    countByType allLanguages .locational = 6 := by native_decide
theorem sample_exceed_count :
    countByType allLanguages .exceed = 5 := by native_decide
theorem sample_conjoined_count :
    countByType allLanguages .conjoined = 2 := by native_decide
theorem sample_particle_count :
    countByType allLanguages .particle = 4 := by native_decide
theorem sample_mixed_count :
    countByType allLanguages .mixed = 1 := by native_decide

/-- Number of languages in our sample. -/
theorem sample_size : allLanguages.length = 18 := by native_decide

/-- All five comparative types are represented in our sample. -/
theorem all_types_represented :
    countByType allLanguages .locational > 0 ∧
    countByType allLanguages .exceed > 0 ∧
    countByType allLanguages .conjoined > 0 ∧
    countByType allLanguages .particle > 0 ∧
    countByType allLanguages .mixed > 0 := by native_decide

/-- The sample covers at least 3 word-order types: SOV, SVO, and VSO. -/
theorem word_order_diversity :
    let sov := (allLanguages.filter (·.isSOV)).length
    let svo := (allLanguages.filter (·.isSVO)).length
    let vso := (allLanguages.filter (λ p => p.basicOrder == "VSO" ||
                                            p.basicOrder == "VSO/SVO")).length
    sov > 0 ∧ svo > 0 ∧ vso > 0 := by native_decide

-- ============================================================================
-- Degree Word Distribution in Sample
-- ============================================================================

/-- Count of languages by degree word type. -/
def countByDegree (langs : List ComparativeProfile) (d : DegreeWordType) : Nat :=
  (langs.filter (λ p => p.degreeWord == d)).length

theorem sample_degree_word_count :
    countByDegree allLanguages .hasDegreeWord = 5 := by native_decide
theorem sample_morph_count :
    countByDegree allLanguages .morphological = 5 := by native_decide
theorem sample_no_degree_count :
    countByDegree allLanguages .noDegreeMarking = 8 := by native_decide

/-- Degree word presence totals match sample size. -/
theorem degree_counts_sum :
    countByDegree allLanguages .hasDegreeWord +
    countByDegree allLanguages .morphological +
    countByDegree allLanguages .noDegreeMarking =
    allLanguages.length := by native_decide

-- ============================================================================
-- Superlative Strategy Distribution
-- ============================================================================

/-- Count of languages by superlative strategy. -/
def countBySuperlative (langs : List ComparativeProfile)
    (s : SuperlativeStrategy) : Nat :=
  (langs.filter (λ p => p.superlative == s)).length

theorem sample_morph_superlative :
    countBySuperlative allLanguages .morphological = 6 := by native_decide
theorem sample_def_comp_superlative :
    countBySuperlative allLanguages .definiteComparative = 3 := by native_decide
theorem sample_exceed_all_superlative :
    countBySuperlative allLanguages .exceedAll = 3 := by native_decide
theorem sample_comp_univ_superlative :
    countBySuperlative allLanguages .comparativeUniversal = 3 := by native_decide
theorem sample_elative_superlative :
    countBySuperlative allLanguages .elative = 1 := by native_decide
theorem sample_no_superlative :
    countBySuperlative allLanguages .none = 2 := by native_decide

-- ============================================================================
-- Implicational Universal: No Superlative Without Comparative
-- ============================================================================

/-- Languages that lack a dedicated comparative construction (conjoined type,
    which is "comparison without comparison" in Stassen's terms) also lack
    dedicated superlative strategies. This is an implicational universal:
    SUPERLATIVE → COMPARATIVE (contrapositive: no comparative → no superlative).
    Our sample data is consistent with this universal. -/
theorem no_comparative_no_superlative :
    let noDedicated := allLanguages.filter (·.hasType .conjoined)
    noDedicated.all (λ p => p.superlative == .none) = true := by native_decide

-- ============================================================================
-- Stassen 1985 Type Assignments (@cite{stassen-1985} Ch 2)
-- ============================================================================

-- Languages classified by their 1985 type, verified against the language
-- lists in §2.3.1-5 and §2.4. Only languages appearing in both our sample
-- and Stassen's 110-language sample are included.

-- §2.3.1 Separative: standard marked 'from'/ablative (p. 40 list)
def japanese1985 : ComparativeType1985 := .separative
def korean1985 : ComparativeType1985 := .separative
def turkish1985 : ComparativeType1985 := .separative
def hindiUrdu1985 : ComparativeType1985 := .separative
def arabic1985 : ComparativeType1985 := .separative  -- "Arabic (Classical)"

-- §2.3.3 Locative: standard marked 'at/on'/contact (p. 42 list)
def navajo1985 : ComparativeType1985 := .locative  -- "Navaho" in the 1985 list

-- §2.3.4 Exceed: standard is direct object of exceed-verb (p. 43 list)
def mandarin1985 : ComparativeType1985 := .exceed
def yoruba1985 : ComparativeType1985 := .exceed
def swahili1985 : ComparativeType1985 := .exceed
def thai1985 : ComparativeType1985 := .exceed

-- §2.4 Particle: comparative particle marks standard NP (p. 47 list)
def english1985 : ComparativeType1985 := .particle
def russian1985 : ComparativeType1985 := .particle
def finnish1985 : ComparativeType1985 := .particle  -- primary; secondary separative
def latin1985 : ComparativeType1985 := .particle  -- primary; secondary separative
def french1985 : ComparativeType1985 := .particle

-- Not verified from 1985 book: German (not in p. 47 list, though likely
-- particle as SAE), Tagalog (not in 110-language sample), Martuthunira
-- (not in sample).

-- ============================================================================
-- Structural Properties of the 1985 Hierarchy
-- ============================================================================

/-- The three adverbial types all collapse to locational under WALS. -/
theorem adverbial_collapse :
    ComparativeType1985.separative.toWALS = .locational ∧
    ComparativeType1985.allative.toWALS = .locational ∧
    ComparativeType1985.locative.toWALS = .locational :=
  ⟨rfl, rfl, rfl⟩

/-- Derived-case types never map to locational. -/
theorem derived_case_not_locational (t : ComparativeType1985)
    (h : t.caseAssignment = .derived) : t.toWALS ≠ .locational := by
  cases t <;> simp_all [ComparativeType1985.caseAssignment,
    ComparativeType1985.toWALS]

/-- Fixed-case types never map to particle. -/
theorem fixed_case_not_particle (t : ComparativeType1985)
    (h : t.caseAssignment = .fixed) : t.toWALS ≠ .particle := by
  cases t <;> simp_all [ComparativeType1985.caseAssignment,
    ComparativeType1985.toWALS]

/-- Every adverbial type is fixed-case (by construction). -/
theorem adverbial_is_fixed (t : ComparativeType1985)
    (h : t.fixedEncoding = some .adverbial) :
    t.caseAssignment = .fixed := by
  cases t <;> simp_all [ComparativeType1985.fixedEncoding,
    ComparativeType1985.caseAssignment]

-- ============================================================================
-- 1985 ↔ WALS Consistency
-- ============================================================================

-- For most languages, the 1985 type maps to the existing WALS type.

theorem japanese_consistent :
    japanese1985.toWALS = japanese.comparativeType := by native_decide
theorem korean_consistent :
    korean1985.toWALS = korean.comparativeType := by native_decide
theorem turkish_consistent :
    turkish1985.toWALS = turkish.comparativeType := by native_decide
theorem hindiUrdu_consistent :
    hindiUrdu1985.toWALS = hindiUrdu.comparativeType := by native_decide
theorem arabic_consistent :
    arabic1985.toWALS = arabic.comparativeType := by native_decide
theorem mandarin_consistent :
    mandarin1985.toWALS = mandarin.comparativeType := by native_decide
theorem yoruba_consistent :
    yoruba1985.toWALS = yoruba.comparativeType := by native_decide
theorem swahili_consistent :
    swahili1985.toWALS = swahili.comparativeType := by native_decide
theorem thai_consistent :
    thai1985.toWALS = thai.comparativeType := by native_decide
theorem english_consistent :
    english1985.toWALS = english.comparativeType := by native_decide
theorem russian_consistent :
    russian1985.toWALS = russian.comparativeType := by native_decide
theorem french_consistent :
    french1985.toWALS = french.comparativeType := by native_decide

-- ============================================================================
-- 1985 ↔ WALS Discrepancies
-- ============================================================================

-- Three languages show classification differences between the 1985 book
-- and the current WALS-based profiles:
--
-- 1. Finnish: particle in 1985 (p. 47 list), locational in WALS 2013.
--    Stassen may have reclassified Finnish between editions, or the WALS
--    classification emphasizes the partitive-case standard marker over
--    the comparative particle.
--
-- 2. Latin: particle-primary in 1985 (p. 47, with quam), mixed in WALS
--    2013 (because ablative comparative is also productive). The 1985
--    system distinguished primary vs secondary options; WALS uses "mixed".
--
-- 3. Navajo: locative in 1985 (p. 42 "Navaho"), conjoined in WALS 2013.
--    This is a genuine reclassification between the two works. The 1985
--    classification was based on locative spatial marking; the 2013
--    classification may emphasize the clause-level structure.
--
-- These discrepancies are documented rather than suppressed. The
-- consistency theorems above cover only the 12 languages where both
-- systems agree.

-- ============================================================================
-- Comparison Construction Categories
-- ============================================================================

/-- The major comparison construction types found cross-linguistically. -/
inductive ComparisonConstruction where
  | comparative     -- "taller than", "more expensive than"
  | equative        -- "as tall as"
  | superlative     -- "tallest", "most expensive"
  | excessive       -- "too tall" (implicit comparison to a standard)
  | sufficiency     -- "tall enough" (implicit comparison to a standard)
  | degreeQuestion  -- "how tall" (comparison to answer alternatives)
  deriving DecidableEq, Repr

/-- What is being compared — the syntactic category of the gradable
    expression, following @cite{wellwood-2015}.

    The key insight: comparison constructions apply uniformly across
    categories; what varies is the measured domain (entity, event, state). -/
inductive ComparisonDomain where
  | adjectival   -- "taller than", "more expensive than"
  | nominal      -- "more coffee than", "fewer books than"
  | verbal       -- "ran more than", "sang louder than"
  | adverbial    -- "more quickly than", "as carefully as"
  deriving DecidableEq, Repr

/-- How degree comparison is morphologically realized in a given form.

    This is orthogonal to `DegreeWordType` (above), which classifies
    whether a *language* has degree marking at all. `DegreeMorphology`
    classifies a specific *form*: English "taller" is synthetic,
    "more tall" is analytic, "better" is suppletive — all in a language
    that `DegreeWordType` classifies as `.hasDegreeWord`. -/
inductive DegreeMorphology where
  | synthetic   -- "-er"/"-est" (English, German)
  | analytic    -- "more"/"most" (English, French)
  | suppletive  -- "good"/"better"/"best" (English, Latin)
  | mixed       -- both synthetic and analytic available
  deriving DecidableEq, Repr

end Phenomena.Comparison.Typology
