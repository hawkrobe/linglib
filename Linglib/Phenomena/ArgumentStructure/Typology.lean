import Linglib.Core.Case.Basic
import Linglib.Core.Lexical.Word
import Linglib.Datasets.WALS.Features.F106A
import Linglib.Datasets.WALS.Features.F107A
import Linglib.Datasets.WALS.Features.F108A
import Linglib.Datasets.WALS.Features.F108B
import Linglib.Datasets.WALS.Features.F109A
import Linglib.Datasets.WALS.Features.F109B
import Linglib.Datasets.WALS.Features.F105A
import Linglib.Datasets.WALS.Features.F111A
import Linglib.Fragments.Finnish.Predicates
import Linglib.Fragments.English.Pronouns
import Linglib.Core.Lexical.MorphRule

/-!
# Cross-Linguistic Typology of Valence and Voice (WALS Chapters 105--111)
@cite{maslova-nedjalkov-2013} @cite{siewierska-2013}
@cite{haspelmath-2013-ditransitive}
@cite{polinsky-2013-antipassive} @cite{polinsky-2013-applicative}
@cite{song-2013-periphrastic} @cite{song-2013-nonperiphrastic}
@cite{nordlinger-2023}
@cite{dalrymple-et-al-1998} @cite{siloni-2008} @cite{siloni-2012}
@cite{konig-kokutani-2006} @cite{dixon-1972} @cite{ryding-2005}
@cite{kimenyi-1980} @cite{galloway-1993}

Typological data on valence-changing and voice constructions, drawn from
WALS (World Atlas of Language Structures) chapters 105--111:

- **Ch 105** (@cite{haspelmath-2013-ditransitive}): Ditransitive constructions ('give') --
  how R (recipient) and T (theme) align with monotransitive P (patient).
  378 languages.
- **Ch 106** (@cite{maslova-nedjalkov-2013}): Reciprocal constructions and their
  relationship to reflexives. 175 languages.
- **Ch 107** (@cite{siewierska-2013}): Passive constructions -- presence/absence across
  373 languages. Passives occur in 44% of sampled languages, concentrated
  in Eurasia and Africa.
- **Ch 108** (@cite{polinsky-2013-antipassive}): Antipassive constructions -- detransitivizing
  operations that demote the patient. 194 languages.
- **Ch 109** (@cite{polinsky-2013-applicative}): Applicative constructions -- valence-increasing
  operations adding an applied object. 183 languages.
- **Ch 110** (@cite{song-2013-periphrastic}): Periphrastic causative constructions -- sequential vs
  purposive types. 118 languages.
- **Ch 111** (@cite{song-2013-nonperiphrastic}): Nonperiphrastic causative constructions -- morphological
  vs compound types. 310 languages.

This module focuses on Ch 105--109 (ditransitives, reciprocals, passives,
antipassives, applicatives). Causative typology (Ch 110--111) is covered in
`Phenomena.Causation.Typology`; only aggregate WALS counts are recorded
here for cross-reference.

-/

namespace Phenomena.ArgumentStructure.Typology

-- ============================================================================
-- Ch 106: Reciprocal Constructions (@cite{maslova-nedjalkov-2013})
-- ============================================================================

/-- WALS Ch 106: How reciprocal situations are encoded relative to reflexives.

    The four values follow @cite{maslova-nedjalkov-2013}'s classification:

    - `noDedicated`: "There are no non-iconic reciprocal constructions" —
      the language lacks a dedicated grammatical reciprocal marker.
    - `distinctFromReflexive`: "All reciprocal constructions are formally
      distinct from reflexive constructions" (e.g. English "each other" vs
      "themselves").
    - `mixed`: "There are both reflexive and non-reflexive reciprocal
      constructions" — the language has both a reflexive-identical strategy
      and a formally distinct one (e.g. German "sich" + "einander").
      Common in Europe.
    - `identicalToReflexive`: "The reciprocal and reflexive constructions
      are formally identical" (e.g. Imbabura Quechua "-ri",
      West Greenlandic "-ssin-"). -/
inductive ReciprocalType where
  | noDedicated
  | distinctFromReflexive
  | mixed
  | identicalToReflexive
  deriving DecidableEq, Repr

-- ============================================================================
-- Reciprocal Morphosyntactic Strategy (@cite{nordlinger-2023}, §3.1)
-- ============================================================================

/-- Morphosyntactic strategy for encoding reciprocity.

    @cite{nordlinger-2023} summarizes the structural typologies of
    König & Kokutani (2006), Nedjalkov (2007a), and Evans (2008), which
    classify reciprocal constructions by the morphosyntactic locus
    of the reciprocal marking:

    - `bipartiteNP`: Bipartite quantifier NP — English "each other",
      Icelandic "hvor...annad" (two independently inflected parts).
    - `recipPronoun`: Reciprocal pronoun — Russian "drug druga",
      Hausa "jùnan-mù". Free-standing pronominal form in object position.
    - `recipClitic`: Reciprocal clitic — French/Czech "se",
      Wambaya "-ngg-" (RR morpheme in auxiliary). Intermediate between
      pronoun and affix; functionally verbal (valence-reducing in most
      cases, though Wambaya retains bivalent syntax via ergative case).
    - `verbalAffix`: Morphological marking on the verb — Swahili "-ana",
      Hungarian "-oz-", Chicheŵa "-an-". Derives an intransitive
      (monovalent) verb from a transitive base.
    - `verbalAuxiliary`: Reciprocal auxiliary — Warrwa "wanji-" replaces
      the regular transitive auxiliary.
    - `lexical`: Inherently reciprocal predicate — English "quarrel",
      "meet". The symmetric meaning is part of the verb's lexical semantics.
    - `compoundVerb`: Compound verb — Mandarin "dǎ-lái-dǎ-qù"
      (beat-come-beat-go = 'beat each other'). -/
inductive RecipStrategy where
  | bipartiteNP
  | recipPronoun
  | recipClitic
  | verbalAffix
  | verbalAuxiliary
  | lexical
  | compoundVerb
  deriving DecidableEq, Repr

/-- Whether the strategy marks the NP/argument position (nominal strategy)
    or the verb/predicate (verbal strategy).
    König & Kokutani (2006)'s primary typological distinction.

    Clitics are classified as non-nominal: Evans (2008) treats them as
    intermediate, but their valence behavior is typically verbal —
    French/Czech "se" reduces valence (monovalent), and even Wambaya
    "-ngg-" is morphologically bound to the auxiliary. -/
def RecipStrategy.isNominal : RecipStrategy → Bool
  | .bipartiteNP     => true
  | .recipPronoun    => true
  | .recipClitic     => false
  | .verbalAffix     => false
  | .verbalAuxiliary => false
  | .lexical         => false
  | .compoundVerb    => false

-- ============================================================================
-- Reciprocal Valency Effect (@cite{nordlinger-2023}, §3.2)
-- ============================================================================

/-- Valency effect of reciprocal construction on the base predicate.

    Maslova (2008) distinguishes "unary" and "binary" reciprocals;
    @cite{nordlinger-2023} (§3.2) discusses how NP/argument strategies
    tend to preserve valency while verb-marked strategies tend to
    reduce it. The correlation is a tendency, not absolute — Malagasy
    verb-marked reciprocals retain full valency at f-structure
    (Hurst 2006, 2012). -/
inductive RecipValency where
  | bivalent    -- two syntactic arguments preserved
  | monovalent  -- verb becomes intransitive (single subject NP)
  deriving DecidableEq, Repr

-- ============================================================================
-- Reciprocal Formation Locus (Siloni 2008, 2012)
-- ============================================================================

/-- Where reciprocal verbs are formed, per Siloni (2008, 2012).

    @cite{nordlinger-2023} (§3.3) discusses Siloni's distinction:
    - `lexical`: formed in the lexicon through "bundling" — two thematic
      roles (agent, patient) merge into a single complex role. Produces
      verbs with inherently symmetric semantics. Can license discontinuous
      reciprocal constructions (subject + comitative argument).
    - `syntactic`: formed in the syntax via an operation that creates
      the symmetric reading. Cannot license discontinuous reciprocals.

    Key empirical prediction: discontinuous reciprocals ("John kissed
    with Mary") are possible only with lexically-formed reciprocal verbs. -/
inductive RecipFormation where
  | lexical
  | syntactic
  deriving DecidableEq, Repr

/-- Can the reciprocal construction appear in discontinuous form
    (reciprocants split across subject and comitative argument)?
    @cite{nordlinger-2023} §3.3. -/
def RecipFormation.allowsDiscontinuous : RecipFormation → Bool
  | .lexical   => true
  | .syntactic => false

-- ============================================================================
-- Ch 107: Passive Constructions (@cite{siewierska-2013})
-- ============================================================================

/-- WALS Ch 107: Whether a language has passive constructions.

    Siewierska defines a passive as having five properties: (i) contrasts
    with active, (ii) active subject demoted or suppressed, (iii) active
    object promoted to subject (if personal passive), (iv) pragmatically
    restricted, (v) special verbal morphology. Includes both personal and
    impersonal passives, both synthetic (Swahili `-w-`) and periphrastic
    (English "be + past participle", Polish `zostac + participle`).

    - `present`: The language has at least one passive construction.
    - `absent`: No passive construction (agent demotion achieved by other
      means: subject omission, impersonal pronoun, 3pl verb form, etc.). -/
inductive PassivePresence where
  | present
  | absent
  deriving DecidableEq, Repr

-- ============================================================================
-- Ch 108: Antipassive Constructions (@cite{polinsky-2013-antipassive})
-- ============================================================================

/-- WALS Ch 108: Antipassive construction type.

    An antipassive is a derived detransitivized construction: the patient-like
    argument is either suppressed or demoted to an oblique. The term indicates the mirror image of the passive: in the
    passive the agent is demoted, in the antipassive the patient.

    - `implicitPatient`: Patient-like argument left implicit (unexpressed).
    - `obliquePatient`: Patient-like argument expressed as oblique complement
      (e.g. Chukchi instrumental `kimitw-e` in antipassive vs absolutive
      `kimitw-xn` in transitive).
    - `noAntipassive`: No antipassive construction. -/
inductive AntipassiveType where
  | implicitPatient
  | obliquePatient
  | noAntipassive
  deriving DecidableEq, Repr

/-- Does this value represent the presence of an antipassive? -/
def AntipassiveType.hasAntipassive : AntipassiveType -> Bool
  | .implicitPatient => true
  | .obliquePatient  => true
  | .noAntipassive   => false

/-- WALS Ch 108 inset map: Productivity of the antipassive.

    - `productive`: Antipassive applies to a wide range of transitive verbs.
    - `partiallyProductive`: Restricted to certain subsets of transitives.
    - `notProductive`: Very limited (lexically specified). -/
inductive AntipassiveProductivity where
  | productive
  | partiallyProductive
  | notProductive
  deriving DecidableEq, Repr

/-- Morphological alignment system (simplified for antipassive correlation).
    The canonical accusative/ergative dichotomy lives in `Core.AlignmentFamily`;
    this file uses that type directly rather than re-declaring it. A richer
    typology (active-stative, tripartite, hierarchical, etc.) is available in
    `Phenomena.Alignment.Typology.AlignmentType`. -/
abbrev AlignmentType := Core.AlignmentFamily

-- ============================================================================
-- Ch 105: Ditransitive Constructions: The Verb 'Give' (@cite{haspelmath-2013-ditransitive})
-- ============================================================================

/-- WALS Ch 105: How ditransitive verbs (prototypically 'give') encode
    the recipient (R) and theme (T) arguments relative to the monotransitive
    patient (P).

    - `indirectObject`: R is treated differently from P (R gets a
      preposition or dative case: "give the book TO Mary").
    - `doubleObject`: R is treated the same as P (both bare NPs:
      "give Mary the book").
    - `secondaryObject`: T is treated differently from P (T gets
      special marking: Ainu, Lakhota).
    - `mixed`: More than one construction type is available. -/
inductive DitransitiveType where
  | indirectObject
  | doubleObject
  | secondaryObject
  | mixed
  deriving DecidableEq, Repr

-- ============================================================================
-- Ch 109: Applicative Constructions (@cite{polinsky-2013-applicative})
-- ============================================================================

/-- WALS Ch 109: Transitivity of the base verb for applicative formation.

    - `bothBases`: Applicatives formed from both transitive and intransitive
      bases (most common pattern when applicatives exist).
    - `transitiveOnly`: Only from transitive bases.
    - `intransitiveOnly`: Only from intransitive bases (rare: Fijian, Wambaya). -/
inductive ApplicativeBase where
  | bothBases
  | transitiveOnly
  | intransitiveOnly
  deriving DecidableEq, Repr

/-- WALS Ch 109: Semantic role of the applied object.

    - `benefactiveOnly`: Applied object restricted to benefactive role.
    - `benefactiveAndOther`: Benefactive plus instrument, locative, etc.
    - `nonbenefactiveOnly`: No benefactive; only instrument, locative, etc. -/
inductive AppliedObjectRole where
  | benefactiveOnly
  | benefactiveAndOther
  | nonbenefactiveOnly
  deriving DecidableEq, Repr

/-- WALS Ch 109: Full applicative type combining base and role.
    `none` for languages without applicative constructions. -/
inductive ApplicativeType where
  | applicative (base : ApplicativeBase) (role : AppliedObjectRole)
  | noApplicative
  deriving DecidableEq, Repr

/-- Does this value represent the presence of an applicative? -/
def ApplicativeType.hasApplicative : ApplicativeType -> Bool
  | .applicative .. => true
  | .noApplicative  => false

-- ============================================================================
-- Ch 110--111: Causative types (cross-reference only; see Causation.Typology)
-- ============================================================================

/-- WALS Ch 110: Periphrastic causative type. -/
inductive PeriphrasticCausativeType where
  | sequentialOnly
  | purposiveOnly
  | both
  deriving DecidableEq, Repr

/-- WALS Ch 111: Nonperiphrastic (morphological/compound) causative type. -/
inductive NonperiphrCausativeType where
  | neither
  | morphologicalOnly
  | compoundOnly
  | both
  deriving DecidableEq, Repr

/-- Does this value represent a morphological causative? -/
def NonperiphrCausativeType.hasMorphological : NonperiphrCausativeType -> Bool
  | .morphologicalOnly => true
  | .both              => true
  | _                  => false

-- ============================================================================
-- WALS Distribution Data — derived from generated modules
-- ============================================================================
-- Full per-language data lives in Datasets.WALS.Features.F{106A..111A}.
-- These theorems re-derive aggregate counts from the generated data, ensuring
-- the numbers in our generalizations below stay in sync with the source.

-- Per-feature dataset sizes (175, 373, 194, 186, 310 for F{106A,107A,108A,108B,111A})
-- are documented in each feature's module docstring; we don't restate them here.

-- ---- F105A: Ditransitive Constructions ----

private abbrev f105a := Datasets.WALS.F105A.allData

/-- Convert WALS 105A value to our DitransitiveType. -/
private def fromWALS105A : Datasets.WALS.F105A.DitransitiveConstructionsTheVerbGive → DitransitiveType
  | .indirectObjectConstruction  => .indirectObject
  | .doubleObjectConstruction    => .doubleObject
  | .secondaryObjectConstruction => .secondaryObject
  | .mixed                       => .mixed

theorem f105a_count_indirectObject :
    (f105a.filter (·.value == .indirectObjectConstruction)).length = 189 := by native_decide
theorem f105a_count_doubleObject :
    (f105a.filter (·.value == .doubleObjectConstruction)).length = 84 := by native_decide
theorem f105a_count_secondaryObject :
    (f105a.filter (·.value == .secondaryObjectConstruction)).length = 65 := by native_decide
theorem f105a_count_mixed :
    (f105a.filter (·.value == .mixed)).length = 40 := by native_decide

-- ---- F109A: Applicative Constructions ----

private abbrev f109a := Datasets.WALS.F109A.allData

/-- Convert WALS 109A value to our ApplicativeType.
    The WALS enum encodes base-transitivity and semantic role together;
    we decompose into `ApplicativeBase` x `AppliedObjectRole`. -/
private def fromWALS109A : Datasets.WALS.F109A.ApplicativeType → ApplicativeType
  | .benefactiveBothBases         => .applicative .bothBases .benefactiveOnly
  | .benefactiveTransOnly         => .applicative .transitiveOnly .benefactiveOnly
  | .benefactiveAndOtherBothBases => .applicative .bothBases .benefactiveAndOther
  | .benefactiveAndOtherTransOnly => .applicative .transitiveOnly .benefactiveAndOther
  | .nonBenefactiveBothBases      => .applicative .bothBases .nonbenefactiveOnly
  | .nonBenefactiveTransOnly      => .applicative .transitiveOnly .nonbenefactiveOnly
  | .nonBenefactiveIntransOnly    => .applicative .intransitiveOnly .nonbenefactiveOnly
  | .noApplicative                => .noApplicative

theorem f109a_count_benefactiveBothBases :
    (f109a.filter (·.value == .benefactiveBothBases)).length = 16 := by native_decide
theorem f109a_count_benefactiveTransOnly :
    (f109a.filter (·.value == .benefactiveTransOnly)).length = 4 := by native_decide
theorem f109a_count_benefactiveAndOtherBothBases :
    (f109a.filter (·.value == .benefactiveAndOtherBothBases)).length = 49 := by native_decide
theorem f109a_count_benefactiveAndOtherTransOnly :
    (f109a.filter (·.value == .benefactiveAndOtherTransOnly)).length = 2 := by native_decide
theorem f109a_count_nonBenefactiveBothBases :
    (f109a.filter (·.value == .nonBenefactiveBothBases)).length = 9 := by native_decide
theorem f109a_count_nonBenefactiveTransOnly :
    (f109a.filter (·.value == .nonBenefactiveTransOnly)).length = 1 := by native_decide
theorem f109a_count_nonBenefactiveIntransOnly :
    (f109a.filter (·.value == .nonBenefactiveIntransOnly)).length = 2 := by native_decide
theorem f109a_count_noApplicative :
    (f109a.filter (·.value == .noApplicative)).length = 100 := by native_decide

-- ---- F109B: Other Roles of Applied Objects ----

private abbrev f109b := Datasets.WALS.F109B.allData

/-- Convert WALS 109B value to an optional AppliedObjectRole.
    Returns `none` for languages without applicative constructions,
    since there is no applied object whose role could be classified.
    Instrument, locative, and instrument-and-locative all map to
    `.nonbenefactiveOnly`; the finer distinction is preserved in the
    WALS source data. -/
private def fromWALS109B : Datasets.WALS.F109B.AppliedObjectRole → Option AppliedObjectRole
  | .instrument            => some .nonbenefactiveOnly
  | .locative              => some .nonbenefactiveOnly
  | .instrumentAndLocative => some .nonbenefactiveOnly
  | .onlyBenefactive       => some .benefactiveOnly
  | .noApplicative         => none

theorem f109b_count_instrument :
    (f109b.filter (·.value == .instrument)).length = 17 := by native_decide
theorem f109b_count_locative :
    (f109b.filter (·.value == .locative)).length = 18 := by native_decide
theorem f109b_count_instrumentAndLocative :
    (f109b.filter (·.value == .instrumentAndLocative)).length = 12 := by native_decide
theorem f109b_count_onlyBenefactive :
    (f109b.filter (·.value == .onlyBenefactive)).length = 36 := by native_decide
theorem f109b_count_noApplicative :
    (f109b.filter (·.value == .noApplicative)).length = 100 := by native_decide

-- ============================================================================
-- Language Profiles
-- ============================================================================

/-- A cross-linguistic valence/voice profile for a single language.

    Covers WALS Ch 106--109 directly, plus Ch 111 causative morphology for
    the applicative-causative correlation. Ch 110 (periphrastic causatives)
    is omitted from profiles since most WALS sources do not report it. -/
structure ValenceProfile where
  language : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Ch 106: Reciprocal construction type -/
  reciprocal : ReciprocalType
  /-- Ch 107: Passive presence -/
  passive : PassivePresence
  /-- Ch 108: Antipassive type -/
  antipassive : AntipassiveType
  /-- Ch 108: Morphological alignment (relevant for antipassive correlation) -/
  alignment : AlignmentType
  /-- Ch 109: Applicative type -/
  applicative : ApplicativeType
  /-- Ch 111: Nonperiphrastic causative type -/
  causative : NonperiphrCausativeType
  deriving Repr, DecidableEq

-- ============================================================================
-- Language Data
-- ============================================================================

/-- English: reciprocal distinct from reflexive ("each other" vs "themselves"),
    periphrastic passive ("was kicked"), no antipassive (accusative alignment),
    no applicative, no productive morphological causative
    (lexical causatives like "kill" only). -/
def english : ValenceProfile :=
  { language := "English"
  , iso := "eng"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Japanese: reciprocal distinct from reflexive ("otagai" vs "jibun"),
    passive ("-(r)are-"), no antipassive, no applicative,
    morphological causative suffix "-(s)ase". -/
def japanese : ValenceProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Turkish: reciprocal distinct from reflexive — "birbirine" (reciprocal)
    is formally distinct from "kendi" (reflexive). WALS Ch 106 codes Turkish
    as Value 2 (distinct from reflexive).
    Passive ("-Il"), no antipassive (accusative), no applicative,
    morphological causative "-dUr". -/
def turkish : ValenceProfile :=
  { language := "Turkish"
  , iso := "tur"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Swahili: reciprocal distinct ("-ana"), passive ("-w-"),
    no antipassive, applicative ("-i-" / "-e-" benefactive + locative
    from both bases), morphological causative ("-ish-" / "-esh-").

    `iso = "swh"` (Standard Swahili individual code) matches WALS;
    "swa" is the macrolanguage code, which WALS does not use. -/
def swahili : ValenceProfile :=
  { language := "Swahili"
  , iso := "swh"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .applicative .bothBases .benefactiveAndOther
  , causative := .morphologicalOnly }

/-- Dyirbal (Pama-Nyungan, Australia): reciprocal distinct from reflexive.
    Reflexive: stem + *-riy* (@cite{dixon-1972} §4.8.1).
    Reciprocal: reduplicated stem + *-(n)bariy* (@cite{dixon-1972} §4.8.2).
    The reciprocal "functions like an intransitive stem" (monovalent).
    No passive, dedicated antipassive with oblique patient,
    ergative alignment, no applicative, morphological causative.
    NOTE: Dyirbal is NOT in WALS Ch 106 sample (175 languages). -/
def dyirbal : ValenceProfile :=
  { language := "Dyirbal"
  , iso := "dbl"
  , reciprocal := .distinctFromReflexive
  , passive := .absent
  , antipassive := .obliquePatient
  , alignment := .ergative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Chukchi (Chukotko-Kamchatkan, Russia): reciprocal distinct,
    no passive (inverse system instead), dedicated antipassive "ine-"
    with oblique patient (instrumental), ergative alignment,
    no applicative, morphological causative. -/
def chukchi : ValenceProfile :=
  { language := "Chukchi"
  , iso := "ckt"
  , reciprocal := .distinctFromReflexive
  , passive := .absent
  , antipassive := .obliquePatient
  , alignment := .ergative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Indonesian: reciprocal distinct from reflexive — "saling" (reciprocal)
    is formally different from "diri sendiri" (reflexive). WALS Ch 106
    codes Indonesian as Value 2 (distinct from reflexive).
    Passive ("di-"), no antipassive, no applicative,
    morphological causative. -/
def indonesian : ValenceProfile :=
  { language := "Indonesian"
  , iso := "ind"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- French: mixed reciprocal type — both reflexive-identical "se" and
    distinct "l'un l'autre" ('each other'). WALS Ch 106 codes French as
    Value 3 (mixed).
    Periphrastic passive ("être + past participle"), no antipassive,
    no applicative.

    Nonperiphrastic causative (Ch 111): WALS codes French as `.both`.
    The periphrastic *faire + INF* construction is Ch 110 (periphrastic
    causatives), excluded from Ch 111 by definition; the previous value
    `.compoundOnly` here appears to have arisen from misclassifying
    *faire + INF* as compound. -/
def french : ValenceProfile :=
  { language := "French"
  , iso := "fra"
  , reciprocal := .mixed
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .both }

/-- Russian: mixed reciprocal type — both reflexive-identical "-sja"/"-s'"
    and distinct "drug druga" ('each other'). WALS Ch 106 codes Russian as
    Value 3 (mixed), parallel to German ("sich" + "einander").
    Passive (synthetic "-sja" + periphrastic), no antipassive,
    no applicative, morphological causative (zero-derivation, e.g.
    "lomat'-sja" anticausative). -/
def russian : ValenceProfile :=
  { language := "Russian"
  , iso := "rus"
  , reciprocal := .mixed
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Arabic (Modern Standard): reciprocal via Form VI (*tafaaʿal-a*),
    formally distinct from Form V reflexive (*tafaʿʿal-a*):
    Form VI inserts long *-aa-* after the first root consonant,
    Form V doubles the medial consonant (@cite{ryding-2005} Ch 27 §1).
    Example: *taʿaanaq-a* 'to embrace one another' (Form VI, reciprocal)
    vs. *takallam-a* 'to speak' (Form V, reflexive/mediopassive).
    Passive via internal vowel change (*kutiba*), no antipassive,
    no applicative, morphological causative (Form IV *ʾafʿala*).
    NOTE: MSA is NOT in WALS Ch 106 sample; Arabic (Egyptian) is
    listed as Value 2 (distinct from reflexive). -/
def arabic : ValenceProfile :=
  { language := "Arabic"
  , iso := "arb"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Hindi: reciprocal distinct ("ek duusre"),
    passive ("-aa" / "jaanaa" periphrastic), no antipassive,
    no applicative, morphological causative ("-aa" / "-vaa"). -/
def hindi : ValenceProfile :=
  { language := "Hindi"
  , iso := "hin"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- West Greenlandic (Eskimo-Aleut): reciprocal-reflexive polysemy
    ("immi-" for both), passive, antipassive with oblique patient,
    ergative alignment, no applicative, morphological causative. -/
def westGreenlandic : ValenceProfile :=
  { language := "West Greenlandic"
  , iso := "kal"
  , reciprocal := .identicalToReflexive
  , passive := .present
  , antipassive := .obliquePatient
  , alignment := .ergative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Kinyarwanda (Bantu, Rwanda): reciprocal suffix *-an-*
    (e.g., *-saban-* 'ask each other'), formally distinct from
    reflexive prefix *-ii-*/*-iiy-* (e.g., *á-r-íi-reeb-a*
    'she watches herself') (@cite{kimenyi-1980} §4.2.1, p. 5).
    Passive *-w-*, no antipassive, applicative *-ir-*/*-er-*
    (benefactive + other from both bases), morphological causative.
    NOTE: Kinyarwanda is NOT in WALS Ch 106 sample. -/
def kinyarwanda : ValenceProfile :=
  { language := "Kinyarwanda"
  , iso := "kin"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .applicative .bothBases .benefactiveAndOther
  , causative := .morphologicalOnly }

/-- Lango (Nilotic, Uganda): reciprocal identical to reflexive.
    WALS Ch 106 codes Lango as Value 4 (identical to reflexive).
    Passive absent, antipassive with implicit patient (per WALS Ch 108
    coding — accusative alignment, one of the accusative-language
    antipassives), no applicative, morphological causative. -/
def lango : ValenceProfile :=
  { language := "Lango"
  , iso := "laj"
  , reciprocal := .identicalToReflexive
  , passive := .absent
  , antipassive := .implicitPatient
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Chamorro (Austronesian, Guam): reciprocal distinct,
    passive present, antipassive with oblique patient
    (accusative alignment), applicative (benefactive + other,
    both bases), morphological causative. -/
def chamorro : ValenceProfile :=
  { language := "Chamorro"
  , iso := "cha"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .obliquePatient
  , alignment := .accusative
  , applicative := .applicative .bothBases .benefactiveAndOther
  , causative := .morphologicalOnly }

/-- Halkomelem (Salishan, Canada): reciprocal suffix *-təl*
    (e.g., *ʔiyá·təl* 'fight', *yéyətəl* 'make friends'),
    formally distinct from reflexive suffixes *-lá·mət* 'oneself'
    and *-(ə)θət* 'oneself, itself' (@cite{galloway-1993} §6.1.3,
    §11.2.1.14–15). Passive present, antipassive with oblique patient,
    ergative alignment, applicative (benefactive + other,
    both bases), morphological causative.
    NOTE: Halkomelem is NOT in WALS Ch 106 sample. -/
def halkomelem : ValenceProfile :=
  { language := "Halkomelem"
  , iso := "hur"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .obliquePatient
  , alignment := .ergative
  , applicative := .applicative .bothBases .benefactiveAndOther
  , causative := .morphologicalOnly }

/-- Modern Greek: mixed reciprocal type — both nonactive voice morphology
    (identical to reflexive) and distinct reciprocal constructions.
    WALS Ch 106 codes Modern Greek as Value 3 (mixed).
    Passive present ("periphrastic with nonactive morphology"),
    no antipassive, no applicative, NEITHER morphological
    nor compound causative (relies on periphrastic causative). -/
def modernGreek : ValenceProfile :=
  { language := "Modern Greek"
  , iso := "ell"
  , reciprocal := .mixed
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .neither }

/-- German: mixed reciprocal type ("sich" reflexive/reciprocal + "einander"
    distinct reciprocal), passive (werden + participle), no antipassive,
    no applicative, morphological causative (zero-derivation). -/
def german : ValenceProfile :=
  { language := "German"
  , iso := "deu"
  , reciprocal := .mixed
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

/-- Finnish: reciprocal distinct from reflexive ("toisiaan" ≠ "itsensä"),
    impersonal "passive" (present — the Fragment's `finnishPassive` has
    semantic content but does not project a syntactic agent), no antipassive,
    accusative alignment, no applicative, morphological causative
    *-tta-* / *-ttä-*. -/
def finnish : ValenceProfile :=
  { language := "Finnish"
  , iso := "fin"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .morphologicalOnly }

def allProfiles : List ValenceProfile :=
  [ english, japanese, turkish, swahili, dyirbal, chukchi, indonesian
  , french, russian, arabic, hindi, westGreenlandic, kinyarwanda
  , lango, chamorro, halkomelem, modernGreek, german, finnish ]

-- ============================================================================
-- Per-Profile Verification
-- ============================================================================

-- Spot-check a selection of profiles to ensure data consistency
example : english.passive = .present := by native_decide
example : english.antipassive = .noAntipassive := by native_decide
example : english.applicative = .noApplicative := by native_decide

example : dyirbal.antipassive = .obliquePatient := by native_decide
example : dyirbal.alignment = .ergative := by native_decide
example : dyirbal.passive = .absent := by native_decide

example : chukchi.antipassive = .obliquePatient := by native_decide
example : chukchi.alignment = .ergative := by native_decide

example : swahili.applicative.hasApplicative = true := by native_decide
example : kinyarwanda.applicative.hasApplicative = true := by native_decide

example : french.causative = .both := by native_decide
example : modernGreek.causative = .neither := by native_decide

example : finnish.passive = .present := by native_decide
example : finnish.causative = .morphologicalOnly := by native_decide

-- ============================================================================
-- WALS Grounding: Profile reciprocal types match generated WALS data
-- ============================================================================

/-- Helper: convert WALS 106A value to our ReciprocalType. Public so that
    `Studies/Nordlinger2023.lean` can reuse it for `RecipProfile` grounding. -/
def fromWALS106A : Datasets.WALS.F106A.ReciprocalType → ReciprocalType
  | .noReciprocalConstruction => .noDedicated
  | .distinctFromReflexive    => .distinctFromReflexive
  | .mixed                    => .mixed
  | .identicalToReflexive     => .identicalToReflexive

/-- For each profile whose language IS in WALS Ch 106, prove its reciprocal
    type matches the WALS data. This eliminates transcription errors by
    construction: if the profile disagrees with WALS, the theorem fails. -/

theorem english_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO english.iso).map (fromWALS106A ·.value) = some english.reciprocal := by
  native_decide
theorem japanese_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO japanese.iso).map (fromWALS106A ·.value) = some japanese.reciprocal := by
  native_decide
theorem turkish_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO turkish.iso).map (fromWALS106A ·.value) = some turkish.reciprocal := by
  native_decide
theorem swahili_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO swahili.iso).map (fromWALS106A ·.value) = some swahili.reciprocal := by
  native_decide
theorem chukchi_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO chukchi.iso).map (fromWALS106A ·.value) = some chukchi.reciprocal := by
  native_decide
theorem indonesian_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO indonesian.iso).map (fromWALS106A ·.value) = some indonesian.reciprocal := by
  native_decide
theorem french_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO french.iso).map (fromWALS106A ·.value) = some french.reciprocal := by
  native_decide
theorem russian_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO russian.iso).map (fromWALS106A ·.value) = some russian.reciprocal := by
  native_decide
theorem hindi_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO hindi.iso).map (fromWALS106A ·.value) = some hindi.reciprocal := by
  native_decide
theorem westGreenlandic_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO westGreenlandic.iso).map (fromWALS106A ·.value) = some westGreenlandic.reciprocal := by
  native_decide
theorem lango_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO lango.iso).map (fromWALS106A ·.value) = some lango.reciprocal := by
  native_decide
theorem chamorro_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO chamorro.iso).map (fromWALS106A ·.value) = some chamorro.reciprocal := by
  native_decide
theorem modernGreek_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO modernGreek.iso).map (fromWALS106A ·.value) = some modernGreek.reciprocal := by
  native_decide
theorem german_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO german.iso).map (fromWALS106A ·.value) = some german.reciprocal := by
  native_decide
theorem finnish_reciprocal_wals :
    (Datasets.WALS.F106A.lookupISO finnish.iso).map (fromWALS106A ·.value) = some finnish.reciprocal := by
  native_decide

-- ============================================================================
-- WALS Grounding: F105A Ditransitive Constructions
-- ============================================================================

/-- Per-language grounding: WALS 105A ditransitive type for profile languages.
    Every profile language appears in the 378-language F105A dataset. -/

theorem english_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO english.iso).map (fromWALS105A ·.value) = some DitransitiveType.mixed := by
  native_decide
theorem japanese_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO japanese.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide
theorem turkish_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO turkish.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide
theorem swahili_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO swahili.iso).map (fromWALS105A ·.value) = some DitransitiveType.doubleObject := by
  native_decide
theorem dyirbal_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO dyirbal.iso).map (fromWALS105A ·.value) = some DitransitiveType.mixed := by
  native_decide
theorem chukchi_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO chukchi.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide
theorem indonesian_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO indonesian.iso).map (fromWALS105A ·.value) = some DitransitiveType.mixed := by
  native_decide
theorem french_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO french.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide
theorem russian_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO russian.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide
theorem hindi_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO hindi.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide
theorem westGreenlandic_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO westGreenlandic.iso).map (fromWALS105A ·.value) = some DitransitiveType.secondaryObject := by
  native_decide
theorem kinyarwanda_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO kinyarwanda.iso).map (fromWALS105A ·.value) = some DitransitiveType.doubleObject := by
  native_decide
theorem lango_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO lango.iso).map (fromWALS105A ·.value) = some DitransitiveType.mixed := by
  native_decide
theorem chamorro_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO chamorro.iso).map (fromWALS105A ·.value) = some DitransitiveType.secondaryObject := by
  native_decide
theorem halkomelem_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO halkomelem.iso).map (fromWALS105A ·.value) = some DitransitiveType.secondaryObject := by
  native_decide
theorem modernGreek_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO modernGreek.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide
theorem german_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO german.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide
theorem finnish_ditransitive_wals :
    (Datasets.WALS.F105A.lookupISO finnish.iso).map (fromWALS105A ·.value) = some DitransitiveType.indirectObject := by
  native_decide

-- ============================================================================
-- WALS Grounding: F109A Applicative Type
-- ============================================================================

/-- Per-language grounding: profile applicative types that match WALS 109A.
    Languages whose profiles disagree with WALS (Dyirbal, Indonesian,
    West Greenlandic, Lango, Chamorro) are omitted -- their profile values
    are based on other sources or use a different classification. -/

theorem english_applicative_wals :
    (Datasets.WALS.F109A.lookupISO english.iso).map (fromWALS109A ·.value) = some english.applicative := by
  native_decide
theorem japanese_applicative_wals :
    (Datasets.WALS.F109A.lookupISO japanese.iso).map (fromWALS109A ·.value) = some japanese.applicative := by
  native_decide
theorem turkish_applicative_wals :
    (Datasets.WALS.F109A.lookupISO turkish.iso).map (fromWALS109A ·.value) = some turkish.applicative := by
  native_decide
theorem swahili_applicative_wals :
    (Datasets.WALS.F109A.lookupISO swahili.iso).map (fromWALS109A ·.value) = some swahili.applicative := by
  native_decide
theorem chukchi_applicative_wals :
    (Datasets.WALS.F109A.lookupISO chukchi.iso).map (fromWALS109A ·.value) = some chukchi.applicative := by
  native_decide
theorem french_applicative_wals :
    (Datasets.WALS.F109A.lookupISO french.iso).map (fromWALS109A ·.value) = some french.applicative := by
  native_decide
theorem russian_applicative_wals :
    (Datasets.WALS.F109A.lookupISO russian.iso).map (fromWALS109A ·.value) = some russian.applicative := by
  native_decide
theorem hindi_applicative_wals :
    (Datasets.WALS.F109A.lookupISO hindi.iso).map (fromWALS109A ·.value) = some hindi.applicative := by
  native_decide
theorem halkomelem_applicative_wals :
    (Datasets.WALS.F109A.lookupISO halkomelem.iso).map (fromWALS109A ·.value) = some halkomelem.applicative := by
  native_decide
theorem modernGreek_applicative_wals :
    (Datasets.WALS.F109A.lookupISO modernGreek.iso).map (fromWALS109A ·.value) = some modernGreek.applicative := by
  native_decide
theorem german_applicative_wals :
    (Datasets.WALS.F109A.lookupISO german.iso).map (fromWALS109A ·.value) = some german.applicative := by
  native_decide
theorem finnish_applicative_wals :
    (Datasets.WALS.F109A.lookupISO finnish.iso).map (fromWALS109A ·.value) = some finnish.applicative := by
  native_decide

-- ============================================================================
-- WALS Grounding: F109B Applied Object Roles
-- ============================================================================

/-- Per-language grounding: WALS 109B applied-object roles for profile
    languages without applicatives. For these languages, F109B records
    `.noApplicative`, and our converter returns `none`. -/

theorem english_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO english.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem japanese_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO japanese.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem turkish_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO turkish.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem chukchi_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO chukchi.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem french_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO french.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem russian_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO russian.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem hindi_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO hindi.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem modernGreek_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO modernGreek.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem german_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO german.iso).map (fromWALS109B ·.value) = some none := by
  native_decide
theorem finnish_appliedRole_wals :
    (Datasets.WALS.F109B.lookupISO finnish.iso).map (fromWALS109B ·.value) = some none := by
  native_decide

-- ============================================================================
-- WALS Grounding: F108A Antipassive Type (per-language)
-- ============================================================================

/-- Convert WALS 108A value to our AntipassiveType. -/
private def fromWALS108A : Datasets.WALS.F108A.AntipassiveType → AntipassiveType
  | .implicitPatient => .implicitPatient
  | .obliquePatient  => .obliquePatient
  | .noAntipassive   => .noAntipassive

/-- Lango: WALS Ch 108 codes Lango as `.implicitPatient` (the patient-like
    argument is left unexpressed). This grounding theorem ties the profile
    field to the WALS dataset by ISO code, so future drift in either
    direction is caught at typecheck. -/
theorem lango_antipassive_wals :
    (Datasets.WALS.F108A.lookupISO lango.iso).map (fromWALS108A ·.value)
      = some lango.antipassive := by native_decide

-- ============================================================================
-- WALS Grounding: F111A Nonperiphrastic Causative (per-language)
-- ============================================================================

/-- Convert WALS 111A value to our NonperiphrCausativeType. -/
private def fromWALS111A : Datasets.WALS.F111A.NonperiphrCausativeType → NonperiphrCausativeType
  | .neither           => .neither
  | .morphologicalOnly => .morphologicalOnly
  | .compoundOnly      => .compoundOnly
  | .both              => .both

/-- French: WALS Ch 111 codes French as `.both` (morphological + compound
    causatives). The `faire + INF` periphrastic causative is Ch 110, not
    Ch 111, so it is excluded from this classification. -/
theorem french_causative_wals :
    (Datasets.WALS.F111A.lookupISO french.iso).map (fromWALS111A ·.value)
      = some french.causative := by native_decide

/-- Finnish impersonal "passive" has semantic content (existential closure
    over agent) — derived from the Fragment's voice head. -/
theorem finnish_passive_has_semantics :
    Fragments.Finnish.Predicates.finnishPassive.hasSemantics = true := rfl

/-- Finnish impersonal "passive" does NOT project a syntactic agent —
    derived from the Fragment's voice head. -/
theorem finnish_passive_no_agent :
    Fragments.Finnish.Predicates.finnishPassive.assignsTheta = false := rfl

-- ============================================================================
-- Generalization 1: Passives are common (44% of WALS sample)
-- ============================================================================

/-- WALS Ch 107: 162 out of 373 languages have passives (43.4%).
    Although a minority, passives are widespread enough that most
    language families include at least some passive-bearing members. -/
theorem passives_substantial_minority :
    let present := (Datasets.WALS.F107A.allData.filter (·.value == .present)).length
    let total := Datasets.WALS.F107A.allData.length
    -- More than a third of languages have passives
    present * 3 > total := by native_decide

/-- In our sample, most languages have a passive. -/
def ValenceProfile.hasPassive (p : ValenceProfile) : Bool :=
  p.passive == .present

theorem majority_of_sample_has_passive :
    let withPassive := allProfiles.filter (·.hasPassive)
    -- At least 14 of 18 profiles have passives
    withPassive.length >= 14 := by native_decide

-- ============================================================================
-- Generalization 2: Antipassives are associated with ergative alignment
-- ============================================================================

/-- In the WALS Ch 108 data, antipassives occur in both accusative and
    ergative languages, but the correlation with ergativity is strong.
    @cite{polinsky-2013-antipassive}: more languages have oblique-patient antipassives
    than implicit-patient antipassives, and the majority have no antipassive. -/
theorem antipassive_distribution :
    let oblique := (Datasets.WALS.F108A.allData.filter (·.value == .obliquePatient)).length
    let implicit := (Datasets.WALS.F108A.allData.filter (·.value == .implicitPatient)).length
    let none_ := (Datasets.WALS.F108A.allData.filter (·.value == .noAntipassive)).length
    oblique > implicit ∧ none_ > oblique + implicit := by native_decide

/-- In our sample: every ergative language has an antipassive,
    but not all accusative languages do. -/
theorem ergative_implies_antipassive_in_sample :
    let ergatives := allProfiles.filter fun p => p.alignment == .ergative
    ergatives.all fun p => p.antipassive.hasAntipassive := by native_decide

/-- In our sample: most accusative languages lack an antipassive. -/
theorem most_accusative_lack_antipassive :
    let accusatives := allProfiles.filter fun p => p.alignment == .accusative
    let withoutAP := accusatives.filter fun p => !p.antipassive.hasAntipassive
    -- More accusative languages lack antipassives than have them
    withoutAP.length > (accusatives.length - withoutAP.length) := by native_decide

-- ============================================================================
-- Generalization 3: Morphological causatives dominate cross-linguistically
-- ============================================================================

/-- WALS Ch 111: The morphological causative type is found in 278 out of
    310 languages (254 morphological-only + 24 both), i.e. ~90%.
    Only 23 languages use neither morphological nor compound causatives.
    This dwarfs periphrastic causatives in frequency. -/
theorem morphological_causative_dominant :
    let morphOnly := (Datasets.WALS.F111A.allData.filter (·.value == .morphologicalOnly)).length
    let both := (Datasets.WALS.F111A.allData.filter (·.value == .both)).length
    let total := Datasets.WALS.F111A.allData.length
    -- Morphological causatives in >80% of languages
    (morphOnly + both) * 10 > total * 8 := by native_decide

/-- In our sample, every language but Modern Greek has at least a
    morphological or compound causative (Modern Greek has neither —
    only periphrastic). -/
theorem almost_all_have_nonperiphr_causative :
    let withNonperiphr := allProfiles.filter fun p =>
      p.causative != .neither
    withNonperiphr.length >= 16 := by native_decide

-- ============================================================================
-- Generalization 4: Applicatives co-occur with morphological causatives
-- ============================================================================

/-- WALS Ch 109 observes that "The main generalization seems to be that
    applicatives are commonly found in those languages that have little
    or no case marking of noun phrases and that have sufficiently rich
    verbal morphology." Since morphological causatives also require rich
    verbal morphology, we expect a correlation.

    In our sample: every language with an applicative also has a
    morphological causative. -/
theorem applicative_implies_morph_causative :
    let withApplicative := allProfiles.filter fun p =>
      p.applicative.hasApplicative
    withApplicative.all fun p => p.causative.hasMorphological := by native_decide

-- ============================================================================
-- Generalization 5: Suffixing dominates in morphological causatives
-- ============================================================================

/-- WALS Ch 111: Among languages with morphological causatives, suffixation
    is by far the most common pattern. @cite{song-2013-nonperiphrastic} lists examples:
    Japanese "-(s)ase", Turkish "-dUr", Swahili "-ish-" / "-esh-".
    Prefixes (Abkhaz "r-"), infixes (Lepcha "-y-"), and circumfixes
    (Georgian "a-...-ineb") exist but are rare. This parallels Greenberg's
    Universal 27: suffixing is generally preferred over prefixing. -/
structure CausativeMorphologyExample where
  language : String
  morpheme : String
  position : String  -- "suffix", "prefix", "infix", "circumfix"
  deriving Repr, DecidableEq

def causativeMorphExamples : List CausativeMorphologyExample :=
  [ { language := "Japanese",   morpheme := "-(s)ase",       position := "suffix" }
  , { language := "Turkish",    morpheme := "-dUr",          position := "suffix" }
  , { language := "Swahili",    morpheme := "-ish-/-esh-",   position := "suffix" }
  , { language := "Hindi",      morpheme := "-aa/-vaa",      position := "suffix" }
  , { language := "Korean",     morpheme := "-i/-hi/-li/-ki", position := "suffix" }
  , { language := "Finnish",    morpheme := "-tta-/-ttä-",   position := "suffix" }
  , { language := "Hungarian",  morpheme := "-tat-/-tet-",   position := "suffix" }
  , { language := "Abkhaz",     morpheme := "r-",            position := "prefix" }
  , { language := "Lepcha",     morpheme := "-y-",           position := "infix" }
  , { language := "Georgian",   morpheme := "a-...-ineb",    position := "circumfix" } ]

/-- Suffixing dominates: most morphological causative examples are suffixes. -/
theorem suffixing_dominates_causatives :
    let suffixes := causativeMorphExamples.filter fun e => e.position == "suffix"
    let nonSuffixes := causativeMorphExamples.filter fun e => e.position != "suffix"
    suffixes.length > nonSuffixes.length * 2 := by native_decide

-- ============================================================================
-- Reciprocal typology: Eurasian patterns
-- ============================================================================

/-- WALS Ch 106 notes a clear areal pattern: Value 1 (no non-iconic
    reciprocal constructions) is concentrated in Oceania, Southeast Asia,
    and parts of Africa. Every Eurasian language in the sample has at
    least one productive grammatical reciprocal construction (Value 2, 3,
    or 4). -/
def isEurasian (p : ValenceProfile) : Bool :=
  p.iso == "eng" || p.iso == "deu" || p.iso == "fra" || p.iso == "rus" ||
  p.iso == "ell" || p.iso == "tur" || p.iso == "hin" || p.iso == "jpn" ||
  p.iso == "arb"

/-- Every Eurasian language in our sample has a productive grammatical
    reciprocal construction (i.e., none are Value 1). -/
theorem eurasian_all_have_productive_reciprocal :
    let eurasians := allProfiles.filter isEurasian
    eurasians.all fun p => p.reciprocal != .noDedicated := by native_decide

-- ============================================================================
-- Cross-Chapter Correlations
-- ============================================================================

/-- Languages without passives tend to have other detransitivizing
    strategies. In our sample, both passive-absent languages with
    ergative alignment have antipassives. -/
theorem no_passive_ergative_has_antipassive :
    let noPassiveErgative := allProfiles.filter fun p =>
      p.passive == .absent && p.alignment == .ergative
    noPassiveErgative.all fun p => p.antipassive.hasAntipassive := by native_decide

/-- Applicatives and antipassives are dual voice operations: applicatives
    increase valence (adding an applied object), antipassives decrease it
    (demoting the patient). Some languages have both -- in our sample,
    Chamorro and Halkomelem combine applicatives with antipassives,
    demonstrating that a single language can productively use both
    valence-increasing and valence-decreasing operations. -/
theorem some_languages_have_both_app_and_antipass :
    (allProfiles.filter fun p =>
      p.applicative.hasApplicative && p.antipassive.hasAntipassive).length = 2 := by
  native_decide

-- ============================================================================
-- Antipassive Alignment Data (from @cite{polinsky-2013-antipassive}, Table 1)
-- ============================================================================

/-- Languages with antipassives classified by alignment, from WALS Ch 108
    Table 1. This is the key empirical evidence for the antipassive-ergativity
    debate (@cite{silverstein-1976}). -/
structure AntipassiveAlignmentDatum where
  language : String
  alignment : AlignmentType
  deriving Repr, DecidableEq

/-- Accusative languages with antipassives (17 in WALS Table 1).
    These are the key counterexamples to the strong claim that
    antipassives are limited to ergative languages. -/
def accusativeAntipassiveLangs : List AntipassiveAlignmentDatum :=
  [ { language := "Acoma",           alignment := .accusative }
  , { language := "Cahuilla",        alignment := .accusative }
  , { language := "Canela-Kraho",    alignment := .accusative }
  , { language := "Chamorro",        alignment := .accusative }
  , { language := "Choctaw",         alignment := .accusative }
  , { language := "Comanche",        alignment := .accusative }
  , { language := "Cree",            alignment := .accusative }
  , { language := "Kiowa",           alignment := .accusative }
  , { language := "Koyraboro Senni", alignment := .accusative }
  , { language := "Krongo",          alignment := .accusative }
  , { language := "Lango",           alignment := .accusative }
  , { language := "Lavukaleve",      alignment := .accusative }
  , { language := "Nez Perce",       alignment := .accusative }
  , { language := "Ojibwa",          alignment := .accusative }
  , { language := "Paiwan",          alignment := .accusative }
  , { language := "Sanuma",          alignment := .accusative }
  , { language := "Thompson",        alignment := .accusative } ]

/-- Ergative languages with antipassives (30 in WALS Table 1). -/
def ergativeAntipassiveLangs : List AntipassiveAlignmentDatum :=
  [ { language := "Archi",           alignment := .ergative }
  , { language := "Bezhta",          alignment := .ergative }
  , { language := "Cakchiquel",      alignment := .ergative }
  , { language := "Central Yup'ik",  alignment := .ergative }
  , { language := "Chechen",         alignment := .ergative }
  , { language := "Chukchi",         alignment := .ergative }
  , { language := "Copainala Zoque", alignment := .ergative }
  , { language := "Diyari",          alignment := .ergative }
  , { language := "Djaru",           alignment := .ergative }
  , { language := "Dyirbal",         alignment := .ergative }
  , { language := "Embaloh",         alignment := .ergative }
  , { language := "Godoberi",        alignment := .ergative }
  , { language := "Gooniyandi",      alignment := .ergative }
  , { language := "Halkomelem",      alignment := .ergative }
  , { language := "Hunzib",          alignment := .ergative }
  , { language := "Jakaltek",        alignment := .ergative }
  , { language := "Kabardian",       alignment := .ergative }
  , { language := "Kapampangan",     alignment := .ergative }
  , { language := "Lai",             alignment := .ergative }
  , { language := "Lak",             alignment := .ergative }
  , { language := "Mam",             alignment := .ergative }
  , { language := "Mangarrayi",      alignment := .ergative }
  , { language := "Pari",            alignment := .ergative }
  , { language := "Tsez",            alignment := .ergative }
  , { language := "Tzutujil",        alignment := .ergative }
  , { language := "Wardaman",        alignment := .ergative }
  , { language := "Warrungu",        alignment := .ergative }
  , { language := "West Greenlandic", alignment := .ergative }
  , { language := "Yidiny",          alignment := .ergative }
  , { language := "Yukulta",         alignment := .ergative } ]

/-- All accusative-alignment entries actually have accusative alignment. -/
theorem accusative_AP_all_accusative :
    accusativeAntipassiveLangs.all fun d => d.alignment == .accusative := by
  native_decide

/-- All ergative-alignment entries actually have ergative alignment. -/
theorem ergative_AP_all_ergative :
    ergativeAntipassiveLangs.all fun d => d.alignment == .ergative := by
  native_decide

/-- Counts match WALS Table 1. -/
theorem AP_accusative_count : accusativeAntipassiveLangs.length = 17 := by native_decide
theorem AP_ergative_count : ergativeAntipassiveLangs.length = 30 := by native_decide

/-- Ergative languages with antipassives outnumber accusative ones. -/
theorem ergative_AP_more_common :
    ergativeAntipassiveLangs.length > accusativeAntipassiveLangs.length := by
  native_decide

-- ============================================================================
-- Applicative Areal Distribution
-- ============================================================================

/-- WALS Ch 109 notes applicatives cluster in three areas: Bantu Africa,
    Western Pacific (Austronesian), and North/Meso-America (Salish, Mayan,
    Uto-Aztecan). The dearth in Eurasia correlates with rich case marking:
    languages with case can use oblique cases instead of applicatives.

    In our sample, applicatives appear only in Bantu, Austronesian, and
    Salishan languages — none of the Eurasian profiles. -/
theorem applicatives_only_in_bantu_austronesian_salishan :
    let withApplicative := allProfiles.filter fun p =>
      p.applicative.hasApplicative
    withApplicative.all fun p =>
      -- Swahili (swh), Kinyarwanda (kin) = Bantu
      -- Chamorro (cha) = Austronesian
      -- Halkomelem (hur) = Salishan
      p.iso == "swh" || p.iso == "kin" || p.iso == "cha" || p.iso == "hur" := by
  native_decide

-- ============================================================================
-- Summary Statistics for Our Sample
-- ============================================================================

/-- Count of languages with each passive value. -/
def samplePassiveCount (v : PassivePresence) : Nat :=
  (allProfiles.filter fun p => p.passive == v).length

/-- Count of languages with each antipassive value. -/
def sampleAntipassiveCount (v : AntipassiveType) : Nat :=
  (allProfiles.filter fun p => p.antipassive == v).length

/-- Count of languages with applicatives in sample. -/
def sampleApplicativeCount : Nat :=
  (allProfiles.filter fun p => p.applicative.hasApplicative).length

example : samplePassiveCount .present = 16 := by native_decide
example : samplePassiveCount .absent = 3 := by native_decide
example : sampleAntipassiveCount .obliquePatient = 5 := by native_decide
example : sampleAntipassiveCount .implicitPatient = 1 := by native_decide
example : sampleAntipassiveCount .noAntipassive = 13 := by native_decide
example : sampleApplicativeCount = 4 := by native_decide

-- ============================================================================
-- Polysemy Cross-Validation (@cite{nordlinger-2023})
-- ============================================================================

/-- @cite{nordlinger-2023} reports that of the 175 languages in
    @cite{maslova-nedjalkov-2013}'s sample, polysemous reflexive/reciprocal
    constructions are present in 60 (34%). In WALS terms, polysemy corresponds
    to Values 3 (mixed) and 4 (identical to reflexive). -/
theorem polysemy_count :
    let mixed := (Datasets.WALS.F106A.allData.filter (·.value == .mixed)).length
    let identical := (Datasets.WALS.F106A.allData.filter (·.value == .identicalToReflexive)).length
    mixed + identical = 60 := by native_decide

/-- 60 out of 175 = 34.3%. -/
theorem polysemy_percentage :
    let polysemous := (Datasets.WALS.F106A.allData.filter
        (fun d => d.value == .mixed || d.value == .identicalToReflexive)).length
    let total := Datasets.WALS.F106A.allData.length
    -- More than a third but less than half
    polysemous * 3 > total ∧ polysemous * 2 < total := by native_decide

-- ============================================================================
-- Fragment Connection: English Reciprocal-Reflexive Distinction
-- ============================================================================

open Fragments.English.Pronouns in

/-- English reciprocal forms ("each other", "one another") are formally
    distinct from reflexive forms ("themselves", etc.) — derived from
    the Fragment's pronoun entries rather than stipulated in the profile. -/
theorem english_reciprocal_distinct_from_reflexive :
    eachOther.pronounType ≠ PronounType.reflexive ∧
    oneAnother.pronounType ≠ PronounType.reflexive := by
  exact ⟨by decide, by decide⟩

end Phenomena.ArgumentStructure.Typology
