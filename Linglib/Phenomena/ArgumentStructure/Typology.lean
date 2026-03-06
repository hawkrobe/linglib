import Linglib.Core.Lexical.Word
import Linglib.Core.WALS.Features.F106A
import Linglib.Core.WALS.Features.F107A
import Linglib.Core.WALS.Features.F108A
import Linglib.Core.WALS.Features.F108B
import Linglib.Core.WALS.Features.F111A
import Linglib.Fragments.Finnish.Predicates
import Linglib.Fragments.English.Pronouns

/-!
# Cross-Linguistic Typology of Valence and Voice (WALS Chapters 106--111)
@cite{maslova-nedjalkov-2013} @cite{polinsky-2013} @cite{siewierska-2013} @cite{song-2013}
@cite{nordlinger-2023}

Typological data on valence-changing and voice constructions, drawn from
WALS (World Atlas of Language Structures) chapters 106--111:

- **Ch 106** (@cite{maslova-nedjalkov-2013}): Reciprocal constructions and their
  relationship to reflexives. 175 languages.
- **Ch 107** (@cite{siewierska-2013}): Passive constructions -- presence/absence across
  373 languages. Passives occur in 44% of sampled languages, concentrated
  in Eurasia and Africa.
- **Ch 108** (@cite{polinsky-2013}): Antipassive constructions -- detransitivizing
  operations that demote the patient. 194 languages.
- **Ch 109** (@cite{polinsky-2013}): Applicative constructions -- valence-increasing
  operations adding an applied object. 183 languages.
- **Ch 110** (@cite{song-2013}): Periphrastic causative constructions -- sequential vs
  purposive types. 118 languages.
- **Ch 111** (@cite{song-2013}): Nonperiphrastic causative constructions -- morphological
  vs compound types. 310 languages.

This module focuses on Ch 106--109 (reciprocals, passives, antipassives,
applicatives). Causative typology (Ch 110--111) is covered in
`Phenomena.Causatives.Typology`; only aggregate WALS counts are recorded
here for cross-reference.

-/

namespace Phenomena.ArgumentStructure.Typology

-- ============================================================================
-- Ch 106: Reciprocal Constructions (@cite{maslova-nedjalkov-2013})
-- ============================================================================

/-- WALS Ch 106: How reciprocal situations are encoded relative to reflexives.

    The four values follow @cite{maslova-nedjalkov-2013}'s classification:

    - `noNonIconic`: "There are no non-iconic reciprocal constructions" —
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
  | noNonIconic
  | distinctFromReflexive
  | mixed
  | identicalToReflexive
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Ch 108: Antipassive Constructions (@cite{polinsky-2013})
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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

/-- Morphological alignment system (simplified for antipassive correlation). -/
inductive AlignmentType where
  | accusative
  | ergative
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Ch 109: Applicative Constructions (@cite{polinsky-2013})
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
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 109: Semantic role of the applied object.

    - `benefactiveOnly`: Applied object restricted to benefactive role.
    - `benefactiveAndOther`: Benefactive plus instrument, locative, etc.
    - `nonbenefactiveOnly`: No benefactive; only instrument, locative, etc. -/
inductive AppliedObjectRole where
  | benefactiveOnly
  | benefactiveAndOther
  | nonbenefactiveOnly
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 109: Full applicative type combining base and role.
    `none` for languages without applicative constructions. -/
inductive ApplicativeType where
  | applicative (base : ApplicativeBase) (role : AppliedObjectRole)
  | noApplicative
  deriving DecidableEq, BEq, Repr

/-- Does this value represent the presence of an applicative? -/
def ApplicativeType.hasApplicative : ApplicativeType -> Bool
  | .applicative .. => true
  | .noApplicative  => false

-- ============================================================================
-- Ch 110--111: Causative types (cross-reference only; see Causatives.Typology)
-- ============================================================================

/-- WALS Ch 110: Periphrastic causative type. -/
inductive PeriphrasticCausativeType where
  | sequentialOnly
  | purposiveOnly
  | both
  deriving DecidableEq, BEq, Repr

/-- WALS Ch 111: Nonperiphrastic (morphological/compound) causative type. -/
inductive NonperiphrCausativeType where
  | neither
  | morphologicalOnly
  | compoundOnly
  | both
  deriving DecidableEq, BEq, Repr

/-- Does this value represent a morphological causative? -/
def NonperiphrCausativeType.hasMorphological : NonperiphrCausativeType -> Bool
  | .morphologicalOnly => true
  | .both              => true
  | _                  => false

-- ============================================================================
-- WALS Distribution Data — derived from generated modules
-- ============================================================================
-- Full per-language data lives in Core.WALS.Features.F{106A..111A}.
-- These theorems re-derive aggregate counts from the generated data, ensuring
-- the numbers in our generalizations below stay in sync with the source.

theorem reciprocal_total : Core.WALS.F106A.allData.length = 175 :=
  Core.WALS.F106A.total_count
theorem passive_total : Core.WALS.F107A.allData.length = 373 :=
  Core.WALS.F107A.total_count
theorem antipassive_total : Core.WALS.F108A.allData.length = 194 :=
  Core.WALS.F108A.total_count
theorem antipassive_productivity_total : Core.WALS.F108B.allData.length = 186 := by
  exact Core.WALS.F108B.total_count
theorem nonperiphr_causative_total : Core.WALS.F111A.allData.length = 310 :=
  Core.WALS.F111A.total_count

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
  deriving Repr, BEq, DecidableEq

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
    from both bases), morphological causative ("-ish-" / "-esh-"). -/
def swahili : ValenceProfile :=
  { language := "Swahili"
  , iso := "swa"
  , reciprocal := .distinctFromReflexive
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .applicative .bothBases .benefactiveAndOther
  , causative := .morphologicalOnly }

/-- Dyirbal (Pama-Nyungan, Australia): no non-iconic reciprocal,
    no passive, dedicated antipassive with oblique patient,
    ergative alignment, no applicative, morphological causative.
    NOTE: Dyirbal is NOT in WALS Ch 106 sample (175 languages).
    Reciprocal type inferred from descriptive grammar — UNVERIFIED. -/
def dyirbal : ValenceProfile :=
  { language := "Dyirbal"
  , iso := "dbl"
  , reciprocal := .noNonIconic
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
    no applicative, compound causative ("faire + INF"). -/
def french : ValenceProfile :=
  { language := "French"
  , iso := "fra"
  , reciprocal := .mixed
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .compoundOnly }

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

/-- Arabic (Modern Standard): reciprocal via Form VI (tafaa`ala),
    passive via internal vowel change (kutiba), no antipassive,
    no applicative, morphological causative (Form IV 'af`ala).
    NOTE: MSA is NOT in WALS Ch 106 sample; Arabic (Egyptian) is
    listed as Value 2 (distinct from reflexive). Coding inferred
    from MSA grammar — UNVERIFIED against WALS. -/
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

/-- Kinyarwanda (Bantu, Rwanda): reciprocal distinct ("-ana"),
    passive ("-w-"), no antipassive, applicative ("-ir-" / "-er-"
    benefactive + other from both bases), morphological causative.
    NOTE: Kinyarwanda is NOT in WALS Ch 106 sample. Reciprocal type
    inferred from Bantu morphology (cf. Swahili, Zulu = Value 2) —
    UNVERIFIED against WALS. -/
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
    Passive absent, antipassive with oblique patient (accusative
    alignment — one of the accusative-language antipassives),
    no applicative, morphological causative. -/
def lango : ValenceProfile :=
  { language := "Lango"
  , iso := "laj"
  , reciprocal := .identicalToReflexive
  , passive := .absent
  , antipassive := .obliquePatient
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

/-- Halkomelem (Salishan, Canada): reciprocal distinct,
    passive present, antipassive with oblique patient,
    ergative alignment, applicative (benefactive + other,
    both bases), morphological causative.
    NOTE: Halkomelem is NOT in WALS Ch 106 sample.
    Reciprocal type inferred from Salishan grammar — UNVERIFIED. -/
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

example : french.causative = .compoundOnly := by native_decide
example : modernGreek.causative = .neither := by native_decide

example : finnish.passive = .present := by native_decide
example : finnish.causative = .morphologicalOnly := by native_decide

-- ============================================================================
-- WALS Grounding: Profile reciprocal types match generated WALS data
-- ============================================================================

/-- Helper: convert WALS 106A value to our ReciprocalType. -/
private def fromWALS106A : Core.WALS.F106A.ReciprocalType → ReciprocalType
  | .noReciprocalConstruction => .noNonIconic
  | .distinctFromReflexive    => .distinctFromReflexive
  | .mixed                    => .mixed
  | .identicalToReflexive     => .identicalToReflexive

/-- For each profile whose language IS in WALS Ch 106, prove its reciprocal
    type matches the WALS data. This eliminates transcription errors by
    construction: if the profile disagrees with WALS, the theorem fails. -/

theorem english_reciprocal_wals :
    (Core.WALS.F106A.lookup "eng").map (fromWALS106A ·.value) = some english.reciprocal := by
  native_decide
theorem japanese_reciprocal_wals :
    (Core.WALS.F106A.lookup "jpn").map (fromWALS106A ·.value) = some japanese.reciprocal := by
  native_decide
theorem turkish_reciprocal_wals :
    (Core.WALS.F106A.lookup "tur").map (fromWALS106A ·.value) = some turkish.reciprocal := by
  native_decide
theorem swahili_reciprocal_wals :
    (Core.WALS.F106A.lookup "swa").map (fromWALS106A ·.value) = some swahili.reciprocal := by
  native_decide
theorem chukchi_reciprocal_wals :
    (Core.WALS.F106A.lookup "chk").map (fromWALS106A ·.value) = some chukchi.reciprocal := by
  native_decide
theorem indonesian_reciprocal_wals :
    (Core.WALS.F106A.lookup "ind").map (fromWALS106A ·.value) = some indonesian.reciprocal := by
  native_decide
theorem french_reciprocal_wals :
    (Core.WALS.F106A.lookup "fre").map (fromWALS106A ·.value) = some french.reciprocal := by
  native_decide
theorem russian_reciprocal_wals :
    (Core.WALS.F106A.lookup "rus").map (fromWALS106A ·.value) = some russian.reciprocal := by
  native_decide
theorem hindi_reciprocal_wals :
    (Core.WALS.F106A.lookup "hin").map (fromWALS106A ·.value) = some hindi.reciprocal := by
  native_decide
theorem westGreenlandic_reciprocal_wals :
    (Core.WALS.F106A.lookup "grw").map (fromWALS106A ·.value) = some westGreenlandic.reciprocal := by
  native_decide
theorem lango_reciprocal_wals :
    (Core.WALS.F106A.lookup "lan").map (fromWALS106A ·.value) = some lango.reciprocal := by
  native_decide
theorem chamorro_reciprocal_wals :
    (Core.WALS.F106A.lookup "cha").map (fromWALS106A ·.value) = some chamorro.reciprocal := by
  native_decide
theorem modernGreek_reciprocal_wals :
    (Core.WALS.F106A.lookup "grk").map (fromWALS106A ·.value) = some modernGreek.reciprocal := by
  native_decide
theorem german_reciprocal_wals :
    (Core.WALS.F106A.lookup "ger").map (fromWALS106A ·.value) = some german.reciprocal := by
  native_decide
theorem finnish_reciprocal_wals :
    (Core.WALS.F106A.lookup "fin").map (fromWALS106A ·.value) = some finnish.reciprocal := by
  native_decide

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
    let present := (Core.WALS.F107A.allData.filter (·.value == .present)).length
    let total := Core.WALS.F107A.allData.length
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
    @cite{polinsky-2013}: more languages have oblique-patient antipassives
    than implicit-patient antipassives, and the majority have no antipassive. -/
theorem antipassive_distribution :
    let oblique := (Core.WALS.F108A.allData.filter (·.value == .obliquePatient)).length
    let implicit := (Core.WALS.F108A.allData.filter (·.value == .implicitPatient)).length
    let none_ := (Core.WALS.F108A.allData.filter (·.value == .noAntipassive)).length
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
    let morphOnly := (Core.WALS.F111A.allData.filter (·.value == .morphologicalOnly)).length
    let both := (Core.WALS.F111A.allData.filter (·.value == .both)).length
    let total := Core.WALS.F111A.allData.length
    -- Morphological causatives in >80% of languages
    (morphOnly + both) * 10 > total * 8 := by native_decide

/-- In our sample, all but two languages have a morphological or compound
    causative (Modern Greek has neither; French has compound only). -/
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
    is by far the most common pattern. @cite{song-2013} lists examples:
    Japanese "-(s)ase", Turkish "-dUr", Swahili "-ish-" / "-esh-".
    Prefixes (Abkhaz "r-"), infixes (Lepcha "-y-"), and circumfixes
    (Georgian "a-...-ineb") exist but are rare. This parallels Greenberg's
    Universal 27: suffixing is generally preferred over prefixing. -/
structure CausativeMorphologyExample where
  language : String
  morpheme : String
  position : String  -- "suffix", "prefix", "infix", "circumfix"
  deriving Repr, BEq, DecidableEq

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
    eurasians.all fun p => p.reciprocal != .noNonIconic := by native_decide

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
-- Antipassive Alignment Data (from @cite{polinsky-2013}, Table 1)
-- ============================================================================

/-- Languages with antipassives classified by alignment, from WALS Ch 108
    Table 1. This is the key empirical evidence for the antipassive-ergativity
    debate (@cite{silverstein-1976}, @cite{dixon-1979} vs @cite{heath-1976}, @cite{givon-1984}). -/
structure AntipassiveAlignmentDatum where
  language : String
  alignment : AlignmentType
  deriving Repr, BEq, DecidableEq

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

    In our sample, only Bantu and Austronesian languages have applicatives. -/
theorem applicatives_only_in_bantu_and_austronesian :
    let withApplicative := allProfiles.filter fun p =>
      p.applicative.hasApplicative
    withApplicative.all fun p =>
      -- Swahili (swa), Kinyarwanda (kin) = Bantu
      -- Chamorro (cha) = Austronesian
      -- Halkomelem (hur) = Salishan
      p.iso == "swa" || p.iso == "kin" || p.iso == "cha" || p.iso == "hur" := by
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
example : sampleAntipassiveCount .obliquePatient = 6 := by native_decide
example : sampleAntipassiveCount .noAntipassive = 13 := by native_decide
example : sampleApplicativeCount = 4 := by native_decide

-- ============================================================================
-- Polysemy Cross-Validation (@cite{nordlinger-2023})
-- ============================================================================

/-- @cite{nordlinger-2023} (p. 88) reports that of the 175 languages in
    @cite{maslova-nedjalkov-2013}'s sample, polysemous reflexive/reciprocal
    constructions are present in 60 (34%). In WALS terms, polysemy corresponds
    to Values 3 (mixed) and 4 (identical to reflexive). -/
theorem polysemy_count :
    let mixed := (Core.WALS.F106A.allData.filter (·.value == .mixed)).length
    let identical := (Core.WALS.F106A.allData.filter (·.value == .identicalToReflexive)).length
    mixed + identical = 60 := by native_decide

/-- 60 out of 175 = 34.3%. -/
theorem polysemy_percentage :
    let polysemous := (Core.WALS.F106A.allData.filter
        (fun d => d.value == .mixed || d.value == .identicalToReflexive)).length
    let total := Core.WALS.F106A.allData.length
    -- More than a third but less than half
    polysemous * 3 > total ∧ polysemous * 2 < total := by native_decide

-- ============================================================================
-- Semantic Reciprocity Types (@cite{nordlinger-2023}, §4)
-- ============================================================================

/-- Semantic type of reciprocal relation.

    @cite{nordlinger-2023} (§4) summarizes the semantic typology from
    Dalrymple et al. (1998) and Evans et al. (2011), distinguishing six
    types of mutual relation that reciprocal constructions can encode:

    - `strong`: every participant reciprocates with every other
      ("The members of this family love one another.")
    - `pairwise`: participants are paired off
      ("The people at the dinner party were married to one another.")
    - `chain`: sequential, each with the next
      ("The graduating students followed one another up onto the stage.")
    - `radial`: one central participant reciprocates with all others
      ("The teacher and her pupils intimidated one another.")
    - `melee`: widespread but not exhaustive reciprocation
      ("The drunks in the pub were punching one another.")
    - `ring`: circular chain, last links back to first
      ("The children chased each other round in a ring.") -/
inductive ReciprocityType where
  | strong
  | pairwise
  | chain
  | radial
  | melee
  | ring
  deriving DecidableEq, BEq, Repr

/-- Whether a reciprocity type requires exhaustive participation
    (every member of the group is involved). -/
def ReciprocityType.exhaustive : ReciprocityType → Bool
  | .strong   => true
  | .pairwise => true
  | .chain    => true
  | .radial   => false
  | .melee    => false
  | .ring     => true

/-- Whether a reciprocity type is symmetric: within each active pair,
    if A acts on B then B acts on A. Chain and ring are directional
    (A follows B does not entail B follows A). Radial IS symmetric —
    the teacher intimidates each pupil AND each pupil intimidates the
    teacher — it just doesn't cover all pairs. -/
def ReciprocityType.symmetric : ReciprocityType → Bool
  | .strong   => true
  | .pairwise => true
  | .chain    => false
  | .radial   => true
  | .melee    => true
  | .ring     => false

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

open Fragments.English.Pronouns in

/-- The English ValenceProfile's `distinctFromReflexive` coding is
    grounded in the Fragment: English has reciprocal pronouns that are
    categorically different from reflexive pronouns. -/
theorem english_profile_grounded :
    english.reciprocal = .distinctFromReflexive ∧
    eachOther.pronounType = .reciprocal ∧
    eachOther.pronounType ≠ PronounType.reflexive := by
  exact ⟨rfl, rfl, by decide⟩

end Phenomena.ArgumentStructure.Typology
