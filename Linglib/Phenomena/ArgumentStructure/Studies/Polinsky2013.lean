import Linglib.Typology.ArgumentStructure
import Linglib.Data.WALS.Features.F108A
import Linglib.Data.WALS.Features.F109A
import Linglib.Data.WALS.Features.F111A
import Linglib.Fragments.Finnish.Predicates
import Linglib.Fragments.English.Pronouns

/-!
# Phenomena.ArgumentStructure.Studies.Polinsky2013
@cite{polinsky-2013-antipassive} @cite{polinsky-2013-applicative}
@cite{maslova-nedjalkov-2013} @cite{siewierska-2013}
@cite{haspelmath-2013-ditransitive}
@cite{song-2013-periphrastic} @cite{song-2013-nonperiphrastic}
@cite{silverstein-1976}

Cross-linguistic analyses anchored on Polinsky's two WALS chapters --
Ch 108 (antipassive) and Ch 109 (applicative) -- and the cross-chapter
correlations they support. The 19-language `ValenceProfile` sample is the
testbed for these correlations, drawing on data from all of Ch 105--111.

Polinsky's central empirical claim (Ch 108) is the antipassive-ergativity
correlation @cite{silverstein-1976}: antipassives are concentrated in
ergative languages, but accusative-language antipassives exist (17 of them
in WALS Table 1, against 30 ergative). This file ports Table 1 and tests
the correlation against the ValenceProfile sample.

For Ch 109 (applicative), Polinsky observes that applicatives "are commonly
found in those languages that have little or no case marking of noun
phrases and that have sufficiently rich verbal morphology" -- correlating
with morphological causatives (Song 2013, Ch 111). The
`applicative_implies_morph_causative` theorem tests this in the sample.

## Contents

- §1. The 19-language `ValenceProfile` sample.
- §2. Sample-grounded cross-chapter generalisations:
  passive prevalence, antipassive-ergativity, applicative-causative
  correlation, areal distribution, no_passive_ergative_has_antipassive.
- §3. The 47-language antipassive alignment data
  (@cite{polinsky-2013-antipassive} Table 1).
- §4. Causative morphology examples (Song 2013).
- §5. Fragment-bridge theorems (English reciprocals, Finnish passive).

## Out of scope

The substrate types (`ReciprocalType`, `ApplicativeType`, `ValenceProfile`,
WALS converters, corpus-only theorems) live in
`Linglib/Typology/ArgumentStructure.lean`. Pylkkänen's structural Appl
classification + WALS divergence is in `Studies/Pylkkanen2008.lean`.
Nordlinger's extended reciprocal apparatus is in `Studies/Nordlinger2023.lean`.
Siloni's lexical/syntactic distinction is in `Studies/Siloni2012.lean`.
-/

set_option autoImplicit false

namespace Phenomena.ArgumentStructure.Studies.Polinsky2013

open Typology.ArgumentStructure

-- ============================================================================
-- §1. The 19-Language ValenceProfile Sample
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

/-- Turkish: reciprocal distinct from reflexive -- "birbirine" (reciprocal)
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

/-- Indonesian: reciprocal distinct from reflexive -- "saling" (reciprocal)
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

/-- French: mixed reciprocal type -- both reflexive-identical "se" and
    distinct "l'un l'autre" ('each other'). WALS Ch 106 codes French as
    Value 3 (mixed).
    Periphrastic passive ("être + past participle"), no antipassive,
    no applicative.

    Nonperiphrastic causative (Ch 111): WALS codes French as `.both`.
    The periphrastic *faire + INF* construction is Ch 110 (periphrastic
    causatives), excluded from Ch 111 by definition. -/
def french : ValenceProfile :=
  { language := "French"
  , iso := "fra"
  , reciprocal := .mixed
  , passive := .present
  , antipassive := .noAntipassive
  , alignment := .accusative
  , applicative := .noApplicative
  , causative := .both }

/-- Russian: mixed reciprocal type -- both reflexive-identical "-sja"/"-s'"
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
    coding -- accusative alignment, one of the accusative-language
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
    §11.2.1.14--15). Passive present, antipassive with oblique patient,
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

/-- Modern Greek: mixed reciprocal type -- both nonactive voice morphology
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
    impersonal "passive" (present -- the Fragment's `finnishPassive` has
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

/-- 19-language sample for cross-chapter generalisations. -/
def allProfiles : List ValenceProfile :=
  [ english, japanese, turkish, swahili, dyirbal, chukchi, indonesian
  , french, russian, arabic, hindi, westGreenlandic, kinyarwanda
  , lango, chamorro, halkomelem, modernGreek, german, finnish ]

example : allProfiles.length = 19 := by native_decide

-- ============================================================================
-- §2. Cross-Chapter Correlations on the Sample
-- ============================================================================

/-- In our sample, most languages have a passive: at least 14 of 19. -/
theorem majority_of_sample_has_passive :
    (allProfiles.filter (·.hasPassive)).length ≥ 14 := by native_decide

/-- @cite{polinsky-2013-antipassive}'s key generalisation in the sample:
    every ergative-alignment language has an antipassive. -/
theorem ergative_implies_antipassive_in_sample :
    let ergatives := allProfiles.filter fun p => p.alignment == .ergative
    ergatives.all fun p => p.antipassive.hasAntipassive := by native_decide

/-- @cite{polinsky-2013-antipassive}'s flip side: most accusative languages
    in the sample lack an antipassive (the converse fails: not all
    accusative languages lack one -- Lango is a counterexample). -/
theorem most_accusative_lack_antipassive :
    let accusatives := allProfiles.filter fun p => p.alignment == .accusative
    let withoutAP := accusatives.filter fun p => !p.antipassive.hasAntipassive
    withoutAP.length > (accusatives.length - withoutAP.length) := by native_decide

/-- @cite{song-2013-nonperiphrastic} dominance reproduced in the sample:
    almost every language has at least a morphological or compound causative
    (Modern Greek is the lone exception -- only periphrastic). -/
theorem almost_all_have_nonperiphr_causative :
    (allProfiles.filter fun p => p.causative != .neither).length ≥ 16 := by
  native_decide

/-- @cite{polinsky-2013-applicative}'s observation: applicatives "are
    commonly found in those languages that have... sufficiently rich verbal
    morphology." Since morphological causatives also require rich verbal
    morphology, we expect a correlation. In the sample: every applicative
    language also has a morphological causative. -/
theorem applicative_implies_morph_causative :
    let withApplicative := allProfiles.filter fun p => p.applicative.hasApplicative
    withApplicative.all fun p => p.causative.hasMorphological := by native_decide

/-- WALS Ch 106 areal pattern: Value 1 (no non-iconic reciprocal
    constructions) is concentrated in Oceania, Southeast Asia, and parts
    of Africa. Every Eurasian language in the sample has at least one
    productive grammatical reciprocal construction. -/
def isEurasian (p : ValenceProfile) : Bool :=
  p.iso == "eng" || p.iso == "deu" || p.iso == "fra" || p.iso == "rus" ||
  p.iso == "ell" || p.iso == "tur" || p.iso == "hin" || p.iso == "jpn" ||
  p.iso == "arb"

theorem eurasian_all_have_productive_reciprocal :
    (allProfiles.filter isEurasian).all
        fun p => p.reciprocal != .noDedicated := by native_decide

/-- Cross-chapter: in the sample, every passive-absent ergative language
    has an antipassive (consistent with ergative languages using
    antipassive in roles where accusative languages use passive). -/
theorem no_passive_ergative_has_antipassive :
    let noPassiveErgative := allProfiles.filter fun p =>
      p.passive == .absent && p.alignment == .ergative
    noPassiveErgative.all fun p => p.antipassive.hasAntipassive := by
  native_decide

/-- Applicatives and antipassives are dual voice operations: applicatives
    increase valence, antipassives decrease it. In the sample, two
    languages combine them (Chamorro and Halkomelem). -/
theorem some_languages_have_both_app_and_antipass :
    (allProfiles.filter fun p =>
        p.applicative.hasApplicative && p.antipassive.hasAntipassive).length = 2 := by
  native_decide

/-- @cite{polinsky-2013-applicative} areal observation: applicatives
    cluster in three areas -- Bantu Africa, Western Pacific (Austronesian),
    and North/Meso-America (Salish, Mayan, Uto-Aztecan). The dearth in
    Eurasia correlates with rich case marking. In the sample, applicatives
    appear only in Bantu, Austronesian, and Salishan languages. -/
theorem applicatives_only_in_bantu_austronesian_salishan :
    (allProfiles.filter fun p => p.applicative.hasApplicative).all
        fun p =>
          -- Swahili (swh), Kinyarwanda (kin) = Bantu
          -- Chamorro (cha) = Austronesian
          -- Halkomelem (hur) = Salishan
          p.iso == "swh" || p.iso == "kin" || p.iso == "cha" || p.iso == "hur" := by
  native_decide

-- ============================================================================
-- §3. Antipassive Alignment Data (Polinsky 2013, Table 1)
-- ============================================================================

/-- Languages with antipassives classified by alignment, from
    @cite{polinsky-2013-antipassive} Table 1. Key empirical evidence for
    the antipassive-ergativity debate (@cite{silverstein-1976}). -/
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

/-- Sample-size and consistency for the Polinsky 2013 Table 1 data. -/
theorem AP_accusative_count : accusativeAntipassiveLangs.length = 17 := by native_decide
theorem AP_ergative_count : ergativeAntipassiveLangs.length = 30 := by native_decide

theorem accusative_AP_all_accusative :
    accusativeAntipassiveLangs.all fun d => d.alignment == .accusative := by
  native_decide

theorem ergative_AP_all_ergative :
    ergativeAntipassiveLangs.all fun d => d.alignment == .ergative := by
  native_decide

/-- @cite{polinsky-2013-antipassive}'s headline ratio: ergative languages
    with antipassives outnumber accusative ones with antipassives. -/
theorem ergative_AP_more_common :
    ergativeAntipassiveLangs.length > accusativeAntipassiveLangs.length := by
  native_decide

-- ============================================================================
-- §4. Causative Morphology Examples (Song 2013)
-- ============================================================================

/-- Examples of morphological causatives by morpheme position.
    @cite{song-2013-nonperiphrastic} reports that suffixation is by far
    the most common pattern, paralleling Greenberg's Universal 27. -/
structure CausativeMorphologyExample where
  language : String
  morpheme : String
  position : String  -- "suffix", "prefix", "infix", "circumfix"
  deriving Repr, DecidableEq

def causativeMorphExamples : List CausativeMorphologyExample :=
  [ { language := "Japanese",   morpheme := "-(s)ase",         position := "suffix" }
  , { language := "Turkish",    morpheme := "-dUr",            position := "suffix" }
  , { language := "Swahili",    morpheme := "-ish-/-esh-",     position := "suffix" }
  , { language := "Hindi",      morpheme := "-aa/-vaa",        position := "suffix" }
  , { language := "Korean",     morpheme := "-i/-hi/-li/-ki",  position := "suffix" }
  , { language := "Finnish",    morpheme := "-tta-/-ttä-",     position := "suffix" }
  , { language := "Hungarian",  morpheme := "-tat-/-tet-",     position := "suffix" }
  , { language := "Abkhaz",     morpheme := "r-",              position := "prefix" }
  , { language := "Lepcha",     morpheme := "-y-",             position := "infix" }
  , { language := "Georgian",   morpheme := "a-...-ineb",      position := "circumfix" } ]

/-- Suffixing dominates: most morphological causative examples are
    suffixes (@cite{song-2013-nonperiphrastic}). -/
theorem suffixing_dominates_causatives :
    let suffixes := causativeMorphExamples.filter fun e => e.position == "suffix"
    let nonSuffixes := causativeMorphExamples.filter fun e => e.position != "suffix"
    suffixes.length > nonSuffixes.length * 2 := by native_decide

-- ============================================================================
-- §5. Fragment-Bridge Theorems
-- ============================================================================

open Fragments.English.Pronouns in
/-- English reciprocal forms ("each other", "one another") are formally
    distinct from reflexive forms ("themselves", etc.) -- derived from
    the Fragment's pronoun entries rather than stipulated in the profile. -/
theorem english_reciprocal_distinct_from_reflexive :
    eachOther.pronounType ≠ PronounType.reflexive ∧
    oneAnother.pronounType ≠ PronounType.reflexive := by
  exact ⟨by decide, by decide⟩

/-- Finnish impersonal "passive" has semantic content (existential closure
    over agent) -- derived from the Fragment's voice head. -/
theorem finnish_passive_has_semantics :
    Fragments.Finnish.Predicates.finnishPassive.HasSemantics := by decide

/-- Finnish impersonal "passive" does NOT project a syntactic agent --
    derived from the Fragment's voice head. The Fragment-grounded discrepancy
    with WALS Ch 107 (which classifies Finnish as `.present`) is real:
    the Finnish "passive" has agent semantics without projecting syntax. -/
theorem finnish_passive_no_agent :
    ¬ Fragments.Finnish.Predicates.finnishPassive.AssignsTheta := by decide

end Phenomena.ArgumentStructure.Studies.Polinsky2013
