import Linglib.Datasets.WALS.Features.F65A
import Linglib.Datasets.WALS.Features.F66A
import Linglib.Datasets.WALS.Features.F67A
import Linglib.Datasets.WALS.Features.F68A
import Linglib.Datasets.WALS.Features.F69A
import Linglib.Datasets.WALS.Features.F78A

/-!
# Tense-aspect typology — substrate types and WALS data
@cite{wals-2013} (Chs 65–69, 78) @cite{comrie-1985}
@cite{dahl-velupillai-2013} @cite{de-haan-2013} @cite{dryer-haspelmath-2013}
@cite{bybee-perkins-pagliuca-1994}

Type-level enums + per-language profile struct for tense-aspect-mood-
evidentiality systems across @cite{wals-2013} chapters 65–69 and 78, plus
WALS distribution data and the principal cross-linguistic generalizations.

## Schema

- `AspectMarking` (Ch 65): grammatical perfective/imperfective marking
- `PastMarking` (Ch 66): past tense marking + remoteness distinctions
- `FutureMarking` (Ch 67): inflectional future tense
- `PerfectType` (Ch 68): perfect category and its diachronic source
- `TAAffixPosition` (Ch 69): position of tense-aspect affixes
- `EvidentialityCoding` (Ch 78): coding strategy for evidentiality
- `TAProfile`: per-language bundle (Chs 65–69 + optional Ch 78)

Per-language data lives in `Fragments/{Lang}/TenseAspect.lean`.

## Note on EvidentialityCoding

`EvidentialityCoding` is currently also declared (under a different name,
`EvidentialCoding`) in `Phenomena/Modality/Typology.lean`. The duplication
will be resolved when Modality/Typology is dissolved — substrate canonical
location TBD at that point.
-/

set_option autoImplicit false

namespace Typology

-- ============================================================================
-- WALS Ch 65: Perfective/imperfective aspect
-- ============================================================================

/-- WALS Ch 65: whether the perfective/imperfective distinction is
    grammaticalized. "Grammatical marking" includes both morphological and
    periphrastic constructions. -/
inductive AspectMarking where
  /-- Grammatical perfective/imperfective marking present. -/
  | grammatical
  /-- No grammatical marking. -/
  | none
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 66: Past tense
-- ============================================================================

/-- WALS Ch 66: past tense marking and remoteness distinctions. Past
    imperfectives (Armenian-style, restricted to imperfective contexts)
    count as past marking. -/
inductive PastMarking where
  /-- Past/non-past marked, no remoteness distinctions. -/
  | marked
  /-- Past/non-past marked + 2–3 degrees of remoteness. -/
  | markedRemoteness2_3
  /-- Past/non-past marked + 4+ degrees of remoteness. -/
  | markedRemoteness4plus
  /-- No grammatical past/non-past distinction. -/
  | none
  deriving DecidableEq, Repr

/-- Whether a language has any past tense marking. -/
def PastMarking.hasMarking : PastMarking → Bool
  | .marked | .markedRemoteness2_3 | .markedRemoteness4plus => true
  | .none => false

-- ============================================================================
-- WALS Ch 67: Future tense
-- ============================================================================

/-- WALS Ch 67: inflectional future marking. Only inflectional marking is
    counted (not periphrastic *will* + V). Irrealis markers that obligatorily
    encode future reference are included. -/
inductive FutureMarking where
  /-- Inflectional future/nonfuture distinction. -/
  | inflectional
  /-- No inflectional future. -/
  | none
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 68: The perfect
-- ============================================================================

/-- WALS Ch 68: perfect category and its diachronic source. A form counts as
    a perfect only if it has both resultative and experiential uses (not a
    general past, not a dedicated resultative). -/
inductive PerfectType where
  /-- 'have'-perfect from possessive construction (almost exclusively
      western Europe). -/
  | fromPossessive
  /-- Perfect from 'finish' or 'already' (concentrated in SE Asia and
      West Africa). -/
  | fromFinishAlready
  /-- Other perfect (dedicated resultative source, or undetermined). -/
  | other
  /-- No perfect category. -/
  | none
  deriving DecidableEq, Repr

/-- Whether a language has any perfect category. -/
def PerfectType.hasPerfect : PerfectType → Bool
  | .fromPossessive | .fromFinishAlready | .other => true
  | .none => false

-- ============================================================================
-- WALS Ch 69: Position of tense-aspect affixes
-- ============================================================================

/-- WALS Ch 69: primary morphological strategy for tense-aspect marking.
    Mixed strategies with no dominant type are coded as `mixed`; infixes and
    stem changes are subsumed under prefix/suffix when localized at edges. -/
inductive TAAffixPosition where
  /-- Tense-aspect prefixes. -/
  | prefixing
  /-- Tense-aspect suffixes. -/
  | suffixing
  /-- Tonal tense-aspect (almost exclusively African). -/
  | tonal
  /-- Mixed strategies, none primary. -/
  | mixed
  /-- No tense-aspect inflection. -/
  | noInflection
  deriving DecidableEq, Repr

/-- Whether a language has any tense-aspect affixation. -/
def TAAffixPosition.hasAffixes : TAAffixPosition → Bool
  | .prefixing | .suffixing | .tonal | .mixed => true
  | .noInflection => false

-- ============================================================================
-- WALS Ch 78: Evidentiality coding
-- ============================================================================

/-- WALS Ch 78: how evidentiality is coded. "Evidentiality" means
    grammaticalized marking of information source. -/
inductive EvidentialityCoding where
  /-- No grammatical evidentiality. -/
  | none
  /-- Evidentiality is part of the tense paradigm (e.g., Turkish *-miş*). -/
  | partOfTense
  /-- Verbal affix. -/
  | verbalAffix
  /-- Clitic. -/
  | clitic
  /-- Particle. -/
  | particle
  /-- Other strategy. -/
  | other
  deriving DecidableEq, Repr

/-- Whether a language has any grammatical evidentiality. -/
def EvidentialityCoding.hasEvidentiality : EvidentialityCoding → Bool
  | .none => false
  | _ => true

-- ============================================================================
-- Per-language profile
-- ============================================================================

/-- A language's tense-aspect-mood-evidentiality profile across
    @cite{wals-2013} Chs 65–69 (mandatory) and Ch 78 (optional). -/
structure TAProfile where
  language : String
  iso : String
  family : String
  /-- Ch 65: perfective/imperfective aspect. -/
  aspect : AspectMarking
  /-- Ch 66: past tense marking. -/
  past : PastMarking
  /-- Ch 67: inflectional future. -/
  future : FutureMarking
  /-- Ch 68: perfect category. -/
  perfect : PerfectType
  /-- Ch 69: tense-aspect affix position. -/
  affixPosition : TAAffixPosition
  /-- Ch 78: evidentiality coding (none if not in WALS Ch 78 sample). -/
  evidentialityCoding : Option EvidentialityCoding := none
  deriving Repr, DecidableEq

/-- Whether a profile has any tense or aspect marking. -/
def TAProfile.hasTenseOrAspect (p : TAProfile) : Bool :=
  p.aspect == .grammatical || p.past.hasMarking || p.future == .inflectional

/-- Whether a profile lacks all three major T/A gram types
    (the SE Asian isolating signature). -/
def TAProfile.lacksMajorTAGrams (p : TAProfile) : Bool :=
  p.aspect == .none && p.past == .none && p.future == .none

-- ============================================================================
-- WALS converters
-- ============================================================================

def fromWALS65A : Datasets.WALS.F65A.PerfectiveImperfective → AspectMarking
  | .grammaticalMarking => .grammatical
  | .noGrammaticalMarking => .none

def fromWALS66A : Datasets.WALS.F66A.PastTenseType → PastMarking
  | .presentNoRemotenessDistinctions => .marked
  | .present23RemotenessDistinctions => .markedRemoteness2_3
  | .present4OrMoreRemotenessDistinctions => .markedRemoteness4plus
  | .noPastTense => .none

def fromWALS67A : Datasets.WALS.F67A.FutureTenseType → FutureMarking
  | .inflectionalFutureExists => .inflectional
  | .noInflectionalFuture => .none

def fromWALS68A : Datasets.WALS.F68A.PerfectType → PerfectType
  | .fromPossessive => .fromPossessive
  | .fromFinishAlready => .fromFinishAlready
  | .otherPerfect => .other
  | .noPerfect => .none

def fromWALS69A : Datasets.WALS.F69A.TenseAspectAffixPosition → TAAffixPosition
  | .tenseAspectPrefixes => .prefixing
  | .tenseAspectSuffixes => .suffixing
  | .tenseAspectTone => .tonal
  | .mixedType => .mixed
  | .noTenseAspectInflection => .noInflection

-- ============================================================================
-- WALS distribution data
-- ============================================================================

/-- WALS Ch 65 distribution (n = 222). -/
structure Ch65Counts where
  grammatical : Nat
  noMarking : Nat
  deriving Repr, DecidableEq

def Ch65Counts.total (c : Ch65Counts) : Nat := c.grammatical + c.noMarking

/-- WALS Ch 65 counts (222 languages). -/
def walsCh65 : Ch65Counts :=
  { grammatical := 101, noMarking := 121 }

/-- WALS Ch 66 distribution (n = 222). -/
structure Ch66Counts where
  markedNoRemoteness : Nat
  markedRemoteness2_3 : Nat
  markedRemoteness4plus : Nat
  noMarking : Nat
  deriving Repr, DecidableEq

def Ch66Counts.total (c : Ch66Counts) : Nat :=
  c.markedNoRemoteness + c.markedRemoteness2_3 + c.markedRemoteness4plus + c.noMarking

def Ch66Counts.totalWithPast (c : Ch66Counts) : Nat :=
  c.markedNoRemoteness + c.markedRemoteness2_3 + c.markedRemoteness4plus

/-- WALS Ch 66 counts (222 languages). -/
def walsCh66 : Ch66Counts :=
  { markedNoRemoteness := 94, markedRemoteness2_3 := 38
  , markedRemoteness4plus := 2, noMarking := 88 }

/-- WALS Ch 67 distribution (n = 222). -/
structure Ch67Counts where
  inflectional : Nat
  noInflectional : Nat
  deriving Repr, DecidableEq

def Ch67Counts.total (c : Ch67Counts) : Nat := c.inflectional + c.noInflectional

/-- WALS Ch 67 counts (222 languages). -/
def walsCh67 : Ch67Counts :=
  { inflectional := 110, noInflectional := 112 }

/-- WALS Ch 68 distribution (n = 222). -/
structure Ch68Counts where
  fromPossessive : Nat
  fromFinishAlready : Nat
  otherPerfect : Nat
  noPerfect : Nat
  deriving Repr, DecidableEq

def Ch68Counts.total (c : Ch68Counts) : Nat :=
  c.fromPossessive + c.fromFinishAlready + c.otherPerfect + c.noPerfect

/-- WALS Ch 68 counts (222 languages). -/
def walsCh68 : Ch68Counts :=
  { fromPossessive := 7, fromFinishAlready := 21, otherPerfect := 80, noPerfect := 114 }

/-- WALS Ch 69 distribution (n = 1131). -/
structure Ch69Counts where
  prefixing : Nat
  suffixing : Nat
  tonal : Nat
  mixed : Nat
  noInflection : Nat
  deriving Repr, DecidableEq

def Ch69Counts.total (c : Ch69Counts) : Nat :=
  c.prefixing + c.suffixing + c.tonal + c.mixed + c.noInflection

/-- WALS Ch 69 counts (1131 languages). -/
def walsCh69 : Ch69Counts :=
  { prefixing := 153, suffixing := 667, tonal := 13, mixed := 24, noInflection := 274 }

-- ============================================================================
-- Cross-linguistic generalizations
-- ============================================================================

/-- A majority of @cite{wals-2013} Ch 66 languages have past marking
    (134 of 222 = 60%). -/
theorem past_marking_majority :
    walsCh66.totalWithPast > walsCh66.noMarking := by decide

/-- Suffix dominance: @cite{wals-2013} Ch 69 suffixes outnumber prefixes by
    more than 4:1 (667 vs 153). -/
theorem suffix_dominant_over_prefix :
    walsCh69.suffixing > 4 * walsCh69.prefixing := by decide

/-- Suffixing is the most common T/A strategy overall. -/
theorem suffix_most_common :
    walsCh69.suffixing > walsCh69.prefixing ∧
    walsCh69.suffixing > walsCh69.tonal ∧
    walsCh69.suffixing > walsCh69.mixed ∧
    walsCh69.suffixing > walsCh69.noInflection := by decide

/-- Suffixing accounts for more than half of all languages in Ch 69. -/
theorem suffix_absolute_majority :
    walsCh69.suffixing * 2 > walsCh69.total := by decide

/-- Tone as a primary T/A strategy is rare (~13/1131 ≈ 1%), almost
    exclusively in Africa. -/
theorem tone_ta_rare : walsCh69.tonal < 15 := by decide

/-- The future-tense split is approximately even (110 vs 112). Neither
    inflectional future nor its absence is a strong majority. -/
theorem future_near_even_split :
    walsCh67.inflectional > 100 ∧ walsCh67.noInflectional > 100 := by decide

/-- 'have'-perfects are extremely rare cross-linguistically (only 7/222),
    restricted almost exclusively to western Europe. -/
theorem have_perfect_rare : walsCh68.fromPossessive < 10 := by decide

/-- 'finish'/'already' perfects are more common than 'have'-perfects
    (21 vs 7), concentrated in SE Asia and West Africa. -/
theorem finish_perfect_more_common_than_have :
    walsCh68.fromFinishAlready > walsCh68.fromPossessive := by decide

/-- Most languages lack a distinct perfect category entirely. -/
theorem no_perfect_majority :
    walsCh68.noPerfect >
    walsCh68.fromPossessive + walsCh68.fromFinishAlready + walsCh68.otherPerfect := by
  decide

/-- Most past-marking languages make no remoteness distinctions
    (94 of 134). Languages with 4+ degrees of remoteness are extremely rare
    (only 2; Yagua being the richest with 5 degrees). -/
theorem remoteness_uncommon :
    walsCh66.markedNoRemoteness >
    walsCh66.markedRemoteness2_3 + walsCh66.markedRemoteness4plus := by decide

/-- Extreme remoteness (4+ degrees) is attested in only 2 languages worldwide
    in the @cite{wals-2013} sample. -/
theorem extreme_remoteness_very_rare :
    walsCh66.markedRemoteness4plus = 2 := by decide

end Typology
