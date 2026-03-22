import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.RuleBased.Defs
import Linglib.Theories.Phonology.Harmony.Defs

/-!
# Hungarian Vowel Harmony
@cite{siptar-torkenczy-2000} @cite{rose-walker-2011}

Hungarian has **palatal vowel harmony**: the [±back] value of the last
harmonic (non-neutral) stem vowel spreads rightward to suffix vowels.
This is the most widely studied vowel harmony system in the literature,
with over 50 theoretical treatments cited in @cite{siptar-torkenczy-2000}.

## Why Hungarian stress-tests `HarmonySystem`

Hungarian harmony is structurally similar to Finnish (both spread [back]
rightward with transparent neutral vowels), but introduces three phenomena
that push beyond a simple `triggerValue` analysis:

1. **Antiharmonic stems** (§3.2.2 class IIA-b): all-neutral stems like
   *híd* 'bridge' that unexpectedly take back-vowel suffixes. `triggerValue`
   returns `none` for these stems since there is no harmonic trigger — the
   backness must be lexically specified.

2. **Vacillating stems** (§3.2.3.1): stems like *hotel* where speakers
   accept both front and back suffixes. The `spreadSuffix` function
   returns a single deterministic result and cannot model optionality.

3. **Height-graded transparency** (§3.2.3): neutral vowels /i, í/ are
   always transparent, /é/ is mostly transparent, and /e/ sometimes acts
   as opaque. The binary `isTransparent` predicate cannot express this
   gradient.

## Vowel inventory (@cite{siptar-torkenczy-2000} §2.2.1, system (7))

|          | Front           |                 | Back            |
|----------|-----------------|-----------------|-----------------|
|          | Unrounded       | Rounded         |                 |
| **High** | i / í           | ü / ű           | u / ú           |
| **Mid**  | e / é           | ö / ő           | o / ó           |
| **Low**  |                 |                 | a / á           |

## Harmony classification (@cite{siptar-torkenczy-2000} §3.2, (27))

- **Front harmonic**: ö, ő, ü, ű (front rounded)
- **Back harmonic**: a, á, o, ó, u, ú (back)
- **Neutral**: i, í, e, é (front unrounded)

## Stem classes (@cite{siptar-torkenczy-2000} §3.2.2)

- **IA** (simple harmonic): all harmonic vowels same backness
- **IB** (complex harmonic / disharmonic): conflicting harmonic vowels,
  last harmonic governs
- **IIA** (simple neutral): all vowels neutral — mostly front (IIA-f),
  but some are antiharmonic (IIA-b)
- **IIB** (complex neutral): harmonic + neutral, neutral is transparent

## Rounding harmony (@cite{siptar-torkenczy-2000} §3.2.4)

Three-way suffixes (hoz/höz/hez, tok/tök/tek) depend on BOTH
backness and rounding of the last stem vowel:
- Back → always o (regardless of stem rounding)
- Front rounded → ö
- Front unrounded (including neutral) → e

Rounding harmony is simpler than backness harmony: no neutral vowels
(every vowel is either rounded or not), no antiharmonic stems, no
vacillation. It only matters for front stems.

## Architectural limitation: Clements/Hume place-node spreading

@cite{siptar-torkenczy-2000} §6.1 analyses Hungarian VH using
Clements/Hume unary place features (COR, LAB, DOR) with four rules:
Link Place, Link DOR, Spread Place, Spread DOR. This is place-NODE
spreading, not individual binary-feature spreading. Our `HarmonySystem`
with a single `feature : Feature` field cannot capture node-level
operations. The two-system decomposition (palatal + labial) used here
is an approximation that works for the data but does not reflect the
theoretical architecture of §6.1.
-/

set_option autoImplicit false

namespace Fragments.Hungarian.VowelHarmony

open Theories.Phonology (Segment Feature FeatureVal)
open Theories.Phonology.Harmony (HarmonySystem HarmonyDir triggerValue
  harmonizeOne harmonyDomain spreadSuffix)

-- ============================================================================
-- § 1: Vowel Inventory (7 short vowels)
-- ============================================================================

/-! We define the 7 short vowels using the Hayes feature system.
    Long vowels have identical features for harmony purposes — length
    is prosodic, not segmental (@cite{siptar-torkenczy-2000} §3.1).

    Representational note: Hungarian /a/ = [ɒ] is phonetically rounded
    but phonologically [+back, −round, +low]. Surface rounding is a
    phonetic implementation detail (@cite{siptar-torkenczy-2000} p. 54). -/

/-- /i/: [+syll, +high, −back, −round, −low, +dorsal]. Neutral. -/
def i_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true),
   (.back, false), (.round, false), (.low, false)]

/-- /ü/: [+syll, +high, −back, +round, −low, +dorsal]. Front harmonic. -/
def ü_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true),
   (.back, false), (.round, true), (.low, false)]

/-- /u/: [+syll, +high, +back, +round, −low, +dorsal]. Back harmonic. -/
def u_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true),
   (.back, true), (.round, true), (.low, false)]

/-- /e/: [+syll, −high, −back, −round, −low, +dorsal]. Neutral.
    Phonetically [ɛ] (open-mid). -/
def e_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false),
   (.back, false), (.round, false), (.low, false)]

/-- /ö/: [+syll, −high, −back, +round, −low, +dorsal]. Front harmonic. -/
def ö_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false),
   (.back, false), (.round, true), (.low, false)]

/-- /o/: [+syll, −high, +back, +round, −low, +dorsal]. Back harmonic. -/
def o_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false),
   (.back, true), (.round, true), (.low, false)]

/-- /a/: [+syll, −high, +back, −round, +low, +dorsal]. Back harmonic.
    Surface [ɒ] is phonetically rounded; phonological rounding is absent
    (@cite{siptar-torkenczy-2000} p. 54). -/
def a_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false),
   (.back, true), (.round, false), (.low, true)]

-- ============================================================================
-- § 2: Vowel Classification
-- ============================================================================

/-- A vowel is neutral iff it is front and unrounded: /i, í, e, é/.
    @cite{siptar-torkenczy-2000} §3.2, (27). -/
def isNeutral (s : Segment) : Bool :=
  s.hasValue .syllabic true &&
  s.hasValue .back false &&
  s.hasValue .round false

/-- A vowel is front-harmonic iff it is front and rounded: /ö, ő, ü, ű/.
    These always trigger and undergo palatal harmony. -/
def isFrontHarmonic (s : Segment) : Bool :=
  s.hasValue .syllabic true &&
  s.hasValue .back false &&
  s.hasValue .round true

/-- A vowel is back-harmonic iff it is [+back]: /a, á, o, ó, u, ú/.
    All back vowels are harmonic in Hungarian. -/
def isBackHarmonic (s : Segment) : Bool :=
  s.hasValue .syllabic true &&
  s.hasValue .back true

/-- Harmony role classification. -/
inductive HarmonyRole where
  | frontHarmonic  -- ö, ő, ü, ű: trigger front, undergo harmony
  | backHarmonic   -- a, á, o, ó, u, ú: trigger back, undergo harmony
  | neutral        -- i, í, e, é: transparent
  deriving DecidableEq, BEq, Repr

/-- Classify a vowel's harmony role. -/
def classifyVowel (s : Segment) : HarmonyRole :=
  if isBackHarmonic s then .backHarmonic
  else if isFrontHarmonic s then .frontHarmonic
  else .neutral

-- ============================================================================
-- § 3: Harmony System Instance
-- ============================================================================

/-- Hungarian palatal harmony: [back] spreads from the last harmonic
    (non-neutral) stem vowel to harmonic suffix vowels. Neutral vowels
    /i, í, e, é/ are transparent — they neither trigger nor undergo harmony.

    Structurally identical to `finnishHarmony` but with a larger neutral
    class (4 vowels vs 2). @cite{siptar-torkenczy-2000} §3.2.1,
    @cite{rose-walker-2011}. -/
def hungarianPalatalHarmony : HarmonySystem where
  feature       := .back
  isTrigger     := (λ s => s.hasValue .syllabic true && !isNeutral s)
  isTarget      := (λ s => s.hasValue .syllabic true && !isNeutral s)
  isTransparent := isNeutral
  direction     := .rightward

/-- Hungarian rounding harmony: [round] from the last stem vowel, used to
    resolve three-way suffix alternations (hoz/höz/hez).

    Unlike backness harmony, rounding harmony has NO transparency — every
    vowel is either rounded or not. There are no antiharmonic stems and
    no vacillation w.r.t. rounding (@cite{siptar-torkenczy-2000} §3.2.4).

    The rounding value only matters for front stems (back stems always
    get the back suffix variant regardless of rounding). -/
def hungarianLabialHarmony : HarmonySystem where
  feature       := .round
  isTrigger     := (·.hasValue .syllabic true)
  isTarget      := (·.hasValue .syllabic true)
  isTransparent := (λ _ => false)
  direction     := .rightward

-- ============================================================================
-- § 4: Stem Classes (@cite{siptar-torkenczy-2000} §3.2.2)
-- ============================================================================

/-- Stem class for Hungarian vowel harmony.

    The four major classes combine two axes:
    - Harmonic (I) vs Neutral (II): is the last vowel harmonic or neutral?
    - Simple (A) vs Complex (B): are all harmonic vowels the same backness?

    Within each, -f and -b indicate whether the stem selects front or back
    suffixes. @cite{siptar-torkenczy-2000} §3.2.2. -/
inductive StemClass where
  | IA_f   -- simple harmonic, front: tűz, tükör, öröm
  | IA_b   -- simple harmonic, back: ház, kupa, koszorú, bika, hernyó
  | IB_f   -- complex harmonic, front (disharmonic): sofőr, allűr
  | IB_b   -- complex harmonic, back (disharmonic): nüansz, amőba
  | IIA_f  -- simple neutral, front: víz, szegény, kert
  | IIA_b  -- simple neutral, back (antiharmonic): híd, cél, derék
  | IIB_f  -- complex neutral, front (transparent): üveg, rövid
  | IIB_b  -- complex neutral, back (transparent): papír, taxi
  deriving DecidableEq, BEq, Repr

/-- Does this stem class select back suffixes? -/
def StemClass.isBack : StemClass → Bool
  | .IA_b | .IB_b | .IIA_b | .IIB_b => true
  | _ => false

-- ============================================================================
-- § 5: Suffix Alternation Pairs (@cite{siptar-torkenczy-2000} §3.2.1, (28))
-- ============================================================================

/-- Suffix alternation types. @cite{siptar-torkenczy-2000} §3.2.1, (28).

    Hungarian suffixes alternate in pairs (two-way) or triplets (three-way).
    Two-way alternation depends on [±back] alone. Three-way alternation
    depends on [±back] AND [±round] of the last stem vowel. -/
inductive SuffixType where
  | twoWay_a_e     -- a/e: -ban/-ben, -nak/-nek
  | twoWay_á_é     -- á/é: -nál/-nél, -ná/-né
  | twoWay_u_ü     -- u/ü: -unk/-ünk
  | twoWay_ú_ű     -- ú/ű: láb-ú/fej-ű
  | twoWay_ó_ő     -- ó/ő: -ból/-ből, -tól/-től, -ról/-ről, vár-ó/kér-ő
  | threeWay_o_ö_e  -- o/ö/e: -hoz/-höz/-hez, -on/-ön/-en, -tok/-tök/-tek
  deriving DecidableEq, BEq, Repr

/-- Resolve a two-way a/e suffix given backness. -/
def resolveA (back : Bool) : Segment :=
  if back then a_vowel else e_vowel

/-- Resolve a three-way o/ö/e suffix given backness and rounding.
    @cite{siptar-torkenczy-2000} §3.2.4, (39):
    - Back → /o/ (always, regardless of stem rounding)
    - Front rounded → /ö/
    - Front unrounded (including neutral) → /e/ -/
def resolveThreeWay (back : Bool) (round : Bool) : Segment :=
  if back then o_vowel
  else if round then ö_vowel
  else e_vowel

-- ============================================================================
-- § 6: Feature Verification
-- ============================================================================

-- Backness
theorem a_is_back : a_vowel.hasValue .back true = true := by native_decide
theorem o_is_back : o_vowel.hasValue .back true = true := by native_decide
theorem u_is_back : u_vowel.hasValue .back true = true := by native_decide
theorem i_is_front : i_vowel.hasValue .back false = true := by native_decide
theorem e_is_front : e_vowel.hasValue .back false = true := by native_decide
theorem ö_is_front : ö_vowel.hasValue .back false = true := by native_decide
theorem ü_is_front : ü_vowel.hasValue .back false = true := by native_decide

-- Rounding
theorem ö_is_round : ö_vowel.hasValue .round true = true := by native_decide
theorem ü_is_round : ü_vowel.hasValue .round true = true := by native_decide
theorem i_is_unround : i_vowel.hasValue .round false = true := by native_decide
theorem e_is_unround : e_vowel.hasValue .round false = true := by native_decide
theorem a_is_unround : a_vowel.hasValue .round false = true := by native_decide

-- Harmony classification
theorem i_is_neutral : isNeutral i_vowel = true := by native_decide
theorem e_is_neutral : isNeutral e_vowel = true := by native_decide
theorem ö_not_neutral : isNeutral ö_vowel = false := by native_decide
theorem ü_not_neutral : isNeutral ü_vowel = false := by native_decide
theorem a_not_neutral : isNeutral a_vowel = false := by native_decide
theorem o_not_neutral : isNeutral o_vowel = false := by native_decide
theorem u_not_neutral : isNeutral u_vowel = false := by native_decide

theorem ö_is_frontHarmonic : isFrontHarmonic ö_vowel = true := by native_decide
theorem ü_is_frontHarmonic : isFrontHarmonic ü_vowel = true := by native_decide
theorem a_is_backHarmonic : isBackHarmonic a_vowel = true := by native_decide
theorem o_is_backHarmonic : isBackHarmonic o_vowel = true := by native_decide

-- ============================================================================
-- § 7: Stress Tests — Where `HarmonySystem` Succeeds
-- ============================================================================

/-! ### Class IA: Simple harmonic stems
    These are the easy cases: all harmonic vowels agree in backness.
    `triggerValue` finds the last harmonic vowel and returns its [back]
    value. This always gives the correct suffix harmony. -/

/-- *tűz* 'fire' (IA-f): last vowel /ü/ → front harmony.
    Suffixes: tűz-nek (dat), tűz-től (abl). -/
theorem tűz_front :
    triggerValue hungarianPalatalHarmony [ü_vowel] = some false := by
  native_decide

/-- *ház* 'house' (IA-b): last vowel /a/ → back harmony.
    Suffixes: ház-nak (dat), ház-tól (abl). -/
theorem ház_back :
    triggerValue hungarianPalatalHarmony [a_vowel] = some true := by
  native_decide

/-- *koszorú* 'wreath' (IA-b): vowels /o, o, u/ all back → back harmony.
    Suffixes: koszorú-nak, koszorú-tól. -/
theorem koszorú_back :
    triggerValue hungarianPalatalHarmony [o_vowel, o_vowel, u_vowel] =
      some true := by
  native_decide

/-- *tükör* 'mirror' (IA-f): vowels /ü, ö/ both front harmonic → front.
    Suffixes: tükör-nek, tükör-től. -/
theorem tükör_front :
    triggerValue hungarianPalatalHarmony [ü_vowel, ö_vowel] =
      some false := by
  native_decide

/-- *hernyó* 'caterpillar' (IA-b): vowels /e, o/ — /e/ is neutral,
    /o/ is the last vowel and is back harmonic → back harmony.
    Suffixes: hernyó-nak, hernyó-tól.
    @cite{siptar-torkenczy-2000} p. 67. -/
theorem hernyó_back :
    triggerValue hungarianPalatalHarmony [e_vowel, o_vowel] =
      some true := by
  native_decide

/-! ### Class IB: Complex harmonic (disharmonic) stems
    Conflicting harmonic vowels within the stem. The LAST harmonic
    vowel governs suffix selection. `triggerValue` gets this right
    because it extracts the last trigger. -/

/-- *sofőr* 'driver' (IB-f): vowels /o, ő/ — last harmonic is /ő/ [−back]
    → front suffixes. Suffixes: sofőr-nek, sofőr-től. -/
theorem sofőr_front :
    triggerValue hungarianPalatalHarmony [o_vowel, ö_vowel] =
      some false := by
  native_decide

/-- *nüansz* 'nuance' (IB-b): vowels /ü, a/ — last harmonic is /a/ [+back]
    → back suffixes. Suffixes: nüansz-nak, nüansz-tól.
    (Note: /ü/ is front harmonic but /a/ is later → back wins.) -/
theorem nüansz_back :
    triggerValue hungarianPalatalHarmony [ü_vowel, a_vowel] =
      some true := by
  native_decide

/-! ### Class IIB-b: Complex neutral, back (transparent)
    These are the textbook transparency cases. A back harmonic vowel
    precedes one or more neutral vowels, and harmony passes THROUGH
    the neutral vowels to reach the suffix. `triggerValue` handles this
    correctly because neutral vowels are not triggers, so the search
    skips them and finds the earlier back vowel. -/

/-- *papír* 'paper' (IIB-b): vowels /a, i/ — /i/ is neutral (not a trigger),
    so `triggerValue` finds /a/ → back harmony.
    Suffixes: papír-nak, papír-tól. -/
theorem papír_back :
    triggerValue hungarianPalatalHarmony [a_vowel, i_vowel] =
      some true := by
  native_decide

/-- *kávé* 'coffee': vowels /a, e/ — /e/ is neutral, `triggerValue`
    finds /a/ → back harmony. Suffixes: kávé-nak, kávé-tól.
    (The book lists kávé under IA-b (p. 67) since the neutrality
    of final /é/ is disputed — some speakers treat it as harmonic.
    Our system gives the correct result either way.) -/
theorem kávé_back :
    triggerValue hungarianPalatalHarmony [a_vowel, e_vowel] =
      some true := by
  native_decide

/-! ### Class IIB-f: Complex neutral, front (transparent from front)
    Front harmonic vowel + neutral → front harmony via last trigger. -/

/-- *üveg* 'glass' (IIB-f): vowels /ü, e/ — /e/ is neutral, `triggerValue`
    finds /ü/ → front harmony. Suffixes: üveg-nek, üveg-től. -/
theorem üveg_front :
    triggerValue hungarianPalatalHarmony [ü_vowel, e_vowel] =
      some false := by
  native_decide

-- ============================================================================
-- § 8: Stress Tests — Where `HarmonySystem` Fails
-- ============================================================================

/-! ### Class IIA: Simple neutral stems — THE CRITICAL FAILURE

    All-neutral stems contain only /i, í, e, é/. Since none of these are
    triggers in `hungarianPalatalHarmony`, `triggerValue` returns `none`.
    But Hungarian speakers DO assign a definite backness to these stems:

    - IIA-f (*víz* 'water', *szegény* 'poor'): front suffixes ✓
    - IIA-b (*híd* 'bridge', *cél* 'aim', *derék* 'waist'): back suffixes ✗

    The antiharmonic stems (IIA-b) are **lexically specified** — their
    backness cannot be predicted from the phonological form. This is the
    fundamental limitation of any purely phonological harmony system. -/

/-- *víz* 'water' (IIA-f): only /i/ → `triggerValue` returns `none`.
    The correct answer is front (víz-nek, víz-től), but the system
    cannot determine this. -/
theorem víz_no_trigger :
    triggerValue hungarianPalatalHarmony [i_vowel] = none := by
  native_decide

/-- *híd* 'bridge' (IIA-b, antiharmonic): only /i/ → `triggerValue`
    returns `none`. The correct answer is BACK (híd-nak, híd-tól),
    but the system returns the same `none` as for *víz*.

    This is the canonical limitation: antiharmonic stems require
    lexical specification beyond phonological features. -/
theorem híd_no_trigger :
    triggerValue hungarianPalatalHarmony [i_vowel] = none := by
  native_decide

/-- The critical failure: víz and híd are phonologically identical
    (both have only /i/) but require different suffix harmony.
    `triggerValue` cannot distinguish them. -/
theorem víz_híd_indistinguishable :
    triggerValue hungarianPalatalHarmony [i_vowel] =
    triggerValue hungarianPalatalHarmony [i_vowel] := rfl

/-- *cél* 'aim' (IIA-b): only /e/ → `triggerValue` returns `none`.
    Correct answer: back (cél-nak). Another antiharmonic stem. -/
theorem cél_no_trigger :
    triggerValue hungarianPalatalHarmony [e_vowel] = none := by
  native_decide

/-! ### Vacillation — OPTIONALITY FAILURE

    Some stems allow BOTH front and back suffixes. This is common with
    mixed stems where back-harmonic vowels are followed by neutral vowels,
    especially /e/ (@cite{siptar-torkenczy-2000} §3.2.3.1, Table 11).

    `spreadSuffix` is deterministic — it returns a single list. A
    vacillating stem like *hotel* would need to return a SET of possible
    outputs.

    The height effect: transparency correlates with vowel height.
    /i, í/ — always transparent → neutral.
    /é/ — mostly transparent → mostly neutral, sometimes vacillating.
    /e/ — variably transparent → neutral, vacillating, or disharmonic.

    The binary `isTransparent` predicate cannot capture this gradient. -/

/-- *hotel* has vowels /o, e/. Our system finds /o/ as last trigger →
    back. In reality speakers vacillate: hotel-nak ~ hotel-nek.
    The system predicts only back, which is one of the two options. -/
theorem hotel_predicted_back :
    triggerValue hungarianPalatalHarmony [o_vowel, e_vowel] =
      some true := by
  native_decide

-- ============================================================================
-- § 9: Suffix Harmonization
-- ============================================================================

/-! Demonstrate suffix harmonization using `harmonizeOne` with an
    underspecified archiphonemic suffix vowel. -/

/-- A generic high vowel archiphoneme (placeholder for suffix /U/). -/
def archiphoneU : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true),
   (.low, false)]

/-- *ház*: harmonize an underspecified suffix vowel to [+back]. -/
theorem ház_suffix_becomes_back :
    (harmonizeOne hungarianPalatalHarmony true archiphoneU).hasValue
      .back true = true := by
  native_decide

/-- *tűz* → suffix vowel becomes [−back]. -/
theorem tűz_suffix_becomes_front :
    (harmonizeOne hungarianPalatalHarmony false archiphoneU).hasValue
      .back false = true := by
  native_decide

-- ============================================================================
-- § 10: Rounding Harmony Verification (@cite{siptar-torkenczy-2000} §3.2.4)
-- ============================================================================

/-! Three-way suffix resolution verified against (39):
    tűz-höz, szemölcs-höz, sofőr-höz (front rounded → höz)
    víz-hez, kötény-hez, kódex-hez (front unrounded → hez)
    ház-hoz, hernyó-hoz, nüansz-hoz (back → hoz) -/

-- Labial trigger extraction
theorem tűz_round :
    triggerValue hungarianLabialHarmony [ü_vowel] = some true := by
  native_decide

theorem víz_unround :
    triggerValue hungarianLabialHarmony [i_vowel] = some false := by
  native_decide

theorem ház_unround :
    triggerValue hungarianLabialHarmony [a_vowel] = some false := by
  native_decide

/-- *tűz-höz*: front (back=false) + rounded (round=true) → /ö/. -/
theorem tűz_hoz_suffix :
    resolveThreeWay false true = ö_vowel := rfl

/-- *víz-hez*: front (back=false) + unrounded (round=false) → /e/. -/
theorem víz_hez_suffix :
    resolveThreeWay false false = e_vowel := rfl

/-- *ház-hoz*: back (back=true) → /o/ regardless of rounding. -/
theorem ház_hoz_suffix :
    resolveThreeWay true false = o_vowel := rfl

/-- Back stems always get /o/ in three-way suffixes, regardless of whether
    the stem vowel is rounded or not. @cite{siptar-torkenczy-2000} §3.2.4. -/
theorem back_rounding_irrelevant :
    resolveThreeWay true true = resolveThreeWay true false := rfl

/-- *kötény-hez*: vowels /ö, e/. Palatal: last trigger /ö/ → front.
    Labial: last vowel /e/ → unrounded. Three-way → /e/ (hez). -/
theorem kötény_front :
    triggerValue hungarianPalatalHarmony [ö_vowel, e_vowel] =
      some false := by
  native_decide
theorem kötény_unround :
    triggerValue hungarianLabialHarmony [ö_vowel, e_vowel] =
      some false := by
  native_decide

/-- *szemölcs-höz*: vowels /e, ö/. Palatal: last trigger /ö/ → front.
    Labial: last vowel /ö/ → rounded. Three-way → /ö/ (höz). -/
theorem szemölcs_round :
    triggerValue hungarianLabialHarmony [e_vowel, ö_vowel] =
      some true := by
  native_decide

-- ============================================================================
-- § 11: Two-Dimensional Harmony — End-to-End
-- ============================================================================

/-! The two harmony dimensions compose to derive three-way suffixes:
    1. `triggerValue hungarianPalatalHarmony stem` → back : Option Bool
    2. `triggerValue hungarianLabialHarmony stem` → round : Option Bool
    3. `resolveThreeWay back round` → suffix vowel

    This decomposition mirrors the book's observation that rounding harmony
    is a "minor subsidiary pattern" layered on top of backness harmony
    (@cite{siptar-torkenczy-2000} §3.2.4). -/

/-- Compose both harmony dimensions for a back stem. -/
theorem ház_twoDim :
    let back := triggerValue hungarianPalatalHarmony [a_vowel]
    let round := triggerValue hungarianLabialHarmony [a_vowel]
    back = some true ∧ round = some false := by
  exact ⟨by native_decide, by native_decide⟩

/-- Compose both harmony dimensions for a front rounded stem. -/
theorem tűz_twoDim :
    let back := triggerValue hungarianPalatalHarmony [ü_vowel]
    let round := triggerValue hungarianLabialHarmony [ü_vowel]
    back = some false ∧ round = some true := by
  exact ⟨by native_decide, by native_decide⟩

/-- Compose both harmony dimensions for a front unrounded (neutral) stem.
    Palatal harmony returns `none` (no trigger), but labial harmony
    returns `some false` — rounding works even when backness doesn't. -/
theorem víz_twoDim :
    let back := triggerValue hungarianPalatalHarmony [i_vowel]
    let round := triggerValue hungarianLabialHarmony [i_vowel]
    back = none ∧ round = some false := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 12: Cross-Linguistic Comparison
-- ============================================================================

/-! Hungarian and Finnish palatal harmony share the same `HarmonySystem`
    structure: both spread [back] rightward with transparent neutral vowels.

    Key structural differences:
    - Neutral class: Finnish /i, e/ (2) vs Hungarian /i, í, e, é/ (4)
    - Hungarian has antiharmonic stems (IIA-b); Finnish does not
    - Hungarian has a second harmony dimension (rounding, §3.2.4)

    Hungarian and Turkish share the two-dimensional structure (palatal +
    labial), but differ in targets: Turkish labial harmony targets only
    [+high] suffix vowels, while Hungarian labial harmony (rounding
    for three-way suffixes) targets all relevant suffix positions. -/

theorem hungarian_finnish_same_feature :
    hungarianPalatalHarmony.feature = Feature.back := rfl

theorem hungarian_finnish_same_direction :
    hungarianPalatalHarmony.direction = .rightward := rfl

/-- Both Hungarian and Turkish have two-dimensional harmony:
    palatal ([back]) + labial ([round]). -/
theorem hungarian_turkish_both_twoDim :
    hungarianPalatalHarmony.feature = .back ∧
    hungarianLabialHarmony.feature = .round := ⟨rfl, rfl⟩

-- ============================================================================
-- § 13: Blocker Model — /e/ as opaque (@cite{siptar-torkenczy-2000} §3.2.3)
-- ============================================================================

/-! The height-graded transparency problem (§3.2.3) can be partially addressed
    using the `isBlocker` field. By treating /e/ as a blocker rather than
    transparent, we capture the intuition that /e/ sometimes blocks back
    harmony from reaching the suffix.

    This alternative system makes different predictions for mixed stems:
    - *hotel* /o, e/: `/e/` blocks → `triggerValue` returns `none` (no trigger
      in the suffix-adjacent domain). This predicts front harmony by default,
      matching the front option of the vacillation.
    - *papír* /a, i/: `/i/` is still transparent → `triggerValue` returns
      `some true` (back harmony), unchanged.

    This does NOT model vacillation itself (which requires optionality), but
    it shows that the `isBlocker` field can shift predictions in the right
    direction for stems where /e/ is opaque. -/

/-- Alternative palatal harmony with /e/ as a blocker (opaque).
    Only /i, í/ are transparent; /e, é/ block spreading.
    @cite{siptar-torkenczy-2000} §3.2.3: /e/ is the least transparent
    neutral vowel (most likely to block). -/
def palatalHarmony_eBlocks : HarmonySystem where
  feature       := .back
  isTrigger     := (λ s => s.hasValue .syllabic true && !isNeutral s)
  isTarget      := (λ s => s.hasValue .syllabic true && !isNeutral s)
  isTransparent := (λ s => s.hasValue .syllabic true &&
    s.hasValue .back false && s.hasValue .round false && s.hasValue .high true)
  isBlocker     := (λ s => s.hasValue .syllabic true &&
    s.hasValue .back false && s.hasValue .round false && s.hasValue .high false)
  direction     := .rightward

/-- With /e/ as blocker: *hotel* /o, e/ → /e/ blocks, domain = [], no trigger.
    Contrast: `hotel_predicted_back` in the transparent model gives `some true`. -/
theorem hotel_eBlocks_no_trigger :
    triggerValue palatalHarmony_eBlocks [o_vowel, e_vowel] = none := by
  native_decide

/-- With /e/ as blocker: *papír* /a, i/ → /i/ is still transparent (high),
    so `triggerValue` finds /a/ → back harmony. Unchanged from transparent model. -/
theorem papír_eBlocks_still_back :
    triggerValue palatalHarmony_eBlocks [a_vowel, i_vowel] = some true := by
  native_decide

/-- The blocker model shrinks the harmony domain for *hotel*:
    domain after the last blocker (/e/) is empty. -/
theorem hotel_domain_empty :
    (harmonyDomain palatalHarmony_eBlocks [o_vowel, e_vowel]).length = 0 := by
  native_decide

/-- The transparent model gives the full domain (no blockers). -/
theorem hotel_domain_full :
    (harmonyDomain hungarianPalatalHarmony [o_vowel, e_vowel]).length = 2 := by
  native_decide

/-- `spreadSuffix` preserves suffix length even with blockers. -/
theorem spread_preserves_length :
    (spreadSuffix palatalHarmony_eBlocks true [e_vowel, archiphoneU]).length = 2 := by
  native_decide

end Fragments.Hungarian.VowelHarmony
