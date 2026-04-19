import Linglib.Theories.Phonology.Featural.Features
import Linglib.Theories.Phonology.Featural.Geometry
import Linglib.Theories.Phonology.RuleBased.Defs
import Linglib.Theories.Phonology.Autosegmental.Defs
import Linglib.Theories.Phonology.Harmony.Defs

/-!
# Turkish Vowel Harmony
@cite{goksel-kerslake-2005} @cite{rose-walker-2011}

Turkish has a perfectly symmetric 2x2x2 vowel inventory and a
**two-dimensional** vowel harmony system (@cite{goksel-kerslake-2005} Ch 3).

## Vowel inventory

|          | Front       |             | Back        |             |
|----------|-------------|-------------|-------------|-------------|
|          | Unrounded   | Rounded     | Unrounded   | Rounded     |
| **High** | i           | ü           | ı           | u           |
| **Non-high** | e       | ö           | a           | o           |

## Two harmony dimensions

1. **Palatal harmony** ([±back]): the last vowel's [back] value spreads to
   *all* suffix vowels. Determines the **twofold** alternation A -> a/e.

2. **Labial harmony** ([±round]): the last vowel's [round] value spreads
   to **[+high] suffix vowels only**. Combined with palatal harmony, this
   yields the **fourfold** alternation I -> ı/i/u/ü.

## Archiphonemic suffix vowels

Turkish grammars use capital letters for harmonizing suffix vowels:
- **A** alternates a/e (twofold: [back] only)
- **I** alternates ı/i/u/ü (fourfold: [back] + [round])

Examples with *ev* 'house' [front, unrounded]:
  Plural ev-ler (A -> e), Accusative ev-i (I -> i)
Examples with *göz* 'eye' [front, rounded]:
  Plural göz-ler (A -> e), Accusative göz-ü (I -> ü)
Examples with *kol* 'arm' [back, rounded]:
  Plural kol-lar (A -> a), Accusative kol-u (I -> u)

## Harmony systems (@cite{rose-walker-2011})

Turkish VH decomposes into two `HarmonySystem` instances:
- `palatalHarmony`: [back] spreads to all suffix vowels (twofold A)
- `labialHarmony`: [round] spreads to high suffix vowels only (fourfold I)
-/

namespace Fragments.Turkish.VowelHarmony

open Phonology (Segment Feature)
open Phonology.Autosegmental (agreeAt)
open Phonology.Harmony (HarmonySystem HarmonyDir triggerValue)

-- ============================================================================
-- § 1: Turkish Vowel Inventory (8 vowels)
-- ============================================================================

def i_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true),
   (.back, false), (.round, false), (.low, false)]

def ü_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true),
   (.back, false), (.round, true), (.low, false)]

def ı_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true),
   (.back, true), (.round, false), (.low, false)]

def u_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true),
   (.back, true), (.round, true), (.low, false)]

def e_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false),
   (.back, false), (.round, false), (.low, false)]

def ö_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false),
   (.back, false), (.round, true), (.low, false)]

def a_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false),
   (.back, true), (.round, false), (.low, true)]

def o_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false),
   (.back, true), (.round, true), (.low, false)]

-- ============================================================================
-- § 2: Harmony System Instances
-- ============================================================================

/-- Palatal harmony: [back] spreads from the last stem vowel to all suffix
    vowels. Every vowel is both trigger and target; no transparency. -/
def palatalHarmony : HarmonySystem :=
  HarmonySystem.mk' (feature := .back)
    (isTrigger     := (·.hasValue .syllabic true))
    (isTarget      := (·.hasValue .syllabic true))
    (isTransparent := (λ _ => false))
    (direction     := .rightward)

/-- Labial harmony: [round] spreads from the last stem vowel to high suffix
    vowels only. Every vowel triggers; only [+high] vowels are targets. -/
def labialHarmony : HarmonySystem :=
  HarmonySystem.mk' (feature := .round)
    (isTrigger     := (·.hasValue .syllabic true))
    (isTarget      := (λ s => s.hasValue .syllabic true && s.hasValue .high true))
    (isTransparent := (λ _ => false))
    (direction     := .rightward)

-- ============================================================================
-- § 3: Archiphoneme Resolution
-- ============================================================================

/-- Resolve archiphonemic **A**: twofold alternation a/e controlled by [back].
    Used for plural -lAr, past -DI, future -(y)AcAK, etc. -/
def resolveA (back : Bool) : Segment :=
  if back then a_vowel else e_vowel

/-- Resolve archiphonemic **I**: fourfold alternation ı/i/u/ü
    controlled by [back] and [round].
    Used for accusative -(y)I, progressive -Iyor, possessive -(I)m, etc. -/
def resolveI : Bool → Bool → Segment
  | true,  false => ı_vowel
  | false, false => i_vowel
  | true,  true  => u_vowel
  | false, true  => ü_vowel

-- ============================================================================
-- § 4: Verification
-- ============================================================================

-- Back/front classification
theorem a_is_back : a_vowel.hasValue .back true = true := by native_decide
theorem e_is_front : e_vowel.hasValue .back false = true := by native_decide
theorem ö_is_front : ö_vowel.hasValue .back false = true := by native_decide
theorem u_is_back : u_vowel.hasValue .back true = true := by native_decide

-- Rounding
theorem ü_is_round : ü_vowel.hasValue .round true = true := by native_decide
theorem ı_is_unround : ı_vowel.hasValue .round false = true := by native_decide

-- Height
theorem i_is_high : i_vowel.hasValue .high true = true := by native_decide
theorem a_is_low : a_vowel.hasValue .low true = true := by native_decide

-- Archiphoneme resolution
theorem resolveA_back : resolveA true = a_vowel := rfl
theorem resolveA_front : resolveA false = e_vowel := rfl
theorem resolveI_back_unround : resolveI true false = ı_vowel := rfl
theorem resolveI_front_round : resolveI false true = ü_vowel := rfl
theorem resolveI_back_round : resolveI true true = u_vowel := rfl
theorem resolveI_front_unround : resolveI false false = i_vowel := rfl

-- ============================================================================
-- § 5: Harmony System Verification
-- ============================================================================

/-- Palatal harmony extracts [back] from a back-vowel stem. -/
theorem palatal_back_stem :
    triggerValue palatalHarmony [a_vowel] = some true := by native_decide

/-- Palatal harmony extracts [−back] from a front-vowel stem. -/
theorem palatal_front_stem :
    triggerValue palatalHarmony [e_vowel] = some false := by native_decide

/-- Labial harmony extracts [round] from a rounded stem. -/
theorem labial_round_stem :
    triggerValue labialHarmony [o_vowel] = some true := by native_decide

/-- Labial harmony extracts [−round] from an unrounded stem. -/
theorem labial_unround_stem :
    triggerValue labialHarmony [ı_vowel] = some false := by native_decide

-- 2D harmony: göz (front, rounded) determines both dimensions
theorem göz_palatal : triggerValue palatalHarmony [ö_vowel] = some false := by
  native_decide
theorem göz_labial : triggerValue labialHarmony [ö_vowel] = some true := by
  native_decide

-- Cross-backness: a and e disagree on dorsal features
theorem a_e_dorsal_disagree :
    agreeAt a_vowel e_vowel .dorsal = false := by native_decide

-- Same-backness: a and o agree on [back]
theorem a_o_same_back :
    a_vowel.hasValue .back true = true ∧
    o_vowel.hasValue .back true = true := ⟨by native_decide, by native_decide⟩

end Fragments.Turkish.VowelHarmony
