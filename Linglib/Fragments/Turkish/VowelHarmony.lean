import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.FeatureGeometry
import Linglib.Theories.Phonology.RuleBased.Defs
import Linglib.Theories.Phonology.Autosegmental.Defs

/-!
# Turkish Vowel Harmony
@cite{goksel-kerslake-2005}

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
-/

namespace Fragments.Turkish.VowelHarmony

open Theories.Phonology (Segment Feature)
open Theories.Phonology.Autosegmental (agreeAt)

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
-- § 2: Stem Harmony Extraction
-- ============================================================================

/-- Extract [back] value of the last vowel in the stem. -/
def stemBack (stem : List Segment) : Option Bool :=
  let vowels := stem.filter (·.hasValue .syllabic true)
  vowels.getLast?.bind (·.spec .back)

/-- Extract [round] value of the last vowel in the stem. -/
def stemRound (stem : List Segment) : Option Bool :=
  let vowels := stem.filter (·.hasValue .syllabic true)
  vowels.getLast?.bind (·.spec .round)

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

-- Stem harmony extraction
theorem back_stem : stemBack [a_vowel] = some true := by native_decide
theorem front_stem : stemBack [e_vowel] = some false := by native_decide
theorem round_stem : stemRound [o_vowel] = some true := by native_decide
theorem unround_stem : stemRound [ı_vowel] = some false := by native_decide

-- 2D harmony: göz (front, rounded) determines both dimensions
theorem göz_back : stemBack [ö_vowel] = some false := by native_decide
theorem göz_round : stemRound [ö_vowel] = some true := by native_decide

-- Cross-backness: a and e disagree on dorsal features
theorem a_e_dorsal_disagree :
    agreeAt a_vowel e_vowel .dorsal = false := by native_decide

-- Same-backness: a and o agree on [back]
theorem a_o_same_back :
    a_vowel.hasValue .back true = true ∧
    o_vowel.hasValue .back true = true := ⟨by native_decide, by native_decide⟩

end Fragments.Turkish.VowelHarmony
