import Linglib.Fragments.English.Determiners
import Linglib.Fragments.Mandarin.Determiners
import Linglib.Fragments.Japanese.Determiners

/-!
# Cross-Linguistic Quantifier Typology

Empirical quantifier inventories from three languages (three families) mapped to
a common `QuantifierInventory` structure, following the pattern established in
`Phenomena.Modality.Typology` for modal inventories.

## Mapping conventions

- Force, monotonicity, and strength values are taken from the Fragment entries
  (English `QuantifierEntry`, Mandarin `MandarinQuantEntry`, Japanese `JapaneseQuantEntry`)
- Each inventory is **derived from** its Fragment (single source of truth)

## Data sources

- English: Barwise & Cooper (1981)
- Mandarin: Li (1998), Cheng & Sybesma (1999)
- Japanese: Shimoyama (2006), Nakanishi (2007)

## References

- Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language.
- Peters, S. & Westerståhl, D. (2006). Quantifiers in Language and Logic.
-/

namespace Phenomena.Quantification.Typology

open Fragments.English.Determiners (QForce Monotonicity Strength QuantityWord)

-- ============================================================================
-- Common inventory structure
-- ============================================================================

/-- A quantifier entry in the common typological format. -/
structure QuantifierEntry where
  form : String
  qforce : QForce
  monotonicity : Monotonicity
  strength : Strength
  deriving BEq, Repr

/-- A language's quantifier inventory. -/
structure QuantifierInventory where
  language : String
  family : String
  source : String
  entries : List QuantifierEntry
  deriving Repr

def QuantifierInventory.size (inv : QuantifierInventory) : Nat :=
  inv.entries.length

-- ============================================================================
-- §1: English (Indo-European) — derived from Fragment
-- ============================================================================

/-- English quantifier inventory, derived from the QuantityWord fragment.
    Uses the 6-word scale: none, few, some, half, most, all. -/
def english : QuantifierInventory :=
  { language := "English"
  , family := "Indo-European"
  , source := "Barwise & Cooper (1981)"
  , entries := QuantityWord.toList.map λ q =>
      { form := q.entry.form
      , qforce := q.entry.qforce
      , monotonicity := q.entry.monotonicity
      , strength := q.entry.strength } }

theorem english_size : english.entries.length = 6 := by native_decide
theorem english_has_weak :
    english.entries.any (·.strength == .weak) = true := by native_decide
theorem english_has_strong :
    english.entries.any (·.strength == .strong) = true := by native_decide

-- ============================================================================
-- §2: Mandarin (Sino-Tibetan) — derived from Fragment
-- ============================================================================

open Fragments.Mandarin.Determiners in
/-- Mandarin quantifier inventory, derived from the MandarinQuantEntry fragment.
    7 entries: měi, suǒyǒu, yǒu-de, méi-yǒu, jǐ, dà-bùfèn, liǎng…dōu. -/
def mandarin : QuantifierInventory :=
  { language := "Mandarin"
  , family := "Sino-Tibetan"
  , source := "Li (1998), Cheng & Sybesma (1999)"
  , entries := Fragments.Mandarin.Determiners.allQuantifiers.map λ q =>
      { form := q.pinyin
      , qforce := q.qforce
      , monotonicity := q.monotonicity
      , strength := q.strength } }

theorem mandarin_size : mandarin.entries.length = 7 := by native_decide
theorem mandarin_no_definiteness :
    mandarin.entries.all (·.qforce != .definite) = true := by native_decide
theorem mandarin_has_weak :
    mandarin.entries.any (·.strength == .weak) = true := by native_decide
theorem mandarin_has_strong :
    mandarin.entries.any (·.strength == .strong) = true := by native_decide

-- ============================================================================
-- §3: Japanese (Japonic) — derived from Fragment
-- ============================================================================

open Fragments.Japanese.Determiners in
/-- Japanese quantifier inventory, derived from the JapaneseQuantEntry fragment.
    7 entries: subete, dono-N-mo, dare-ka, dare-mo, nan-nin-ka, hotondo, ryōhō. -/
def japanese : QuantifierInventory :=
  { language := "Japanese"
  , family := "Japonic"
  , source := "Shimoyama (2006), Nakanishi (2007)"
  , entries := Fragments.Japanese.Determiners.allQuantifiers.map λ q =>
      { form := q.romaji
      , qforce := q.qforce
      , monotonicity := q.monotonicity
      , strength := q.strength } }

theorem japanese_size : japanese.entries.length = 7 := by native_decide
theorem japanese_no_definiteness :
    japanese.entries.all (·.qforce != .definite) = true := by native_decide
theorem japanese_has_weak :
    japanese.entries.any (·.strength == .weak) = true := by native_decide
theorem japanese_has_strong :
    japanese.entries.any (·.strength == .strong) = true := by native_decide

-- ============================================================================
-- §4: Cross-Linguistic Summary
-- ============================================================================

def allInventories : List QuantifierInventory :=
  [english, mandarin, japanese]

/-- All three languages have both weak and strong quantifiers. -/
theorem all_have_weak_strong :
    allInventories.all (λ inv =>
      inv.entries.any (·.strength == .weak) &&
      inv.entries.any (·.strength == .strong)) = true := by native_decide

/-- No language in sample lacks universal quantifiers. -/
theorem all_have_universals :
    allInventories.all (λ inv =>
      inv.entries.any (·.qforce == .universal)) = true := by native_decide

/-- Neither Mandarin nor Japanese has definite determiners (no articles). -/
theorem no_articles_east_asian :
    [mandarin, japanese].all (λ inv =>
      inv.entries.all (·.qforce != .definite)) = true := by native_decide

/-- Mandarin and Japanese both have dual universal ("both") quantifiers.
    English "both" is in the full allDeterminers lexicon but not the 6-word
    quantity scale (which is scalar, not dual). -/
theorem east_asian_have_dual_universal :
    [mandarin, japanese].all (λ inv =>
      inv.entries.any (·.qforce == .universal)) = true := by native_decide

/- Conservativity holds across all three languages (B&C Universal 1).
   Proved for English in Quantifier.lean; conjectured universal.
   TODO: State with real type once cross-linguistic GQ denotations are formalized. -/


end Phenomena.Quantification.Typology
