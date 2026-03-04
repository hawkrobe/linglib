import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Derivation
import Linglib.Theories.Syntax.Minimalism.Core.FromFragments
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns

/-!
# Minimalist Derivations

Minimalist Program derivations using the Fragments lexicon, expressed as
`Derivation` structures with step-by-step Merge operations.

## Architecture

  Fragments/English/... → Lexical entries (VerbEntry, PronounEntry, etc.)
          ↓
  Theories/Minimalism/FromFragments → Interpretation: Entry → SyntacticObject
          ↓
  Theories/Minimalism/Derivations → Minimalist derivations (this file)
-/

namespace Minimalism.Phenomena.Derivations

open Minimalism
open Minimalism.Core.FromFragments
open Fragments.English.Lexicon (LexResult)

-- ============================================================================
-- Lexical Items from Fragments (as formal SyntacticObjects)
-- ============================================================================

-- Pronouns
private def heSO : SyntacticObject :=
  pronounToSO Fragments.English.Pronouns.he 1
private def herSO : SyntacticObject :=
  pronounToSO Fragments.English.Pronouns.her 2
private def _theySO : SyntacticObject :=
  pronounToSO Fragments.English.Pronouns.they 3

-- Proper nouns
private def johnSO : SyntacticObject :=
  nounToSO Fragments.English.Nouns.john 10
private def marySO : SyntacticObject :=
  nounToSO Fragments.English.Nouns.mary 11

-- Common nouns
private def catSO : SyntacticObject :=
  nounToSO Fragments.English.Nouns.cat 20
private def pizzaSO : SyntacticObject :=
  nounToSO Fragments.English.Nouns.pizza 21
private def bookSO : SyntacticObject :=
  nounToSO Fragments.English.Nouns.book 22

-- Verbs
private def sleepsSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.sleep 30
private def seesSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.see 31
private def eatsSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.eat 32
private def arrivesSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.arrive 33
private def devoursSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.devour 34
private def givesSO : SyntacticObject :=
  verbToSO Fragments.English.Predicates.Verbal.give 35

-- Determiner
private def theSO : SyntacticObject :=
  mkLeafPhon .D [.N] "the" 40

-- ============================================================================
-- Word Order Derivations
-- ============================================================================

section WordOrder

/-- "John sees Mary": `[S John [VP sees Mary]]` -/
def john_sees_mary : Derivation :=
  { initial := seesSO
    steps := [.emR marySO, .emL johnSO] }

/-- "Mary eats pizza": `[S Mary [VP eats pizza]]` -/
def mary_eats_pizza : Derivation :=
  { initial := eatsSO
    steps := [.emR pizzaSO, .emL marySO] }

/-- "He sees her": `[S he [VP sees her]]` -/
def he_sees_her : Derivation :=
  { initial := seesSO
    steps := [.emR herSO, .emL heSO] }

/-- "The cat eats pizza": `[S [DP the cat] [VP eats pizza]]` -/
def the_cat_eats_pizza : Derivation :=
  { initial := eatsSO
    steps := [.emR pizzaSO, .emL (merge theSO catSO)] }

theorem john_sees_mary_phon :
    john_sees_mary.final.phonYield = ["John", "sees", "Mary"] := by native_decide

theorem mary_eats_pizza_phon :
    mary_eats_pizza.final.phonYield = ["Mary", "eats", "pizza"] := by native_decide

theorem he_sees_her_phon :
    he_sees_her.final.phonYield = ["he", "sees", "her"] := by native_decide

theorem the_cat_eats_pizza_phon :
    the_cat_eats_pizza.final.phonYield = ["the", "cat", "eats", "pizza"] := by
  native_decide

end WordOrder

-- ============================================================================
-- Subcategorization Derivations
-- ============================================================================

section Subcategorization

/-- "John sleeps": `[S John sleeps]` -/
def john_sleeps : Derivation :=
  { initial := sleepsSO
    steps := [.emL johnSO] }

/-- "Mary arrives": `[S Mary arrives]` -/
def mary_arrives : Derivation :=
  { initial := arrivesSO
    steps := [.emL marySO] }

/-- "John devours pizza": `[S John [VP devours pizza]]` -/
def john_devours_pizza : Derivation :=
  { initial := devoursSO
    steps := [.emR pizzaSO, .emL johnSO] }

/-- "Mary sees John": `[S Mary [VP sees John]]` -/
def mary_sees_john : Derivation :=
  { initial := seesSO
    steps := [.emR johnSO, .emL marySO] }

/-- "John gives Mary the book": `[S John [VP [V' gives book] Mary]]` -/
def john_gives_mary_book : Derivation :=
  { initial := givesSO
    steps := [.emR bookSO, .emR marySO, .emL johnSO] }

theorem john_sleeps_phon :
    john_sleeps.final.phonYield = ["John", "sleeps"] := by native_decide

theorem mary_arrives_phon :
    mary_arrives.final.phonYield = ["Mary", "arrives"] := by native_decide

theorem john_devours_pizza_phon :
    john_devours_pizza.final.phonYield = ["John", "devours", "pizza"] := by native_decide

theorem mary_sees_john_phon :
    mary_sees_john.final.phonYield = ["Mary", "sees", "John"] := by native_decide

theorem john_gives_mary_book_phon :
    john_gives_mary_book.final.phonYield = ["John", "gives", "book", "Mary"] := by
  native_decide

end Subcategorization

end Minimalism.Phenomena.Derivations
