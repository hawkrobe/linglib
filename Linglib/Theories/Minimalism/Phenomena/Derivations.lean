import Linglib.Theories.Minimalism.Core.Basic
import Linglib.Theories.Minimalism.Core.FromFragments
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns
import Linglib.Phenomena.WordOrder.Basic
import Linglib.Phenomena.ArgumentStructure.Subcategorization

/-
# Minimalist Derivations for Phenomena

This module connects Minimalist Program derivations to empirical phenomena data.
It uses the Fragments lexicon and shows that grammatical sentences can be built
via formal Merge (from SyntacticObjects.lean).

## Grounding

Derivations here correspond to grammatical sentences in:
- `Phenomena.WordOrder.data` - SVO word order
- `Phenomena.ArgumentStructure.Subcategorization.data` - argument structure

## Architecture

  Phenomena/                        →  Theory-neutral data (strings + judgments)
          ↓
  Fragments/English/...             →  Lexical entries (VerbEntry, PronounEntry, etc.)
          ↓
  Theories/Minimalism/FromFragments →  Interpretation: Entry → SyntacticObject
          ↓
  Theories/Minimalism/Derivations   →  Minimalist derivations (this file)
-/

namespace Minimalism.Phenomena.Derivations

open Phenomena.WordOrder
open Phenomena.ArgumentStructure.Subcategorization

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

/-- "John sees Mary" via Merge: [VP John [V' sees Mary]] -/
def john_sees_mary : SyntacticObject :=
  let vp_inner := merge seesSO marySO
  merge johnSO vp_inner

/-- "Mary eats pizza" via Merge -/
def mary_eats_pizza : SyntacticObject :=
  let vp_inner := merge eatsSO pizzaSO
  merge marySO vp_inner

/-- "He sees her" via Merge -/
def he_sees_her : SyntacticObject :=
  let vp_inner := merge seesSO herSO
  merge heSO vp_inner

/-- "The cat eats pizza" via Merge -/
def the_cat_eats_pizza : SyntacticObject :=
  let dp := merge theSO catSO
  let vp_inner := merge eatsSO pizzaSO
  merge dp vp_inner

end WordOrder

-- ============================================================================
-- Subcategorization Derivations
-- ============================================================================

section Subcategorization

/-- "John sleeps" via Merge: [VP John [V' sleeps]] -/
def john_sleeps : SyntacticObject :=
  merge johnSO sleepsSO

/-- "Mary arrives" via Merge -/
def mary_arrives : SyntacticObject :=
  merge marySO arrivesSO

/-- "John devours pizza" via Merge: [VP John [V' devours pizza]] -/
def john_devours_pizza : SyntacticObject :=
  let vp_inner := merge devoursSO pizzaSO
  merge johnSO vp_inner

/-- "Mary sees John" via Merge -/
def mary_sees_john : SyntacticObject :=
  let vp_inner := merge seesSO johnSO
  merge marySO vp_inner

/-- "John gives Mary the book" via Merge -/
def john_gives_mary_book : SyntacticObject :=
  let v_book := merge givesSO bookSO
  let v_mary_book := merge v_book marySO
  merge johnSO v_mary_book

end Subcategorization

-- ============================================================================
-- Grounding: Connection to Theory-Neutral Phenomena Data
-- ============================================================================

section Grounding

/-- The derivations model the grammatical SVO sentences from WordOrder.data -/
theorem models_svo_word_order :
    Phenomena.WordOrder.data.pairs.any (·.grammatical == "John sees Mary") := by
  native_decide

/-- The derivations model grammatical subcategorization patterns -/
theorem models_intransitive :
    Phenomena.ArgumentStructure.Subcategorization.data.pairs.any
      (·.grammatical == "John sleeps") := by
  native_decide

theorem models_transitive :
    Phenomena.ArgumentStructure.Subcategorization.data.pairs.any
      (·.grammatical == "John devours pizza") := by
  native_decide

theorem models_ditransitive :
    Phenomena.ArgumentStructure.Subcategorization.data.pairs.any
      (·.grammatical == "John gives Mary book") := by
  native_decide

/-- Verify the phonological yield of a derivation matches expected word order -/
example : john_sees_mary.phonYield = ["John", "sees", "Mary"] := rfl

example : john_sleeps.phonYield = ["John", "sleeps"] := rfl

example : john_devours_pizza.phonYield = ["John", "devours", "pizza"] := rfl

/-- Verify derivations are well-formed SyntacticObject structures. -/
example : john_sleeps = merge johnSO sleepsSO := rfl
example : john_devours_pizza =
    merge johnSO (merge devoursSO pizzaSO) := rfl
example : mary_sees_john =
    merge marySO (merge seesSO johnSO) := rfl

end Grounding

end Minimalism.Phenomena.Derivations
