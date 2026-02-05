/-
# CCG Derivations for Phenomena

This module connects CCG derivations to empirical phenomena data.
It imports from Phenomena/ and proves that CCG can derive the grammatical sentences.

## Architecture

  Phenomena/WordOrder/Basic.lean     →  Empirical data (no theory)
  Phenomena/ArgumentStructure/...    →  Empirical data (no theory)
          ↓
  Theories/CCG/Derivations.lean      →  CCG derivations + verification theorems
-/

import Linglib.Theories.CCG.Core.Basic
import Linglib.Phenomena.WordOrder.Basic
import Linglib.Phenomena.ArgumentStructure.Subcategorization

namespace CCG.Derivations

open CCG

-- ============================================================================
-- Word Order Derivations
-- ============================================================================

section WordOrder

open Phenomena.WordOrder

/-- "John sees Mary" = NP + (TV + NP) → S -/
def john_sees_mary : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))

/-- "Mary eats pizza" = NP + (TV + NP) → S -/
def mary_eats_pizza : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.fapp (.lex ⟨"eats", TV⟩) (.lex ⟨"pizza", NP⟩))

/-- "He sees her" = NP + (TV + NP) → S -/
def he_sees_her : DerivStep :=
  .bapp (.lex ⟨"he", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"her", NP⟩))

/-- "The cat eats pizza" = (Det + N) + (TV + NP) → S -/
def the_cat_eats_pizza : DerivStep :=
  .bapp (.fapp (.lex ⟨"the", Det⟩) (.lex ⟨"cat", N⟩))
        (.fapp (.lex ⟨"eats", TV⟩) (.lex ⟨"pizza", NP⟩))

-- Verification: grammatical SVO sentences derive category S

theorem john_sees_mary_derives_S : derivesS john_sees_mary = true := rfl
theorem mary_eats_pizza_derives_S : derivesS mary_eats_pizza = true := rfl
theorem he_sees_her_derives_S : derivesS he_sees_her = true := rfl
theorem the_cat_eats_pizza_derives_S : derivesS the_cat_eats_pizza = true := rfl

/-
CCG encodes word order through slash direction:

  TV = (S\NP)/NP

This means:
- TV looks RIGHT for an NP (the object) first
- Then the resulting (S\NP) looks LEFT for an NP (the subject)

This enforces SVO order. SOV "John Mary sees" would require the verb to
look left for both arguments, but TV looks right first.
-/

end WordOrder

-- ============================================================================
-- Subcategorization Derivations
-- ============================================================================

section Subcategorization

open Phenomena.ArgumentStructure.Subcategorization

/-- "John sleeps" = NP + IV → S -/
def john_sleeps : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩)

/-- "Mary arrives" = NP + IV → S -/
def mary_arrives : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"arrives", IV⟩)

/-- "John devours pizza" = NP + (TV + NP) → S -/
def john_devours_pizza : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"devours", TV⟩) (.lex ⟨"pizza", NP⟩))

/-- "Mary sees John" = NP + (TV + NP) → S -/
def mary_sees_john : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"John", NP⟩))

/-- "John gives Mary the book" = NP + ((DTV + NP) + NP) → S -/
def john_gives_mary_book : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩)
    (.fapp (.fapp (.lex ⟨"gives", DTV⟩) (.lex ⟨"Mary", NP⟩)) (.lex ⟨"book", NP⟩))

-- Verification: grammatical sentences derive category S

theorem john_sleeps_derives_S : derivesS john_sleeps = true := rfl
theorem mary_arrives_derives_S : derivesS mary_arrives = true := rfl
theorem john_devours_pizza_derives_S : derivesS john_devours_pizza = true := rfl
theorem mary_sees_john_derives_S : derivesS mary_sees_john = true := rfl
theorem john_gives_mary_book_derives_S : derivesS john_gives_mary_book = true := rfl

/-
CCG captures subcategorization through category assignment:

  IV  = S\NP           (intransitive: needs subject only)
  TV  = (S\NP)/NP      (transitive: needs object then subject)
  DTV = ((S\NP)/NP)/NP (ditransitive: needs two objects then subject)

* "John devours" fails: TV = (S\NP)/NP needs an NP on the right before
  it can combine with the subject.

* "John sleeps book" fails: IV = S\NP is fully saturated after combining
  with subject - no way to incorporate extra NP.

These are implicit category-theoretic failures: no valid derivation exists.
-/

end Subcategorization

end CCG.Derivations
