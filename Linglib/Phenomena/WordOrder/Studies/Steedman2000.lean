import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Phenomena.WordOrder.Basic

/-!
# CCG Derivations of Word Order
@cite{steedman-2000}

CCG encodes word order through slash direction:

    TV = (S\NP)/NP

This means TV looks RIGHT for an NP (the object) first, then the
resulting (S\NP) looks LEFT for an NP (the subject). This enforces
SVO order. SOV "John Mary sees" would require the verb to look left
for both arguments, but TV looks right first.
-/

namespace Phenomena.WordOrder.Studies.Steedman2000

open CCG
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

end Phenomena.WordOrder.Studies.Steedman2000
