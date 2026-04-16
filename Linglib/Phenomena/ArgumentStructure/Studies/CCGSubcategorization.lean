import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Phenomena.ArgumentStructure.Subcategorization

/-!
# Bridge: CCG → Subcategorization Data

Connects CCG category assignments to the subcategorization data in
`Phenomena/ArgumentStructure/Subcategorization.lean`.

CCG captures subcategorization through category assignment:

    IV = S\NP (intransitive: needs subject only)
    TV = (S\NP)/NP (transitive: needs object then subject)
    DTV = ((S\NP)/NP)/NP (ditransitive: needs two objects then subject)

A verb assigned TV cannot appear without an object (no valid derivation),
and a verb assigned IV cannot take one. These are implicit category-theoretic
failures: no valid derivation exists.
-/

namespace CCGSubcategorization

open CCG

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

end CCGSubcategorization
