import Linglib.Syntax.Category.Determiner.Basic

/-!
# Shan determiner inventory

Shan (Southwestern Tai, Kra-Dai) has no overt definite or indefinite
articles, and its demonstratives *nâj/nân* are optional in anaphoric
contexts, so bare nouns express both unique and anaphoric definiteness.

## References

* [moroney-2021]
-/

namespace Shan.Determiners

/-- The Shan determiners are the optional demonstratives *nâj/nân*, which
    obligatorily expone no definite use, and a possessive form. -/
def inventory : Determiner.Inventory :=
  [ .demonstrative { form := "nâj", deictic := .proximal, definiteUses := [] },
    .demonstrative { form := "nân", deictic := .distal, definiteUses := [] },
    .possessive { form := "POSS" } ]

/-- Shan derives the `.unmarked` Moroney cell. -/
theorem marking : inventory.markingStrategy = .unmarked := by decide

end Shan.Determiners
