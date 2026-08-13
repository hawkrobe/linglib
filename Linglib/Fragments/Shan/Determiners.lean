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

/-- *nâj* 'this', the proximal demonstrative, which obligatorily expones no
    definite use. -/
def naj : DemonstrativeDeterminer := { form := "nâj", deictic := .proximal }

/-- *nân* 'that', the distal demonstrative, which obligatorily expones no
    definite use. -/
def nan : DemonstrativeDeterminer := { form := "nân", deictic := .distal }

/-- The Shan determiners are the optional demonstratives *nâj/nân*. -/
def inventory : Determiner.Inventory := [.demonstrative naj, .demonstrative nan]

/-- Shan derives the `.unmarked` Moroney cell. -/
theorem marking : inventory.markingStrategy = .unmarked := by decide

/-- Both Shan demonstratives encode a distance contrast. -/
theorem naj_nan_encode_distance :
    (Demonstrative.deixis naj).EncodesDistance ∧
    (Demonstrative.deixis nan).EncodesDistance := by decide

end Shan.Determiners
