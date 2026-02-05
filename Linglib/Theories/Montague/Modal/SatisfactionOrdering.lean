import Linglib.Core.OrderTheory

/-!
# Satisfaction Ordering (Linguistic Instantiations)

Linguistic applications of `Core.OrderTheory.SatisfactionOrdering`:
- Kratzer's world ordering (worlds by propositions)
- Phillips-Brown's proposition ordering (propositions by desires)
-/

namespace Montague.Modal

open Core.OrderTheory (SatisfactionOrdering)

-- Re-export for backwards compatibility
export Core.OrderTheory (SatisfactionOrdering)

/-- Kratzer's world ordering: w satisfies p iff p(w) = true. -/
def worldOrdering (World : Type*) (props : List (World → Bool)) :
    SatisfactionOrdering World (World → Bool) where
  satisfies := λ w p => p w
  criteria := props

/-- Phillips-Brown's proposition ordering: a satisfies p iff a entails p. -/
def propositionOrdering (World : Type*) [BEq World] (worlds : List World)
    (desires : List (World → Bool)) :
    SatisfactionOrdering (World → Bool) (World → Bool) where
  satisfies := λ a p => worlds.all λ w => !a w || p w
  criteria := desires

/-- Proposition entailment: a entails p iff every a-world is a p-world. -/
def propEntails {World : Type*} (worlds : List World) (a p : World → Bool) : Bool :=
  worlds.all λ w => !a w || p w

end Montague.Modal
