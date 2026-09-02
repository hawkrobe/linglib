import Linglib.Syntax.Category.Coordinator
import Linglib.Semantics.Composition.Tree

/-!
# Coordination in the composition engine

`tryCoord` wires `Coordinator.op` into [heim-kratzer-1998] type-driven interpretation —
the composition-engine mode that is the sibling of `tryFA`/`tryIFA`/`tryPM`. `tryPM`
(intersective predicate modification) is its `⟨e,t⟩` conjunction case
(`tryPM_eq_tryCoord_j`), so the engine's existing modification mode already routes
through the Coordinator API.

`tryCoord` is an *engine* mode (the `tryX` convention), not part of the `Coordinator`
API surface: it dispatches on the sisters' type at runtime through
`Denot.booleanAlgebra?` and applies `Coordinator.op` in the algebra found.
-/

namespace Semantics.Composition.Tree

open Intensional

/-- **Coordination composition mode** — the sibling of `tryFA`/`tryIFA`/`tryPM`.
    Two same-conjoinable-type sisters combine via `Coordinator.op` in the Boolean algebra
    of their type, threaded through the effect functor `M`. Non-conjoinable or
    type-mismatched sisters yield `none`. -/
def tryCoord {E W : Type} {M : Type → Type} [Applicative M] (role : Coordinator.Role)
    (d1 d2 : TypedDenot E W M) : Option (TypedDenot E W M) :=
  if h : d1.ty = d2.ty then
    (Denot.booleanAlgebra? E W d1.ty).map fun (i : BooleanAlgebra (Denot E W d1.ty)) =>
      ⟨d1.ty, (letI := i; Coordinator.op role) <$> d1.val <*> (h ▸ d2.val)⟩
  else none

/-- `tryPM` is the `⟨e,t⟩` conjunction case of `tryCoord`: intersective predicate
    modification *is* generalized conjunction at `⟨e,t⟩`. -/
theorem tryPM_eq_tryCoord_j {E W : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot E W M) (h1 : d1.ty = (.e ⇒ .t)) (h2 : d2.ty = (.e ⇒ .t)) :
    tryPM d1 d2 = tryCoord .j d1 d2 := by
  obtain ⟨t1, v1⟩ := d1
  obtain ⟨t2, v2⟩ := d2
  subst h1; subst h2
  rfl

end Semantics.Composition.Tree
