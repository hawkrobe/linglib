module

public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Semantics.Composition.Tree

/-!
# Coordination in the composition engine

This file adds coordination to the composition engine of `Composition/Tree.lean` as a binary
mode beside functional application, intensional application and predicate modification. Two
sisters of the same conjoinable type combine by the denotation of the coordinator's semantic
type on the pair, `Coordinator.Role.denote`, in the pointwise complete Boolean algebra of that
type, which the mode finds at runtime through `Ty.Domain.completeBooleanAlgebra?`. Predicate
modification is the conjunctive case at `⟨e,t⟩`, so the engine's modification mode already
agrees with the coordinator's denotation.

## Main definitions

* `Semantics.Composition.Tree.coordinate?`: the coordination mode.

## Main results

* `predicateModification?_eq_coordinate?_conjunctive`: predicate modification is conjunctive
  coordination at `⟨e,t⟩`.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

namespace Semantics.Composition.Tree

open Semantics.Composition

/-- `coordinate? role d1 d2` combines two sisters of the same conjoinable type by
`role.denote` on the pair, in the complete Boolean algebra of their type, threaded through the
effect `M`, and is `none` on sisters of different or non-conjoinable types. -/
def coordinate? {E W : Type} {M : Type → Type} [Applicative M] (role : Coordinator.Role)
    (d1 d2 : Denotation E W M) : Option (Denotation E W M) :=
  if h : d1.1 = d2.1 then
    (Ty.Domain.completeBooleanAlgebra? E W d1.1).map
      fun (i : CompleteBooleanAlgebra (Ty.Domain E W d1.1)) =>
        ⟨d1.1, (fun p q ↦ letI := i; role.denote {p, q}) <$> d1.2 <*> (h ▸ d2.2)⟩
  else none

/-- Predicate modification is generalized conjunction at `⟨e,t⟩`. -/
theorem predicateModification?_eq_coordinate?_conjunctive {E W : Type} {M : Type → Type}
    [Applicative M] (d1 d2 : Denotation E W M) (h1 : d1.1 = (.e ⇒ .t)) (h2 : d2.1 = (.e ⇒ .t)) :
    predicateModification? d1 d2 = coordinate? .conjunctive d1 d2 := by
  obtain ⟨t1, v1⟩ := d1
  obtain ⟨t2, v2⟩ := d2
  subst h1; subst h2
  have h : (Modifier.intersective : Ty.Domain E W (.e ⇒ .t) → _) =
      fun p q ↦ Coordinator.Role.denote .conjunctive {p, q} := by
    funext p q; simp [Modifier.intersective]
  exact congrArg (fun F ↦ some (⟨.e ⇒ .t, F <$> v1 <*> v2⟩ : Denotation E W M)) h

end Semantics.Composition.Tree
