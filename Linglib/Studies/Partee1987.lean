import Linglib.Semantics.Composition.TypeShifting
import Linglib.Fragments.English.Toy

/-!
# Partee (1987): Noun Phrase Interpretation and Type-shifting Principles

This file formalizes the treatment of the copula in [partee-1987]: among the type-shifting
principles that let a noun phrase denote an entity, a predicate, or a generalized quantifier
as its environment demands, English *be* is the functor `BE` that lowers a generalized
quantifier to a predicate, so that *John is a teacher* reduces to the predication of
*teacher* of John and, on a proper-name subject, to the identity shift `ident` (`be_sem`,
`be_transparent`).

## Implementation notes

The shifts live in `Semantics/Composition/TypeShifting`. Only the copula section of the paper
is formalized, and its sketch is explicitly about English, so it licenses no cross-linguistic
predictions.

## References

* [partee-1987]
-/

namespace Partee1987

open Quantification (BE individual)
open Semantics.Composition.TypeShifting (ident BE_individual_eq_ident)
open Semantics.Composition (Denot Ty)

variable {E W : Type}

/-- ⟦be⟧ = BE: the copula IS the type-shifting functor, taking a
    generalized quantifier to a predicate. -/
abbrev be_sem (E W : Type) : Denot E W Ty.ett → Denot E W Ty.et := BE

/-- The copula is semantically transparent for proper names.
    "John is a teacher" with `⟦John⟧ = individual(j)`:
    `BE(individual(j)) = ident(j) = λx. [j = x]`. -/
theorem be_transparent (j : Denot E W .e) :
    be_sem E W (individual j) = ident j :=
  BE_individual_eq_ident j

/-! ### Toy-fragment examples -/

section ToyExamples

open Semantics.Montague (ToyEntity)
open Semantics.Montague.ToyLexicon (john_sem sleeps_sem)

example : individual (α := ToyEntity) john_sem sleeps_sem :=
  show sleeps_sem john_sem from trivial

example : BE (E := ToyEntity) (individual john_sem) = ident john_sem :=
  BE_individual_eq_ident john_sem

end ToyExamples

end Partee1987
