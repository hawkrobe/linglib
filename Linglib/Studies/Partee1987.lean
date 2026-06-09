import Linglib.Semantics.Composition.TypeShifting

/-!
# Partee (1987): Noun Phrase Interpretation and Type-shifting Principles
[partee-1987]

Partee's §5 sketches an analysis of English `be` as a type-shifting
functor that lowers a generalized quantifier (`⟨⟨e,t⟩,t⟩`) to a
predicate (`⟨e,t⟩`):

  BE = λQ.λx. Q(λy. y = x)  :  ⟨⟨e,t⟩,t⟩ → ⟨e,t⟩

The copula's combined effect for "John is a teacher" is then
`BE(⟦a teacher⟧)(⟦John⟧) = teacher'(john')`. On proper-name subjects
the composition reduces to the `ident` shift `λx. [j = x]`.

Partee's paper is about type-shifting principles in general; the `be`
treatment is one section's sketch, not the paper's main content, and
is explicitly framed as for English. Cross-linguistic predictions over
typological samples are outside the paper's scope and do not belong
in this study file.
-/

namespace Partee1987

open Semantics.Composition.TypeShifting (BE lift ident BE_lift_eq_ident)
open Core.Logic.Intensional (Denot Ty)

variable {E W : Type}

/-- ⟦be⟧ = BE: the copula IS the type-shifting functor, taking a
    generalized quantifier to a predicate. -/
abbrev be_sem (E W : Type) : Denot E W Ty.ett → Denot E W Ty.et := BE

/-- The copula is semantically transparent for proper names.
    "John is a teacher" with `⟦John⟧ = lift(j)`:
    `BE(lift(j)) = ident(j) = λx. [j = x]`. -/
theorem be_transparent (j : Denot E W .e) :
    be_sem E W (lift j) = ident j :=
  BE_lift_eq_ident j

end Partee1987
