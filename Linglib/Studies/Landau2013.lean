/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Control.Diagnostics

/-!
# Landau (2013): Control in Generative Grammar: A Research Companion

This file formalizes the signature of obligatory control of [landau-2013]: the controller must
be a co-dependent of the clause, and the controlled element, or part of it, is interpreted as a
bound variable. The familiar criteria follow from the two clauses: co-dependence excludes
arbitrary, long-distance, and non-c-commanding control and forces the sloppy reading under
ellipsis, and variable binding excludes the strict reading under *only*. The `Control.Excludes`
instance records this derivation, so that the library's `Control.Profile` returns the book's
characterizations: a profile satisfying both clauses admits no criterial configuration and one
satisfying neither admits them all. `ofNoncoreferential` reads such a profile off whether a
clause type licenses a noncoreferential subject, which the studies of overt controlled subjects
consume.

## Implementation notes

The book was not available for this pass, and the example and section numbers carried over
from the earlier version of this file are marked as unverified. Obligatory *de se* is not
criterial for obligatory control, being a property of the attitude tier, and the lexical-subject
diagnostic is a criterion of obligatory nullness rather than of obligatory control, the
separation the overt-subject studies turn on; the positive human-reference clause of the
non-obligatory signature is not modelled.

## References

* [landau-2013]
-/

namespace Landau2013

open Control

-- UNVERIFIED: the signature is the book's (74), its derivation of the criteria (75)–(79).

/-- The two clauses of the signature of obligatory control: the co-dependence clause admits
implicit, split, and, through "part of it", partial control. -/
inductive Clause74 where
  /-- The controller or controllers must be co-dependents of the clause. -/
  | codependent
  /-- The controlled element is interpreted as a bound variable. -/
  | boundVariable
  deriving DecidableEq, Repr, Fintype

/-- The derivation of the criteria from the signature: co-dependence excludes the three
antecedence configurations and the strict ellipsis reading, variable binding the strict reading
under *only*. -/
instance : Excludes Clause74 where
  excludedBy
    | .strictUnderOnly => .boundVariable
    | _                => .codependent
  surjective := by
    rintro (_ | _)
    exacts [⟨.arbitraryControl, rfl⟩, ⟨.strictUnderOnly, rfl⟩]

/-- The profile determined by whether a clause type licenses noncoreferential subjects: free
reference fails both clauses, obligatory coreference satisfies both. -/
def ofNoncoreferential (noncoreferential : Bool) : Profile Clause74 :=
  λ _ => !noncoreferential

@[simp] theorem isObligatory_ofNoncoreferential {b : Bool} :
    (ofNoncoreferential b).IsObligatory ↔ b = false := by
  cases b <;> decide

end Landau2013
