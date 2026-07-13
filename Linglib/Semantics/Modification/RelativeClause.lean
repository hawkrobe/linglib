import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Intensional.Variables
import Linglib.Semantics.Modification.Basic

/-!
# Relative-clause denotation
[heim-kratzer-1998]

The framework-neutral meaning of a head noun combined with a (restrictive)
relative clause: an RC is an **intersective clausal modifier** of the head. Its
modifier-property is the relative clause abstracted over its gap (Predicate
Abstraction, [heim-kratzer-1998] Ch. 5); modifying the head with it is the
intersective modification shared with adjectives and PPs. This is the
adnominal-modifier diagnostic (a relative clause's framework-neutral essence is
clausal modification of a nominal head) made compositional: the syntactic
frameworks differ in how they derive the gap abstraction (a Minimalist trace, an
HPSG `SLASH` discharge, a CCG type-raised argument) but converge on this
denotation.

This is the **semantic half of the `RelativeClause` API**; the classification half
(`Realization`, `AHPosition`, `NPRelType`, …) lives in `Syntax/RelativeClause/`,
sharing the root `RelativeClause` namespace without either importing the other.

## Main declarations

* `RelativeClause.denote` — the relative-clause denotation, built *by construction*
  as `Modification.intersective` applied to the gap-abstracted clause.
* `RelativeClause.denote_comm` — head and clause modify symmetrically.

## Implementation notes

Only the restrictive (intersective) denotation is provided; the non-restrictive
(appositive) denotation is a distinct, non-intersective mechanism and is deferred
until a study reifies it.
-/

namespace RelativeClause

open Intensional Intensional.Variables
open Modifier (intersective intersective_comm)

/--
The framework-neutral relative-clause denotation: the head modified by the
relative clause, qua intersective modifier.

For "the N that ... t_n ...":
1. abstract the relative clause over its gap, `λx. ⟦... t_n ...⟧^{g[n ↦ x]}`
   (Predicate Abstraction) — this is the RC's modifier-property;
2. modify the head noun with it intersectively (`Modification.intersective`).

Result: `λx. ⟦relative clause⟧(x) ∧ N(x)` — the head property intersected with the
abstracted clause property (the restrictive case; see the implementation note).
That the RC is an intersective modifier is true by construction.
-/
def denote {E W : Type} (n : ℕ)
    (headNoun : DenotG E W (.e ⇒ .t))
    (relClauseBody : DenotG E W .t)
    : DenotG E W (.e ⇒ .t) :=
  fun g => intersective (lambdaAbsG n relClauseBody g) (headNoun g)

/-- Head and relative clause modify symmetrically: the head noun and the
    gap-abstracted clause intersect in either order (intersective modification is
    commutative). -/
theorem denote_comm {E W : Type} (n : ℕ)
    (headNoun : DenotG E W (.e ⇒ .t))
    (relClauseBody : DenotG E W .t)
    (g : Core.Assignment E)
    : denote n headNoun relClauseBody g =
      intersective (headNoun g) (lambdaAbsG n relClauseBody g) := by
  show intersective (lambdaAbsG n relClauseBody g) (headNoun g) =
       intersective (headNoun g) (lambdaAbsG n relClauseBody g)
  exact intersective_comm _ _

end RelativeClause
