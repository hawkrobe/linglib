/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Control.Diagnostics

/-!
# Landau (2013): Control in Generative Grammar

[landau-2013]'s OC signature ((74), §1.3): in a control construction, (a) the
controller(s) must be co-dependent(s) of the clause, and (b) the controlled
element (or part of it) must be interpreted as a bound variable. The familiar
OC criteria are *derived* ((75)–(79)): co-dependence excludes arbitrary,
long-distance, and non-c-commanding control and forces sloppy ellipsis
readings; variable binding excludes strict readings under *only*. The
`Control.Excludes` instance records that derivation, and the general
`Control.Profile` machinery returns the book's characterizations: the OC
signature admits no criterial configuration, its NOC mirror (§7.1) admits
all.

Deliberately absent, per §1.3: obligatory *de se* is NOT criterial for OC —
it is an attitude-tier property. Per §1.4, the lexical-subject diagnostic is
rejected as an "obligatory nullness criterion" rather than an OC criterion —
the separation the overt-PRO studies (`Studies/Ostrove2026.lean`,
`Studies/Allotey2021.lean`) turn on. The full NOC signature (453) also adds a third, positive clause —
PRO is `[+human]` — which the book (tentatively) defends as irreducible
(§7.5; retracted by name in [landau-2024]); the
two-clause mirror covers only the criteria that (74)'s clauses derive.
-/

namespace Landau2013

open Control

/-- The two clauses of [landau-2013]'s OC signature ((74)): the
    co-dependence clause admits implicit, split, and (via "part of it")
    partial control. -/
inductive Clause74 where
  /-- (74a): the controller(s) must be co-dependent(s) of the clause. -/
  | codependent
  /-- (74b): the controlled element is interpreted as a bound variable. -/
  | boundVariable
  deriving DecidableEq, Repr, Fintype

/-- The derivation of the criteria from the signature ((75)–(79)):
    co-dependence excludes the three antecedence configurations and strict
    ellipsis readings; variable binding excludes strict *only*-readings. -/
instance : Excludes Clause74 where
  excludedBy
    | .strictUnderOnly => .boundVariable
    | _                => .codependent
  surjective := by
    rintro (_ | _)
    exacts [⟨.arbitraryControl, rfl⟩, ⟨.strictUnderOnly, rfl⟩]

/-- The profile determined by whether a clause type licenses
    noncoreferential subjects: free reference fails both clauses, obligatory
    coreference forces both. -/
def ofNoncoreferential (noncoreferential : Bool) : Profile Clause74 :=
  fun _ => !noncoreferential

@[simp] theorem isObligatory_ofNoncoreferential {b : Bool} :
    (ofNoncoreferential b).IsObligatory ↔ b = false := by
  cases b <;> decide

end Landau2013
