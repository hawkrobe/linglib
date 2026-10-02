/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Person.Lattice

/-!
# Person resolution in a person system

A system without clusivity has no value for the join of a first and a second person, so it
resolves a coordination by coarsening the join into its values. In the tripartition resolution
then follows the hierarchy 1 > 2 > 3 of Corbett's resolution rules, which Zwicky states as the
order in which the persons are chosen.

## Main definitions

* `Person.coarsenTo`: coarsening a value into a system.
* `Person.resolveIn`, `Person.System.resolve`: resolution within a person system.

## Main results

* `Person.System.tripartition_resolve`: in the tripartition, resolution selects the more
  prominent conjunct.

## References

* [corbett-2006]
* [zwicky-1977b]
-/

@[expose] public section

namespace Person

/-- Coarsening into a system keeps a value the system has and otherwise collapses clusivity. -/
def coarsenTo (sys : List Person) (p : Person) : Person :=
  if p ∈ sys then p
  else if p.coarsen ∈ sys then p.coarsen
  else p

/-- Resolution within a system is the join coarsened into the system. -/
def resolveIn (sys : List Person) (a b : Person) : Person :=
  coarsenTo sys (a ⊔ b)

theorem resolveIn_comm (sys : List Person) (a b : Person) :
    resolveIn sys a b = resolveIn sys b a := by
  rw [resolveIn, resolveIn, sup_comm]

/-- `ns.resolve` is resolution within the values of the person system `ns`. -/
def System.resolve (ns : System) (a b : Person) : Person :=
  resolveIn ns.values a b

/-- In the tripartition, resolution selects the more prominent conjunct. -/
theorem System.tripartition_resolve :
    ∀ p ∈ tripartition.values, ∀ q ∈ tripartition.values,
      tripartition.resolve p q = if q.prominence ≤ p.prominence then p else q := by
  decide

end Person
