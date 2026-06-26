/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language

/-!
# Named Constraints

The framework-neutral constraint vocabulary shared by Optimality Theory and
Harmonic Grammar: a `NamedConstraint` is a violation-counting function with a
faithfulness/markedness label.

## Main definitions

* `ConstraintFamily` — the faithfulness/markedness distinction.
* `NamedConstraint` — a named violation-counting constraint over candidates.
* `mkMark` / `mkFaith` / `mkMarkGrad` / `mkFaithGrad` — constraint constructors.
* `NamedConstraint.comap` — pull a constraint back along a candidate map.
* `NamedConstraint.zeroSet` — the zero-violation language of a constraint.
-/

namespace Constraints

/-- Constraint families in OT. -/
inductive ConstraintFamily where
  /-- Faithfulness: penalizes deviation from the input. -/
  | faithfulness
  /-- Markedness: penalizes marked structures in the output. -/
  | markedness
  deriving DecidableEq, Repr

/-- A named OT constraint: a violation-counting function tagged with a
    faithfulness/markedness family. -/
structure NamedConstraint (C : Type*) where
  /-- Documentary label; no evaluation reads it. Defaults to `""`. -/
  name : String := ""
  /-- Faithfulness/markedness classification. -/
  family : ConstraintFamily
  /-- Number of violations a candidate incurs. -/
  eval : C → Nat

/-! ### Constraint constructors -/

variable {C D : Type*}

/-- A binary markedness constraint: `1` if `P c`, else `0`. `P` is a decidable
    predicate, so call sites use propositional `=` rather than `Bool` `==`. -/
def mkMark (name : String) (P : C → Prop) [DecidablePred P] : NamedConstraint C :=
  { name, family := .markedness, eval := fun c => if P c then 1 else 0 }

/-- A binary faithfulness constraint: `1` if `P c`, else `0`. The faithfulness
    twin of `mkMark`. -/
def mkFaith (name : String) (P : C → Prop) [DecidablePred P] : NamedConstraint C :=
  { name, family := .faithfulness, eval := fun c => if P c then 1 else 0 }

/-- A gradient markedness constraint with a `Nat`-valued violation count. -/
def mkMarkGrad (name : String) (violations : C → Nat) : NamedConstraint C :=
  { name, family := .markedness, eval := violations }

/-- A gradient faithfulness constraint with a `Nat`-valued violation count. -/
def mkFaithGrad (name : String) (violations : C → Nat) : NamedConstraint C :=
  { name, family := .faithfulness, eval := violations }

/-- Pull a `NamedConstraint D` back along `f : C → D`: compose `eval` with `f`,
    inherit `name` and `family`. Lets a specific carrier reuse a constraint
    defined on a more general one. -/
def NamedConstraint.comap (f : C → D) (c : NamedConstraint D) : NamedConstraint C :=
  { name := c.name, family := c.family, eval := c.eval ∘ f }

@[simp] theorem NamedConstraint.comap_eval (f : C → D) (c : NamedConstraint D) (x : C) :
    (c.comap f).eval x = c.eval (f x) := rfl

@[simp] theorem NamedConstraint.comap_name (f : C → D)
    (c : NamedConstraint D) : (c.comap f).name = c.name := rfl

@[simp] theorem NamedConstraint.comap_family (f : C → D)
    (c : NamedConstraint D) : (c.comap f).family = c.family := rfl

variable {α : Type*}

/-- The language of list candidates that satisfy `c` (zero violations), as a
`Language α`. Lets the `eval = 0` predicate compose with `Language.IsRegular`
and the project's subregular classifiers (`IsTierStrictlyLocal`, `IsBTC`). -/
def NamedConstraint.zeroSet (c : NamedConstraint (List α)) : Language α :=
  { w | c.eval w = 0 }

theorem NamedConstraint.mem_zeroSet (c : NamedConstraint (List α)) (w : List α) :
    w ∈ c.zeroSet ↔ c.eval w = 0 := Iff.rfl

end Constraints
