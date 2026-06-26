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

The tableau/violation-profile vocabulary built on these lives in
`Constraints.Profile`; the lexicographic tableau machinery proper lives in
`OptimalityTheory`.
-/

namespace Constraints

/-- Constraint families in OT. -/
inductive ConstraintFamily where
  /-- Faithfulness: penalizes deviation from the input. -/
  | faithfulness
  /-- Markedness: penalizes marked structures in the output. -/
  | markedness
  deriving DecidableEq, Repr

/-- A named OT constraint with family classification.
    `eval c` returns the number of violations candidate `c` incurs.

    The `name` field is purely documentary — no evaluation function reads it.
    It defaults to `""` so constraints can be defined without a name when
    the string label adds no information. -/
structure NamedConstraint (C : Type*) where
  name : String := ""
  family : ConstraintFamily
  eval : C → Nat

-- ============================================================================
-- § 1b: Constraint Constructors
-- ============================================================================

variable {C D : Type*}

/-- Build a binary markedness constraint (violated → 1, otherwise 0).

    Takes a `Prop`-valued predicate with `[DecidablePred]` so that callers
    can use propositional equality (`=`) and other Prop predicates rather
    than `Bool`-valued operators (`==`). Decidability is required to evaluate
    the constraint on a candidate. -/
def mkMark (name : String) (P : C → Prop) [DecidablePred P] :
    NamedConstraint C :=
  { name, family := .markedness, eval := fun c => if P c then 1 else 0 }

/-- Build a binary faithfulness constraint (violated → 1, otherwise 0).

    Takes a `Prop`-valued predicate with `[DecidablePred]` so that callers
    can use propositional equality (`=`) and other Prop predicates rather
    than `Bool`-valued operators (`==`). -/
def mkFaith (name : String) (P : C → Prop) [DecidablePred P] :
    NamedConstraint C :=
  { name, family := .faithfulness, eval := fun c => if P c then 1 else 0 }

/-- Build a gradient markedness constraint with a Nat-valued violation count. -/
def mkMarkGrad (name : String) (violations : C → Nat) : NamedConstraint C :=
  { name, family := .markedness, eval := violations }

/-- Build a gradient faithfulness constraint with a Nat-valued violation count. -/
def mkFaithGrad (name : String) (violations : C → Nat) : NamedConstraint C :=
  { name, family := .faithfulness, eval := violations }

/-- Pull a `NamedConstraint D` back along a candidate map `f : C → D`. The
    name and family are inherited; the new `eval` composes the original
    with the projection. Lets paper-specific carrier types reuse a
    constraint defined on a more general carrier. -/
def NamedConstraint.comap (f : C → D) (c : NamedConstraint D) :
    NamedConstraint C :=
  { name := c.name, family := c.family, eval := c.eval ∘ f }

@[simp] theorem NamedConstraint.comap_eval (f : C → D)
    (c : NamedConstraint D) (x : C) :
    (c.comap f).eval x = c.eval (f x) := rfl

@[simp] theorem NamedConstraint.comap_name (f : C → D)
    (c : NamedConstraint D) : (c.comap f).name = c.name := rfl

@[simp] theorem NamedConstraint.comap_family (f : C → D)
    (c : NamedConstraint D) : (c.comap f).family = c.family := rfl

variable {α : Type*}

/-- The zero-violation set of a `NamedConstraint` over list candidates,
viewed as a `Language α`. Lets the OT-side `eval = 0` predicate compose
with mathlib's `Language.IsRegular` and the project's
`IsTierStrictlyLocal`/`IsBTC` classifiers. The dot-notation form
`c.zeroSet` is the canonical access pattern. -/
def NamedConstraint.zeroSet (c : NamedConstraint (List α)) :
    Language α :=
  { w | c.eval w = 0 }

lemma NamedConstraint.mem_zeroSet
    (c : NamedConstraint (List α)) (w : List α) :
    w ∈ c.zeroSet ↔ c.eval w = 0 := Iff.rfl

end Constraints
