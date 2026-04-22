import Mathlib.Tactic.Common

/-!
# Variable: Named Causal Atoms (V2)

The default vertex carrier for theory-side SEMs. A `Variable` is just a
named atom; semantic content lives in mechanisms attached to vertices,
not in the variable itself.

`CausalGraph V` is generic in the vertex type `V`; `Variable` is the
canonical default. Use directly when you don't need polymorphism.
-/

namespace Core.Causal.V2

/-- A variable in a causal model: a named atom. Semantic content lives in
    the `Mechanism` attached to a vertex, not in the variable itself. -/
structure Variable where
  name : String
  deriving DecidableEq, Hashable, Repr, Inhabited

instance : BEq Variable where beq a b := decide (a = b)

instance : LawfulBEq Variable where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

instance : ToString Variable where
  toString v := v.name

/-- Create a variable from a string literal. -/
def mkVar (name : String) : Variable := ⟨name⟩

end Core.Causal.V2
