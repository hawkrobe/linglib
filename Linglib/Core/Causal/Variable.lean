import Mathlib.Tactic.Common

/-!
# Variable: Named Causal Atoms (V2)

The default vertex carrier for theory-side SEMs. A `Variable` is just a
named atom; semantic content lives in mechanisms attached to vertices,
not in the variable itself.

`CausalGraph V` is generic in the vertex type `V`; `Variable` is the
canonical default. Use directly when you don't need polymorphism.
-/

namespace Core.Causal

/-- A variable in a causal model: a named atom. Semantic content lives in
    the `Mechanism` attached to a vertex, not in the variable itself.

    `BEq`/`LawfulBEq` are auto-derived from `DecidableEq` via
    `instBEqOfDecidableEq`. -/
structure Variable where
  name : String
  deriving DecidableEq, Hashable, Repr, Inhabited

instance : ToString Variable where
  toString v := v.name

end Core.Causal
