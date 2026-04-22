import Linglib.Core.Causal.V2.Graph.Defs
import Mathlib.Order.RelClasses
import Mathlib.Logic.Relation

/-!
# CausalGraph: Acyclicity, Ancestor Relation (V2)

`IsDAG` is a `Prop` mixin class on `CausalGraph V` (mirroring
`IsMarkovKernel` from `Mathlib/Probability/Kernel/Defs.lean`): required
only by operations that genuinely need acyclicity (topological sort,
well-founded fixpoint induction).

The ancestor relation uses `Relation.ReflTransGen` directly (no
intermediate adapter); consumers can use mathlib's existing API for
reflexive-transitive closures.
-/

namespace Core.Causal.V2.CausalGraph

variable {V : Type*}

/-- `IsAncestor G u v` iff there is a chain `v ← w₁ ← ... ← u` via `parents`.
    Defined via mathlib's `Relation.ReflTransGen` over the inlined
    "is-parent-of" relation. -/
def IsAncestor (G : CausalGraph V) : V → V → Prop :=
  Relation.ReflTransGen (fun u v => u ∈ G.parents v)

/-- `IsStrictAncestor G u v` iff there is a *nonempty* chain via `parents`.
    Defined via mathlib's `Relation.TransGen`. -/
def IsStrictAncestor (G : CausalGraph V) : V → V → Prop :=
  Relation.TransGen (fun u v => u ∈ G.parents v)

/-- **Acyclicity mixin**: the strict-ancestor relation is well-founded —
    no infinite chain of parents. Required by `topologicalOrder`,
    `develop` fixpoint, and well-founded recursion over the parent
    relation.

    Mathlib analogue: `IsMarkovKernel` from
    `Mathlib.Probability.Kernel.Defs` — a `Prop` class on a value of a
    structure, marking a property consumers may require.

    A `Std.Irrefl` instance for `IsStrictAncestor` follows from
    well-foundedness; deferred until a consumer needs it. -/
class IsDAG (G : CausalGraph V) : Prop where
  /-- The strict-ancestor relation has no infinite descending chain. -/
  wf : WellFounded G.IsStrictAncestor

end Core.Causal.V2.CausalGraph
