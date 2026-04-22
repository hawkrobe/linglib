import Linglib.Core.Causal.V2.Graph.Defs
import Mathlib.Order.RelClasses
import Mathlib.Logic.Relation

/-!
# CausalGraph: Acyclicity, Ancestor Relation (V2)

`IsDAG` is a `Prop` mixin class on `CausalGraph V` (mirroring
`IsMarkovKernel` from `Mathlib/Probability/Kernel/Defs.lean`): it's
required only by operations that genuinely need acyclicity (topological
sort, well-founded fixpoint induction). Parent lookup and root detection
in `Graph/Defs.lean` work for any graph.

The ancestor relation is defined via `Relation.ReflTransGen` from mathlib —
the standard reflexive-transitive closure construction.
-/

namespace Core.Causal.V2.CausalGraph

variable {V : Type*}

/-- The "is parent of" relation lifted from `parents : V → Finset V`. -/
def parentRel (G : CausalGraph V) : V → V → Prop :=
  fun u v => u ∈ G.parents v

/-- `IsAncestor G u v` iff there is a chain `v ← w₁ ← ... ← u` via `parents`.
    Defined via mathlib's `Relation.ReflTransGen`. -/
def IsAncestor (G : CausalGraph V) : V → V → Prop :=
  Relation.ReflTransGen G.parentRel

/-- `IsStrictAncestor G u v` iff there is a *nonempty* chain via `parents`.
    Defined via mathlib's `Relation.TransGen`. -/
def IsStrictAncestor (G : CausalGraph V) : V → V → Prop :=
  Relation.TransGen G.parentRel

theorem IsAncestor.refl (G : CausalGraph V) (v : V) : G.IsAncestor v v :=
  Relation.ReflTransGen.refl

theorem IsAncestor.trans {G : CausalGraph V} {u v w : V}
    (h₁ : G.IsAncestor u v) (h₂ : G.IsAncestor v w) : G.IsAncestor u w :=
  Relation.ReflTransGen.trans h₁ h₂

/-- **Acyclicity mixin**: the strict-ancestor relation is well-founded, i.e.,
    every nonempty chain of parents must terminate. Equivalent to "no
    nontrivial cycles" in the standard graph-theoretic sense.

    Mathlib analogue: `IsMarkovKernel` from `Mathlib.Probability.Kernel.Defs` —
    a `Prop` class on a value of a structure, marking a property that
    consumers (`topologicalOrder`, `develop` fixpoint) may require.
    `WellFounded` chosen because it directly enables well-founded recursion
    over the parent relation. -/
class IsDAG (G : CausalGraph V) : Prop where
  /-- The strict-ancestor relation has no infinite descending chain. -/
  wf : WellFounded G.IsStrictAncestor

end Core.Causal.V2.CausalGraph
