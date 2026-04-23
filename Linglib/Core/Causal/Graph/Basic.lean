import Linglib.Core.Causal.Graph.Defs
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

namespace Core.Causal.CausalGraph

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

/-- **Depth-based IsDAG construction**: a graph is acyclic if every edge
    strictly decreases some `ℕ`-valued depth function (parent depth <
    child depth). Reuses `Subrelation.wf` over `InvImage Nat.lt depth`,
    which is well-founded by `Nat`'s standard wellfoundedness.

    The standard mathlib pattern for proving wellfoundedness of finite
    inductive relations: define a measure into `ℕ`, show the relation
    decreases it, conclude. -/
theorem IsDAG.of_depth (G : CausalGraph V) (depth : V → ℕ)
    (hdepth : ∀ {u v : V}, u ∈ G.parents v → depth u < depth v) :
    IsDAG G where
  wf := by
    have hsub : ∀ u v, G.IsStrictAncestor u v → depth u < depth v := by
      intro u v huv
      induction huv with
      | single hp => exact hdepth hp
      | tail _ hp ih => exact lt_trans ih (hdepth hp)
    exact Subrelation.wf (fun {a b} => hsub a b)
      (InvImage.wf depth Nat.lt_wfRel.wf)

end Core.Causal.CausalGraph
