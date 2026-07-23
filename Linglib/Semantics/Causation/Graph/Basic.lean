import Linglib.Semantics.Causation.Graph.Defs
import Linglib.Core.Relation.ReflTransGen
import Mathlib.Order.RelClasses
import Mathlib.Logic.Relation

/-!
# CausalGraph: Acyclicity, Ancestor Relation

`IsDAG` is a `Prop` mixin class on `CausalGraph V` (mirroring
`IsMarkovKernel` from `Mathlib/Probability/Kernel/Defs.lean`): required
only by operations that genuinely need acyclicity (topological sort,
well-founded fixpoint induction).

The ancestor relation uses `Relation.ReflTransGen` directly (no
intermediate adapter); consumers can use mathlib's existing API for
reflexive-transitive closures.

Acyclicity certificates come bundled as `Ranking` (parents rank strictly
below children) and its strict-successor refinement `TimeIndex` (parents
immediately precede children, the time-indexed causal models of
[cao-white-lassiter-2025]); `IsDAG.of_depth` passes the loose form.
-/

namespace Causation.CausalGraph

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

/-- `Decidable (G.IsAncestor u v)` via the `Core.Relation.ReflTransGen`
substrate's `Fintype` headline. The relation `fun u v => u ∈ G.parents v`
has decidable successors `G.children u` (already defined as
`Finset.univ.filter (v ∈ G.parents ·)` in `Defs.lean`). -/
instance IsAncestor.decidable [Fintype V] [DecidableEq V] (G : CausalGraph V)
    (u v : V) : Decidable (G.IsAncestor u v) :=
  Relation.ReflTransGen.decidable_of_fintype_step G.children
    (fun a b => by simp [G.mem_children_iff]) u v

/-- `Decidable (G.IsStrictAncestor u v)` via the substrate's `TransGen`
`Fintype` headline. -/
instance IsStrictAncestor.decidable [Fintype V] [DecidableEq V] (G : CausalGraph V)
    (u v : V) : Decidable (G.IsStrictAncestor u v) :=
  Relation.ReflTransGen.decidable_TransGen_of_fintype_step G.children
    (fun a b => by simp [G.mem_children_iff]) u v

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

/-- A ranking of a causal graph is a `ℕ`-valued measure on which every
    parent ranks strictly below its children — the bundled form of the
    depth certificate consumed by `IsDAG.of_depth` and, per model, by the
    fuel bridges (`causallyEntails_iff_fuel`, `causallyNecessary_iff_fuel`). -/
structure Ranking (G : CausalGraph V) where
  /-- The rank of each vertex. -/
  rank : V → ℕ
  /-- Parents rank strictly below their children. -/
  parent_lt : ∀ {u v : V}, u ∈ G.parents v → rank u < rank v

/-- A ranking certifies acyclicity: ranks strictly increase along the
    strict-ancestor relation, so the relation embeds in `Nat.lt`.

    The standard mathlib pattern for proving wellfoundedness of finite
    inductive relations: define a measure into `ℕ`, show the relation
    decreases it, conclude. -/
theorem Ranking.isDAG {G : CausalGraph V} (r : Ranking G) : IsDAG G where
  wf := by
    have hsub : ∀ u v, G.IsStrictAncestor u v → r.rank u < r.rank v := by
      intro u v huv
      induction huv with
      | single hp => exact r.parent_lt hp
      | tail _ hp ih => exact lt_trans ih (r.parent_lt hp)
    exact Subrelation.wf (fun {a b} => hsub a b)
      (InvImage.wf r.rank Nat.lt_wfRel.wf)

/-- A graph is acyclic if every edge strictly decreases some `ℕ`-valued
    depth function — `Ranking.isDAG` with the certificate passed loose. -/
theorem IsDAG.of_depth (G : CausalGraph V) (depth : V → ℕ)
    (hdepth : ∀ {u v : V}, u ∈ G.parents v → depth u < depth v) :
    IsDAG G :=
  Ranking.isDAG ⟨depth, hdepth⟩

/-- A time index for a causal graph is a timestep assignment on which
    each parent sits exactly one step before its children — the
    time-indexed causal models of [cao-white-lassiter-2025]
    (their definition 1) and [cao-geiger-kreiss-icard-gerstenberg-2023]. -/
structure TimeIndex (G : CausalGraph V) where
  /-- The timestep of each variable. -/
  time : V → ℕ
  /-- Parents immediately precede their children. -/
  parent_succ : ∀ {u v : V}, u ∈ G.parents v → time u + 1 = time v

/-- The ranking underlying a time index. -/
def TimeIndex.toRanking {G : CausalGraph V} (ti : TimeIndex G) : Ranking G :=
  ⟨ti.time, fun h => by have := ti.parent_succ h; omega⟩

/-- A time index certifies acyclicity. -/
theorem TimeIndex.isDAG {G : CausalGraph V} (ti : TimeIndex G) : IsDAG G :=
  ti.toRanking.isDAG

end Causation.CausalGraph
