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

/-- **Acyclicity**: the strict-ancestor relation is well-founded — no
    infinite chain of parents. An `abbrev` for mathlib's `IsWellFounded`
    class, so its API (`IsWellFounded.wf`, induction, `fix`) applies
    directly; required by the `develop` fixpoint and well-founded
    recursion over the parent relation. -/
abbrev IsDAG (G : CausalGraph V) : Prop :=
  IsWellFounded V G.IsStrictAncestor

/-- A ranking of a causal graph is a relation homomorphism from the
    parent relation into `<` on `ℕ` — mathlib's `RelHom`, so the bundled
    form of the depth certificate consumed by `IsDAG.of_depth` and, per
    model, by the fuel bridges. -/
abbrev Ranking (G : CausalGraph V) : Type _ :=
  (· ∈ G.parents ·) →r ((· < ·) : ℕ → ℕ → Prop)

/-- A ranking certifies acyclicity: well-foundedness transfers along the
    homomorphism (`RelHomClass.wellFounded`) and lifts to the transitive
    closure (`WellFounded.transGen`). -/
theorem Ranking.isDAG {G : CausalGraph V} (r : Ranking G) : IsDAG G :=
  ⟨(RelHomClass.wellFounded r wellFounded_lt).transGen⟩

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
