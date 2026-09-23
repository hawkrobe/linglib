module

public import Linglib.Semantics.Causation.Graph.Defs
public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Order.RelClasses
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.EquivFin

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
[cao-white-lassiter-2025]); `IsDAG.of_depth` passes the loose form. A finite graph is acyclic
once no vertex is its own strict ancestor (`IsDAG.of_irrefl`, decidable), and is then ranked by
counting strict ancestors (`ancestorRanking`), below the number of vertices.

Ancestry in an acyclic graph is a partial order, causal precedence (`CausalGraph.partialOrder`),
and a linear order when the graph is a single causal chain (`CausalGraph.linearOrder`). An account
that reads a participant's place in a causal chain orders the chain's events this way.
-/

@[expose] public section

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
    infinite chain of parents. An `abbrev` for `WellFounded`, which mathlib
    registers as a class, so its API (induction, `fix`) applies directly;
    required by the `develop` fixpoint and well-founded recursion over the
    parent relation. -/
abbrev IsDAG (G : CausalGraph V) : Prop :=
  WellFounded G.IsStrictAncestor

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
  (RelHomClass.wellFounded r wellFounded_lt).transGen

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

/-! ### Finite acyclic graphs -/

/-- A finite graph in which no vertex is its own strict ancestor is acyclic. -/
theorem IsDAG.of_irrefl [Finite V] {G : CausalGraph V} (h : ∀ v, ¬ G.IsStrictAncestor v v) :
    G.IsDAG :=
  have : IsTrans V G.IsStrictAncestor := ⟨fun _ _ _ ↦ Relation.TransGen.trans⟩
  have : Std.Irrefl G.IsStrictAncestor := ⟨h⟩
  Finite.wellFounded_of_trans_of_irrefl _

section Finite

variable [Fintype V] [DecidableEq V]

/-- The canonical ranking of a finite acyclic graph: a vertex's number of strict ancestors. A
parent's strict ancestors are strict ancestors of its child, which has the parent besides. -/
def ancestorRanking (G : CausalGraph V) [hG : G.IsDAG] : Ranking G :=
  ⟨fun v ↦ (Finset.univ.filter (G.IsStrictAncestor · v)).card, fun {u _} h ↦
    Finset.card_lt_card <| (Finset.ssubset_iff_of_subset fun w hw ↦ Finset.mem_filter.2
      ⟨Finset.mem_univ w, .tail (Finset.mem_filter.1 hw).2 h⟩).2
      ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, .single h⟩, fun h' ↦
        have h' : G.IsStrictAncestor u u := (Finset.mem_filter.1 h').2
        @WellFounded.asymmetric _ _ hG u u h' h'⟩⟩

/-- The canonical ranking stays below the number of vertices, since no vertex is its own strict
ancestor. -/
theorem ancestorRanking_lt_card (G : CausalGraph V) [hG : G.IsDAG] (v : V) :
    G.ancestorRanking v < Fintype.card V :=
  Finset.card_lt_card <| Finset.filter_ssubset.2
    ⟨v, Finset.mem_univ v, fun h ↦ @WellFounded.asymmetric _ _ hG v v h h⟩

end Finite

/-! ### Causal precedence -/

/-- Causal precedence: in an acyclic causal graph, ancestry is a partial order, a node preceding
the nodes it is an ancestor of. A reducible definition, like `partialOrderOfCovers`, for a
consumer to install as the order on its nodes. -/
@[reducible] def partialOrder (G : CausalGraph V) (hG : G.IsDAG) : PartialOrder V where
  le := G.IsAncestor
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ := Relation.ReflTransGen.antisymm_of_irrefl_transGen
    fun a h ↦ @WellFounded.asymmetric _ _ hG a a h h

/-- A causal graph whose ancestry is total, a single causal chain, is linearly ordered by causal
precedence. -/
@[reducible] def linearOrder [Fintype V] [DecidableEq V] (G : CausalGraph V) (hG : G.IsDAG)
    (htotal : ∀ a b, G.IsAncestor a b ∨ G.IsAncestor b a) : LinearOrder V where
  __ := G.partialOrder hG
  le_total := htotal
  toDecidableLE := IsAncestor.decidable G
  toDecidableEq := inferInstance

end Causation.CausalGraph
