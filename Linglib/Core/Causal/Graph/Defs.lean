import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# CausalGraph: Bare Directed Graph over a Vertex Type (V2)

A `CausalGraph V` is the underlying DAG topology of a structural causal
model: just `parents : V → Finset V`. No mechanisms, no value types, no
acyclicity hypothesis (that lives in `Graph/Basic.lean` as the `IsDAG` mixin).

This separation mirrors mathlib's `Mathlib/Combinatorics/Digraph/Basic.lean`
(`structure Digraph V where adj : V → V → Prop`) but uses `Finset V` parents
because Pearl SEM API consumes parent enumerations directly (mechanisms
fold over `parents v`).
-/

namespace Core.Causal

/-- A directed graph over `V` represented by parent finsets. The graph
    structure is value-type-agnostic: mechanisms and values layer on top
    via `Mechanism` and `Valuation`. -/
structure CausalGraph (V : Type*) where
  /-- The set of parents of each vertex. -/
  parents : V → Finset V

namespace CausalGraph

variable {V : Type*}

/-- The empty graph: every vertex is a root. -/
def empty : CausalGraph V := ⟨fun _ => ∅⟩

instance : Inhabited (CausalGraph V) := ⟨empty⟩

/-- A vertex is a root iff it has no parents. -/
def isRoot (G : CausalGraph V) (v : V) : Prop :=
  G.parents v = ∅

instance (G : CausalGraph V) (v : V) [DecidableEq V] : Decidable (G.isRoot v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The children of a vertex: vertices `u` for which `v ∈ parents u`.
    Requires `[DecidableEq V] [Fintype V]` to enumerate candidates. -/
def children (G : CausalGraph V) [DecidableEq V] [Fintype V] (v : V) : Finset V :=
  Finset.univ.filter (fun u => v ∈ G.parents u)

@[simp] theorem mem_children_iff (G : CausalGraph V) [DecidableEq V] [Fintype V]
    {u v : V} : u ∈ G.children v ↔ v ∈ G.parents u := by
  simp [children]

@[simp] theorem isRoot_iff_parents_empty (G : CausalGraph V) (v : V) :
    G.isRoot v ↔ G.parents v = ∅ := Iff.rfl

theorem isRoot_iff_card_zero (G : CausalGraph V) (v : V) :
    G.isRoot v ↔ (G.parents v).card = 0 := by
  simp [isRoot, Finset.card_eq_zero]

end CausalGraph

end Core.Causal
