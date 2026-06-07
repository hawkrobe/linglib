import Mathlib.Logic.Relation
import Mathlib.Data.List.Defs
import Linglib.Core.Relation.ReflTransGen

/-!
# Inheritance Networks — Basic Types and Taxonomy

[hudson-2010]

Hudson's Word Grammar organizes all linguistic knowledge as networks of nodes
connected by labeled directed links. Properties are not key-value pairs attached
to nodes — they ARE links between nodes. "Bird has wing" is a link labeled
`front-limb` from `bird` to `wing`. IsA links form a taxonomy; properties flow
down the taxonomy by default inheritance.

## Hudson's six primitive relations (Ch 3 summary box, p. 68)

`isA`, `argument`, `value`, `or` (choice), `quantity`, `identity` —
listed verbatim in [hudson-2010]'s Ch 3 summary box on p. 68 under
"Links between concepts are therefore of two types: primitive relations /
conceptual relations".

This module distinguishes three link kinds at the type level:

- **isA** — taxonomic classification (`bird isA animal`)
- **or** — mutual exclusivity / choice sets (`male or female`)
- **prop** — named property/relation links (`bird --front-limb--> wing`),
  covering `argument`, `value`, `identity`, `quantity` via the relation label

## Key definitions

- `LinkKind`, `Link`, `Network`
- `Network.nodeUniverse` — finite carrier derived from the link list
- `parents`, `ancestorsBound`, `ancestors` — computational taxonomy traversal
- `IsA` — the canonical reflexive-transitive `isA`, defined as
  `Relation.ReflTransGen` of the parent edge

`IsA` is the API; `parents`/`ancestors` are computational evidence
producers. `IsA` is decidable for any concrete network via the
`Relation.ReflTransGen.decidable_of_finite_step` substrate, so positive and
negative `IsA` claims both reduce by `decide`. Termination of `ancestors`
is bounded by `nodeUniverse.length`, not a magic constant.
-/

set_option autoImplicit false

universe u v

namespace WordGrammar.Inheritance

-- ============================================================================
-- Links
-- ============================================================================

/-- Distinguished link types in a WG network [hudson-2010] §3.2.
`isA` and `or` are separated from general property links because the
inheritance algorithm must traverse `isA` links and choice-set resolution
uses `or` links. -/
inductive LinkKind where
  | isA   -- taxonomic inheritance
  | or    -- mutual exclusivity (choice set)
  | prop  -- named property / relation
  deriving Repr, DecidableEq

/-- A labeled directed edge: `source --[kind, label]--> target`.
In WG, all knowledge is encoded as links between nodes: "cat isA mammal",
"bird --front-limb--> wing", "male or female". -/
structure Link (α : Type u) (R : Type v) where
  kind : LinkKind
  source : α
  target : α
  label : Option R := none
  deriving Repr, DecidableEq

-- ============================================================================
-- Network
-- ============================================================================

/-- A WG inheritance network: nodes connected by labeled directed links.
Parameterized over node type `α` and relation-label type `R`. -/
structure Network (α : Type u) (R : Type v) [DecidableEq α] [DecidableEq R] where
  links : List (Link α R)

section NetworkOps

variable {α : Type u} {R : Type v} [DecidableEq α] [DecidableEq R]

/-- The finite set of nodes mentioned by the network's links.
Used as the natural termination bound for traversals — the longest acyclic
path in a finite network cannot exceed `nodeUniverse.length` steps. -/
def Network.nodeUniverse (net : Network α R) : List α :=
  (net.links.map Link.source ++ net.links.map Link.target).dedup

-- ============================================================================
-- Taxonomy (isA)
-- ============================================================================

/-- Direct isA parents of a node. -/
def parents (net : Network α R) (node : α) : List α :=
  (net.links.filter (fun l => l.kind == .isA && l.source == node)).map Link.target

/-- Bounded transitive closure of `parents`. The `bound` parameter is intended
to be ≥ `(nodeUniverse net).length`; under that assumption every reachable
ancestor appears. Structurally recursive on `Nat` to keep `decide` happy. -/
def ancestorsBound (net : Network α R) (node : α) : Nat → List α
  | 0 => []
  | n + 1 =>
    let ps := parents net node
    ps ++ ps.flatMap (fun p => ancestorsBound net p n)

/-- Transitive ancestors of `node` in the isA taxonomy. The recursion bound
is derived from the network itself (number of distinct nodes), so finite
networks always traverse to fixpoint without a magic constant. -/
def ancestors (net : Network α R) (node : α) : List α :=
  ancestorsBound net node net.nodeUniverse.length

-- ============================================================================
-- IsA: propositional reflexive-transitive `isA` via mathlib's `ReflTransGen`
-- ============================================================================

/-- The single-step parent relation. -/
def isAEdge (net : Network α R) (a b : α) : Prop := b ∈ parents net a

instance (net : Network α R) (a b : α) : Decidable (isAEdge net a b) :=
  inferInstanceAs (Decidable (b ∈ parents net a))

/-- Reflexive-transitive `isA`: `a` inherits from `b` along the chain of isA
links. Defined as `Relation.ReflTransGen` of the parent edge — the same
construction mathlib uses for transitive closures elsewhere, so every lemma
about `ReflTransGen` (and the `Preorder` structure in `WordGrammar.Inheritance.Order`)
applies for free. -/
def IsA (net : Network α R) (a b : α) : Prop := Relation.ReflTransGen (isAEdge net) a b

/-- Every node `IsA` itself. -/
theorem IsA.refl (net : Network α R) (a : α) : IsA net a a :=
  Relation.ReflTransGen.refl

/-- `IsA` is transitive (mathlib gives this for free via `ReflTransGen.trans`). -/
theorem IsA.trans (net : Network α R) {a b c : α}
    (hab : IsA net a b) (hbc : IsA net b c) : IsA net a c :=
  Relation.ReflTransGen.trans hab hbc

-- ----------------------------------------------------------------------------
-- Decidability of IsA via Core.Relation.ReflTransGen substrate
-- ----------------------------------------------------------------------------

/-- Direct parents of any node are mentioned by some isA link, hence in
`nodeUniverse`. The "successor in universe" witness fed to the substrate. -/
theorem mem_nodeUniverse_of_mem_parents (net : Network α R) (a b : α)
    (h : b ∈ parents net a) : b ∈ net.nodeUniverse := by
  simp only [parents, List.mem_map, List.mem_filter] at h
  obtain ⟨l, ⟨hmem, _⟩, htgt⟩ := h
  simp only [Network.nodeUniverse, List.mem_dedup]
  exact List.mem_append_right _ (List.mem_map.2 ⟨l, hmem, htgt⟩)

/-- `IsA` is decidable on finite networks: the network's own `nodeUniverse`
provides the bound, and `Relation.ReflTransGen.decidable_of_finite_step`
supplies the path-compression argument. -/
instance IsA.decidable (net : Network α R) (a b : α) : Decidable (IsA net a b) :=
  Relation.ReflTransGen.decidable_of_finite_step
    (parents net) net.nodeUniverse
    (fun _ _ => Iff.rfl)
    (mem_nodeUniverse_of_mem_parents net) a b

end NetworkOps

end WordGrammar.Inheritance
