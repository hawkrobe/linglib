import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Relation
import Mathlib.Data.List.Defs

/-!
# Inheritance Networks — Basic Types and Taxonomy

@cite{hudson-2010}

Hudson's Word Grammar organizes all linguistic knowledge as networks of nodes
connected by labeled directed links. Properties are not key-value pairs attached
to nodes — they ARE links between nodes. "Bird has wing" is a link labeled
`front-limb` from `bird` to `wing`. IsA links form a taxonomy; properties flow
down the taxonomy by default inheritance.

## Hudson's six primitive relations (Ch 3 summary, p. 68)

`isA`, `argument`, `value`, `or` (choice), `quantity`, `identity` —
listed in the Chapter 3 summary box on p. 68 of @cite{hudson-2010}
(under "Links between concepts are therefore of two types: primitive
relations / conceptual relations").

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
- `Prototype` — graded category membership

`IsA` is the API; `parents`/`ancestors` are computational evidence producers
(`b ∈ ancestors net a → IsA net a b` via `IsA.of_mem_ancestors`). Termination
of `ancestors` is bounded by `nodeUniverse.length`, not a magic constant.
-/

set_option autoImplicit false

namespace Core.Inheritance

-- ============================================================================
-- Links
-- ============================================================================

/-- Distinguished link types in a WG network @cite{hudson-2010} §3.2.
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
structure Link (α R : Type) where
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
structure Network (α R : Type) [DecidableEq α] [DecidableEq R] where
  links : List (Link α R)

section NetworkOps

variable {α R : Type} [DecidableEq α] [DecidableEq R]

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

/-- Reflexive-transitive `isA`: `a` inherits from `b` along the chain of isA
links. Defined as `Relation.ReflTransGen` of the parent edge — the same
construction mathlib uses for transitive closures elsewhere, so every lemma
about `ReflTransGen` (and the `Preorder` structure in `Core.Inheritance.Order`)
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
-- Constructors and computational-evidence bridges
-- ----------------------------------------------------------------------------

/-- Single isA links are tracked: if `a → b` is an isA link, then `b ∈ parents net a`. -/
theorem mem_parents_of_isALink (net : Network α R) {a b : α}
    (h : ⟨LinkKind.isA, a, b, none⟩ ∈ net.links) :
    b ∈ parents net a := by
  simp only [parents, List.mem_map, List.mem_filter]
  exact ⟨⟨LinkKind.isA, a, b, none⟩, ⟨h, by simp⟩, rfl⟩

/-- A direct isA edge gives the propositional `IsA` in one step. -/
theorem IsA.of_isAEdge (net : Network α R) {a b : α}
    (h : isAEdge net a b) : IsA net a b :=
  Relation.ReflTransGen.single h

/-- Membership in the bounded transitive closure implies `IsA`. Proved by
induction on the fuel. -/
theorem IsA.of_mem_ancestorsBound (net : Network α R) :
    ∀ (n : Nat) (a b : α), b ∈ ancestorsBound net a n → IsA net a b
  | 0, _, _, h => by simp [ancestorsBound] at h
  | n + 1, a, b, h => by
    simp only [ancestorsBound, List.mem_append, List.mem_flatMap] at h
    rcases h with hpar | ⟨p, hp_par, hp_anc⟩
    · exact IsA.of_isAEdge net hpar
    · have h_pa : isAEdge net a p := hp_par
      have h_pb : IsA net p b := IsA.of_mem_ancestorsBound net n p b hp_anc
      exact Relation.ReflTransGen.head h_pa h_pb

/-- Membership in `ancestors` implies `IsA`. The convenience entry point for
constructing `IsA net a b` proofs from a `decide`-able list-membership goal:
`IsA.of_mem_ancestors _ (by decide)`. -/
theorem IsA.of_mem_ancestors (net : Network α R) {a b : α}
    (h : b ∈ ancestors net a) : IsA net a b :=
  IsA.of_mem_ancestorsBound net _ a b h

/-! The reverse direction `IsA net a b → a = b ∨ b ∈ ancestors net a` requires
path compression: any `ReflTransGen` chain in a finite network reduces to one
with no repeated nodes (length `≤ nodeUniverse.length`), which then sits inside
`ancestorsBound` at that fuel. Not yet formalized — TODO(0.230.50+). Until
then, `¬IsA net a b` for a concrete network must be argued via direct case
analysis on `Relation.ReflTransGen`, or expressed as the strictly weaker,
decidable fact `b ∉ ancestors net a` (which says only that the BFS doesn't
witness the relationship, not that no `ReflTransGen` chain can exist). -/

end NetworkOps

-- ============================================================================
-- Prototype Effects
-- ============================================================================

/-- A prototype: a category with graded typicality over instances.
Higher values = more prototypical @cite{hudson-2010} Ch 2. -/
structure Prototype (α : Type) where
  category : α
  typicality : α → ℚ

/-- Whether `a` is at least as typical as `b` in a prototype. -/
def Prototype.atLeastAsTypical {α : Type} (proto : Prototype α) (a b : α) : Bool :=
  proto.typicality a ≥ proto.typicality b

/-- Whether `a` is strictly more typical than `b` in a prototype. -/
def Prototype.moreTypical {α : Type} (proto : Prototype α) (a b : α) : Bool :=
  proto.typicality a > proto.typicality b

/-- `atLeastAsTypical` is reflexive. -/
theorem Prototype.atLeastAsTypical_refl {α : Type} (proto : Prototype α) (a : α) :
    proto.atLeastAsTypical a a = true := by
  simp [atLeastAsTypical]

/-- `atLeastAsTypical` is transitive. -/
theorem Prototype.atLeastAsTypical_trans {α : Type} (proto : Prototype α) (a b c : α)
    (hab : proto.atLeastAsTypical a b = true)
    (hbc : proto.atLeastAsTypical b c = true) :
    proto.atLeastAsTypical a c = true := by
  simp [atLeastAsTypical] at *
  linarith

end Core.Inheritance
