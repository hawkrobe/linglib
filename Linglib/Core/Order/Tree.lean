import Mathlib.Data.Set.Basic
import Mathlib.Order.Defs.PartialOrder
import Linglib.Core.Order.LeftLinear

/-!
# Tree Orders

[barker-pullum-1990]'s framework-agnostic notion of a syntactic tree:
a set of nodes equipped with a dominance partial order. This is the carrier
on which command relations (`Core.Order.commandRelation`) are defined.

The structure is **framework-agnostic** — Minimalism, HPSG, Dependency
Grammar, CCG, and Construction Grammar each pick a node type with a
`PartialOrder` instance giving dominance, then inherit the entire B&P
theory of command relations as a free corollary.

The dominance order is supplied by `[PartialOrder Node]` — reflexivity,
antisymmetry, and transitivity come from `le_refl`/`le_antisymm`/`le_trans`.
A `TreeOrder` only adds what is tree-specific: a designated `root`, the
`nodes` subset that participates in the tree, the **Connected Ancestor
Condition (CAC)**, and dominance closure on `nodes`.

The CAC is what B&P's Constituency Theorem (Theorem 7), the
Embeddability Theorem (Theorem 8), and the reverse direction of the
Union Theorem (Theorem 9) require; Boundedness (Theorem 4) uses only
the root.

## Main Definitions

* `TreeOrder Node` — `[PartialOrder Node]` plus a designated `root`, a
  `nodes : Set Node` subset, the CAC, and dominance closure.
* `TreeOrder.properDom` — strict dominance, `a ≤ b ∧ a ≠ b`.
* `upperBounds` — proper P-dominators of a node.
-/

namespace Core.Order

open Set

/-- Tree-shaped subset of a partially-ordered `Node` type
    ([barker-pullum-1990] Definitions 1 and 15 consolidated: Def 1 is
    the Wall-style tree — Single Root, Exclusivity, Nontangling — and
    Def 15 is the CAC, which B&P prove Def-1 trees entail, p. 22).

    The dominance order is `(· ≤ ·)` from `[PartialOrder Node]`; this
    structure adds tree-specific data: a designated root, the `nodes`
    subset, and the **Connected Ancestor Condition (CAC)**.

    Reflexivity (`a ≤ a`), antisymmetry, and transitivity of dominance
    are inherited from `PartialOrder` and are not restipulated here. -/
structure TreeOrder (Node : Type*) [PartialOrder Node] where
  /-- The set of nodes that belong to this tree. -/
  nodes : Set Node
  /-- The designated root node. -/
  root : Node
  /-- The root belongs to the tree. -/
  root_in_nodes : root ∈ nodes
  /-- The root dominates every node in the tree. -/
  root_le_all : ∀ a ∈ nodes, root ≤ a
  /-- **Connected Ancestor Condition (CAC)**: if both `x` and `y`
      dominate `z`, then `x ≤ y` or `y ≤ x`. Ancestors are linearly
      ordered. -/
  ancestor_connected : ∀ x y z : Node, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x

/-- Proper dominance: `a` properly dominates `b` iff `a ≤ b` and `a ≠ b`.
    Definitionally equal to `<` on the underlying partial order via
    `lt_iff_le_and_ne`, but kept as a named `And` so destructuring with
    `.1`/`.2` works in proofs. -/
def TreeOrder.properDom {Node : Type*} [PartialOrder Node]
    (_T : TreeOrder Node) (a b : Node) : Prop :=
  a ≤ b ∧ a ≠ b

/-- **Upper bounds** of a node with respect to property `P`
    ([barker-pullum-1990] Definition 2).

    `UB(a, P) = {b | b properly dominates a ∧ b ∈ P}`. -/
def upperBounds {Node : Type*} [PartialOrder Node]
    (T : TreeOrder Node) (a : Node) (P : Set Node) : Set Node :=
  {b | T.properDom b a ∧ b ∈ P}

/-- A `TreeOrder`'s Connected Ancestor Condition is exactly left-linearity: the
    syntactic-tree CAC and the branching-time no-backward-branching axiom are one and
    the same. Use `haveI := T.toIsLeftLinear` to inherit `IsLeftLinear.isChain_Iio`
    ("ancestors are linearly ordered") on the node type. -/
@[reducible] def TreeOrder.toIsLeftLinear {Node : Type*} [PartialOrder Node]
    (T : TreeOrder Node) : IsLeftLinear Node :=
  ⟨@fun a b c => T.ancestor_connected a b c⟩

end Core.Order
