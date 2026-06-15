import Linglib.Core.Combinatorics.RootedTree.Nonplanar

/-!
# Rebinarization: contracting unary (non-branching) nodes
[marcolli-chomsky-berwick-2025]

`contractUnary` collapses every unary node (a vertex with exactly one child)
into that child, the edge-contraction that takes a syntactic object to its
**unique maximal binary rooted tree** (MCB Def. 1.2.5). It is the second step
of MCB's deletion quotient `T/ᵈF_v`: delete the cut subtrees (leaving the
not-necessarily-binary `T/ᵖF_v`), then `contractUnary` to rebinarize.

Each contracted unary node removes exactly one vertex, so
`weight (contractUnary t) + unaryCount t = weight t`.
-/

namespace RootedTree

namespace Planar

variable {α : Type*}

/-! ### Definitions -/

mutual
/-- Contract every unary node into its child (rebinarize to maximal binary). -/
def contractUnary : Planar α → Planar α
  | .node a []              => .node a []
  | .node _ [c]             => contractUnary c
  | .node a (c₁ :: c₂ :: cs) => .node a (contractUnaryList (c₁ :: c₂ :: cs))
/-- Auxiliary: `contractUnary` across a list of children. -/
def contractUnaryList : List (Planar α) → List (Planar α)
  | []      => []
  | c :: cs => contractUnary c :: contractUnaryList cs
end

mutual
/-- The number of unary (single-child) nodes in a tree. -/
def unaryCount : Planar α → Nat
  | .node _ []              => 0
  | .node _ [c]             => 1 + unaryCount c
  | .node _ (c₁ :: c₂ :: cs) => unaryCountList (c₁ :: c₂ :: cs)
/-- Auxiliary: total unary-node count across a list of trees. -/
def unaryCountList : List (Planar α) → Nat
  | []      => 0
  | c :: cs => unaryCount c + unaryCountList cs
end

@[simp] theorem contractUnaryList_cons (c : Planar α) (cs : List (Planar α)) :
    contractUnaryList (c :: cs) = contractUnary c :: contractUnaryList cs := rfl

@[simp] theorem unaryCountList_cons (c : Planar α) (cs : List (Planar α)) :
    unaryCountList (c :: cs) = unaryCount c + unaryCountList cs := rfl

/-! ### Weight conservation: each contracted unary node drops one vertex -/

mutual
theorem weight_contractUnary_add :
    ∀ (t : Planar α), weight (contractUnary t) + unaryCount t = weight t
  | .node a []              => rfl
  | .node a [c]             => by
    have ih := weight_contractUnary_add c
    show weight (contractUnary c) + (1 + unaryCount c) = 1 + weight c
    omega
  | .node a (c₁ :: c₂ :: cs) => by
    have ihl := weightList_contractUnaryList_add (c₁ :: c₂ :: cs)
    show (1 + weightList (contractUnaryList (c₁ :: c₂ :: cs)))
        + unaryCountList (c₁ :: c₂ :: cs) = 1 + weightList (c₁ :: c₂ :: cs)
    omega
theorem weightList_contractUnaryList_add :
    ∀ (cs : List (Planar α)),
      weightList (contractUnaryList cs) + unaryCountList cs = weightList cs
  | []      => rfl
  | c :: cs => by
    have ih := weight_contractUnary_add c
    have ihl := weightList_contractUnaryList_add cs
    show (weight (contractUnary c) + weightList (contractUnaryList cs))
        + (unaryCount c + unaryCountList cs) = weight c + weightList cs
    omega
end

end Planar

end RootedTree
