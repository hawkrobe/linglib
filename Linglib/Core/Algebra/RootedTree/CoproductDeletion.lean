import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Combinatorics.RootedTree.PlanarCut
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

set_option autoImplicit false

universe u

/-!
# Δ^p (deletion) coproduct on `RootedTree.Planar α`
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-introduction-hopf-algebras-trees}

The **deletion variant** of the Connes-Kreimer coproduct on planar
n-ary rooted trees. For a tree T:

  Δ^p(T) = T ⊗ 1 + Σ_{c : Cut T} of'(cutForest c) ⊗ ofTree(remainderDeletion c)

where the empty cut contributes `1 ⊗ T` (since cutForest empty = ∅).

**The deletion variant** removes cut subtrees entirely, so the parent
vertex's arity decreases. The result lives in `Planar α` (no trace
markers needed). MCB §1.11.6 calls this `T/^p T_v`.

For the trace variant Δ^c (parent arity preserved via trace leaves),
see `CoproductTrace.lean` (Phase D — substantive cuts-of-cuts content).

## Foissy clean coassoc

Δ^p satisfies the Hochschild 1-cocycle condition with B+:

  Δ^p ∘ B+_a = B+_a ⊗ 1 + (id ⊗ B+_a) ∘ Δ^p

where B+_a (forest) = the tree with new root labeled a and the forest as
children. This is what makes the Foissy clean proof of coassoc work
(see `Cocycle.lean` and `Bialgebra.lean`).

## Status

`[UPSTREAM]` candidate. cutSummands recursive definition mirrors the
legacy `cutSummands` for FCM CK but for n-ary planar without traces.
-/

namespace RootedTree

namespace Algebra

namespace ConnesKreimer

open scoped TensorProduct
open Finsupp

variable {R : Type*} [CommSemiring R] {α : Type u}

/-! ## §1: cutSummandsP — multiset of (cut forest, deletion remainder) pairs

Recursive enumeration of cut summands. For a leaf, the only cut is the
empty cut. For a node, sum over all per-child decisions: each child can
either be extracted whole (contributes to cut forest, drops from
remainder) OR recurse with a smaller cut (contributes whatever its cut
extracts, leaves its deletion-remainder in the remainder list). -/

mutual
/-- Multiset of (cut forest, deletion remainder) pairs for a planar tree.
    Each summand corresponds to one admissible cut on T under the
    deletion semantics. -/
noncomputable def cutSummandsP : Planar α →
    Multiset (Forest (Planar α) × Planar α)
  | .node a cs => (cutListSummandsP cs).map (fun p => (p.1, .node a p.2))
/-- Auxiliary: cut summands for a list of children. The remainder is a
    list (children of the parent that survived the cut). -/
noncomputable def cutListSummandsP : List (Planar α) →
    Multiset (Forest (Planar α) × List (Planar α))
  | [] => {((0 : Forest (Planar α)), ([] : List (Planar α)))}
  | t :: ts =>
      ((augActionP t ×ˢ cutListSummandsP ts) : Multiset _).map
        (fun p => match p.1.2 with
          | Option.none => (p.1.1 + p.2.1, p.2.2)
          | Option.some r => (p.1.1 + p.2.1, r :: p.2.2))
/-- Auxiliary: per-child action — either extract whole (`none` remainder)
    or recurse with a cut (`some remainder`). -/
noncomputable def augActionP : Planar α →
    Multiset (Forest (Planar α) × Option (Planar α))
  | t => (({t} : Forest (Planar α)), Option.none) ::ₘ
         (cutSummandsP t).map (fun p => (p.1, Option.some p.2))
end

/-- Recursive formula on a node: cutSummandsP unfolds via cutListSummandsP. -/
@[simp] theorem cutSummandsP_node (a : α) (cs : List (Planar α)) :
    cutSummandsP (Planar.node a cs) =
      (cutListSummandsP cs).map (fun p => (p.1, .node a p.2)) := by
  unfold cutSummandsP; rfl

/-- Recursive formula for cutListSummandsP on empty list. -/
@[simp] theorem cutListSummandsP_nil :
    cutListSummandsP ([] : List (Planar α)) =
      {((0 : Forest (Planar α)), ([] : List (Planar α)))} := by
  unfold cutListSummandsP; rfl

/-! ## §2: comulTreePlanarP — tree-level Δ^p

Sum the cut summands as tensors, plus the explicit `T ⊗ 1` term. -/

/-- The **planar tree-level Δ^p** coproduct: explicit `T ⊗ 1` term plus
    the sum of cut-summand tensors. -/
noncomputable def comulTreePlanarP (T : Planar α) :
    ConnesKreimer R (Planar α) ⊗[R] ConnesKreimer R (Planar α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Planar α))
  + ((cutSummandsP T).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-! ## §3: comulForestPlanarP — forest-level Δ^p

Multiplicative extension over the disjoint-union product on forests:
Δ(F + G) = Δ(F) · Δ(G). -/

/-- The **planar forest-level Δ^p**: multiplicative product of tree-level
    coproducts over the components of the forest. -/
noncomputable def comulForestPlanarP (F : Forest (Planar α)) :
    ConnesKreimer R (Planar α) ⊗[R] ConnesKreimer R (Planar α) :=
  (F.map (comulTreePlanarP (R := R))).prod

@[simp] theorem comulForestPlanarP_zero :
    comulForestPlanarP (R := R) (0 : Forest (Planar α)) = 1 := by
  simp only [comulForestPlanarP, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForestPlanarP_add (F G : Forest (Planar α)) :
    comulForestPlanarP (R := R) (F + G) =
      comulForestPlanarP (R := R) F * comulForestPlanarP (R := R) G := by
  unfold comulForestPlanarP
  rw [Multiset.map_add, Multiset.prod_add]

/-! ## §4: comulMonoidHom and comulAlgHom

Package the multiplicative extension as a `MonoidHom`, then lift to the
full `AlgHom` via `AddMonoidAlgebra.lift`. -/

/-- comulForestPlanarP as a monoid hom from `Multiplicative (Forest (Planar α))`. -/
noncomputable def comulMonoidHomP :
    Multiplicative (Forest (Planar α)) →*
      (ConnesKreimer R (Planar α) ⊗[R] ConnesKreimer R (Planar α)) where
  toFun F := comulForestPlanarP (R := R) F.toAdd
  map_one' := comulForestPlanarP_zero
  map_mul' F G := comulForestPlanarP_add F.toAdd G.toAdd

/-- The **Δ^p coproduct on `ConnesKreimer R (Planar α)`** as an algebra hom. -/
noncomputable def comulAlgHomP :
    ConnesKreimer R (Planar α) →ₐ[R]
      ConnesKreimer R (Planar α) ⊗[R] ConnesKreimer R (Planar α) :=
  AddMonoidAlgebra.lift R
    ((ConnesKreimer R (Planar α)) ⊗[R] (ConnesKreimer R (Planar α)))
    (Forest (Planar α)) comulMonoidHomP

@[simp] theorem comulAlgHomP_apply_of' (F : Forest (Planar α)) :
    comulAlgHomP (R := R) (α := α) (of' F) = comulForestPlanarP F := by
  show AddMonoidAlgebra.lift R _ _ comulMonoidHomP (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem comulAlgHomP_apply_ofTree (T : Planar α) :
    comulAlgHomP (R := R) (α := α) (ofTree T) = comulTreePlanarP T := by
  unfold ofTree
  rw [comulAlgHomP_apply_of']
  unfold comulForestPlanarP
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

end ConnesKreimer

end Algebra

end RootedTree
