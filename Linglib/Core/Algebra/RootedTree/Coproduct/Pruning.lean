import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Data.RoseTree.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

set_option autoImplicit false

/-!
# Δ^ρ (admissible-cut, root-component pruning) coproduct on `RoseTree α`
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The **admissible-cut, root-component pruning** variant of the
Connes-Kreimer coproduct on ordered (planar) n-ary rooted trees `RoseTree α`.
For a tree T:

  Δ^ρ(T) = T ⊗ 1 + Σ_{c : Cut T} of'(cutForest c) ⊗ ofTree(remainderDeletion c)

where the empty cut contributes `1 ⊗ T` (since cutForest empty = ∅).

**Naming.** Linglib's "Δ^ρ" corresponds to MCB Definition 1.2.6's
**Δ^ρ** (book p. 31) — the admissible-cut coproduct whose right channel
is the root component `ρ_C(T)` after pruning the cut subtrees from the
parent's children list. The result lives in *at-most-n-ary* trees
(Lemma 1.2.11, book p. 38). Per MCB Remark 1.2.9 (book p. 34), this Δ^ρ
coproduct corresponds to the **Foissy Connes-Kreimer Hopf algebra of
(not-necessarily-binary) rooted trees**, where the right channel can
contain rooted trees that are not binary.

NOT MCB's **Δ^d** (Definition 1.2.5, p. 31), which is "deletion +
rebinarization" — Δ^d additionally contracts edges to recover binarity.
Δ^d is the closest to PF Externalization and would be derived from this
Δ^ρ (or built independently) when a consumer needs it. See sibling
`Coproduct/Deletion.lean` (FUTURE) for that.

For the trace variant **Δ^c** (T/^c F_v, parent arity preserved via
trace leaves; MCB Definition 1.2.4, book p. 30), see sibling
`Coproduct/Trace.lean`. MCB Δ^c on binary nonplanar = restriction of
the Connes-Kreimer Hopf algebra of Feynman graphs (a different, related
Hopf algebra; Remark 1.2.9, p. 34). Used at the C-I (semantic)
interface for FormCopy.

## Relation to the generic cut enumeration

The bespoke `cutSummandsP`/`cutListSummandsP`/`augActionP` block below is
the deletion (Δ^ρ) sibling of the extraction-policy-parameterized
`cutSummandsG` in `Coproduct/Defs.lean`. It is NOT re-expressed as
`cutSummandsG (fun _ => some [])` because the downstream coassoc proof
(`Coproduct/PruningNonplanar.lean`) is written against the `Option`
remainder encoding used here — deletion is `Option.none`, a surviving
child is `Option.some r` — whereas `cutSummandsG` carries `List`
remainders (deletion `[]`, survival `[r]`). Folding onto `cutSummandsG`
would change the public return type of `augActionP` (Option → List) and
the shapes of `augActionP_eq`/`cutListSummandsP_cons`, all of which
`PruningNonplanar.lean` consumes; so the two enumerations coexist.
(Δ^c in `Trace.lean` *does* derive from `cutSummandsG`, since it was
written against the `List` encoding.)

## Foissy clean coassoc

Δ^ρ satisfies the Hochschild 1-cocycle condition with B+ (graft as
new root):

  Δ^ρ ∘ B+_a = B+_a ⊗ 1 + (id ⊗ B+_a) ∘ Δ^ρ

The B+ operator only well-defines on `Multiset (Nonplanar α) → Nonplanar α`
(unordered children of a new root). On `RoseTree α` with `Multiset`
forests, B+ would need a canonical ordering. Hence the sorry-free
coassoc proof for Δ^ρ lives in `Coproduct/PruningNonplanar.lean` on
`RootedTree.Nonplanar α`. (Note: this Foissy clean coassoc strategy
does NOT generalize to Δ^c — B+ is not a Hochschild 1-cocycle for the
trace variant. Δ^c coassoc uses Grossman-Larson duality instead; see
the GL substrate when it lands.)

## Status

`[UPSTREAM]` candidate. cutSummands recursive definition; full
Bialgebra structure (descent + coassoc + counit + Hopf antipode) lives
in `Coproduct/PruningNonplanar.lean` and `HopfAlgebraNonplanar.lean`.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct
open Finsupp

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### cutSummandsP — multiset of (cut forest, deletion remainder) pairs

Recursive enumeration of cut summands. For a leaf, the only cut is the
empty cut. For a node, sum over all per-child decisions: each child can
either be extracted whole (contributes to cut forest, drops from
remainder) OR recurse with a smaller cut (contributes whatever its cut
extracts, leaves its deletion-remainder in the remainder list). -/

mutual
/-- Multiset of (cut forest, deletion remainder) pairs for a tree.
    Each summand corresponds to one admissible cut on T under the
    deletion semantics. -/
def cutSummandsP : RoseTree α →
    Multiset (Forest (RoseTree α) × RoseTree α)
  | .node a cs => (cutListSummandsP cs).map (fun p => (p.1, .node a p.2))
/-- Auxiliary: cut summands for a list of children. The remainder is a
    list (children of the parent that survived the cut). -/
def cutListSummandsP : List (RoseTree α) →
    Multiset (Forest (RoseTree α) × List (RoseTree α))
  | [] => {((0 : Forest (RoseTree α)), ([] : List (RoseTree α)))}
  | t :: ts =>
      ((augActionP t ×ˢ cutListSummandsP ts) : Multiset _).map
        (fun p => match p.1.2 with
          | Option.none => (p.1.1 + p.2.1, p.2.2)
          | Option.some r => (p.1.1 + p.2.1, r :: p.2.2))
/-- Auxiliary: per-child action — either extract whole (`none` remainder)
    or recurse with a cut (`some remainder`). -/
def augActionP : RoseTree α →
    Multiset (Forest (RoseTree α) × Option (RoseTree α))
  | t => (({t} : Forest (RoseTree α)), Option.none) ::ₘ
         (cutSummandsP t).map (fun p => (p.1, Option.some p.2))
end

/-- Recursive formula on a node: cutSummandsP unfolds via cutListSummandsP. -/
@[simp] theorem cutSummandsP_node (a : α) (cs : List (RoseTree α)) :
    cutSummandsP (RoseTree.node a cs) =
      (cutListSummandsP cs).map (fun p => (p.1, .node a p.2)) := by
  unfold cutSummandsP; rfl

/-- Recursive formula for cutListSummandsP on empty list. -/
@[simp] theorem cutListSummandsP_nil :
    cutListSummandsP ([] : List (RoseTree α)) =
      {((0 : Forest (RoseTree α)), ([] : List (RoseTree α)))} := by
  unfold cutListSummandsP; rfl

/-- Recursive formula for cutListSummandsP on a cons list. -/
@[simp] theorem cutListSummandsP_cons (t : RoseTree α) (ts : List (RoseTree α)) :
    cutListSummandsP (t :: ts) =
      ((augActionP t ×ˢ cutListSummandsP ts) : Multiset _).map
        (fun p => match p.1.2 with
          | Option.none => (p.1.1 + p.2.1, p.2.2)
          | Option.some r => (p.1.1 + p.2.1, r :: p.2.2)) := by
  conv_lhs => unfold cutListSummandsP

/-- Recursive formula for augActionP. -/
@[simp] theorem augActionP_eq (t : RoseTree α) :
    augActionP t = (({t} : Forest (RoseTree α)), Option.none) ::ₘ
                   (cutSummandsP t).map (fun p => (p.1, Option.some p.2)) := by
  conv_lhs => unfold augActionP

/-! ### comulTreePlanarP — tree-level Δ^ρ

Sum the cut summands as tensors, plus the explicit `T ⊗ 1` term. -/

/-- The **tree-level Δ^ρ** coproduct: explicit `T ⊗ 1` term plus
    the sum of cut-summand tensors. -/
noncomputable def comulTreePlanarP (T : RoseTree α) :
    ConnesKreimer R (RoseTree α) ⊗[R] ConnesKreimer R (RoseTree α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (RoseTree α))
  + ((cutSummandsP T).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-! ### comulForestPlanarP — forest-level Δ^ρ

Multiplicative extension over the disjoint-union product on forests:
Δ(F + G) = Δ(F) · Δ(G). -/

/-- The **forest-level Δ^ρ**: multiplicative product of tree-level
    coproducts over the components of the forest. -/
noncomputable def comulForestPlanarP (F : Forest (RoseTree α)) :
    ConnesKreimer R (RoseTree α) ⊗[R] ConnesKreimer R (RoseTree α) :=
  (F.map (comulTreePlanarP (R := R))).prod

@[simp] theorem comulForestPlanarP_zero :
    comulForestPlanarP (R := R) (0 : Forest (RoseTree α)) = 1 := by
  simp only [comulForestPlanarP, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForestPlanarP_add (F G : Forest (RoseTree α)) :
    comulForestPlanarP (R := R) (F + G) =
      comulForestPlanarP (R := R) F * comulForestPlanarP (R := R) G := by
  unfold comulForestPlanarP
  rw [Multiset.map_add, Multiset.prod_add]

/-! ### comulMonoidHom and comulAlgHom

Package the multiplicative extension as a `MonoidHom`, then lift to the
full `AlgHom` via `AddMonoidAlgebra.lift`. -/

/-- comulForestPlanarP as a monoid hom from `Multiplicative (Forest (RoseTree α))`. -/
noncomputable def comulMonoidHomP :
    Multiplicative (Forest (RoseTree α)) →*
      (ConnesKreimer R (RoseTree α) ⊗[R] ConnesKreimer R (RoseTree α)) where
  toFun F := comulForestPlanarP (R := R) F.toAdd
  map_one' := comulForestPlanarP_zero
  map_mul' F G := comulForestPlanarP_add F.toAdd G.toAdd

/-- The **Δ^ρ coproduct on `ConnesKreimer R (RoseTree α)`** as an algebra hom. -/
noncomputable def comulAlgHomP :
    ConnesKreimer R (RoseTree α) →ₐ[R]
      ConnesKreimer R (RoseTree α) ⊗[R] ConnesKreimer R (RoseTree α) :=
  AddMonoidAlgebra.lift R
    ((ConnesKreimer R (RoseTree α)) ⊗[R] (ConnesKreimer R (RoseTree α)))
    (Forest (RoseTree α)) comulMonoidHomP

@[simp] theorem comulAlgHomP_apply_of' (F : Forest (RoseTree α)) :
    comulAlgHomP (R := R) (α := α) (of' F) = comulForestPlanarP F := by
  show AddMonoidAlgebra.lift R _ _ comulMonoidHomP (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem comulAlgHomP_apply_ofTree (T : RoseTree α) :
    comulAlgHomP (R := R) (α := α) (ofTree T) = comulTreePlanarP T := by
  unfold ofTree
  rw [comulAlgHomP_apply_of']
  unfold comulForestPlanarP
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

end ConnesKreimer

end RootedTree
