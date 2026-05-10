import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Combinatorics.RootedTree.PlanarCut
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

set_option autoImplicit false

/-!
# Δ^c (trace-aware admissible-cut) coproduct on `RootedTree.Planar (α ⊕ β)`
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-introduction-hopf-algebras-trees}

The **trace-preserving variant** of the Connes-Kreimer admissible-cut
coproduct on planar n-ary rooted trees, parameterized by a trace
encoder `τ : Planar (α ⊕ β) → β`. For a tree T:

  Δ^c_τ(T) = T ⊗ 1 + Σ_{c : Cut T} of'(cutForest c) ⊗ ofTree(remainderTrace c)

where `remainderTrace c` keeps a placeholder leaf at every cut site —
the leaf's label is `Sum.inr (τ T_v)` for the cut subtree `T_v`. This
contrasts with the deletion variant `Δ^p` (sibling `Coproduct.lean`),
where cut sites simply disappear (the parent loses a child).

## Carrier and encoder

The carrier is `Planar (α ⊕ β)` directly: original-decoration vertices
sit on `Sum.inl`, trace-marker vertices on `Sum.inr`. Output trees from
Δ^c only ever introduce trace markers as leaves; this is provable as a
property rather than baked into the carrier (no `DecoratedTree` wrapper).

The trace encoder `τ` is an explicit per-definition parameter, not a
section variable. Consumers pick `τ` to encode whatever trace
information they want about the cut subtree:

- **Unit trace**: `β = Unit`, `τ = Function.const _ ()` — placeholder is
  a single Unit-labeled leaf, identical for every cut. Distinct from
  MCB's Δ^d (Definition 1.2.5, p. 31), which is deletion-then-rebinarize
  and would require separate substrate.
- **Identity trace**: `τ = id` if β = Planar (α ⊕ β) — placeholder
  carries the full cut subtree as label. Closest match to the book's
  notation `F̄_v`.
- **Quotient trace**: `τ` projects to syntactic features, semantic
  representations, etc. (consumer-specific).

## Embedding α-only trees

The substrate is encoder-free: an α-only tree T : Planar α is embedded
into Planar (α ⊕ β) via `Planar.map Sum.inl T`. No separate
`mapDecoration` primitive.

## MCB anchors

- **Definition 1.2.4** (book p. 30): T/^c F_v — contraction of each
  cut subtree to its root vertex, which becomes a leaf carrying a
  trace label F̄_v. Parent arity preserved.
- **Definition 1.2.8** (book p. 33), formula (1.2.8) with ω = c: the
  coproduct itself, Δ^c(T) := T ⊗ 1 + 1 ⊗ T + Σ F_v ⊗ T/^c F_v. The
  `1 ⊗ T` term is absorbed into the sum here as the empty-cut summand
  (matching `Coproduct.lean`'s convention; the `T ⊗ 1` term is kept
  explicit).
- **Remark 1.2.9** (book p. 34): on nonplanar binary rooted trees, Δ^c
  is the restriction of the coproduct of the Connes-Kreimer Hopf
  algebra of Feynman graphs.
- **Lemma 1.2.10** (book p. 35): coassociativity of Δ^c (proved at the
  Nonplanar layer; not in this file).

The trace-leaf contraction underlies the C-I (semantic) interface for
FormCopy in the MCB analysis. For the admissible-cut variant Δ^p
(corresponds to MCB's Δ^ρ; cut sites removed entirely; result lives
in *at-most-n-ary* trees), see `Coproduct.lean`.

## Status

`[UPSTREAM]` candidate; future home something like
`Mathlib.Combinatorics.RootedTree.CoproductDecorated`. Sorry-free.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct
open Finsupp

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### `traceLeaf` — placeholder for a cut subtree -/

/-- The trace-marker placeholder leaf carrying the encoded label `b : β`. -/
def traceLeaf (b : β) : Planar (α ⊕ β) := .node (Sum.inr b) []

/-! ### cutSummandsCP — multiset of (cut forest, trace remainder) pairs

Mirrors `cutSummandsP` (Δ^p): the "extract whole" branch in `augActionCP`
produces `traceLeaf (τ t)` instead of `Option.none`, so the remainder
type is `Planar`, not `Option Planar`.

**Trace-leaf restriction.** The "extract whole" branch fires ONLY when
the input is rooted at `Sum.inl` (an original-decoration vertex). For
inputs rooted at `Sum.inr` (a trace-marker vertex from a previous Δ^c
application), the extract branch is omitted — only the empty-cut summand
survives. This matches MCB Definition 1.2.2's restriction of cuts to
"accessible terms" at internal non-root vertices, which excludes trace
placeholders, AND is required for coassociativity: without the
restriction, iterated Δ^c produces "trace of trace" right-channel terms
that break the coassoc bijection. -/

mutual
/-- Multiset of (cut forest, trace remainder) pairs for a planar tree
    in `Planar (α ⊕ β)`. Each summand is one admissible cut on T
    under the trace-preserving semantics. -/
def cutSummandsCP (τ : Planar (α ⊕ β) → β) : Planar (α ⊕ β) →
    Multiset (Forest (Planar (α ⊕ β)) × Planar (α ⊕ β))
  | .node a cs => (cutListSummandsCP τ cs).map (fun p => (p.1, .node a p.2))
/-- Auxiliary: cut summands for a list of children. The remainder is a
    list of children of the parent (each entry is either an original
    child, a recursively-cut remainder, or a trace placeholder). -/
def cutListSummandsCP (τ : Planar (α ⊕ β) → β) : List (Planar (α ⊕ β)) →
    Multiset (Forest (Planar (α ⊕ β)) × List (Planar (α ⊕ β)))
  | [] => {((0 : Forest (Planar (α ⊕ β))), ([] : List (Planar (α ⊕ β))))}
  | t :: ts =>
      ((augActionCP τ t ×ˢ cutListSummandsCP τ ts) : Multiset _).map
        (fun p => (p.1.1 + p.2.1, p.1.2 :: p.2.2))
/-- Auxiliary: per-child action. For an `Sum.inl`-rooted (non-trace)
    subtree, either extract whole (remainder = `traceLeaf (τ t)`) or
    apply a (possibly empty) cut to t. For a `Sum.inr`-rooted (trace)
    subtree, extract is forbidden — only cuts inherited from
    `cutSummandsCP` survive (the empty cut at minimum). -/
def augActionCP (τ : Planar (α ⊕ β) → β) : Planar (α ⊕ β) →
    Multiset (Forest (Planar (α ⊕ β)) × Planar (α ⊕ β))
  | .node (Sum.inl a) cs =>
      (({Planar.node (Sum.inl a) cs} : Forest (Planar (α ⊕ β))),
        traceLeaf (τ (Planar.node (Sum.inl a) cs))) ::ₘ
        cutSummandsCP τ (Planar.node (Sum.inl a) cs)
  | .node (Sum.inr b) cs =>
      cutSummandsCP τ (Planar.node (Sum.inr b) cs)
end

/-- Recursive formula on a node: cutSummandsCP unfolds via cutListSummandsCP. -/
@[simp] theorem cutSummandsCP_node (τ : Planar (α ⊕ β) → β)
    (a : α ⊕ β) (cs : List (Planar (α ⊕ β))) :
    cutSummandsCP τ (Planar.node a cs) =
      (cutListSummandsCP τ cs).map (fun p => (p.1, .node a p.2)) := by
  unfold cutSummandsCP; rfl

/-- Recursive formula for cutListSummandsCP on empty list. -/
@[simp] theorem cutListSummandsCP_nil (τ : Planar (α ⊕ β) → β) :
    cutListSummandsCP τ ([] : List (Planar (α ⊕ β))) =
      {((0 : Forest (Planar (α ⊕ β))), ([] : List (Planar (α ⊕ β))))} := by
  unfold cutListSummandsCP; rfl

/-- Recursive formula for cutListSummandsCP on a cons list. -/
@[simp] theorem cutListSummandsCP_cons (τ : Planar (α ⊕ β) → β)
    (t : Planar (α ⊕ β)) (ts : List (Planar (α ⊕ β))) :
    cutListSummandsCP τ (t :: ts) =
      ((augActionCP τ t ×ˢ cutListSummandsCP τ ts) : Multiset _).map
        (fun p => (p.1.1 + p.2.1, p.1.2 :: p.2.2)) := by
  conv_lhs => unfold cutListSummandsCP

/-- Recursive formula for augActionCP on an `Sum.inl`-rooted (non-trace)
    subtree: includes the trace-extract branch. -/
@[simp] theorem augActionCP_inl (τ : Planar (α ⊕ β) → β)
    (a : α) (cs : List (Planar (α ⊕ β))) :
    augActionCP τ (Planar.node (Sum.inl a) cs) =
      (({Planar.node (Sum.inl a) cs} : Forest (Planar (α ⊕ β))),
        traceLeaf (τ (Planar.node (Sum.inl a) cs))) ::ₘ
          cutSummandsCP τ (Planar.node (Sum.inl a) cs) := by
  unfold augActionCP; rfl

/-- Recursive formula for augActionCP on an `Sum.inr`-rooted (trace)
    subtree: NO trace-extract branch — only the inherited cut summands. -/
@[simp] theorem augActionCP_inr (τ : Planar (α ⊕ β) → β)
    (b : β) (cs : List (Planar (α ⊕ β))) :
    augActionCP τ (Planar.node (Sum.inr b) cs) =
      cutSummandsCP τ (Planar.node (Sum.inr b) cs) := by
  unfold augActionCP; rfl

/-! ### comulCTreePlanar — tree-level Δ^c

Sum the cut summands as tensors, plus the explicit `T ⊗ 1` term. -/

/-- The **planar tree-level Δ^c** coproduct: explicit `T ⊗ 1` term plus
    the sum of cut-summand tensors with trace-preserving remainders. -/
noncomputable def comulCTreePlanar (τ : Planar (α ⊕ β) → β)
    (T : Planar (α ⊕ β)) :
    ConnesKreimer R (Planar (α ⊕ β)) ⊗[R] ConnesKreimer R (Planar (α ⊕ β)) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Planar (α ⊕ β)))
  + ((cutSummandsCP τ T).map
      (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-! ### comulCForestPlanar — forest-level Δ^c, multiplicative extension -/

/-- The **planar forest-level Δ^c**: multiplicative product of tree-level
    coproducts over the components of the forest. -/
noncomputable def comulCForestPlanar (τ : Planar (α ⊕ β) → β)
    (F : Forest (Planar (α ⊕ β))) :
    ConnesKreimer R (Planar (α ⊕ β)) ⊗[R] ConnesKreimer R (Planar (α ⊕ β)) :=
  (F.map (comulCTreePlanar (R := R) τ)).prod

@[simp] theorem comulCForestPlanar_zero (τ : Planar (α ⊕ β) → β) :
    comulCForestPlanar (R := R) τ (0 : Forest (Planar (α ⊕ β))) = 1 := by
  simp only [comulCForestPlanar, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulCForestPlanar_add (τ : Planar (α ⊕ β) → β)
    (F G : Forest (Planar (α ⊕ β))) :
    comulCForestPlanar (R := R) τ (F + G) =
      comulCForestPlanar (R := R) τ F * comulCForestPlanar (R := R) τ G := by
  unfold comulCForestPlanar
  rw [Multiset.map_add, Multiset.prod_add]

/-! ### comulCMonoidHomP and comulCAlgHomP — AlgHom packaging -/

/-- `comulCForestPlanar τ` as a monoid hom from
    `Multiplicative (Forest (Planar (α ⊕ β)))`. -/
noncomputable def comulCMonoidHomP (τ : Planar (α ⊕ β) → β) :
    Multiplicative (Forest (Planar (α ⊕ β))) →*
      (ConnesKreimer R (Planar (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Planar (α ⊕ β))) where
  toFun F := comulCForestPlanar (R := R) τ F.toAdd
  map_one' := comulCForestPlanar_zero τ
  map_mul' F G := comulCForestPlanar_add τ F.toAdd G.toAdd

/-- The **Δ^c coproduct on `ConnesKreimer R (Planar (α ⊕ β))`** as an
    algebra hom, parameterized by the trace encoder `τ`. -/
noncomputable def comulCAlgHomP (τ : Planar (α ⊕ β) → β) :
    ConnesKreimer R (Planar (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (Planar (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Planar (α ⊕ β)) :=
  AddMonoidAlgebra.lift R
    ((ConnesKreimer R (Planar (α ⊕ β))) ⊗[R]
      (ConnesKreimer R (Planar (α ⊕ β))))
    (Forest (Planar (α ⊕ β))) (comulCMonoidHomP τ)

@[simp] theorem comulCAlgHomP_apply_of' (τ : Planar (α ⊕ β) → β)
    (F : Forest (Planar (α ⊕ β))) :
    comulCAlgHomP (R := R) τ (of' F) = comulCForestPlanar τ F := by
  show AddMonoidAlgebra.lift R _ _ (comulCMonoidHomP τ)
        (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem comulCAlgHomP_apply_ofTree (τ : Planar (α ⊕ β) → β)
    (T : Planar (α ⊕ β)) :
    comulCAlgHomP (R := R) τ (ofTree T) = comulCTreePlanar τ T := by
  unfold ofTree
  rw [comulCAlgHomP_apply_of']
  unfold comulCForestPlanar
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

/-! ### Sanity tests -/

section Tests

/-- A leaf has exactly one cut summand: the empty cut `(0, leaf)`. -/
example (τ : Planar (Unit ⊕ Unit) → Unit) :
    cutSummandsCP τ (Planar.leaf (Sum.inl ()) : Planar (Unit ⊕ Unit))
      = {((0 : Forest (Planar (Unit ⊕ Unit))),
          (Planar.leaf (Sum.inl ()) : Planar (Unit ⊕ Unit)))} := by
  show cutSummandsCP τ (Planar.node (Sum.inl ()) []) = _
  rw [cutSummandsCP_node, cutListSummandsCP_nil]
  rfl

/-- The trace-extract branch sits in `augActionCP`'s output for an
    `Sum.inl`-rooted (non-trace) subtree. This is the structural witness
    that Δ^c (placeholder leaf) differs from Δ^p (`Option.none`). -/
example (τ : Planar (Unit ⊕ Unit) → Unit) :
    (({Planar.leaf (Sum.inl ())} : Forest (Planar (Unit ⊕ Unit))),
      traceLeaf (τ (Planar.leaf (Sum.inl ())))) ∈
        augActionCP τ (Planar.leaf (Sum.inl ()) : Planar (Unit ⊕ Unit)) := by
  show _ ∈ augActionCP τ (Planar.node (Sum.inl ()) [])
  rw [augActionCP_inl]; exact Multiset.mem_cons_self _ _

/-- Trace-marker leaves are NOT extracted by `augActionCP`: only the
    inherited cut summands (the empty cut at minimum) survive. Required
    for coassoc — without this restriction, iterated Δ^c produces
    "trace of trace" terms that break the bijection. -/
example (b : Unit) (τ : Planar (Unit ⊕ Unit) → Unit) :
    augActionCP τ (traceLeaf b : Planar (Unit ⊕ Unit))
      = cutSummandsCP τ (Planar.node (Sum.inr b) []) := by
  show augActionCP τ (Planar.node (Sum.inr b) []) = _
  rw [augActionCP_inr]

/-- The `traceLeaf` placeholder is a `Sum.inr`-labeled leaf. -/
example (b : β) : (traceLeaf b : Planar (α ⊕ β)).arity = 0 := rfl

example (b : β) :
    (traceLeaf b : Planar (α ⊕ β)).label = Sum.inr b := rfl

end Tests

end ConnesKreimer

end RootedTree
