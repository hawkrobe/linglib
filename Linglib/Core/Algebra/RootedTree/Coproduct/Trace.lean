import Linglib.Core.Algebra.RootedTree.Coproduct.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

set_option autoImplicit false

/-!
# Δ^c (trace-aware admissible-cut) coproduct on `Tree (α ⊕ β)`
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The **trace-preserving variant** of the Connes-Kreimer admissible-cut
coproduct on n-ary rooted trees, parameterized by a trace encoder
`τ : Tree (α ⊕ β) → β`. For a tree T:

  Δ^c_τ(T) = T ⊗ 1 + Σ_{c : Cut T} of'(cutForest c) ⊗ ofTree(remainderTrace c)

where `remainderTrace c` keeps a placeholder leaf at every cut site —
the leaf's label is `Sum.inr (τ T_v)` for the cut subtree `T_v`. This
contrasts with the deletion variant `Δ^ρ` (sibling `Pruning.lean`),
where cut sites simply disappear (the parent loses a child).

## Carrier and encoder

The carrier is `Tree (α ⊕ β)` directly: original-decoration vertices
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
- **Identity trace**: `τ = id` if β = Tree (α ⊕ β) — placeholder
  carries the full cut subtree as label. Closest match to the book's
  notation `F̄_v`.
- **Quotient trace**: `τ` projects to syntactic features, semantic
  representations, etc. (consumer-specific).

## Embedding α-only trees

The substrate is encoder-free: an α-only tree T : Tree α is embedded
into Tree (α ⊕ β) via `Tree.map Sum.inl T`. No separate
`mapDecoration` primitive.

## MCB anchors

- **Definition 1.2.4** (book p. 30): T/^c F_v — contraction of each
  cut subtree to its root vertex, which becomes a leaf carrying a
  trace label F̄_v. Parent arity preserved.
- **Definition 1.2.8** (book p. 33), formula (1.2.8) with ω = c: the
  coproduct itself, Δ^c(T) := T ⊗ 1 + 1 ⊗ T + Σ F_v ⊗ T/^c F_v. The
  `1 ⊗ T` term is absorbed into the sum here as the empty-cut summand
  (matching `Pruning.lean`'s convention; the `T ⊗ 1` term is kept
  explicit).
- **Remark 1.2.9** (book p. 34): on nonplanar binary rooted trees, Δ^c
  is the restriction of the coproduct of the Connes-Kreimer Hopf
  algebra of Feynman graphs.
- **Lemma 1.2.10** (book p. 35): coassociativity of Δ^c (proved at the
  Nonplanar layer; not in this file).

The trace-leaf contraction underlies the C-I (semantic) interface for
FormCopy in the MCB analysis. For the admissible-cut variant Δ^ρ
(corresponds to MCB's Δ^ρ; cut sites removed entirely; result lives
in *at-most-n-ary* trees), see `Pruning.lean`.

## Architecture

The cut enumeration is delegated to `Defs.lean`'s `cutSummandsG (extract)`,
parameterized by an extraction policy. Δ^c specializes via the extraction
policy `extractC τ`:

- For `Sum.inl`-rooted (non-trace) subtrees: extract whole, leaving
  `[traceLeaf (τ t)]` as a single replacement leaf.
- For `Sum.inr`-rooted (trace) subtrees: do not extract. Required for
  coassoc (without this restriction, iterated Δ^c produces "trace of
  trace" right-channel terms that break the bijection); also matches
  MCB Definition 1.2.2's restriction of cuts to "accessible terms" at
  internal non-root vertices, which excludes trace placeholders.

## Status

`[UPSTREAM]` candidate; future home something like
`Mathlib.Combinatorics.RootedTree.CoproductDecorated`. Sorry-free.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### `traceLeaf` — placeholder for a cut subtree -/

/-- The trace-marker placeholder leaf carrying the encoded label `b : β`. -/
def traceLeaf (b : β) : Tree (α ⊕ β) := .node (Sum.inr b) []

/-! ### Δ^c extraction policy -/

/-- The Δ^c extraction policy: for `Sum.inl`-rooted (non-trace)
    subtrees, extract whole leaving a single `traceLeaf (τ t)` in the
    parent's child slot. For `Sum.inr`-rooted (trace) subtrees, decline
    to extract. -/
def extractC (τ : Tree (α ⊕ β) → β) :
    Tree (α ⊕ β) → Option (List (Tree (α ⊕ β)))
  | t@(.node (Sum.inl _) _) => some [traceLeaf (τ t)]
  | .node (Sum.inr _) _ => none

@[simp] theorem extractC_inl (τ : Tree (α ⊕ β) → β)
    (a : α) (cs : List (Tree (α ⊕ β))) :
    extractC τ (Tree.node (Sum.inl a) cs) =
      some [traceLeaf (τ (Tree.node (Sum.inl a) cs))] := rfl

@[simp] theorem extractC_inr (τ : Tree (α ⊕ β) → β)
    (b : β) (cs : List (Tree (α ⊕ β))) :
    extractC τ (Tree.node (Sum.inr b) cs) = none := rfl

/-! ### `cutSummandsCP` — Δ^c cut enumeration via the generic `cutSummandsG`

Defined as `cutSummandsG (extractC τ)`. The generic-side simp lemmas
(`cutSummandsG_node`, `cutListSummandsG_*`, `augActionG_*`) compose with
`extractC_inl`/`extractC_inr` to give the Δ^c-specific reductions. -/

/-- The Δ^c cut summands: cuts at non-trace subtrees with trace
    placeholders, skipping cuts at trace leaves. -/
def cutSummandsCP (τ : Tree (α ⊕ β) → β) :
    Tree (α ⊕ β) → Multiset (Forest (Tree (α ⊕ β)) × Tree (α ⊕ β)) :=
  cutSummandsG (extractC τ)

theorem cutSummandsCP_def (τ : Tree (α ⊕ β) → β) (T : Tree (α ⊕ β)) :
    cutSummandsCP τ T = cutSummandsG (extractC τ) T := rfl

@[simp] theorem cutSummandsCP_node (τ : Tree (α ⊕ β) → β)
    (a : α ⊕ β) (cs : List (Tree (α ⊕ β))) :
    cutSummandsCP τ (Tree.node a cs) =
      (cutListSummandsG (extractC τ) cs).map (fun p => (p.1, .node a p.2)) := by
  rw [cutSummandsCP_def, cutSummandsG_node]

/-! ### comulCTreePlanar — tree-level Δ^c

Sum the cut summands as tensors, plus the explicit `T ⊗ 1` term. -/

/-- The **tree-level Δ^c** coproduct: explicit `T ⊗ 1` term plus the sum
    of cut-summand tensors with trace-preserving remainders. -/
noncomputable def comulCTreePlanar (τ : Tree (α ⊕ β) → β)
    (T : Tree (α ⊕ β)) :
    ConnesKreimer R (Tree (α ⊕ β)) ⊗[R] ConnesKreimer R (Tree (α ⊕ β)) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Tree (α ⊕ β)))
  + ((cutSummandsCP τ T).map
      (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-! ### comulCForestPlanar — forest-level Δ^c, multiplicative extension -/

/-- The **forest-level Δ^c**: multiplicative product of tree-level
    coproducts over the components of the forest. -/
noncomputable def comulCForestPlanar (τ : Tree (α ⊕ β) → β)
    (F : Forest (Tree (α ⊕ β))) :
    ConnesKreimer R (Tree (α ⊕ β)) ⊗[R] ConnesKreimer R (Tree (α ⊕ β)) :=
  (F.map (comulCTreePlanar (R := R) τ)).prod

@[simp] theorem comulCForestPlanar_zero (τ : Tree (α ⊕ β) → β) :
    comulCForestPlanar (R := R) τ (0 : Forest (Tree (α ⊕ β))) = 1 := by
  simp only [comulCForestPlanar, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulCForestPlanar_add (τ : Tree (α ⊕ β) → β)
    (F G : Forest (Tree (α ⊕ β))) :
    comulCForestPlanar (R := R) τ (F + G) =
      comulCForestPlanar (R := R) τ F * comulCForestPlanar (R := R) τ G := by
  unfold comulCForestPlanar
  rw [Multiset.map_add, Multiset.prod_add]

/-! ### comulCMonoidHomP and comulCAlgHomP — AlgHom packaging -/

/-- `comulCForestPlanar τ` as a monoid hom from
    `Multiplicative (Forest (Tree (α ⊕ β)))`. -/
noncomputable def comulCMonoidHomP (τ : Tree (α ⊕ β) → β) :
    Multiplicative (Forest (Tree (α ⊕ β))) →*
      (ConnesKreimer R (Tree (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Tree (α ⊕ β))) where
  toFun F := comulCForestPlanar (R := R) τ F.toAdd
  map_one' := comulCForestPlanar_zero τ
  map_mul' F G := comulCForestPlanar_add τ F.toAdd G.toAdd

/-- The **Δ^c coproduct on `ConnesKreimer R (Tree (α ⊕ β))`** as an
    algebra hom, parameterized by the trace encoder `τ`. -/
noncomputable def comulCAlgHomP (τ : Tree (α ⊕ β) → β) :
    ConnesKreimer R (Tree (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (Tree (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Tree (α ⊕ β)) :=
  AddMonoidAlgebra.lift R
    ((ConnesKreimer R (Tree (α ⊕ β))) ⊗[R]
      (ConnesKreimer R (Tree (α ⊕ β))))
    (Forest (Tree (α ⊕ β))) (comulCMonoidHomP τ)

@[simp] theorem comulCAlgHomP_apply_of' (τ : Tree (α ⊕ β) → β)
    (F : Forest (Tree (α ⊕ β))) :
    comulCAlgHomP (R := R) τ (of' F) = comulCForestPlanar τ F := by
  show AddMonoidAlgebra.lift R _ _ (comulCMonoidHomP τ)
        (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem comulCAlgHomP_apply_ofTree (τ : Tree (α ⊕ β) → β)
    (T : Tree (α ⊕ β)) :
    comulCAlgHomP (R := R) τ (ofTree T) = comulCTreePlanar τ T := by
  unfold ofTree
  rw [comulCAlgHomP_apply_of']
  unfold comulCForestPlanar
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

/-! ### Sanity tests -/

section Tests

/-- A leaf has exactly one cut summand: the empty cut `(0, leaf)`. -/
example (τ : Tree (Unit ⊕ Unit) → Unit) :
    cutSummandsCP τ (Tree.leaf (Sum.inl ()) : Tree (Unit ⊕ Unit))
      = {((0 : Forest (Tree (Unit ⊕ Unit))),
          (Tree.leaf (Sum.inl ()) : Tree (Unit ⊕ Unit)))} := by
  rw [Tree.leaf, cutSummandsCP_node, cutListSummandsG_nil]
  rfl

/-- The trace-extract branch sits in the augmented per-child action for
    a `Sum.inl`-rooted subtree. Witness that Δ^c (placeholder leaf)
    differs from Δ^ρ (admissible-cut pruning). -/
example (τ : Tree (Unit ⊕ Unit) → Unit) :
    (({Tree.leaf (Sum.inl ())} : Forest (Tree (Unit ⊕ Unit))),
      [traceLeaf (τ (Tree.leaf (Sum.inl ())))]) ∈
        augActionG (extractC τ)
          (Tree.leaf (Sum.inl ()) : Tree (Unit ⊕ Unit)) := by
  rw [Tree.leaf, augActionG_eq_some _ _ _ (extractC_inl τ () [])]
  exact Multiset.mem_cons_self _ _

/-- Trace-marker leaves are NOT extracted: `extractC τ` returns `none`,
    so the per-child action only inherits cuts from `cutSummandsG`. -/
example (b : Unit) (τ : Tree (Unit ⊕ Unit) → Unit) :
    augActionG (extractC τ) (traceLeaf b : Tree (Unit ⊕ Unit))
      = (cutSummandsG (extractC τ) (Tree.node (Sum.inr b) [])).map
          (fun p => (p.1, [p.2])) :=
  augActionG_eq_none _ _ (extractC_inr τ b [])

/-- The `traceLeaf` placeholder is a `Sum.inr`-labeled leaf. -/
example (b : β) : (traceLeaf b : Tree (α ⊕ β)).arity = 0 := rfl

example (b : β) :
    (traceLeaf b : Tree (α ⊕ β)).value = Sum.inr b := rfl

end Tests

end ConnesKreimer

end RootedTree
