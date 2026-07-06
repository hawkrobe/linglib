import Linglib.Core.Algebra.RootedTree.Coproduct.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

set_option autoImplicit false

/-!
# Δ^c (trace-aware admissible-cut) coproduct on `RoseTree (α ⊕ β)`
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The **trace-preserving variant** of the Connes-Kreimer admissible-cut
coproduct on n-ary rooted trees, parameterized by a trace encoder
`τ : RoseTree (α ⊕ β) → β`. For a tree T:

  Δ^c_τ(T) = T ⊗ 1 + Σ_{(F, R) ∈ cutSummandsCP τ T} of' F ⊗ ofTree R

where the remainder `R` keeps a placeholder leaf at every cut site —
the leaf's label is `Sum.inr (τ T_v)` for the cut subtree `T_v`. This
contrasts with the deletion variant `Δ^ρ` (sibling `Pruning.lean`),
where cut sites simply disappear (the parent loses a child).

## Carrier and encoder

The carrier is `RoseTree (α ⊕ β)` directly: original-decoration vertices
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
- **Identity trace**: `τ = id` if β = RoseTree (α ⊕ β) — placeholder
  carries the full cut subtree as label. Closest match to the book's
  notation `F̄_v`.
- **Quotient trace**: `τ` projects to syntactic features, semantic
  representations, etc. (consumer-specific).

## Embedding α-only trees

The substrate is encoder-free: an α-only tree T : RoseTree α is embedded
into RoseTree (α ⊕ β) via `RoseTree.map Sum.inl T`. No separate
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
def traceLeaf (b : β) : RoseTree (α ⊕ β) := .node (Sum.inr b) []

/-! ### Δ^c extraction policy -/

/-- The Δ^c extraction policy: for `Sum.inl`-rooted (non-trace)
    subtrees, extract whole leaving a single `traceLeaf (τ t)` in the
    parent's child slot. For `Sum.inr`-rooted (trace) subtrees, decline
    to extract. -/
def extractC (τ : RoseTree (α ⊕ β) → β) :
    RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))
  | t@(.node (Sum.inl _) _) => some [traceLeaf (τ t)]
  | .node (Sum.inr _) _ => none

@[simp] theorem extractC_inl (τ : RoseTree (α ⊕ β) → β)
    (a : α) (cs : List (RoseTree (α ⊕ β))) :
    extractC τ (RoseTree.node (Sum.inl a) cs) =
      some [traceLeaf (τ (RoseTree.node (Sum.inl a) cs))] := rfl

@[simp] theorem extractC_inr (τ : RoseTree (α ⊕ β) → β)
    (b : β) (cs : List (RoseTree (α ⊕ β))) :
    extractC τ (RoseTree.node (Sum.inr b) cs) = none := rfl

/-! ### `cutSummandsCP` — Δ^c cut enumeration via the generic `cutSummandsG`

Defined as `cutSummandsG (extractC τ)`. The generic-side simp lemmas
(`cutSummandsG_node`, `cutListSummandsG_*`, `augActionG_*`) compose with
`extractC_inl`/`extractC_inr` to give the Δ^c-specific reductions. -/

/-- The Δ^c cut summands: cuts at non-trace subtrees with trace
    placeholders, skipping cuts at trace leaves. -/
def cutSummandsCP (τ : RoseTree (α ⊕ β) → β) :
    RoseTree (α ⊕ β) → Multiset (Forest (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β)) :=
  cutSummandsG (extractC τ)

theorem cutSummandsCP_def (τ : RoseTree (α ⊕ β) → β) (T : RoseTree (α ⊕ β)) :
    cutSummandsCP τ T = cutSummandsG (extractC τ) T := rfl

@[simp] theorem cutSummandsCP_node (τ : RoseTree (α ⊕ β) → β)
    (a : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    cutSummandsCP τ (RoseTree.node a cs) =
      (cutListSummandsG (extractC τ) cs).map (fun p => (p.1, .node a p.2)) := by
  rw [cutSummandsCP_def, cutSummandsG_node]

/-! ### comulCTreePlanar — tree-level Δ^c

Sum the cut summands as tensors, plus the explicit `T ⊗ 1` term. -/

/-- The **tree-level Δ^c** coproduct: explicit `T ⊗ 1` term plus the sum
    of cut-summand tensors with trace-preserving remainders. -/
noncomputable def comulCTreePlanar (τ : RoseTree (α ⊕ β) → β)
    (T : RoseTree (α ⊕ β)) :
    ConnesKreimer R (RoseTree (α ⊕ β)) ⊗[R] ConnesKreimer R (RoseTree (α ⊕ β)) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (RoseTree (α ⊕ β)))
  + ((cutSummandsCP τ T).map
      (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-! ### comulCForestPlanar — forest-level Δ^c, multiplicative extension -/

/-- The **forest-level Δ^c**: multiplicative product of tree-level
    coproducts over the components of the forest. -/
noncomputable def comulCForestPlanar (τ : RoseTree (α ⊕ β) → β)
    (F : Forest (RoseTree (α ⊕ β))) :
    ConnesKreimer R (RoseTree (α ⊕ β)) ⊗[R] ConnesKreimer R (RoseTree (α ⊕ β)) :=
  (F.map (comulCTreePlanar (R := R) τ)).prod

@[simp] theorem comulCForestPlanar_zero (τ : RoseTree (α ⊕ β) → β) :
    comulCForestPlanar (R := R) τ (0 : Forest (RoseTree (α ⊕ β))) = 1 := by
  simp only [comulCForestPlanar, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulCForestPlanar_add (τ : RoseTree (α ⊕ β) → β)
    (F G : Forest (RoseTree (α ⊕ β))) :
    comulCForestPlanar (R := R) τ (F + G) =
      comulCForestPlanar (R := R) τ F * comulCForestPlanar (R := R) τ G := by
  unfold comulCForestPlanar
  rw [Multiset.map_add, Multiset.prod_add]

/-! ### comulCMonoidHomP and comulCAlgHomP — AlgHom packaging -/

/-- `comulCForestPlanar τ` as a monoid hom from
    `Multiplicative (Forest (RoseTree (α ⊕ β)))`. -/
noncomputable def comulCMonoidHomP (τ : RoseTree (α ⊕ β) → β) :
    Multiplicative (Forest (RoseTree (α ⊕ β))) →*
      (ConnesKreimer R (RoseTree (α ⊕ β)) ⊗[R]
        ConnesKreimer R (RoseTree (α ⊕ β))) where
  toFun F := comulCForestPlanar (R := R) τ F.toAdd
  map_one' := comulCForestPlanar_zero τ
  map_mul' F G := comulCForestPlanar_add τ F.toAdd G.toAdd

/-- The **Δ^c coproduct on `ConnesKreimer R (RoseTree (α ⊕ β))`** as an
    algebra hom, parameterized by the trace encoder `τ`. -/
noncomputable def comulCAlgHomP (τ : RoseTree (α ⊕ β) → β) :
    ConnesKreimer R (RoseTree (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (RoseTree (α ⊕ β)) ⊗[R]
        ConnesKreimer R (RoseTree (α ⊕ β)) :=
  ConnesKreimer.lift (comulCMonoidHomP τ)

@[simp] theorem comulCAlgHomP_apply_of' (τ : RoseTree (α ⊕ β) → β)
    (F : Forest (RoseTree (α ⊕ β))) :
    comulCAlgHomP (R := R) τ (of' F) = comulCForestPlanar τ F := by
  rw [comulCAlgHomP, ConnesKreimer.lift_of']
  rfl

@[simp] theorem comulCAlgHomP_apply_ofTree (τ : RoseTree (α ⊕ β) → β)
    (T : RoseTree (α ⊕ β)) :
    comulCAlgHomP (R := R) τ (ofTree T) = comulCTreePlanar τ T := by
  unfold ofTree
  rw [comulCAlgHomP_apply_of']
  unfold comulCForestPlanar
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

/-! ### Sanity tests -/

section Tests

/-- A leaf has exactly one cut summand: the empty cut `(0, leaf)`. -/
example (τ : RoseTree (Unit ⊕ Unit) → Unit) :
    cutSummandsCP τ (RoseTree.leaf (Sum.inl ()) : RoseTree (Unit ⊕ Unit))
      = {((0 : Forest (RoseTree (Unit ⊕ Unit))),
          (RoseTree.leaf (Sum.inl ()) : RoseTree (Unit ⊕ Unit)))} := by
  rw [RoseTree.leaf, cutSummandsCP_node, cutListSummandsG_nil]
  rfl

/-- The trace-extract branch sits in the augmented per-child action for
    a `Sum.inl`-rooted subtree. Witness that Δ^c (placeholder leaf)
    differs from Δ^ρ (admissible-cut pruning). -/
example (τ : RoseTree (Unit ⊕ Unit) → Unit) :
    (({RoseTree.leaf (Sum.inl ())} : Forest (RoseTree (Unit ⊕ Unit))),
      [traceLeaf (τ (RoseTree.leaf (Sum.inl ())))]) ∈
        augActionG (extractC τ)
          (RoseTree.leaf (Sum.inl ()) : RoseTree (Unit ⊕ Unit)) := by
  rw [RoseTree.leaf, augActionG_eq_some _ _ _ (extractC_inl τ () [])]
  exact Multiset.mem_cons_self _ _

/-- Trace-marker leaves are NOT extracted: `extractC τ` returns `none`,
    so the per-child action only inherits cuts from `cutSummandsG`. -/
example (b : Unit) (τ : RoseTree (Unit ⊕ Unit) → Unit) :
    augActionG (extractC τ) (traceLeaf b : RoseTree (Unit ⊕ Unit))
      = (cutSummandsG (extractC τ) (RoseTree.node (Sum.inr b) [])).map
          (fun p => (p.1, [p.2])) :=
  augActionG_eq_none _ _ (extractC_inr τ b [])

/-- The `traceLeaf` placeholder is a `Sum.inr`-labeled leaf. -/
example (b : β) : (traceLeaf b : RoseTree (α ⊕ β)).arity = 0 := rfl

example (b : β) :
    (traceLeaf b : RoseTree (α ⊕ β)).value = Sum.inr b := rfl

end Tests

end ConnesKreimer

end RootedTree
