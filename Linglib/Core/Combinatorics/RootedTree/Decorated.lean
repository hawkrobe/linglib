import Mathlib.Algebra.Free
import Mathlib.Data.Multiset.Basic

/-!
# Decorated Binary Rooted Trees @cite{marcolli-chomsky-berwick-2025} @cite{foissy-2002}

The decorated binary rooted tree carrier of the Connes-Kreimer-style
Hopf algebra of (binary nonplanar) decorated forests, parameterized
over a leaf type `α : Type*`.

## Substrate choice

`DecoratedTree α` is a single inductive with three constructors:

- `leaf  : α → DecoratedTree α`
- `trace : DecoratedTree α → DecoratedTree α`
- `node  : DecoratedTree α → DecoratedTree α → DecoratedTree α`

Mathematically this is the free term algebra over the signature
`{leaf : α → 1, trace : 1 → 1, node : 1 × 1 → 1}`. The carrier shape
is the standard one for *decorated* Connes-Kreimer Hopf algebras
(cf. @cite{foissy-2002} on planar decorated rooted-tree Hopf algebras
H^D_{P,R} — generalizing the non-planar Connes-Kreimer H^D_R). Note:
M-C-B themselves do not cite Foissy directly; they appeal to the
Connes-Kreimer-Feynman-graph proof for coassociativity (book p. 38
references). The Foissy attribution here is the formaliser's reading
of the closest mathematical predecessor for the *decorated* binary
case. The `Mul (DecoratedTree α)` instance (via `node`) recovers
`FreeMagma`-style `*` notation; the recursor `recOnMul` mirrors
`FreeMagma.recOnMul`.

## Two faithfulness gaps re. M-C-B Definition 1.1.1

@cite{marcolli-chomsky-berwick-2025} Definition 1.1.1 says the
abstract syntactic-object set is a free non-associative *commutative*
magma `Magma_{na,c}(SO_0, M)`. mathlib's `FreeMagma α` is the
non-commutative version. Two distinct gaps relative to mathlib
infrastructure:

**Gap 1 — Planar vs nonplanar.** `DecoratedTree α` inherits the
planar structure: `node l r ≠ node r l` as an equality. A faithful
encoding would `Quotient` by `node l r ~ node r l`. Proofs that need
the abstract identification require that quotient; this file does
not develop it (see CHANGELOG 0.230.655's note on the in-flight
`FreeCommMagma` work). M-C-B handle this gap implicitly via
equivalence-class drawings — book p. 23 example shows
α∧β∧γ = α∧γ∧β as the same nonplanar tree.

**Gap 2 — Set vs multiset (the singleton-collapse).** M-C-B p. 25
§1.1.3.1's "very mild" remark refers SPECIFICALLY to the
set-vs-multiset clash for syntactic objects: since trees are binary
(not n-ary for n ≥ 3), repeated-label ambiguity at a single node is
limited, and they explicitly identify {a, a} with {a} for binary
nodes. (This is the `idem` axiom the comm-quotient does NOT add by
default.) NOT to be confused with Gap 1 — this is a separate concern.

For workspaces (`Forest α := Multiset (DecoratedTree α)`), the
multiset structure handles the analogous gap at the workspace level
automatically. Both gaps remain open at the *intra-tree* level until
the comm-quotient + singleton-collapse are wired in (Stage 4a/4b per
`scratch/mcb_stage1_plan.md`).

## Trace constructor and self-reference

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.2.4, the
contraction quotient T/^c T_v carries a trace label *T_v* that holds
the contracted subtree as data. To support iterated coproducts
`(Δ ⊗ id) ∘ Δ` (per the proof of Lemma 1.2.10), the trace must be
able to carry a `DecoratedTree α` that itself contains traces. This
forces self-reference in the inductive — hence the third constructor
`trace : DecoratedTree α → DecoratedTree α`.

## Layer status

`[UPSTREAM]` candidate. Future home is something like
`Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.DecoratedTree`. This
file is part of the Stage 0.5 hoist out of `Theories/Syntax/Minimalist/Hopf/`
(per `scratch/mcb_stage1_plan.md`). Namespace is `ConnesKreimer`
(renamed from `Minimalist.Hopf` in Stage 0.7).
-/

namespace ConnesKreimer

/-! ## DecoratedTree -/

/-- A binary nonplanar rooted tree with leaves labelled by `α` and
    self-decoration via `trace`. Three constructors:

    - `leaf a` — a leaf vertex labelled with `a : α`
    - `trace t` — a trace leaf carrying a subtree `t` as data
      (treated as a leaf for tree-traversal; `t` is metadata)
    - `node l r` — a binary internal vertex with children `l` and `r`

    The `trace` constructor enables nested decorations (a trace can
    contain trace-bearing trees), which is essential for iterated
    coproducts `(Δ ⊗ id) ∘ Δ`. -/
inductive DecoratedTree (α : Type*) where
  | leaf  (a : α) : DecoratedTree α
  | trace (t : DecoratedTree α) : DecoratedTree α
  | node  (l r : DecoratedTree α) : DecoratedTree α
  deriving Repr, DecidableEq

namespace DecoratedTree

/-! ## Mathlib-style algebra hooks -/

/-- `DecoratedTree α` is a magma via the `node` constructor, mirroring
    `FreeMagma`. This gives `l * r = .node l r` for free. -/
instance {α : Type*} : Mul (DecoratedTree α) := ⟨.node⟩

/-- `node l r = l * r` by definition. -/
@[simp] theorem node_eq_mul {α : Type*} (l r : DecoratedTree α) :
    node l r = l * r := rfl

/-- Recursor using `*` notation in the `node`/`mul` case, mirroring
    `FreeMagma.recOnMul`. Useful for proofs and definitions that
    prefer the multiplicative interface. -/
@[elab_as_elim]
def recOnMul {α : Type*} {motive : DecoratedTree α → Sort*}
    (t : DecoratedTree α)
    (leaf  : ∀ a, motive (.leaf a))
    (trace : ∀ s, motive s → motive (.trace s))
    (mul   : ∀ a b, motive a → motive b → motive (a * b)) : motive t :=
  match t with
  | .leaf a   => leaf a
  | .trace s  => trace s (recOnMul s leaf trace mul)
  | .node a b => mul a b (recOnMul a leaf trace mul) (recOnMul b leaf trace mul)

/-- Number of leaves in a `DecoratedTree`. Both `.leaf` and `.trace` count
    as leaves (each occupies one leaf vertex in the tree shape; the
    contracted subtree carried by `.trace` is metadata, not part of the
    visible tree). -/
def leafCount {α : Type*} : DecoratedTree α → Nat
  | .leaf _   => 1
  | .trace _  => 1
  | .node l r => l.leafCount + r.leafCount

@[simp] theorem leafCount_leaf {α : Type*} (a : α) :
    (DecoratedTree.leaf a).leafCount = 1 := rfl

@[simp] theorem leafCount_trace {α : Type*} (t : DecoratedTree α) :
    (DecoratedTree.trace t).leafCount = 1 := rfl

@[simp] theorem leafCount_node {α : Type*} (l r : DecoratedTree α) :
    (DecoratedTree.node l r).leafCount = l.leafCount + r.leafCount := rfl

theorem leafCount_pos {α : Type*} (t : DecoratedTree α) : 0 < t.leafCount := by
  induction t with
  | leaf _ => exact Nat.one_pos
  | trace _ _ => exact Nat.one_pos
  | node l r ihl _ihr =>
    simp only [leafCount]
    omega

end DecoratedTree

/-! ## Forest

A forest is a multiset of decorated trees. Disjoint union ⊔
corresponds to `· + ·` on multisets (commutative, ∅ = 0).
@cite{marcolli-chomsky-berwick-2025} Definition 1.2.1. -/

/-- A decorated forest: a multiset of decorated trees. -/
abbrev Forest (α : Type*) := Multiset (DecoratedTree α)

end ConnesKreimer
