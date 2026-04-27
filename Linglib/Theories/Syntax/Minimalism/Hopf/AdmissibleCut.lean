import Linglib.Theories.Syntax.Minimalism.Hopf.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Multiset.Basic

/-!
# Admissible Cuts on Decorated Trees (Hopf-Algebra Layer)
@cite{marcolli-chomsky-berwick-2025}

Per M-C-B 2025 Definition 1.2.6, an **admissible cut** of a binary
rooted tree T is a removal of a collection of edges of T such that no
two lie on the same root-to-leaf path. Equivalently (Lemma 1.2.7), the
data of an admissible cut on T is the same as a forest
F_v = T_{v₁} ⊔ ⋯ ⊔ T_{vₙ} of disjoint accessible terms of T.

This file is **[UPSTREAM]** — generic over the leaf type `α`.

## Crucial M-C-B reading: leaves ARE accessible terms

Per M-C-B Definition 1.2.2, accessible terms are subtrees `T_v` for
`v ∈ V_int(T) := V(T) \ {root of T}`. M-C-B's "internal" excludes the
root vertex but **includes leaves** — so leaves of `T` are accessible
terms. (Verified against the worked example in §1.3.4: for
`T₂ = .node β γ`, the coproduct expansion treats β and γ as
extractable accessible terms.)

## Representation: 5-constructor enum

A `CutShape T` for `T : DecoratedTree α` records cut choices position-
by-position. Leaves admit only the trivial pass-through (no edges to
cut); nodes have four choices based on (cut left edge?) × (cut right
edge?). The antichain condition (M-C-B Def 1.2.6: no two cuts on the
same root-leaf path) is baked in by construction.

## Status

- **[UPSTREAM]** Fully parameterized over leaf type. Once antipode
  lands, ports cleanly to `Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.AdmissibleCut`.
- **No sorries**, no `noncomputable`, no `native_decide`.
-/

namespace Minimalism.Hopf

variable {α : Type}

/-! ## §1: Cut shape

Universe-monomorphic for now (`α : Type`, not `Type*`). Universe
polymorphism is deferred to a follow-up; mathlib upstream will need
it but the partial parameterization here is enough to get the
generic structure right and keep downstream code working. -/

/-- An admissible cut on a decorated tree `T : DecoratedTree α`. -/
inductive CutShape : {α : Type} → DecoratedTree α → Type where
  /-- An α-leaf admits only the empty cut (no edges to cut). -/
  | atLeaf {α : Type} {a : α} : CutShape (.leaf a)
  /-- A trace leaf admits only the empty cut. -/
  | atTrace {α : Type} {t : DecoratedTree α} : CutShape (.trace t)
  /-- Cut both child edges of this node. -/
  | bothCut {α : Type} {l r : DecoratedTree α} : CutShape (.node l r)
  /-- Cut the left child edge, recurse into `r` with sub-cut `cr`. -/
  | onlyLeftCut {α : Type} {l r : DecoratedTree α} (cr : CutShape r) :
      CutShape (.node l r)
  /-- Recurse into `l` with sub-cut `cl`, cut the right child edge. -/
  | onlyRightCut {α : Type} {l r : DecoratedTree α} (cl : CutShape l) :
      CutShape (.node l r)
  /-- Don't cut at this node; recurse in both children. -/
  | bothRecurse {α : Type} {l r : DecoratedTree α} (cl : CutShape l)
      (cr : CutShape r) : CutShape (.node l r)

namespace CutShape

/-! ## §2: The empty (trivial) cut -/

/-- The empty cut on T: extract nothing, leave T unchanged. -/
def empty : (T : DecoratedTree α) → CutShape T
  | .leaf _  => .atLeaf
  | .trace _ => .atTrace
  | .node l r => .bothRecurse (empty l) (empty r)

/-! ## §3: Decidable equality and finite enumeration -/

instance decEq [DecidableEq α] :
    (T : DecoratedTree α) → DecidableEq (CutShape T)
  | .leaf _  => fun
      | .atLeaf, .atLeaf => isTrue rfl
  | .trace _ => fun
      | .atTrace, .atTrace => isTrue rfl
  | .node l r => fun a b =>
      have _ : DecidableEq (CutShape l) := decEq l
      have _ : DecidableEq (CutShape r) := decEq r
      match a, b with
      | .bothCut, .bothCut => isTrue rfl
      | .bothCut, .onlyLeftCut _ => isFalse (by intro h; cases h)
      | .bothCut, .onlyRightCut _ => isFalse (by intro h; cases h)
      | .bothCut, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .onlyLeftCut _, .bothCut => isFalse (by intro h; cases h)
      | .onlyLeftCut cr₁, .onlyLeftCut cr₂ =>
          if h : cr₁ = cr₂ then isTrue (by subst h; rfl)
          else isFalse (by intro heq; cases heq; exact h rfl)
      | .onlyLeftCut _, .onlyRightCut _ => isFalse (by intro h; cases h)
      | .onlyLeftCut _, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .onlyRightCut _, .bothCut => isFalse (by intro h; cases h)
      | .onlyRightCut _, .onlyLeftCut _ => isFalse (by intro h; cases h)
      | .onlyRightCut cl₁, .onlyRightCut cl₂ =>
          if h : cl₁ = cl₂ then isTrue (by subst h; rfl)
          else isFalse (by intro heq; cases heq; exact h rfl)
      | .onlyRightCut _, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .bothCut => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .onlyLeftCut _ => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .onlyRightCut _ => isFalse (by intro h; cases h)
      | .bothRecurse cl₁ cr₁, .bothRecurse cl₂ cr₂ =>
          if h₁ : cl₁ = cl₂ then
            if h₂ : cr₁ = cr₂ then isTrue (by subst h₁; subst h₂; rfl)
            else isFalse (by intro heq; cases heq; exact h₂ rfl)
          else isFalse (by intro heq; cases heq; exact h₁ rfl)

/-- The finite set of all cut shapes on T. -/
def all [DecidableEq α] : (T : DecoratedTree α) → Finset (CutShape T)
  | .leaf _  => {.atLeaf}
  | .trace _ => {.atTrace}
  | .node l r =>
      have _ : DecidableEq (CutShape (.node l r)) := decEq (.node l r)
      have allL : Finset (CutShape l) := all l
      have allR : Finset (CutShape r) := all r
      {CutShape.bothCut}
        ∪ allR.image (fun cr => CutShape.onlyLeftCut cr)
        ∪ allL.image (fun cl => CutShape.onlyRightCut cl)
        ∪ ((allL ×ˢ allR).image (fun p => CutShape.bothRecurse p.1 p.2))

/-- Every cut shape on T is in `all T`. -/
theorem mem_all [DecidableEq α] :
    ∀ (T : DecoratedTree α) (c : CutShape T), c ∈ all T
  | .leaf _, .atLeaf => by simp [all]
  | .trace _, .atTrace => by simp [all]
  | .node l r, .bothCut => by simp [all]
  | .node l r, .onlyLeftCut cr => by
      simp only [all, Finset.mem_union, Finset.mem_image,
        Finset.mem_singleton, Finset.mem_product]
      refine Or.inl (Or.inl (Or.inr ⟨cr, mem_all r cr, rfl⟩))
  | .node l r, .onlyRightCut cl => by
      simp only [all, Finset.mem_union, Finset.mem_image,
        Finset.mem_singleton, Finset.mem_product]
      refine Or.inl (Or.inr ⟨cl, mem_all l cl, rfl⟩)
  | .node l r, .bothRecurse cl cr => by
      simp only [all, Finset.mem_union, Finset.mem_image,
        Finset.mem_singleton, Finset.mem_product]
      refine Or.inr ⟨(cl, cr), ⟨mem_all l cl, mem_all r cr⟩, rfl⟩

instance fintype [DecidableEq α] (T : DecoratedTree α) :
    Fintype (CutShape T) where
  elems := all T
  complete := mem_all T

/-! ## §4: Pruned forest `F_v` and remainder `T/^c F_v`

For an admissible cut `c : CutShape T`:
- `cutForest c : Forest α` is the multiset of subtrees being extracted
  (M-C-B's F_v in Def 1.2.4 / Lemma 1.2.7)
- `remainder c : DecoratedTree α` is the tree obtained by replacing
  each cut subtree with a `.trace` leaf labelled with what was cut
  (M-C-B's T/^c F_v in Def 1.2.4)

The trace label is first-class: extracting `T` produces a remainder
containing `.trace T`, and `T` itself can already contain trace
leaves (from a previous coproduct iteration). No fallback,
no placeholder, no unsoundness. -/

/-- The pruned forest of a cut: the multiset of extracted subtrees.
    M-C-B Definition 1.2.4: F_v = T_{v_1} ⊔ ⋯ ⊔ T_{v_n}. -/
def cutForest : ∀ {T : DecoratedTree α}, CutShape T → Forest α
  | .leaf _, .atLeaf => 0
  | .trace _, .atTrace => 0
  | .node l r, .bothCut => ({l, r} : Multiset (DecoratedTree α))
  | .node l _, .onlyLeftCut cr =>
      ({l} : Multiset (DecoratedTree α)) + cutForest cr
  | .node _ r, .onlyRightCut cl =>
      cutForest cl + ({r} : Multiset (DecoratedTree α))
  | .node _ _, .bothRecurse cl cr => cutForest cl + cutForest cr

/-- The remainder of a cut (contraction-with-trace, M-C-B Def 1.2.4):
    T with each cut subtree replaced by a `.trace` leaf carrying the
    cut subtree as metadata. The `DecoratedTree.trace` constructor
    takes any subtree (including trace-bearing ones), so iterated
    cuts compose without any fallback or placeholder. Used by Δ^c. -/
def remainder : ∀ {T : DecoratedTree α}, CutShape T → DecoratedTree α
  | .leaf tok, .atLeaf => .leaf tok
  | .trace t,  .atTrace => .trace t
  | .node l r, .bothCut => .node (.trace l) (.trace r)
  | .node l _, .onlyLeftCut cr => .node (.trace l) (remainder cr)
  | .node _ r, .onlyRightCut cl => .node (remainder cl) (.trace r)
  | .node _ _, .bothRecurse cl cr => .node (remainder cl) (remainder cr)

/-- The remainder of a cut (deletion-with-rebinarization, M-C-B
    Def 1.2.5): T with each cut subtree REMOVED (no trace), then
    edge-contracted to recover binarity. Used by Δ^d (the coproduct
    that linguistic Merge uses, per M-C-B Lemma 1.5.1).

    Returns `Option (DecoratedTree α)` because cutting both children
    of a node leaves a vertex with no children — neither a leaf nor
    a binary node. Such a vertex collapses (returns `None`); upstream
    binders absorb the collapse via edge contraction:

    - At a node, if BOTH children's deletion-remainder collapse, the
      node itself collapses.
    - At a node, if ONE child collapses, the other becomes the
      remainder (the parent's edge to the survivor is "contracted",
      effectively absorbing the parent into the survivor).

    This handling is faithful to M-C-B Def 1.2.5's "unique maximal
    binary rooted tree obtainable via contraction." -/
def remainderDeletion : ∀ {T : DecoratedTree α},
    CutShape T → Option (DecoratedTree α)
  | .leaf tok, .atLeaf => some (.leaf tok)
  | .trace t,  .atTrace => some (.trace t)
  | .node _ _, .bothCut => none
  | .node _ _, .onlyLeftCut cr => remainderDeletion cr
  | .node _ _, .onlyRightCut cl => remainderDeletion cl
  | .node _ _, .bothRecurse cl cr =>
      match remainderDeletion cl, remainderDeletion cr with
      | some l', some r' => some (.node l' r')
      | some l', none    => some l'
      | none,    some r' => some r'
      | none,    none    => none

/-! ## §5: Sanity checks -/

/-- The empty cut extracts nothing. -/
@[simp] theorem cutForest_empty : ∀ (T : DecoratedTree α),
    (empty T).cutForest = (0 : Forest α)
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      show (CutShape.bothRecurse (empty l) (empty r)).cutForest = (0 : Forest α)
      rw [cutForest, cutForest_empty l, cutForest_empty r]
      rfl

/-- The empty cut leaves T unchanged. -/
@[simp] theorem remainder_empty : ∀ (T : DecoratedTree α),
    (empty T).remainder = T
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      show (CutShape.bothRecurse (empty l) (empty r)).remainder = .node l r
      rw [remainder, remainder_empty l, remainder_empty r]

/-- Cut both child edges of a node: extracts both children. -/
@[simp] theorem cutForest_bothCut {l r : DecoratedTree α} :
    (bothCut : CutShape (.node l r)).cutForest =
      ({l, r} : Multiset (DecoratedTree α)) := rfl

end CutShape

end Minimalism.Hopf
