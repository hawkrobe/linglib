import Linglib.Core.Combinatorics.RootedTree.Decorated
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Multiset.Basic

/-!
# Admissible Cuts on Decorated Trees @cite{marcolli-chomsky-berwick-2025}

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.2.6, an
**admissible cut** of a binary rooted tree T is a removal of a
collection of edges of T such that no two lie on the same root-to-leaf
path. Equivalently (Lemma 1.2.7), the data of an admissible cut on T
is the same as a forest F_v = T_{v₁} ⊔ ⋯ ⊔ T_{vₙ} of disjoint
accessible terms of T.

This file is **[UPSTREAM]** — generic over the leaf type `α`.

## Crucial M-C-B reading: leaves ARE accessible terms

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.2.2, accessible
terms are subtrees `T_v` for `v ∈ V_int(T) := V(T) \ {root of T}`.
M-C-B's "internal" excludes the root vertex but **includes leaves** —
so leaves of `T` are accessible terms. (Verified against the worked
example on book p. 35, inline in §1.2 just before §1.2.1: for
T = α∧(β∧γ) with α="eat(en)", β="the", γ="apple", the Δ^c expansion
has α, β, γ all appearing as extractable accessible terms in the left
channel.)

## Representation: 5-constructor enum

A `CutShape T` for `T : DecoratedTree α` records cut choices position-
by-position. Leaves admit only the trivial pass-through (no edges to
cut); nodes have four choices based on (cut left edge?) × (cut right
edge?). The antichain condition (M-C-B Def 1.2.6: no two cuts on the
same root-leaf path) is baked in by construction.

## Layer status

`[UPSTREAM]`. Future home is something like
`Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.AdmissibleCut`. This
file is part of the Stage 0.5 hoist out of `Theories/Syntax/Minimalist/Hopf/`
(per `scratch/mcb_stage1_plan.md`).

- **No sorries**, no `noncomputable`, no `decide`.
-/

namespace ConnesKreimer

variable {α : Type*}

/-! ## §1: Cut shape

Universe-polymorphic in `α : Type*` since Stage 1.6. The inductive
takes `α` as a parameter (not a per-constructor index), which lets
mathlib upstream reuse this construction over arbitrary leaf types. -/

/-- An admissible cut on a decorated tree `T : DecoratedTree α`.

    **Trace-extraction restriction (substrate fix for coassoc).** The cuts that
    EXTRACT a child subtree (`bothCut`, `onlyLeftCut`, `onlyRightCut`) require
    that child to NOT be a `.trace` marker (`IsNotTrace`). Without this
    restriction, iterated cuts on the remainder of an outer cut would
    accumulate `.trace (.trace _)` nesting, breaking the cuts-of-cuts bijection
    (M-C-B Lemma 1.2.10 / Foissy 2002 §2).

    The `bothRecurse` constructor — which doesn't extract anything at this node —
    has no restriction; it composes recursively into the children's CutShapes.
    The atomic `atLeaf` / `atTrace` constructors are also unrestricted.

    See `Linglib/Scratch/CoassocCheck.lean` for the explicit verification that
    the unrestricted version (no `IsNotTrace` hypotheses) breaks coassoc. -/
inductive CutShape {α : Type*} : DecoratedTree α → Type _ where
  /-- An α-leaf admits only the empty cut (no edges to cut). -/
  | atLeaf {a : α} : CutShape (.leaf a)
  /-- A trace leaf admits only the empty cut. -/
  | atTrace {t : DecoratedTree α} : CutShape (.trace t)
  /-- Cut both child edges of this node. Requires both children to be
      non-trace (cuts cannot extract `.trace` markers). -/
  | bothCut {l r : DecoratedTree α} (hl : DecoratedTree.IsNotTrace l)
      (hr : DecoratedTree.IsNotTrace r) : CutShape (.node l r)
  /-- Cut the left child edge, recurse into `r` with sub-cut `cr`. Requires
      the left child to be non-trace. -/
  | onlyLeftCut {l r : DecoratedTree α} (hl : DecoratedTree.IsNotTrace l)
      (cr : CutShape r) : CutShape (.node l r)
  /-- Recurse into `l` with sub-cut `cl`, cut the right child edge. Requires
      the right child to be non-trace. -/
  | onlyRightCut {l r : DecoratedTree α} (hr : DecoratedTree.IsNotTrace r)
      (cl : CutShape l) : CutShape (.node l r)
  /-- Don't cut at this node; recurse in both children. No restrictions
      since nothing is extracted at this level. -/
  | bothRecurse {l r : DecoratedTree α} (cl : CutShape l)
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
      | .bothCut _ _, .bothCut _ _ => isTrue rfl
      | .bothCut _ _, .onlyLeftCut _ _ => isFalse (by intro h; cases h)
      | .bothCut _ _, .onlyRightCut _ _ => isFalse (by intro h; cases h)
      | .bothCut _ _, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .onlyLeftCut _ _, .bothCut _ _ => isFalse (by intro h; cases h)
      | .onlyLeftCut _ cr₁, .onlyLeftCut _ cr₂ =>
          if h : cr₁ = cr₂ then isTrue (by subst h; rfl)
          else isFalse (by intro heq; cases heq; exact h rfl)
      | .onlyLeftCut _ _, .onlyRightCut _ _ => isFalse (by intro h; cases h)
      | .onlyLeftCut _ _, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .onlyRightCut _ _, .bothCut _ _ => isFalse (by intro h; cases h)
      | .onlyRightCut _ _, .onlyLeftCut _ _ => isFalse (by intro h; cases h)
      | .onlyRightCut _ cl₁, .onlyRightCut _ cl₂ =>
          if h : cl₁ = cl₂ then isTrue (by subst h; rfl)
          else isFalse (by intro heq; cases heq; exact h rfl)
      | .onlyRightCut _ _, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .bothCut _ _ => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .onlyLeftCut _ _ => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .onlyRightCut _ _ => isFalse (by intro h; cases h)
      | .bothRecurse cl₁ cr₁, .bothRecurse cl₂ cr₂ =>
          if h₁ : cl₁ = cl₂ then
            if h₂ : cr₁ = cr₂ then isTrue (by subst h₁; subst h₂; rfl)
            else isFalse (by intro heq; cases heq; exact h₂ rfl)
          else isFalse (by intro heq; cases heq; exact h₁ rfl)

/-- The finite set of all cut shapes on T. The `bothCut` / `onlyLeftCut` /
    `onlyRightCut` constructors are conditionally included based on whether the
    relevant children pass `IsNotTrace`. -/
def all [DecidableEq α] : (T : DecoratedTree α) → Finset (CutShape T)
  | .leaf _  => {.atLeaf}
  | .trace _ => {.atTrace}
  | .node l r =>
      have _ : DecidableEq (CutShape (.node l r)) := decEq (.node l r)
      have allL : Finset (CutShape l) := all l
      have allR : Finset (CutShape r) := all r
      have bothCutSet : Finset (CutShape (.node l r)) :=
        if hl : DecoratedTree.IsNotTrace l then
          if hr : DecoratedTree.IsNotTrace r then {CutShape.bothCut hl hr}
          else ∅
        else ∅
      have leftCutSet : Finset (CutShape (.node l r)) :=
        if hl : DecoratedTree.IsNotTrace l then
          allR.image (fun cr => CutShape.onlyLeftCut hl cr)
        else ∅
      have rightCutSet : Finset (CutShape (.node l r)) :=
        if hr : DecoratedTree.IsNotTrace r then
          allL.image (fun cl => CutShape.onlyRightCut hr cl)
        else ∅
      bothCutSet ∪ leftCutSet ∪ rightCutSet
        ∪ ((allL ×ˢ allR).image (fun p => CutShape.bothRecurse p.1 p.2))

/-- Every cut shape on T is in `all T`. -/
theorem mem_all [DecidableEq α] :
    ∀ (T : DecoratedTree α) (c : CutShape T), c ∈ all T
  | .leaf _, .atLeaf => by simp [all]
  | .trace _, .atTrace => by simp [all]
  | .node l r, .bothCut hl hr => by
      simp only [all, Finset.mem_union, Finset.mem_image,
        Finset.mem_product]
      refine Or.inl (Or.inl (Or.inl ?_))
      simp [hl, hr]
  | .node l r, .onlyLeftCut hl cr => by
      simp only [all, Finset.mem_union, Finset.mem_image,
        Finset.mem_product]
      refine Or.inl (Or.inl (Or.inr ?_))
      simp only [hl, ↓reduceDIte, Finset.mem_image]
      exact ⟨cr, mem_all r cr, rfl⟩
  | .node l r, .onlyRightCut hr cl => by
      simp only [all, Finset.mem_union, Finset.mem_image,
        Finset.mem_product]
      refine Or.inl (Or.inr ?_)
      simp only [hr, ↓reduceDIte, Finset.mem_image]
      exact ⟨cl, mem_all l cl, rfl⟩
  | .node l r, .bothRecurse cl cr => by
      simp only [all, Finset.mem_union, Finset.mem_image,
        Finset.mem_product]
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
  | .node l r, .bothCut _ _ => ({l, r} : Multiset (DecoratedTree α))
  | .node l _, .onlyLeftCut _ cr =>
      ({l} : Multiset (DecoratedTree α)) + cutForest cr
  | .node _ r, .onlyRightCut _ cl =>
      cutForest cl + ({r} : Multiset (DecoratedTree α))
  | .node _ _, .bothRecurse cl cr => cutForest cl + cutForest cr

/-- The remainder of a cut (contraction-with-trace, M-C-B Def 1.2.4):
    T with each cut subtree replaced by a `.trace` leaf carrying the
    cut subtree as metadata. The `DecoratedTree.trace` constructor
    takes any subtree (including trace-bearing ones), so iterated
    cuts compose without any fallback or placeholder. Used by Δ^c.

    Note: by the `IsNotTrace` constraint on the extracting constructors, the
    children getting wrapped with `.trace` here are guaranteed to NOT already
    be `.trace` markers — so no `.trace (.trace _)` nesting can occur. -/
def remainder : ∀ {T : DecoratedTree α}, CutShape T → DecoratedTree α
  | .leaf tok, .atLeaf => .leaf tok
  | .trace t,  .atTrace => .trace t
  | .node l r, .bothCut _ _ => .node (.trace l) (.trace r)
  | .node l _, .onlyLeftCut _ cr => .node (.trace l) (remainder cr)
  | .node _ r, .onlyRightCut _ cl => .node (remainder cl) (.trace r)
  | .node _ _, .bothRecurse cl cr => .node (remainder cl) (remainder cr)

/-- The remainder of a cut (deletion-with-rebinarization, M-C-B
    Def 1.2.5): T with each cut subtree REMOVED (no trace), then
    edge-contracted to recover binarity. Used by Δ^d (the coproduct
    that linguistic Merge uses, per M-C-B Definition 1.3.4 p. 42:
    "consider the coproduct Δ = Δ^d of (1.2.8)").

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
  | .node _ _, .bothCut _ _ => none
  | .node _ _, .onlyLeftCut _ cr => remainderDeletion cr
  | .node _ _, .onlyRightCut _ cl => remainderDeletion cl
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
@[simp] theorem cutForest_bothCut {l r : DecoratedTree α}
    (hl : DecoratedTree.IsNotTrace l) (hr : DecoratedTree.IsNotTrace r) :
    (bothCut hl hr : CutShape (.node l r)).cutForest =
      ({l, r} : Multiset (DecoratedTree α)) := rfl

/-- The unique cut on a leaf has empty `cutForest`. -/
@[simp] theorem cutForest_atLeaf {a : α} :
    (atLeaf : CutShape (.leaf a)).cutForest = (0 : Forest α) := rfl

/-- The unique cut on a leaf leaves the leaf unchanged. -/
@[simp] theorem remainder_atLeaf {a : α} :
    (atLeaf : CutShape (.leaf a)).remainder = .leaf a := rfl

/-- The unique cut on a trace has empty `cutForest`. -/
@[simp] theorem cutForest_atTrace {t : DecoratedTree α} :
    (atTrace : CutShape (.trace t)).cutForest = (0 : Forest α) := rfl

/-- The unique cut on a trace leaves the trace unchanged. -/
@[simp] theorem remainder_atTrace {t : DecoratedTree α} :
    (atTrace : CutShape (.trace t)).remainder = .trace t := rfl

/-! ## §6: Position vs. value: cutForest is NOT injective (and that's correct)

A natural question: is `cutForest : CutShape T → Forest α` injective
(per M-C-B Lemma 1.2.7's bijection)? The answer is **no in general**,
and that's actually consistent with M-C-B.

Counterexample: take `T = .node X X` (same subtree X on both sides).
Then `bothRecurse cl cr` and `bothRecurse cr cl` are syntactically
distinct `CutShape T` values but produce identical `cutForest`
multisets (multiset addition is commutative). More generally,
whenever subtrees on the left and right have shared substructure,
swapping cut choices gives the same value-level multiset but distinct
positional cut data.

This is consistent with M-C-B because Eq (1.2.8)'s `Σ_{F_v}` ranges
over **positional** subforests of disjoint accessible terms (per
M-C-B's "disjoint in T" qualifier in Lemma 1.2.7), not over value-
deduplicated multisets. Two positionally-distinct cuts that happen to
extract the same value-multiset CONTRIBUTE TWO TERMS to the sum.

Our `Σ c : CutShape T` correctly enumerates positionally — `CutShape T`
is the **positional cut data**. The map `cutForest` then projects
position to value; non-injectivity here corresponds to
multiplicities in the value-multiset projection of the sum, which is
exactly what M-C-B's sum is supposed to track.

**Bottom line**: don't try to prove `cutForest` injective; the sum
over CutShape is the right semantics, and value-level collisions are
genuine multiplicity contributions. -/

end CutShape

end ConnesKreimer
