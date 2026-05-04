import Linglib.Core.Algebra.ConnesKreimer.AugmentedCut
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# `LhsIndex T` — structurally indexed enumeration of LHS double-cut data
@cite{marcolli-chomsky-berwick-2025} @cite{marcolli-skigin-2025}

For the substantive Foissy bijection (M-C-B Lemma 1.2.10), we need to
enumerate the LHS-style double-cut data: for each outer cut `cl_outer :
CutShape T`, plus per-tree `T' ∈ cutForest cl_outer` choice of an
augmented cut `ac' : AugCutShape T'`.

The naive formulation uses `Multiset.Sections` (mathlib idiom for
enumerating per-element choices over a multiset). Two issues:
- `Sections` requires homogeneous element types; `AugCutShape T'` is
  heterogeneous in `T'`.
- The Sections-based form doesn't admit a clean `Fintype`/`DecidableEq`
  derivation suitable for an `Equiv` with `GeoCut T .top`.

This file's solution: define `LhsIndex T : Type _` as a **structurally
indexed inductive** that mirrors `CutShape`'s recursion and absorbs the
per-T' AugCutShape choices into the constructor structure. Each
`LhsIndex T` value uniquely encodes a `(cl_outer, π)` pair without
heterogeneous Sections.

## Constructor correspondence

For `T = .node l r`, the four `LhsIndex` constructors mirror the four
`CutShape` constructors:

| LhsIndex ctor                     | CutShape ctor      | per-T' data            |
|-----------------------------------|--------------------|------------------------|
| `bothCut hl hr ac_l ac_r`         | `bothCut hl hr`    | `ac_l, ac_r` directly  |
| `onlyLeftCut hl ac_l rhs`         | `onlyLeftCut hl _` | `ac_l` for l, `rhs : LhsIndex r` recursive for cr-side |
| `onlyRightCut hr lhs ac_r`        | `onlyRightCut hr _`| recursive on l, `ac_r` for r |
| `bothRecurse lhs rhs`             | `bothRecurse _ _`  | recursive on both sides |

Counting LhsIndex variants per `.node`:
- `bothCut`: 2 (`AugCutShape l`) × 2 (`AugCutShape r`) = 4 sub-cases.
- `onlyLeftCut`: 2 × `card LhsIndex r` (recursive).
- `onlyRightCut`: `card LhsIndex l` × 2 (symmetric).
- `bothRecurse`: `card LhsIndex l` × `card LhsIndex r`.

For the `(.node leaf leaf)` base: 4 + 2 + 2 + 1 = 9 LhsIndex values,
matching exactly the 9 `(lL, rL)` cells of `GeoCut (.node leaf leaf) .top`.

## Layer status

`[UPSTREAM]` candidate, paired with `LhsEquiv.lean` (the bijection with
GeoCut). Future home: `Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.LhsIndex`.
-/

namespace ConnesKreimer

variable {α : Type*} [DecidableEq α]

/-! ## §1: `LhsIndex T` — the inductive

Each constructor encodes a CutShape ctor + per-T' AugCutShape choice. -/

/-- LHS-style double-cut data for `T : TraceTree α Unit`.

    Structurally indexes `(cl_outer : CutShape T, π : ∀ T' ∈ cutForest cl_outer, AugCutShape T')`
    via constructors paralleling `CutShape`. The recursive constructors
    (`onlyLeftCut`, `onlyRightCut`, `bothRecurse`) absorb the per-T'
    AugCutShape choices for the recursive child into the recursive
    `LhsIndex` argument; the `bothCut` constructor (which has no recursive
    cut) takes both `AugCutShape` choices directly.

    See module docstring for the constructor↔CutShape correspondence. -/
inductive LhsIndex : TraceTree α Unit → Type _ where
  /-- An α-leaf admits only the trivial LHS index (no extracted subtrees). -/
  | atLeaf {a : α} : LhsIndex (.leaf a)
  /-- A trace leaf admits only the trivial LHS index. -/
  | atTrace : LhsIndex (.trace ())
  /-- Outer cut at `bothCut hl hr` with per-child AugCutShape choices `ac_l`, `ac_r`. -/
  | bothCut {l r : TraceTree α Unit}
      (hl : TraceTree.IsNotTrace l) (hr : TraceTree.IsNotTrace r)
      (ac_l : AugCutShape l) (ac_r : AugCutShape r) : LhsIndex (.node l r)
  /-- Outer cut at `onlyLeftCut hl _` with `ac_l : AugCutShape l` for the
      left child and a recursive `rhs : LhsIndex r` encoding the right
      subtree's cut + per-T'-in-cutForest choices. -/
  | onlyLeftCut {l r : TraceTree α Unit}
      (hl : TraceTree.IsNotTrace l) (ac_l : AugCutShape l)
      (rhs : LhsIndex r) : LhsIndex (.node l r)
  /-- Symmetric to `onlyLeftCut`: outer cut at `onlyRightCut hr _`,
      recursive on l, direct AugCutShape on r. -/
  | onlyRightCut {l r : TraceTree α Unit}
      (hr : TraceTree.IsNotTrace r) (lhs : LhsIndex l)
      (ac_r : AugCutShape r) : LhsIndex (.node l r)
  /-- Outer cut at `bothRecurse _ _`, recursive on both children. -/
  | bothRecurse {l r : TraceTree α Unit}
      (lhs : LhsIndex l) (rhs : LhsIndex r) : LhsIndex (.node l r)

namespace LhsIndex

/-! ## §2: Decidable equality

Structural recursion on T + case analysis on constructors. Mirrors
the pattern in `CutShape.decEq`. -/

instance decEq : (T : TraceTree α Unit) → DecidableEq (LhsIndex T)
  | .leaf _ => fun
      | .atLeaf, .atLeaf => isTrue rfl
  | .trace _ => fun
      | .atTrace, .atTrace => isTrue rfl
  | .node l r => fun a b =>
      have _ : DecidableEq (LhsIndex l) := decEq l
      have _ : DecidableEq (LhsIndex r) := decEq r
      match a, b with
      | .bothCut _ _ ac_l₁ ac_r₁, .bothCut _ _ ac_l₂ ac_r₂ =>
          if h₁ : ac_l₁ = ac_l₂ then
            if h₂ : ac_r₁ = ac_r₂ then isTrue (by subst h₁; subst h₂; rfl)
            else isFalse (by intro heq; cases heq; exact h₂ rfl)
          else isFalse (by intro heq; cases heq; exact h₁ rfl)
      | .bothCut _ _ _ _, .onlyLeftCut _ _ _ => isFalse (by intro h; cases h)
      | .bothCut _ _ _ _, .onlyRightCut _ _ _ => isFalse (by intro h; cases h)
      | .bothCut _ _ _ _, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .onlyLeftCut _ _ _, .bothCut _ _ _ _ => isFalse (by intro h; cases h)
      | .onlyLeftCut _ ac_l₁ rhs₁, .onlyLeftCut _ ac_l₂ rhs₂ =>
          if h₁ : ac_l₁ = ac_l₂ then
            if h₂ : rhs₁ = rhs₂ then isTrue (by subst h₁; subst h₂; rfl)
            else isFalse (by intro heq; cases heq; exact h₂ rfl)
          else isFalse (by intro heq; cases heq; exact h₁ rfl)
      | .onlyLeftCut _ _ _, .onlyRightCut _ _ _ => isFalse (by intro h; cases h)
      | .onlyLeftCut _ _ _, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .onlyRightCut _ _ _, .bothCut _ _ _ _ => isFalse (by intro h; cases h)
      | .onlyRightCut _ _ _, .onlyLeftCut _ _ _ => isFalse (by intro h; cases h)
      | .onlyRightCut _ lhs₁ ac_r₁, .onlyRightCut _ lhs₂ ac_r₂ =>
          if h₁ : lhs₁ = lhs₂ then
            if h₂ : ac_r₁ = ac_r₂ then isTrue (by subst h₁; subst h₂; rfl)
            else isFalse (by intro heq; cases heq; exact h₂ rfl)
          else isFalse (by intro heq; cases heq; exact h₁ rfl)
      | .onlyRightCut _ _ _, .bothRecurse _ _ => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .bothCut _ _ _ _ => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .onlyLeftCut _ _ _ => isFalse (by intro h; cases h)
      | .bothRecurse _ _, .onlyRightCut _ _ _ => isFalse (by intro h; cases h)
      | .bothRecurse lhs₁ rhs₁, .bothRecurse lhs₂ rhs₂ =>
          if h₁ : lhs₁ = lhs₂ then
            if h₂ : rhs₁ = rhs₂ then isTrue (by subst h₁; subst h₂; rfl)
            else isFalse (by intro heq; cases heq; exact h₂ rfl)
          else isFalse (by intro heq; cases heq; exact h₁ rfl)

/-! ## §3: Finite enumeration

The finite set of all LhsIndex T values, with conditional inclusion of
`bothCut`/`onlyLeftCut`/`onlyRightCut` based on `IsNotTrace l/r`. -/

/-- The finite set of all LhsIndex values on T. -/
def all : (T : TraceTree α Unit) → Finset (LhsIndex T)
  | .leaf _ => {.atLeaf}
  | .trace _ => {.atTrace}
  | .node l r =>
      have _ : DecidableEq (LhsIndex (.node l r)) := decEq (.node l r)
      have allL : Finset (LhsIndex l) := all l
      have allR : Finset (LhsIndex r) := all r
      have augL : Finset (AugCutShape l) := Finset.univ
      have augR : Finset (AugCutShape r) := Finset.univ
      have bothCutSet : Finset (LhsIndex (.node l r)) :=
        if hl : TraceTree.IsNotTrace l then
          if hr : TraceTree.IsNotTrace r then
            (augL ×ˢ augR).image
              (fun p => LhsIndex.bothCut hl hr p.1 p.2)
          else ∅
        else ∅
      have onlyLeftCutSet : Finset (LhsIndex (.node l r)) :=
        if hl : TraceTree.IsNotTrace l then
          (augL ×ˢ allR).image
            (fun p => LhsIndex.onlyLeftCut hl p.1 p.2)
        else ∅
      have onlyRightCutSet : Finset (LhsIndex (.node l r)) :=
        if hr : TraceTree.IsNotTrace r then
          (allL ×ˢ augR).image
            (fun p => LhsIndex.onlyRightCut hr p.1 p.2)
        else ∅
      have bothRecurseSet : Finset (LhsIndex (.node l r)) :=
        (allL ×ˢ allR).image (fun p => LhsIndex.bothRecurse p.1 p.2)
      bothCutSet ∪ onlyLeftCutSet ∪ onlyRightCutSet ∪ bothRecurseSet

/-- Every LhsIndex value is in `all T`. -/
theorem mem_all : ∀ (T : TraceTree α Unit) (idx : LhsIndex T), idx ∈ all T
  | .leaf _, .atLeaf => by simp [all]
  | .trace _, .atTrace => by simp [all]
  | .node l r, .bothCut hl hr ac_l ac_r => by
      simp only [all, Finset.mem_union]
      refine Or.inl (Or.inl (Or.inl ?_))
      simp only [hl, hr, ↓reduceDIte]
      refine Finset.mem_image.mpr ⟨(ac_l, ac_r), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  | .node l r, .onlyLeftCut hl ac_l rhs => by
      simp only [all, Finset.mem_union]
      refine Or.inl (Or.inl (Or.inr ?_))
      simp only [hl, ↓reduceDIte]
      refine Finset.mem_image.mpr ⟨(ac_l, rhs), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_all r rhs⟩
  | .node l r, .onlyRightCut hr lhs ac_r => by
      simp only [all, Finset.mem_union]
      refine Or.inl (Or.inr ?_)
      simp only [hr, ↓reduceDIte]
      refine Finset.mem_image.mpr ⟨(lhs, ac_r), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨mem_all l lhs, Finset.mem_univ _⟩
  | .node l r, .bothRecurse lhs rhs => by
      simp only [all, Finset.mem_union]
      refine Or.inr ?_
      refine Finset.mem_image.mpr ⟨(lhs, rhs), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨mem_all l lhs, mem_all r rhs⟩

/-- `Fintype` instance derived from `all` + `mem_all`. -/
instance fintype (T : TraceTree α Unit) : Fintype (LhsIndex T) where
  elems := all T
  complete := mem_all T

/-! ## §4: Triple-tensor projection

For each `LhsIndex T` value, extract the triple-tensor
`(BOT-extracted forest) ⊗ (MID-extracted forest) ⊗ {TOP-skeleton}`
that the LHS-side coproduct produces.

The triple's three slots:
- **botForest**: union of `cutForest_aug ac'` over all per-T'-in-cutForest AugCutShape choices.
- **midForest**: union of `remainderForest ac'`.
- **slot3**: `{remainder cl_outer}` — the outer cut's tree-with-trace-markers.

For the inductive constructors, these slots accumulate via the
`AugCutShape.cutForest_aug`/`remainderForest` projections plus
recursive accumulation through `onlyLeftCut`/`onlyRightCut`/`bothRecurse`. -/

section TripleTensor

variable (R : Type*) [CommSemiring R]

open scoped TensorProduct

/-- The BOT-extracted forest contributed by an `LhsIndex T` value.

    For each per-T' AugCutShape choice, take its `cutForest_aug` (the
    "left channel" of that choice's coproduct contribution). Sum over
    all per-T' choices in the index. -/
def botForest : ∀ {T : TraceTree α Unit}, LhsIndex T → TraceForest α Unit
  | .leaf _, .atLeaf => 0
  | .trace _, .atTrace => 0
  | .node _ _, .bothCut _ _ ac_l ac_r =>
      AugCutShape.cutForest_aug ac_l + AugCutShape.cutForest_aug ac_r
  | .node _ _, .onlyLeftCut _ ac_l rhs =>
      AugCutShape.cutForest_aug ac_l + botForest rhs
  | .node _ _, .onlyRightCut _ lhs ac_r =>
      botForest lhs + AugCutShape.cutForest_aug ac_r
  | .node _ _, .bothRecurse lhs rhs => botForest lhs + botForest rhs

/-- The MID-extracted forest contributed by an `LhsIndex T` value.

    For each per-T' AugCutShape choice, take its `remainderForest` (the
    "right channel" of that choice's coproduct contribution — singleton
    `{remainder C'}` for `real C'`, empty for `extractWhole`). Sum over
    all per-T' choices. -/
def midForest : ∀ {T : TraceTree α Unit}, LhsIndex T → TraceForest α Unit
  | .leaf _, .atLeaf => 0
  | .trace _, .atTrace => 0
  | .node _ _, .bothCut _ _ ac_l ac_r =>
      AugCutShape.remainderForest ac_l + AugCutShape.remainderForest ac_r
  | .node _ _, .onlyLeftCut _ ac_l rhs =>
      AugCutShape.remainderForest ac_l + midForest rhs
  | .node _ _, .onlyRightCut _ lhs ac_r =>
      midForest lhs + AugCutShape.remainderForest ac_r
  | .node _ _, .bothRecurse lhs rhs => midForest lhs + midForest rhs

/-- The outer cut `cl_outer : CutShape T` extracted from an `LhsIndex T`
    value. The constructor structure determines `cl_outer` directly. -/
def outerCut : ∀ {T : TraceTree α Unit}, LhsIndex T → CutShape T
  | .leaf _, .atLeaf => .atLeaf
  | .trace _, .atTrace => .atTrace
  | .node _ _, .bothCut hl hr _ _ => .bothCut hl hr
  | .node _ _, .onlyLeftCut hl _ rhs => .onlyLeftCut hl (outerCut rhs)
  | .node _ _, .onlyRightCut hr lhs _ => .onlyRightCut hr (outerCut lhs)
  | .node _ _, .bothRecurse lhs rhs => .bothRecurse (outerCut lhs) (outerCut rhs)

/-- The triple-tensor for an `LhsIndex T` value:
    `forestToHc botForest ⊗ (forestToHc midForest ⊗ forestToHc {remainder outerCut})`. -/
noncomputable def tripleTensor {T : TraceTree α Unit} (idx : LhsIndex T) :
    Hc R α ⊗[R] (Hc R α ⊗[R] Hc R α) :=
  forestToHc (R := R) (botForest idx)
    ⊗ₜ[R] (forestToHc (R := R) (midForest idx)
            ⊗ₜ[R] forestToHc (R := R)
              ({CutShape.remainder (outerCut idx)} : TraceForest α Unit))

end TripleTensor

/-! ## §5: Per-`outerCut` enumeration

For the bridge `lhsRealCuts_eq_lhsIndexSum`, we factor the LhsIndex
enumeration by outer cut: for each `cl_outer : CutShape T`, the subset of
LhsIndex values with `outerCut = cl_outer`. This subset has a clean
recursive structure mirroring the LhsIndex constructors, and admits
direct multiset comparison with the `(Sections ((cutForest cl_outer).map
pairsMS))` form on the LHS-of-bridge. -/

/-- The finite set of LhsIndex values with `outerCut = cl_outer`. Defined
    by structural recursion on `cl_outer` (= equivalently, on T). -/
def allWith : ∀ (T : TraceTree α Unit) (cl_outer : CutShape T), Finset (LhsIndex T)
  | .leaf _, .atLeaf => {.atLeaf}
  | .trace _, .atTrace => {.atTrace}
  | .node l r, .bothCut hl hr =>
      ((Finset.univ : Finset (AugCutShape l)) ×ˢ (Finset.univ : Finset (AugCutShape r))).image
        (fun p => LhsIndex.bothCut hl hr p.1 p.2)
  | .node l r, .onlyLeftCut hl cr =>
      ((Finset.univ : Finset (AugCutShape l)) ×ˢ (allWith r cr)).image
        (fun p => LhsIndex.onlyLeftCut hl p.1 p.2)
  | .node l r, .onlyRightCut hr cl =>
      ((allWith l cl) ×ˢ (Finset.univ : Finset (AugCutShape r))).image
        (fun p => LhsIndex.onlyRightCut hr p.1 p.2)
  | .node l r, .bothRecurse cl cr =>
      ((allWith l cl) ×ˢ (allWith r cr)).image
        (fun p => LhsIndex.bothRecurse p.1 p.2)

/-- `outerCut` projects every element of `allWith T cl_outer` back to `cl_outer`. -/
theorem outerCut_of_mem_allWith :
    ∀ (T : TraceTree α Unit) (cl_outer : CutShape T) (rhs : LhsIndex T),
      rhs ∈ allWith T cl_outer → outerCut rhs = cl_outer
  | .leaf _, .atLeaf, _, h => by
      simp only [allWith, Finset.mem_singleton] at h
      subst h; rfl
  | .trace _, .atTrace, _, h => by
      simp only [allWith, Finset.mem_singleton] at h
      subst h; rfl
  | .node l r, .bothCut hl hr, rhs, h => by
      simp only [allWith, Finset.mem_image, Finset.mem_product] at h
      obtain ⟨⟨ac_l, ac_r⟩, _, hrhs⟩ := h
      subst hrhs; rfl
  | .node l r, .onlyLeftCut hl cr, rhs, h => by
      simp only [allWith, Finset.mem_image, Finset.mem_product] at h
      obtain ⟨⟨ac_l, rhs'⟩, ⟨_, hmem⟩, hrhs⟩ := h
      subst hrhs
      have hcr := outerCut_of_mem_allWith r cr rhs' hmem
      show CutShape.onlyLeftCut hl (outerCut rhs') = _
      rw [hcr]
  | .node l r, .onlyRightCut hr cl, rhs, h => by
      simp only [allWith, Finset.mem_image, Finset.mem_product] at h
      obtain ⟨⟨lhs', ac_r⟩, ⟨hmem, _⟩, hrhs⟩ := h
      subst hrhs
      have hcl := outerCut_of_mem_allWith l cl lhs' hmem
      show CutShape.onlyRightCut hr (outerCut lhs') = _
      rw [hcl]
  | .node l r, .bothRecurse cl cr, rhs, h => by
      simp only [allWith, Finset.mem_image, Finset.mem_product] at h
      obtain ⟨⟨lhs', rhs'⟩, ⟨hmemL, hmemR⟩, hrhs⟩ := h
      subst hrhs
      have hcl := outerCut_of_mem_allWith l cl lhs' hmemL
      have hcr := outerCut_of_mem_allWith r cr rhs' hmemR
      show CutShape.bothRecurse (outerCut lhs') (outerCut rhs') = _
      rw [hcl, hcr]

/-- Every LhsIndex value belongs to the `allWith` set for its own `outerCut`. -/
theorem mem_allWith : ∀ (T : TraceTree α Unit) (rhs : LhsIndex T),
    rhs ∈ allWith T (outerCut rhs)
  | .leaf _, .atLeaf => Finset.mem_singleton.mpr rfl
  | .trace _, .atTrace => Finset.mem_singleton.mpr rfl
  | .node l r, .bothCut hl hr ac_l ac_r => by
      show _ ∈ allWith (.node l r) (CutShape.bothCut hl hr)
      unfold allWith
      refine Finset.mem_image.mpr ⟨(ac_l, ac_r), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  | .node l r, .onlyLeftCut hl ac_l rhs => by
      show _ ∈ allWith (.node l r) (CutShape.onlyLeftCut hl (outerCut rhs))
      unfold allWith
      refine Finset.mem_image.mpr ⟨(ac_l, rhs), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_allWith r rhs⟩
  | .node l r, .onlyRightCut hr lhs ac_r => by
      show _ ∈ allWith (.node l r) (CutShape.onlyRightCut hr (outerCut lhs))
      unfold allWith
      refine Finset.mem_image.mpr ⟨(lhs, ac_r), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨mem_allWith l lhs, Finset.mem_univ _⟩
  | .node l r, .bothRecurse lhs rhs => by
      show _ ∈ allWith (.node l r) (CutShape.bothRecurse (outerCut lhs) (outerCut rhs))
      unfold allWith
      refine Finset.mem_image.mpr ⟨(lhs, rhs), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨mem_allWith l lhs, mem_allWith r rhs⟩

/-- The `allWith T cl_outer` sets are pairwise disjoint across `cl_outer`. Combined
    with `mem_allWith` and `outerCut_of_mem_allWith`, this gives the partition
    `(univ : LhsIndex T) = ⋃ cl_outer, allWith T cl_outer` (disjoint union). -/
theorem allWith_disjoint {T : TraceTree α Unit} {cl₁ cl₂ : CutShape T}
    (hne : cl₁ ≠ cl₂) : Disjoint (allWith T cl₁) (allWith T cl₂) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  subst hab
  have h1 := outerCut_of_mem_allWith T cl₁ a ha
  have h2 := outerCut_of_mem_allWith T cl₂ a hb
  exact hne (h1.symm.trans h2)

end LhsIndex

end ConnesKreimer

/-!
## §6: Bridge to `lhsRealCuts` (Session 2)

The bridge theorem `lhsRealCuts T = (Finset.univ : Finset (LhsIndex T)).val.map
(LhsIndex.tripleTensor R)` is proven in `LhsBridge.lean`, factored through the
per-`outerCut` enumeration `LhsIndex.allWith` defined above.
-/

