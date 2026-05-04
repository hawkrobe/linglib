import Linglib.Core.Combinatorics.RootedTree.Decorated
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Multiset.Basic

/-!
# Admissible Cuts on Trees @cite{marcolli-chomsky-berwick-2025}

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.2.6, an
**admissible cut** of a binary rooted tree T is a removal of a
collection of edges of T such that no two lie on the same root-to-leaf
path. Equivalently (Lemma 1.2.7), the data of an admissible cut on T
is the same as a forest F_v = T_{v₁} ⊔ ⋯ ⊔ T_{vₙ} of disjoint
accessible terms of T.

## Trees with scalar trace labels

This file defines `CutShape` on `TraceTree α β` (not on `DecoratedTree α`).
The `TraceTree` carrier has scalar trace labels (`.trace (b : β)`)
rather than recursive subtree data. This is the carrier the bialgebra
of @cite{marcolli-chomsky-berwick-2025} Lemma 1.2.10 actually inhabits;
see `Decorated.lean` for the rationale: per @cite{marcolli-skigin-2025}
§10.1 (clarifying the brief discussion in M-C-B §1.3), trace labels
are elements of a disjoint marked copy `̄SO₀` of the leaf alphabet,
NOT recursive subtrees, for the bialgebra structure to be well-formed.

For the bialgebra layer, `β = Unit` (no informative trace label) — the
minimal instance, sufficient for coassoc but a strict simplification
of M-S. For the linguistic layer (CI interpretation, FormCopy), a
richer `β` plus a head-function-transparent extractor realizes
@cite{marcolli-skigin-2025} Definition 10.3 (head function projects
each contracted subtree to its head leaf's struck-through label).

This file is **[UPSTREAM]** — generic over `α : Type*` and `β : Type*`.

## Crucial M-C-B reading: leaves ARE accessible terms

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.2.2, accessible
terms are subtrees `T_v` for `v ∈ V_int(T) := V(T) \ {root of T}`.
M-C-B's "internal" excludes the root vertex but **includes leaves** —
so leaves of `T` are accessible terms. (Verified against the worked
example on book p. 35, inline in §1.2 just before §1.2.1.)

## Representation: 5-constructor enum

A `CutShape T` for `T : TraceTree α β` records cut choices position-
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

variable {α β : Type*}

/-! ## §1: Cut shape

Universe-polymorphic in `α : Type*` and `β : Type*`. The inductive
takes both as parameters (not per-constructor indices), letting mathlib
upstream reuse this construction over arbitrary leaf-and-trace-label types. -/

/-- An admissible cut on a tree `T : TraceTree α β`.

    **Trace-extraction restriction (substrate fix for coassoc).** The cuts that
    EXTRACT a child subtree (`bothCut`, `onlyLeftCut`, `onlyRightCut`) require
    that child to NOT be a `.trace` marker (`IsNotTrace`). Without this
    restriction, iterated cuts on the remainder of an outer cut would
    accumulate `.trace`-of-`.trace` nesting, breaking the cuts-of-cuts bijection
    (M-C-B Lemma 1.2.10 / Foissy 2002 §2). With scalar trace labels (β not
    DecoratedTree), this nesting is what causes the basis cardinality to blow
    up; the `IsNotTrace` constraint prevents it.

    The `bothRecurse` constructor — which doesn't extract anything at this node —
    has no restriction; it composes recursively into the children's CutShapes.
    The atomic `atLeaf` / `atTrace` constructors are also unrestricted. -/
inductive CutShape {α β : Type*} : TraceTree α β → Type _ where
  /-- An α-leaf admits only the empty cut (no edges to cut). -/
  | atLeaf {a : α} : CutShape (.leaf a)
  /-- A trace leaf admits only the empty cut. -/
  | atTrace {b : β} : CutShape (.trace b)
  /-- Cut both child edges of this node. Requires both children to be
      non-trace (cuts cannot extract `.trace` markers). -/
  | bothCut {l r : TraceTree α β} (hl : TraceTree.IsNotTrace l)
      (hr : TraceTree.IsNotTrace r) : CutShape (.node l r)
  /-- Cut the left child edge, recurse into `r` with sub-cut `cr`. Requires
      the left child to be non-trace. -/
  | onlyLeftCut {l r : TraceTree α β} (hl : TraceTree.IsNotTrace l)
      (cr : CutShape r) : CutShape (.node l r)
  /-- Recurse into `l` with sub-cut `cl`, cut the right child edge. Requires
      the right child to be non-trace. -/
  | onlyRightCut {l r : TraceTree α β} (hr : TraceTree.IsNotTrace r)
      (cl : CutShape l) : CutShape (.node l r)
  /-- Don't cut at this node; recurse in both children. No restrictions
      since nothing is extracted at this level. -/
  | bothRecurse {l r : TraceTree α β} (cl : CutShape l)
      (cr : CutShape r) : CutShape (.node l r)

namespace CutShape

/-! ## §2: The empty (trivial) cut -/

/-- The empty cut on T: extract nothing, leave T unchanged. -/
def empty : (T : TraceTree α β) → CutShape T
  | .leaf _  => .atLeaf
  | .trace _ => .atTrace
  | .node l r => .bothRecurse (empty l) (empty r)

/-! ## §3: Decidable equality and finite enumeration -/

instance decEq [DecidableEq α] [DecidableEq β] :
    (T : TraceTree α β) → DecidableEq (CutShape T)
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
def all [DecidableEq α] [DecidableEq β] : (T : TraceTree α β) → Finset (CutShape T)
  | .leaf _  => {.atLeaf}
  | .trace _ => {.atTrace}
  | .node l r =>
      have _ : DecidableEq (CutShape (.node l r)) := decEq (.node l r)
      have allL : Finset (CutShape l) := all l
      have allR : Finset (CutShape r) := all r
      have bothCutSet : Finset (CutShape (.node l r)) :=
        if hl : TraceTree.IsNotTrace l then
          if hr : TraceTree.IsNotTrace r then {CutShape.bothCut hl hr}
          else ∅
        else ∅
      have leftCutSet : Finset (CutShape (.node l r)) :=
        if hl : TraceTree.IsNotTrace l then
          allR.image (fun cr => CutShape.onlyLeftCut hl cr)
        else ∅
      have rightCutSet : Finset (CutShape (.node l r)) :=
        if hr : TraceTree.IsNotTrace r then
          allL.image (fun cl => CutShape.onlyRightCut hr cl)
        else ∅
      bothCutSet ∪ leftCutSet ∪ rightCutSet
        ∪ ((allL ×ˢ allR).image (fun p => CutShape.bothRecurse p.1 p.2))

/-- Every cut shape on T is in `all T`. -/
theorem mem_all [DecidableEq α] [DecidableEq β] :
    ∀ (T : TraceTree α β) (c : CutShape T), c ∈ all T
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

instance fintype [DecidableEq α] [DecidableEq β] (T : TraceTree α β) :
    Fintype (CutShape T) where
  elems := all T
  complete := mem_all T

/-! ## §4: Pruned forest `F_v` and remainder `T/^c F_v`

For an admissible cut `c : CutShape T`:
- `cutForest c : TraceForest α β` is the multiset of subtrees being extracted
  (M-C-B's F_v in Def 1.2.4 / Lemma 1.2.7)
- `remainder c : TraceTree α β` is the tree obtained by replacing
  each cut subtree with a `.trace` leaf labelled with what was cut
  (M-C-B's T/^c F_v in Def 1.2.4)

The trace label is a SCALAR `β` (not a recursive subtree). For `β = Unit`,
the trace marker carries no information; for `β = α`, it carries a head
label per @cite{marcolli-skigin-2025} Definition 10.3. -/

/-- The pruned forest of a cut: the multiset of extracted subtrees.
    M-C-B Definition 1.2.4: F_v = T_{v_1} ⊔ ⋯ ⊔ T_{v_n}. -/
def cutForest : ∀ {T : TraceTree α β}, CutShape T → TraceForest α β
  | .leaf _, .atLeaf => 0
  | .trace _, .atTrace => 0
  | .node l r, .bothCut _ _ => ({l, r} : Multiset (TraceTree α β))
  | .node l _, .onlyLeftCut _ cr =>
      ({l} : Multiset (TraceTree α β)) + cutForest cr
  | .node _ r, .onlyRightCut _ cl =>
      cutForest cl + ({r} : Multiset (TraceTree α β))
  | .node _ _, .bothRecurse cl cr => cutForest cl + cutForest cr

/-- The remainder of a cut (contraction-with-trace, M-C-B Def 1.2.4):
    T with each cut subtree replaced by a `.trace` leaf. The trace label
    is `default : β` from `[Inhabited β]` (e.g., `()` for the bialgebra
    layer with `β = Unit`). For richer trace labels (head function, etc.),
    use a different projection at the bialgebra boundary; this default
    suffices for `Hc R α := AddMonoidAlgebra R (TraceForest α Unit)`.

    Note: by the `IsNotTrace` constraint on the extracting constructors, the
    children getting wrapped with `.trace` here are guaranteed to NOT already
    be `.trace` markers. -/
def remainder [Inhabited β] : ∀ {T : TraceTree α β}, CutShape T → TraceTree α β
  | .leaf tok, .atLeaf => .leaf tok
  | .trace b,  .atTrace => .trace b
  | .node _ _, .bothCut _ _ => .node (.trace default) (.trace default)
  | .node _ _, .onlyLeftCut _ cr => .node (.trace default) (remainder cr)
  | .node _ _, .onlyRightCut _ cl => .node (remainder cl) (.trace default)
  | .node _ _, .bothRecurse cl cr => .node (remainder cl) (remainder cr)

/-- The remainder of a cut (deletion-with-rebinarization, M-C-B
    Def 1.2.5): T with each cut subtree REMOVED (no trace), then
    edge-contracted to recover binarity. Used by Δ^d (the coproduct
    that linguistic Merge uses, per M-C-B Definition 1.3.4 p. 42:
    "consider the coproduct Δ = Δ^d of (1.2.8)").

    Returns `Option (TraceTree α β)` because cutting both children of a
    node leaves a vertex with no children — neither a leaf nor a binary
    node. Such a vertex collapses (returns `None`); upstream binders absorb
    the collapse via edge contraction:

    - At a node, if BOTH children's deletion-remainder collapse, the
      node itself collapses.
    - At a node, if ONE child collapses, the other becomes the
      remainder (the parent's edge to the survivor is "contracted",
      effectively absorbing the parent into the survivor).

    This handling is faithful to M-C-B Def 1.2.5's "unique maximal
    binary rooted tree obtainable via contraction." -/
def remainderDeletion : ∀ {T : TraceTree α β},
    CutShape T → Option (TraceTree α β)
  | .leaf tok, .atLeaf => some (.leaf tok)
  | .trace b,  .atTrace => some (.trace b)
  | .node _ _, .bothCut _ _ => none
  | .node _ _, .onlyLeftCut _ cr => remainderDeletion cr
  | .node _ _, .onlyRightCut _ cl => remainderDeletion cl
  | .node _ _, .bothRecurse cl cr =>
      match remainderDeletion cl, remainderDeletion cr with
      | some l', some r' => some (.node l' r')
      | some l', none    => some l'
      | none,    some r' => some r'
      | none,    none    => none

/-! ## §5: Structural facts about `cutForest` -/

/-- Every subtree extracted by a cut on `T` is a proper subtree of `T` —
    its `size` is strictly less than `T.size`. Used to prove `T ∉ cutForest c`,
    which in turn drives the term-elimination in algebraic Merge bridge proofs
    (`Theories/Syntax/Minimalist/Hopf/MergeAction.lean`). -/
theorem size_lt_of_mem_cutForest :
    ∀ {T : TraceTree α β} (c : CutShape T) (t : TraceTree α β),
      t ∈ CutShape.cutForest c → t.size < T.size
  | .leaf _, .atLeaf, _, h => by simp [cutForest] at h
  | .trace _, .atTrace, _, h => by simp [cutForest] at h
  | .node l r, .bothCut _ _, t, h => by
      simp only [cutForest] at h
      rw [show ({l, r} : Multiset (TraceTree α β)) = l ::ₘ ({r} : Multiset _) from rfl]
        at h
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at h
      rcases h with rfl | rfl <;> simp [TraceTree.size] <;> omega
  | .node l r, .onlyLeftCut _ cr, t, h => by
      simp only [cutForest, Multiset.mem_add, Multiset.mem_singleton] at h
      rcases h with rfl | hcr
      · simp [TraceTree.size]; omega
      · have ihr := size_lt_of_mem_cutForest cr t hcr
        simp only [TraceTree.size]; omega
  | .node l r, .onlyRightCut _ cl, t, h => by
      simp only [cutForest, Multiset.mem_add, Multiset.mem_singleton] at h
      rcases h with hcl | rfl
      · have ihl := size_lt_of_mem_cutForest cl t hcl
        simp only [TraceTree.size]; omega
      · simp [TraceTree.size]; omega
  | .node l r, .bothRecurse cl cr, t, h => by
      simp only [cutForest, Multiset.mem_add] at h
      rcases h with hcl | hcr
      · have ihl := size_lt_of_mem_cutForest cl t hcl
        simp only [TraceTree.size]; omega
      · have ihr := size_lt_of_mem_cutForest cr t hcr
        simp only [TraceTree.size]; omega

/-- A tree is not a member of any of its own cut forests (proper subtrees). -/
theorem not_mem_cutForest_self {T : TraceTree α β} (c : CutShape T) :
    T ∉ CutShape.cutForest c := by
  intro h
  exact absurd (size_lt_of_mem_cutForest c T h) (lt_irrefl _)

/-- A cut forest never equals the singleton multiset of the source tree. -/
theorem cutForest_ne_singleton_self {T : TraceTree α β} (c : CutShape T) :
    CutShape.cutForest c ≠ ({T} : Multiset (TraceTree α β)) := by
  intro h
  apply not_mem_cutForest_self c
  rw [h]
  exact Multiset.mem_singleton.mpr rfl

/-- **Pair-cross elimination**: for cuts `c : CutShape S` and `c' : CutShape S'`,
    the multiset sum `cutForest c + cutForest c'` cannot equal `{S, S'}`.

    Used in the algebraic Merge bridge (`Theories/Syntax/Minimalist/Hopf/MergeAction.lean`)
    to eliminate cross-terms in the expansion of `Δ^d({S, S'})`: any cut on one
    side combined with any cut on the other side produces a cut-forest different
    from `{S, S'}`, so `δ_{S,S'}` zeroes that term.

    Proof: if the sum were `{S, S'}`, then `S` and `S'` are each in either
    `cutForest c` or `cutForest c'`. Membership in `cutForest c` (resp. `c'`)
    forces a strict size decrease versus `S` (resp. `S'`), so `S ∉ cutForest c`
    and `S' ∉ cutForest c'`. This forces `S ∈ cutForest c'` and `S' ∈ cutForest c`,
    yielding `S.size < S'.size` and `S'.size < S.size` — contradiction. -/
theorem cutForest_add_ne_insert_pair {S S' : TraceTree α β}
    (c : CutShape S) (c' : CutShape S') :
    CutShape.cutForest c + CutShape.cutForest c'
      ≠ ({S, S'} : Multiset (TraceTree α β)) := by
  intro h
  have hSmem : S ∈ ({S, S'} : Multiset (TraceTree α β)) :=
    Multiset.mem_cons_self _ _
  have hS'mem : S' ∈ ({S, S'} : Multiset (TraceTree α β)) :=
    Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr rfl)
  rw [← h, Multiset.mem_add] at hSmem hS'mem
  rcases hSmem with hSc | hSc'
  · exact absurd (size_lt_of_mem_cutForest c S hSc) (lt_irrefl _)
  · rcases hS'mem with hS'c | hS'c'
    · have h1 : S.size < S'.size := size_lt_of_mem_cutForest c' S hSc'
      have h2 : S'.size < S.size := size_lt_of_mem_cutForest c S' hS'c
      omega
    · exact absurd (size_lt_of_mem_cutForest c' S' hS'c') (lt_irrefl _)

/-- **Empty-cut characterization**: `cutForest c = 0` iff `c = empty T`.

    Used in the algebraic Merge bridge's factor-out lemma to identify the unique
    LEFT-empty contributor in `comulTreeDel T`. -/
theorem eq_empty_of_cutForest_eq_zero :
    ∀ {T : TraceTree α β} (c : CutShape T),
      CutShape.cutForest c = (0 : Multiset (TraceTree α β)) → c = CutShape.empty T
  | .leaf _, .atLeaf, _ => rfl
  | .trace _, .atTrace, _ => rfl
  | .node l r, .bothCut hl hr, h => by
      simp only [CutShape.cutForest] at h
      have : l ∈ ({l, r} : Multiset (TraceTree α β)) :=
        Multiset.mem_cons_self _ _
      rw [h] at this
      exact absurd this (Multiset.notMem_zero _)
  | .node l r, .onlyLeftCut hl cr, h => by
      simp only [CutShape.cutForest] at h
      have hl_mem : l ∈ ({l} : Multiset (TraceTree α β)) + cr.cutForest :=
        Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
      rw [h] at hl_mem
      exact absurd hl_mem (Multiset.notMem_zero _)
  | .node l r, .onlyRightCut hr cl, h => by
      simp only [CutShape.cutForest] at h
      have hr_mem : r ∈ cl.cutForest + ({r} : Multiset (TraceTree α β)) :=
        Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
      rw [h] at hr_mem
      exact absurd hr_mem (Multiset.notMem_zero _)
  | .node l r, .bothRecurse cl cr, h => by
      simp only [CutShape.cutForest] at h
      have hcards : (cl.cutForest + cr.cutForest).card
                  = (0 : Multiset (TraceTree α β)).card := by rw [h]
      rw [Multiset.card_add, Multiset.card_zero] at hcards
      have hcl_card : cl.cutForest.card = 0 := by omega
      have hcr_card : cr.cutForest.card = 0 := by omega
      have hcl : cl.cutForest = 0 := Multiset.card_eq_zero.mp hcl_card
      have hcr : cr.cutForest = 0 := Multiset.card_eq_zero.mp hcr_card
      have ihl : cl = CutShape.empty l := eq_empty_of_cutForest_eq_zero cl hcl
      have ihr : cr = CutShape.empty r := eq_empty_of_cutForest_eq_zero cr hcr
      subst ihl; subst ihr
      rfl

/-- **Combined empty-cut characterization**: `cutForest c = 0 ↔ c = empty T`.
    The `mpr` direction restates `cutForest_empty` (in §6 below). -/
theorem cutForest_eq_zero_iff {T : TraceTree α β} (c : CutShape T) :
    CutShape.cutForest c = (0 : Multiset (TraceTree α β)) ↔ c = CutShape.empty T := by
  refine ⟨eq_empty_of_cutForest_eq_zero c, fun h => ?_⟩
  subst h
  -- Show (empty T).cutForest = 0 by induction on T.
  induction T with
  | leaf _ => rfl
  | trace _ => rfl
  | node l r ihl ihr =>
    show (CutShape.bothRecurse (CutShape.empty l) (CutShape.empty r)).cutForest = 0
    rw [CutShape.cutForest, ihl, ihr]
    rfl

/-! ## §6: Sanity checks -/

/-- The empty cut extracts nothing. -/
@[simp] theorem cutForest_empty : ∀ (T : TraceTree α β),
    (empty T).cutForest = (0 : TraceForest α β)
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      show (CutShape.bothRecurse (empty l) (empty r)).cutForest = (0 : TraceForest α β)
      rw [cutForest, cutForest_empty l, cutForest_empty r]
      rfl

/-- The empty cut leaves T unchanged. -/
@[simp] theorem remainder_empty [Inhabited β] : ∀ (T : TraceTree α β),
    (empty T).remainder = T
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      show (CutShape.bothRecurse (empty l) (empty r)).remainder = .node l r
      rw [remainder, remainder_empty l, remainder_empty r]

/-- The empty cut's deletion-remainder is `some T` — the whole tree, unchanged.
    Used by the algebraic Merge bridge's factor-out lemma to identify the
    empty-cut term in `comulTreeDel T` as `1 ⊗ forestToHc {T}`. -/
@[simp] theorem remainderDeletion_empty : ∀ (T : TraceTree α β),
    (empty T).remainderDeletion = some T
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      show (CutShape.bothRecurse (empty l) (empty r)).remainderDeletion = some (.node l r)
      simp only [remainderDeletion, remainderDeletion_empty l, remainderDeletion_empty r]

/-- Cut both child edges of a node: extracts both children. -/
@[simp] theorem cutForest_bothCut {l r : TraceTree α β}
    (hl : TraceTree.IsNotTrace l) (hr : TraceTree.IsNotTrace r) :
    (bothCut hl hr : CutShape (.node l r)).cutForest =
      ({l, r} : Multiset (TraceTree α β)) := rfl

/-- The unique cut on a leaf has empty `cutForest`. -/
@[simp] theorem cutForest_atLeaf {a : α} :
    (atLeaf : CutShape (.leaf a : TraceTree α β)).cutForest = (0 : TraceForest α β) := rfl

/-- The unique cut on a leaf leaves the leaf unchanged. -/
@[simp] theorem remainder_atLeaf [Inhabited β] {a : α} :
    (atLeaf : CutShape (.leaf a : TraceTree α β)).remainder = .leaf a := rfl

/-- The unique cut on a trace has empty `cutForest`. -/
@[simp] theorem cutForest_atTrace {b : β} :
    (atTrace : CutShape (.trace b : TraceTree α β)).cutForest =
      (0 : TraceForest α β) := rfl

/-- The unique cut on a trace leaves the trace unchanged. -/
@[simp] theorem remainder_atTrace [Inhabited β] {b : β} :
    (atTrace : CutShape (.trace b : TraceTree α β)).remainder = .trace b := rfl

/-! ## §6: Position vs. value: cutForest is NOT injective (and that's correct)

A natural question: is `cutForest : CutShape T → TraceForest α β` injective
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

/-! ## §7: `IsNotTrace` is preserved by `remainder`

For `cl : CutShape l`, `remainder cl` has the same top-level constructor as `l`
(modulo `.trace` markers introduced for extracted children). In particular,
`IsNotTrace l` holds iff `IsNotTrace (remainder cl)` holds — the only `.trace`-
shaped tree's only CutShape is `atTrace`, whose remainder is the same `.trace`. -/

/-- `IsNotTrace` is preserved by `remainder` in both directions. -/
theorem isNotTrace_remainder_iff [Inhabited β] {l : TraceTree α β} (cl : CutShape l) :
    TraceTree.IsNotTrace (remainder cl) ↔ TraceTree.IsNotTrace l := by
  cases l with
  | leaf _ => cases cl; exact Iff.rfl
  | trace _ => cases cl; exact Iff.rfl
  | node _ _ => cases cl <;> exact Iff.rfl

/-- Forward direction: if `l` is not a trace marker, neither is its remainder
    after any cut. -/
theorem isNotTrace_remainder [Inhabited β] {l : TraceTree α β} (cl : CutShape l)
    (h : TraceTree.IsNotTrace l) : TraceTree.IsNotTrace (remainder cl) :=
  (isNotTrace_remainder_iff cl).mpr h

/-- Backward direction: if `remainder cl` is not a trace marker, neither is `l`. -/
theorem isNotTrace_of_isNotTrace_remainder [Inhabited β] {l : TraceTree α β} (cl : CutShape l)
    (h : TraceTree.IsNotTrace (remainder cl)) : TraceTree.IsNotTrace l :=
  (isNotTrace_remainder_iff cl).mp h

end CutShape

end ConnesKreimer
