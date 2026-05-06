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
    T with each cut subtree replaced by a `.trace default` leaf.

    The trace label is `default : β` from `[Inhabited β]`. Both
    algebraic-side `β = Unit` (default = `()`, irrelevant) and
    linguistic-side `β = Nat` (default = `0`, sentinel binding index)
    have Inhabited automatically. Callers wanting a specific label can
    provide it via a custom `Inhabited β` instance at the call site
    (rare; in practice the default suffices).

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
    (`Theories/Syntax/Minimalist/Merge/Action.lean`). -/
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

    Used in the algebraic Merge bridge (`Theories/Syntax/Minimalist/Merge/Action.lean`)
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

/-! ## §5.5: Cut depth (cost weighting for Minimal Search)
@cite{marcolli-chomsky-berwick-2025} §1.5

Per @cite{marcolli-chomsky-berwick-2025} Definition in §1.5.2 (p. 59), each
extracted accessible term `T_v ⊂ T` carries a weight `ε^{d_v}` where
`d_v = dist(v, v_T)` is the depth of vertex `v` from the root of `T`.

`cutTotalDepth c` computes the sum `Σ d_v` over all subtrees extracted by
`c`. This is the load-bearing quantity for the Minimal Search cost
function: `c(M(α, β)) = depth(α) + depth(β)` per M-C-B rule 5 (p. 59), and
the cost of a single mergeOp call equals `cutTotalDepth` of the joint cut
producing `(α, β)`.

The empty cut contributes 0 (no extractions). The non-empty cut on a node
adds 1 (depth of immediate children) plus recursive contributions shifted
by 1.

Phase 7d (Minimal Search) consumes this for the weighted Merge operator
`M^ε` and Proposition 1.5.1 (p. 60) — EM/IM are zero-cost; Sideward is
positive-cost.

Note: this captures only the EXTRACTION-side depth (positive contributions
per M-C-B rule 1). Quotient depth (rule 2, with `ε^{-d}` weights) cancels
the extraction depth in the IM composition; we don't track it separately
here because the cancellation-aware ℕ cost function we'll build computes
the final `c(M)` directly. -/

/-- The total depth of a cut: the sum, over all subtrees extracted by `c`,
    of the depth at which each subtree was extracted (= distance from
    the root of the source tree to the vertex where the cut occurred).

    For a cut on `.node l r`:
    - `bothCut`: extracts `l` and `r` each at depth 1 → total = 2.
    - `onlyLeftCut hl cr`: extracts `l` at depth 1, plus `cr`'s extractions
      from inside `r` (each shifted +1) → 1 + (cutTotalDepth cr + |cutForest cr|).
    - `onlyRightCut hr cl`: symmetric.
    - `bothRecurse cl cr`: shifted contributions from both children. -/
def cutTotalDepth : ∀ {T : TraceTree α β}, CutShape T → ℕ
  | .leaf _,   .atLeaf       => 0
  | .trace _,  .atTrace      => 0
  | .node _ _, .bothCut _ _  => 2
  | .node _ _, .onlyLeftCut _ cr =>
      1 + (cutTotalDepth cr + (CutShape.cutForest cr).card)
  | .node _ _, .onlyRightCut _ cl =>
      (cutTotalDepth cl + (CutShape.cutForest cl).card) + 1
  | .node _ _, .bothRecurse cl cr =>
      (cutTotalDepth cl + (CutShape.cutForest cl).card) +
      (cutTotalDepth cr + (CutShape.cutForest cr).card)

/-! ## §5.5.1: Sanity checks for `cutTotalDepth` -/

/-- Helper: the empty cut's `cutForest` is empty (this matches `cutForest_empty`
    in §6 below; restated here as a `private` because §5.5 precedes §6). -/
private theorem cutForest_empty_aux : ∀ (T : TraceTree α β),
    CutShape.cutForest (CutShape.empty T) = (0 : Multiset (TraceTree α β))
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      show CutShape.cutForest
              (CutShape.bothRecurse (CutShape.empty l) (CutShape.empty r))
            = (0 : Multiset (TraceTree α β))
      rw [CutShape.cutForest, cutForest_empty_aux l, cutForest_empty_aux r]
      rfl

/-- The empty cut has depth 0 (no extractions). -/
@[simp] theorem cutTotalDepth_empty : ∀ (T : TraceTree α β),
    cutTotalDepth (CutShape.empty T) = 0
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      show cutTotalDepth (CutShape.bothRecurse (CutShape.empty l) (CutShape.empty r)) = 0
      rw [cutTotalDepth, cutTotalDepth_empty l, cutTotalDepth_empty r,
          cutForest_empty_aux l, cutForest_empty_aux r,
          Multiset.card_zero]

/-- A cut has depth 0 iff its cut-forest is empty (extracts nothing).
    Combined with `cutForest_eq_zero_iff`, this gives `cutTotalDepth c = 0
    ↔ c = empty T`. The cost-weighted Minimal Search formalism uses this
    to characterize "no actual extraction" cases. -/
theorem cutTotalDepth_eq_zero_of_cutForest_eq_zero
    {T : TraceTree α β} (c : CutShape T) (h : CutShape.cutForest c = 0) :
    cutTotalDepth c = 0 := by
  have : c = CutShape.empty T := (cutForest_eq_zero_iff c).mp h
  subst this
  exact cutTotalDepth_empty T

/-- Converse: `cutTotalDepth c = 0` forces `c = empty T`. The non-empty
    cut constructors all contribute strictly positive depth (extracting
    at least one subtree at depth ≥ 1). -/
theorem eq_empty_of_cutTotalDepth_eq_zero :
    ∀ {T : TraceTree α β} (c : CutShape T),
      cutTotalDepth c = 0 → c = CutShape.empty T
  | .leaf _, .atLeaf, _ => rfl
  | .trace _, .atTrace, _ => rfl
  | .node _ _, .bothCut _ _, h => by
      simp only [cutTotalDepth] at h
      omega
  | .node _ _, .onlyLeftCut _ _, h => by
      simp only [cutTotalDepth] at h
      omega
  | .node _ _, .onlyRightCut _ _, h => by
      simp only [cutTotalDepth] at h
      omega
  | .node l r, .bothRecurse cl cr, h => by
      simp only [cutTotalDepth] at h
      have hcl_zero : cutTotalDepth cl = 0 := by omega
      have hcl_card_zero : (CutShape.cutForest cl).card = 0 := by omega
      have hcr_zero : cutTotalDepth cr = 0 := by omega
      have hcr_card_zero : (CutShape.cutForest cr).card = 0 := by omega
      have ihl : cl = CutShape.empty l := eq_empty_of_cutTotalDepth_eq_zero cl hcl_zero
      have ihr : cr = CutShape.empty r := eq_empty_of_cutTotalDepth_eq_zero cr hcr_zero
      subst ihl; subst ihr
      rfl

/-- The full characterization: `cutTotalDepth c = 0 ↔ c = empty T`. -/
theorem cutTotalDepth_eq_zero_iff
    {T : TraceTree α β} (c : CutShape T) :
    cutTotalDepth c = 0 ↔ c = CutShape.empty T :=
  ⟨eq_empty_of_cutTotalDepth_eq_zero c,
   fun h => h ▸ cutTotalDepth_empty T⟩

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
    TraceTree.IsNotTrace cl.remainder ↔ TraceTree.IsNotTrace l := by
  cases l with
  | leaf _ => cases cl; exact Iff.rfl
  | trace _ => cases cl; exact Iff.rfl
  | node _ _ => cases cl <;> exact Iff.rfl

/-- Forward direction: if `l` is not a trace marker, neither is its remainder
    after any cut. -/
theorem isNotTrace_remainder [Inhabited β] {l : TraceTree α β} (cl : CutShape l)
    (h : TraceTree.IsNotTrace l) : TraceTree.IsNotTrace cl.remainder :=
  (isNotTrace_remainder_iff cl).mpr h

/-- Backward direction: if `remainder cl` is not a trace marker, neither is `l`. -/
theorem isNotTrace_of_isNotTrace_remainder [Inhabited β]
    {l : TraceTree α β} (cl : CutShape l)
    (h : TraceTree.IsNotTrace cl.remainder) : TraceTree.IsNotTrace l :=
  (isNotTrace_remainder_iff cl).mp h

/-! ## §8: Δ^d leafCount conservation (M-C-B Def 1.6.2 + book p. 64 remark)

For any admissible cut `c` on `T`, the deletion-coproduct's two channels
together account for all of `T`'s leaves:

  c.cutForest.degForest + (deletionLeafCount c) = T.leafCount

where `deletionLeafCount c` is `(t.leafCount)` if `c.remainderDeletion =
some t`, else `0`. This is M-C-B's degree-conservation observation
(book p. 64, paragraph after Def 1.6.2): "the overall deg(F) = #L(F) of
the workspace F ∈ 𝔉_{SO_0} is a conserved quantity throughout all the
forms of Merge described by (1.3.7)."

Load-bearing for the IM positive direction of Prop 1.6.10
(`im_satisfiesNCL` in `Theories/Syntax/Minimalist/Merge/NoComplexityLoss.lean`):
the IM workspace
transformation `{T} → {.node Q β}` preserves total leafCount because
`β.leafCount + Q.leafCount = T.leafCount` for `Q = T/β` via this lemma. -/

/-- Total leafCount of the deletion-remainder, defined structurally on the
    cut. For each cut constructor, the remainder leaf count is computed
    directly: extracted leaves count as 1 (atLeaf/atTrace), edge contractions
    contribute 0 (bothCut), recursive cases pass through (only*Cut), and
    bothRecurse adds children's contributions.

    Equivalent to `Option.elim 0 leafCount ∘ remainderDeletion` but
    structurally tractable for proofs. -/
def deletionLeafCount : ∀ {T : TraceTree α β}, CutShape T → Nat
  | .leaf _,   .atLeaf => 1
  | .trace _,  .atTrace => 1
  | .node _ _, .bothCut _ _ => 0
  | .node _ _, .onlyLeftCut _ cr => deletionLeafCount cr
  | .node _ _, .onlyRightCut _ cl => deletionLeafCount cl
  | .node _ _, .bothRecurse cl cr => deletionLeafCount cl + deletionLeafCount cr

/-- **Δ^d analog of M-C-B's degree-conservation remark, book p. 64**: the
    deletion-coproduct preserves total leafCount. For any cut `c` on `T`:
    `c.cutForest.degForest + deletionLeafCount c = T.leafCount`.

    M-C-B (book p. 64, paragraph after Def 1.6.2): "Observe that the overall
    degree deg(F) = #L(F) of the workspace … is a conserved quantity
    throughout all the forms of Merge described by (1.3.7), as none of the
    lexical items originally in the workspace is ever removed."

    Note: this is the `leafCount` (= `#L`) slice only. M-C-B's **Lemma 1.6.3**
    (book p. 65) and **Proposition 1.6.4** (book p. 66) concern α (accessible
    terms count) and σ (= b₀ + α), which are different counting functions and
    are NOT formalized here. Those would be needed for the Sideward NCL
    negative directions (per Remark 1.6.9, leafCount alone cannot distinguish
    Sideward 2(b) from IM).

    Structural induction on the cut: each constructor's contribution
    balances out so the total leafCount is conserved. -/
theorem cut_leafCount_conservation :
    ∀ {T : TraceTree α β} (c : CutShape T),
      TraceForest.degForest c.cutForest + deletionLeafCount c = T.leafCount
  | .leaf _, .atLeaf => by
      simp only [cutForest, deletionLeafCount, TraceTree.leafCount_leaf,
                 TraceForest.degForest_zero, Nat.zero_add]
  | .trace _, .atTrace => by
      simp only [cutForest, deletionLeafCount, TraceTree.leafCount_trace,
                 TraceForest.degForest_zero, Nat.zero_add]
  | .node l r, .bothCut _ _ => by
      -- cutForest = {l, r}, deletionLeafCount = 0; collapses via degForest_pair
      simp only [cutForest, deletionLeafCount, TraceTree.leafCount_node,
                 TraceForest.degForest_pair, add_zero]
  | .node l r, .onlyLeftCut _ cr => by
      simp only [cutForest, deletionLeafCount, TraceTree.leafCount_node,
                 TraceForest.degForest_add, TraceForest.degForest_singleton]
      have ih := cut_leafCount_conservation cr
      omega
  | .node l r, .onlyRightCut _ cl => by
      simp only [cutForest, deletionLeafCount, TraceTree.leafCount_node,
                 TraceForest.degForest_add, TraceForest.degForest_singleton]
      have ih := cut_leafCount_conservation cl
      omega
  | .node l r, .bothRecurse cl cr => by
      simp only [cutForest, deletionLeafCount, TraceTree.leafCount_node,
                 TraceForest.degForest_add]
      have ihl := cut_leafCount_conservation cl
      have ihr := cut_leafCount_conservation cr
      omega

/-- **Master bridge**: the structural `deletionLeafCount` agrees with the
    `Option.elim 0 leafCount` of `remainderDeletion`. Both encode "leaves
    surviving in the deletion-quotient", but `deletionLeafCount` is
    structural (induction-friendly) while `remainderDeletion` is the actual
    Δ^d output (Option-valued). -/
theorem deletionLeafCount_eq_option_elim :
    ∀ {T : TraceTree α β} (c : CutShape T),
      deletionLeafCount c = (c.remainderDeletion).elim 0 TraceTree.leafCount
  | .leaf _, .atLeaf => by
      simp only [deletionLeafCount, remainderDeletion, TraceTree.leafCount_leaf,
                 Option.elim]
  | .trace _, .atTrace => by
      simp only [deletionLeafCount, remainderDeletion, TraceTree.leafCount_trace,
                 Option.elim]
  | .node _ _, .bothCut _ _ => by
      simp only [deletionLeafCount, remainderDeletion, Option.elim]
  | .node _ _, .onlyLeftCut _ cr => by
      simp only [deletionLeafCount]
      exact deletionLeafCount_eq_option_elim cr
  | .node _ _, .onlyRightCut _ cl => by
      simp only [deletionLeafCount]
      exact deletionLeafCount_eq_option_elim cl
  | .node _ _, .bothRecurse cl cr => by
      simp only [deletionLeafCount]
      have ihl := deletionLeafCount_eq_option_elim cl
      have ihr := deletionLeafCount_eq_option_elim cr
      -- Reduce remainderDeletion (.bothRecurse cl cr) by case-split on the children
      cases hcl : remainderDeletion cl <;> cases hcr : remainderDeletion cr <;>
        simp only [hcl, hcr, remainderDeletion, TraceTree.leafCount_node,
                   Option.elim] at ihl ihr ⊢ <;>
        omega

/-- Corollary: when a cut has a non-trivial Δ^d remainder `some t`, the
    structural `deletionLeafCount` agrees with `t.leafCount`. The IM-NCL
    theorem in `Theories/Syntax/Minimalist/Merge/NoComplexityLoss.lean` uses
    this to identify `Q.leafCount = deletionLeafCount c0` for
    `c0.remainderDeletion = some Q`. -/
theorem deletionLeafCount_eq_of_remainderDeletion_some {T : TraceTree α β}
    (c : CutShape T) (t : TraceTree α β) (h : c.remainderDeletion = some t) :
    deletionLeafCount c = t.leafCount := by
  rw [deletionLeafCount_eq_option_elim, h]
  rfl

/-! ## §9: Δ^d size conservation (MCB Lemma 1.6.3 size analog)

The size analog of `cut_leafCount_conservation`: for any admissible cut
`c` on `T`,

  `T.size = c.cutForest.sizeForest + deletionSize c + numContractions c`

where:
- `cutForest.sizeForest` is the total vertex count of extracted subtrees;
- `deletionSize c = (c.remainderDeletion).elim 0 size` is the vertex count
  of the binarized deletion-quotient (0 if it collapses entirely);
- `numContractions c` counts the vertices LOST to edge-contraction during
  the deletion-quotient construction. A `.bothCut` always contracts 1
  parent vertex; an `only*Cut` always contracts 1 (its parent has only
  the trace child after the recursion); a `.bothRecurse cl cr` contracts
  1 iff at least one child's remainder collapses (parent loses ≥ 1 child
  → contracts), 0 otherwise.

This generalizes the leafCount conservation (which is contraction-free
because contractions only affect non-leaf vertices). The single-edge
case (`cutForest = {β_t}`, `remainderDeletion = some Q`) yields
`T.size = β_t.size + Q.size + 1` (exactly 1 contraction at the immediate
parent of the cut edge). -/

/-- Number of vertices lost to edge contraction in the Δ^d quotient. See
    §9 docstring for the per-constructor recursion. -/
def numContractions : ∀ {T : TraceTree α β}, CutShape T → Nat
  | .leaf _,   .atLeaf       => 0
  | .trace _,  .atTrace      => 0
  | .node _ _, .bothCut _ _  => 1
  | .node _ _, .onlyLeftCut _ cr => 1 + numContractions cr
  | .node _ _, .onlyRightCut _ cl => 1 + numContractions cl
  | .node _ _, .bothRecurse cl cr =>
      numContractions cl + numContractions cr +
      (match cl.remainderDeletion, cr.remainderDeletion with
       | some _, some _ => 0
       | _,      _      => 1)

/-- **Δ^d size conservation** (MCB Lemma 1.6.3 size analog, book p. 65).
    For any cut `c` on `T`, the source tree's vertex count decomposes
    as the sum of extracted-subtree vertices, deletion-remainder
    vertices, and contracted vertices. Structural induction; each cut
    constructor contributes a known number of contractions per the
    `numContractions` recursion. -/
theorem cut_size_conservation :
    ∀ {T : TraceTree α β} (c : CutShape T),
      T.size = c.cutForest.sizeForest +
                 (c.remainderDeletion).elim 0 TraceTree.size +
                 numContractions c
  | .leaf _, .atLeaf => by
      simp only [cutForest, remainderDeletion, numContractions,
                 TraceForest.sizeForest_zero, Option.elim,
                 TraceTree.size_leaf]
  | .trace _, .atTrace => by
      simp only [cutForest, remainderDeletion, numContractions,
                 TraceForest.sizeForest_zero, Option.elim,
                 TraceTree.size_trace]
  | .node l r, .bothCut _ _ => by
      simp only [cutForest, remainderDeletion, numContractions,
                 TraceForest.sizeForest_pair, Option.elim,
                 TraceTree.size_node]
      omega
  | .node l r, .onlyLeftCut _ cr => by
      have ih := cut_size_conservation cr
      simp only [cutForest, remainderDeletion, numContractions,
                 TraceForest.sizeForest_add, TraceForest.sizeForest_singleton,
                 TraceTree.size_node]
      omega
  | .node l r, .onlyRightCut _ cl => by
      have ih := cut_size_conservation cl
      simp only [cutForest, remainderDeletion, numContractions,
                 TraceForest.sizeForest_add, TraceForest.sizeForest_singleton,
                 TraceTree.size_node]
      omega
  | .node l r, .bothRecurse cl cr => by
      have ihl := cut_size_conservation cl
      have ihr := cut_size_conservation cr
      simp only [cutForest, numContractions,
                 TraceForest.sizeForest_add, TraceTree.size_node]
      cases hl : cl.remainderDeletion <;> cases hr : cr.remainderDeletion <;>
        simp only [hl, hr, remainderDeletion, Option.elim,
                   TraceTree.size_node] at ihl ihr ⊢ <;>
        omega

/-! ### Δ^c size conservation -/

/-- **Δ^c size conservation** (MCB Lemma 1.6.3 size analog for the
    contraction quotient, book p. 65). For any cut `c` on a trace-free
    `T`, the source tree's vertex count decomposes cleanly into
    extracted-subtree vertices plus the contraction-remainder's
    NON-TRACE vertex count:

      `T.size = c.cutForest.sizeForest + (c.remainder).nonTraceSize`

    The trace-free hypothesis is encoded as `T.nonTraceSize = T.size` —
    matching MCB's setup where syntactic objects in the workspace are
    trace-free; trace markers appear only in quotient trees.

    No "contraction count" appears here — Δ^c preserves all parent
    vertices (they hold the trace markers). The trace markers in the
    remainder don't count toward `nonTraceSize`, exactly recovering the
    extracted subtrees' vertex bookkeeping.

    Compare to `cut_size_conservation` for Δ^d which has an extra
    `numContractions c` term. -/
theorem cut_size_conservation_contraction [Inhabited β] :
    ∀ {T : TraceTree α β} (c : CutShape T),
      T.nonTraceSize = T.size →
      T.size = c.cutForest.sizeForest + c.remainder.nonTraceSize
  | .leaf _, .atLeaf, _ => by
      simp only [cutForest, remainder, TraceForest.sizeForest_zero,
                 TraceTree.nonTraceSize_leaf, TraceTree.size_leaf]
  | .trace _, .atTrace, h_tf => by
      -- Trace at root: nonTraceSize = 0, size = 1, contradicts hypothesis.
      simp only [TraceTree.nonTraceSize_trace, TraceTree.size_trace] at h_tf
      omega
  | .node l r, .bothCut hl hr, h_tf => by
      simp only [cutForest, remainder, TraceForest.sizeForest_pair,
                 TraceTree.nonTraceSize_node, TraceTree.nonTraceSize_trace,
                 TraceTree.size_node]
      -- l, r both trace-free from hypothesis (nonTraceSize_node = size_node).
      simp only [TraceTree.nonTraceSize_node, TraceTree.size_node] at h_tf
      have hl_tf : l.nonTraceSize = l.size := by
        have := l.nonTraceSize_le_size
        have := r.nonTraceSize_le_size
        omega
      have hr_tf : r.nonTraceSize = r.size := by
        have := l.nonTraceSize_le_size
        have := r.nonTraceSize_le_size
        omega
      omega
  | .node l r, .onlyLeftCut hl cr, h_tf => by
      simp only [TraceTree.nonTraceSize_node, TraceTree.size_node] at h_tf
      have hl_tf : l.nonTraceSize = l.size := by
        have := l.nonTraceSize_le_size
        have := r.nonTraceSize_le_size
        omega
      have hr_tf : r.nonTraceSize = r.size := by
        have := l.nonTraceSize_le_size
        have := r.nonTraceSize_le_size
        omega
      have ih := cut_size_conservation_contraction cr hr_tf
      simp only [cutForest, remainder, TraceForest.sizeForest_add,
                 TraceForest.sizeForest_singleton,
                 TraceTree.nonTraceSize_node, TraceTree.nonTraceSize_trace,
                 TraceTree.size_node]
      omega
  | .node l r, .onlyRightCut hr cl, h_tf => by
      simp only [TraceTree.nonTraceSize_node, TraceTree.size_node] at h_tf
      have hl_tf : l.nonTraceSize = l.size := by
        have := l.nonTraceSize_le_size
        have := r.nonTraceSize_le_size
        omega
      have hr_tf : r.nonTraceSize = r.size := by
        have := l.nonTraceSize_le_size
        have := r.nonTraceSize_le_size
        omega
      have ih := cut_size_conservation_contraction cl hl_tf
      simp only [cutForest, remainder, TraceForest.sizeForest_add,
                 TraceForest.sizeForest_singleton,
                 TraceTree.nonTraceSize_node, TraceTree.nonTraceSize_trace,
                 TraceTree.size_node]
      omega
  | .node l r, .bothRecurse cl cr, h_tf => by
      simp only [TraceTree.nonTraceSize_node, TraceTree.size_node] at h_tf
      have hl_tf : l.nonTraceSize = l.size := by
        have := l.nonTraceSize_le_size
        have := r.nonTraceSize_le_size
        omega
      have hr_tf : r.nonTraceSize = r.size := by
        have := l.nonTraceSize_le_size
        have := r.nonTraceSize_le_size
        omega
      have ihl := cut_size_conservation_contraction cl hl_tf
      have ihr := cut_size_conservation_contraction cr hr_tf
      simp only [cutForest, remainder, TraceForest.sizeForest_add,
                 TraceTree.nonTraceSize_node, TraceTree.size_node]
      omega

/-- Trace-freeness propagates: any subtree extracted by a cut on a
    trace-free `T` is itself trace-free. Used by Δ^c counting to certify
    that extracted accessible terms (β_t) have `accCountC = accCount`. -/
theorem nonTraceSize_eq_size_of_mem_cutForest :
    ∀ {T : TraceTree α β} (c : CutShape T) (t : TraceTree α β),
      T.nonTraceSize = T.size →
      t ∈ c.cutForest →
      t.nonTraceSize = t.size
  | .leaf _, .atLeaf, _, _, h_mem => by
      simp only [cutForest, Multiset.notMem_zero] at h_mem
  | .trace _, .atTrace, _, _, h_mem => by
      simp only [cutForest, Multiset.notMem_zero] at h_mem
  | .node l r, .bothCut _ _, t, h_tf, h_mem => by
      simp only [TraceTree.nonTraceSize_node, TraceTree.size_node] at h_tf
      have hl : l.nonTraceSize = l.size := by
        have := l.nonTraceSize_le_size; have := r.nonTraceSize_le_size; omega
      have hr : r.nonTraceSize = r.size := by
        have := l.nonTraceSize_le_size; have := r.nonTraceSize_le_size; omega
      simp only [cutForest] at h_mem
      rw [show ({l, r} : TraceForest α β) = l ::ₘ {r} from rfl,
          Multiset.mem_cons, Multiset.mem_singleton] at h_mem
      rcases h_mem with rfl | rfl
      · exact hl
      · exact hr
  | .node l r, .onlyLeftCut _ cr, t, h_tf, h_mem => by
      simp only [TraceTree.nonTraceSize_node, TraceTree.size_node] at h_tf
      have hl : l.nonTraceSize = l.size := by
        have := l.nonTraceSize_le_size; have := r.nonTraceSize_le_size; omega
      have hr : r.nonTraceSize = r.size := by
        have := l.nonTraceSize_le_size; have := r.nonTraceSize_le_size; omega
      simp only [cutForest, Multiset.mem_add, Multiset.mem_singleton] at h_mem
      rcases h_mem with rfl | h_in_cr
      · exact hl
      · exact nonTraceSize_eq_size_of_mem_cutForest cr t hr h_in_cr
  | .node l r, .onlyRightCut _ cl, t, h_tf, h_mem => by
      simp only [TraceTree.nonTraceSize_node, TraceTree.size_node] at h_tf
      have hl : l.nonTraceSize = l.size := by
        have := l.nonTraceSize_le_size; have := r.nonTraceSize_le_size; omega
      have hr : r.nonTraceSize = r.size := by
        have := l.nonTraceSize_le_size; have := r.nonTraceSize_le_size; omega
      simp only [cutForest, Multiset.mem_add, Multiset.mem_singleton] at h_mem
      rcases h_mem with h_in_cl | rfl
      · exact nonTraceSize_eq_size_of_mem_cutForest cl t hl h_in_cl
      · exact hr
  | .node l r, .bothRecurse cl cr, t, h_tf, h_mem => by
      simp only [TraceTree.nonTraceSize_node, TraceTree.size_node] at h_tf
      have hl : l.nonTraceSize = l.size := by
        have := l.nonTraceSize_le_size; have := r.nonTraceSize_le_size; omega
      have hr : r.nonTraceSize = r.size := by
        have := l.nonTraceSize_le_size; have := r.nonTraceSize_le_size; omega
      simp only [cutForest, Multiset.mem_add] at h_mem
      rcases h_mem with h_in_cl | h_in_cr
      · exact nonTraceSize_eq_size_of_mem_cutForest cl t hl h_in_cl
      · exact nonTraceSize_eq_size_of_mem_cutForest cr t hr h_in_cr

/-- For a cut on a `.node` source tree, the contraction-remainder has
    `nonTraceSize ≥ 1` (the root parent vertex is preserved as a `.node`,
    contributing 1 regardless of which child is replaced by `.trace`). -/
theorem nonTraceSize_remainder_pos_of_node [Inhabited β]
    {l r : TraceTree α β} (c : CutShape (.node l r)) :
    c.remainder.nonTraceSize ≥ 1 := by
  cases c with
  | bothCut _ _ => simp only [remainder, TraceTree.nonTraceSize_node,
                                TraceTree.nonTraceSize_trace]; omega
  | onlyLeftCut _ _ => simp only [remainder, TraceTree.nonTraceSize_node,
                                    TraceTree.nonTraceSize_trace]; omega
  | onlyRightCut _ _ => simp only [remainder, TraceTree.nonTraceSize_node,
                                     TraceTree.nonTraceSize_trace]; omega
  | bothRecurse _ _ => simp only [remainder, TraceTree.nonTraceSize_node]; omega

/-- A cut with a singleton cutForest forces `T` to be a `.node`. (Leaf
    and trace roots have only the trivial empty cut, with `cutForest = 0`.)
    Useful for downstream proofs that need to use
    `nonTraceSize_remainder_pos_of_node` on a `T` introduced as
    `TraceTree α β` rather than `.node l r` syntactically. -/
theorem isNode_of_cutForest_singleton :
    ∀ {T : TraceTree α β} (c : CutShape T) (β_t : TraceTree α β),
      c.cutForest = ({β_t} : TraceForest α β) →
      ∃ l r, T = .node l r
  | .leaf _, .atLeaf, β_t, h => by
      exfalso
      simp only [cutForest] at h
      have : β_t ∈ ({β_t} : TraceForest α β) := Multiset.mem_singleton.mpr rfl
      rw [← h] at this; exact absurd this (Multiset.notMem_zero _)
  | .trace _, .atTrace, β_t, h => by
      exfalso
      simp only [cutForest] at h
      have : β_t ∈ ({β_t} : TraceForest α β) := Multiset.mem_singleton.mpr rfl
      rw [← h] at this; exact absurd this (Multiset.notMem_zero _)
  | .node l r, _, _, _ => ⟨l, r, rfl⟩

/-- Convenience wrapper: a cut with singleton cutForest has
    `remainder.nonTraceSize ≥ 1` regardless of how `T` is syntactically
    introduced. Combines `isNode_of_cutForest_singleton` and
    `nonTraceSize_remainder_pos_of_node`. -/
theorem nonTraceSize_remainder_pos_of_cutForest_singleton [Inhabited β]
    {T : TraceTree α β} (c : CutShape T) (β_t : TraceTree α β)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β)) :
    c.remainder.nonTraceSize ≥ 1 := by
  obtain ⟨l, r, rfl⟩ := isNode_of_cutForest_singleton c β_t h_cf
  exact nonTraceSize_remainder_pos_of_node c

/-- **MCB Lemma 1.6.3 eq. 1.6.8** (book p. 65): for a single-edge cut on
    `T` extracting accessible term `β_t`, the contraction-quotient's
    accCountC satisfies `α(T) = α(T_v) + α^c(T/^c T_v) + 1`. The `+1`
    accounts for the root vertex of `T` (counted in `accCount T = T.size − 1`
    but not in the per-piece sum since the root is the new merged node
    when re-merging).

    Concretely: `T.size − 1 = (β_t.size − 1) + ((T/^c β_t).nonTraceSize − 1) + 1`
    follows from `cut_size_conservation_contraction` with cutForest = {β_t}
    and the size-pos witnesses. -/
theorem singleEdgeCut_contraction_alpha [Inhabited β]
    {T : TraceTree α β} (c : CutShape T) (β_t : TraceTree α β)
    (h_tf : T.nonTraceSize = T.size)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β)) :
    T.accCount = β_t.accCount + c.remainder.accCountC + 1 := by
  have h := cut_size_conservation_contraction c h_tf
  rw [h_cf, TraceForest.sizeForest_singleton] at h
  have hβ := β_t.size_pos
  have hRem_pos : c.remainder.nonTraceSize ≥ 1 :=
    nonTraceSize_remainder_pos_of_cutForest_singleton c β_t h_cf
  show T.size - 1 = (β_t.size - 1) + (c.remainder.nonTraceSize - 1) + 1
  omega

/-- **MCB Lemma 1.6.3 eq. 1.6.10** (book p. 65): `σ(T) = σ(T_v) + σ(T/^c T_v)`
    for a single-edge cut on T extracting β_t. (No `+1` in this case — the
    root vertex is already counted in σ_v + σ_q via the b₀ contribution.)

    Concretely: `1 + (T.size − 1) = (1 + (β_t.size − 1)) + (1 + ((T/^c β_t).nonTraceSize − 1))`
    follows from `cut_size_conservation_contraction`. -/
theorem singleEdgeCut_contraction_sigma [Inhabited β]
    {T : TraceTree α β} (c : CutShape T) (β_t : TraceTree α β)
    (h_tf : T.nonTraceSize = T.size)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β)) :
    TraceForest.sigma ({T} : TraceForest α β)
      = TraceForest.sigma ({β_t} : TraceForest α β)
      + TraceForest.sigmaC ({c.remainder} : TraceForest α β) := by
  have h_alpha := singleEdgeCut_contraction_alpha c β_t h_tf h_cf
  rw [TraceForest.sigma_singleton, TraceForest.sigma_singleton,
      TraceForest.sigmaC_singleton]
  show 1 + T.accCount = 1 + β_t.accCount + (1 + c.remainder.accCountC)
  omega

/-- **Single-edge cut produces non-collapsing remainder**: if a cut has
    a singleton `cutForest = {β_t}`, then its `remainderDeletion` is
    `some _` (cannot be `none`). Contrapositive: a `none` remainder requires
    a `.bothCut` at some node, which contributes ≥ 2 elements to `cutForest`.

    Proved by structural recursion on the tree (and case-analysis on the
    cut at each level), using `eq_empty_of_cutForest_eq_zero` to identify
    the empty subordinate cuts and `remainderDeletion_empty` to discharge
    them. -/
theorem remainderDeletion_ne_none_of_cutForest_singleton :
    ∀ {T : TraceTree α β} (c : CutShape T) (β_t : TraceTree α β),
      c.cutForest = ({β_t} : TraceForest α β) →
      c.remainderDeletion ≠ none
  | .leaf _, .atLeaf, β_t, h_cf => by
      exfalso
      simp only [cutForest] at h_cf
      have : β_t ∈ ({β_t} : TraceForest α β) := Multiset.mem_singleton.mpr rfl
      rw [← h_cf] at this
      exact absurd this (Multiset.notMem_zero _)
  | .trace _, .atTrace, β_t, h_cf => by
      exfalso
      simp only [cutForest] at h_cf
      have : β_t ∈ ({β_t} : TraceForest α β) := Multiset.mem_singleton.mpr rfl
      rw [← h_cf] at this
      exact absurd this (Multiset.notMem_zero _)
  | .node l r, .bothCut _ _, β_t, h_cf => by
      exfalso
      simp only [cutForest] at h_cf
      have hc : ({l, r} : TraceForest α β).card = ({β_t} : TraceForest α β).card := by
        rw [h_cf]
      rw [show ({l, r} : TraceForest α β) = l ::ₘ {r} from rfl,
          Multiset.card_cons, Multiset.card_singleton, Multiset.card_singleton] at hc
      omega
  | .node l r, .onlyLeftCut _ cr, β_t, h_cf => by
      simp only [cutForest] at h_cf
      have h_card : (({l} : TraceForest α β) + cr.cutForest).card = 1 := by
        rw [h_cf]; exact Multiset.card_singleton _
      rw [Multiset.card_add, Multiset.card_singleton] at h_card
      have h_cr_card : cr.cutForest.card = 0 := by omega
      have h_cr_zero : cr.cutForest = 0 := Multiset.card_eq_zero.mp h_cr_card
      have h_cr_empty : cr = CutShape.empty r :=
        eq_empty_of_cutForest_eq_zero cr h_cr_zero
      simp only [remainderDeletion]
      rw [h_cr_empty, remainderDeletion_empty]
      exact Option.some_ne_none _
  | .node l r, .onlyRightCut _ cl, β_t, h_cf => by
      simp only [cutForest] at h_cf
      have h_card : (cl.cutForest + ({r} : TraceForest α β)).card = 1 := by
        rw [h_cf]; exact Multiset.card_singleton _
      rw [Multiset.card_add, Multiset.card_singleton] at h_card
      have h_cl_card : cl.cutForest.card = 0 := by omega
      have h_cl_zero : cl.cutForest = 0 := Multiset.card_eq_zero.mp h_cl_card
      have h_cl_empty : cl = CutShape.empty l :=
        eq_empty_of_cutForest_eq_zero cl h_cl_zero
      simp only [remainderDeletion]
      rw [h_cl_empty, remainderDeletion_empty]
      exact Option.some_ne_none _
  | .node l r, .bothRecurse cl cr, β_t, h_cf => by
      simp only [cutForest] at h_cf
      have h_card : (cl.cutForest + cr.cutForest).card = 1 := by
        rw [h_cf]; exact Multiset.card_singleton _
      rw [Multiset.card_add] at h_card
      rcases Nat.eq_zero_or_pos cl.cutForest.card with h_cl_zero_card | h_cl_pos
      · have h_cl_zero : cl.cutForest = 0 := Multiset.card_eq_zero.mp h_cl_zero_card
        have h_cl_empty : cl = CutShape.empty l :=
          eq_empty_of_cutForest_eq_zero cl h_cl_zero
        have h_cr_eq : cr.cutForest = ({β_t} : TraceForest α β) := by
          rw [h_cl_zero, zero_add] at h_cf; exact h_cf
        have ih_cr := remainderDeletion_ne_none_of_cutForest_singleton cr β_t h_cr_eq
        simp only [remainderDeletion]
        rw [h_cl_empty, remainderDeletion_empty]
        cases h_cr_rd : cr.remainderDeletion with
        | none => exact absurd h_cr_rd ih_cr
        | some _ => exact Option.some_ne_none _
      · have h_cr_zero_card : cr.cutForest.card = 0 := by omega
        have h_cr_zero : cr.cutForest = 0 := Multiset.card_eq_zero.mp h_cr_zero_card
        have h_cr_empty : cr = CutShape.empty r :=
          eq_empty_of_cutForest_eq_zero cr h_cr_zero
        have h_cl_eq : cl.cutForest = ({β_t} : TraceForest α β) := by
          rw [h_cr_zero, add_zero] at h_cf; exact h_cf
        have ih_cl := remainderDeletion_ne_none_of_cutForest_singleton cl β_t h_cl_eq
        simp only [remainderDeletion]
        rw [h_cr_empty, remainderDeletion_empty]
        cases h_cl_rd : cl.remainderDeletion with
        | none => exact absurd h_cl_rd ih_cl
        | some _ => exact Option.some_ne_none _

/-- The empty cut contracts no vertices. -/
@[simp] theorem numContractions_empty :
    ∀ (T : TraceTree α β), numContractions (CutShape.empty T) = 0
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      show numContractions
              (CutShape.bothRecurse (CutShape.empty l) (CutShape.empty r)) = 0
      simp only [numContractions, remainderDeletion_empty,
                 numContractions_empty l, numContractions_empty r]

/-- **Vertex-accounting master equation** (sharper bookkeeping at the
    cardinality layer; companion to `cut_size_conservation` at the size
    layer).

    For any cut `c : CutShape T`,
    `c.cutForest.card = numContractions c + (1 if rd = none, else 0)`.

    Geometric reading: each cut edge contributes one extracted subtree
    to `cutForest` and one contracted parent vertex to `numContractions`.
    The root of `T` contributes an *extra* contraction precisely when
    the cut includes a `.bothCut` at the root (`rd = none`); when
    `rd = some`, the root survives into the deletion remainder.

    Subsumes the legacy single-edge / two-edge contraction-count lemmas
    (`numContractions_singleEdge`, `numContractions_twoEdge`); both are
    restated below as 1-line `omega` corollaries. -/
theorem cutForest_card_eq_numContractions_add :
    ∀ {T : TraceTree α β} (c : CutShape T),
      c.cutForest.card =
        numContractions c + c.remainderDeletion.elim 1 (fun _ => 0)
  | .leaf _, .atLeaf => rfl
  | .trace _, .atTrace => rfl
  | .node l r, .bothCut _ _ => by
      show ({l, r} : TraceForest α β).card = 1 + 1
      rw [show ({l, r} : TraceForest α β) = l ::ₘ {r} from rfl,
          Multiset.card_cons, Multiset.card_singleton]
  | .node _ _, .onlyLeftCut _ cr => by
      have ih := cutForest_card_eq_numContractions_add cr
      simp only [cutForest, Multiset.card_add, Multiset.card_singleton,
                 numContractions, remainderDeletion]
      omega
  | .node _ _, .onlyRightCut _ cl => by
      have ih := cutForest_card_eq_numContractions_add cl
      simp only [cutForest, Multiset.card_add, Multiset.card_singleton,
                 numContractions, remainderDeletion]
      omega
  | .node _ _, .bothRecurse cl cr => by
      have ihl := cutForest_card_eq_numContractions_add cl
      have ihr := cutForest_card_eq_numContractions_add cr
      simp only [cutForest, Multiset.card_add, numContractions, remainderDeletion]
      cases h_cl : cl.remainderDeletion with
      | some _ =>
          rw [h_cl] at ihl
          cases h_cr : cr.remainderDeletion with
          | some _ => rw [h_cr] at ihr; simp only [Option.elim] at ihl ihr ⊢; omega
          | none   => rw [h_cr] at ihr; simp only [Option.elim] at ihl ihr ⊢; omega
      | none =>
          rw [h_cl] at ihl
          cases h_cr : cr.remainderDeletion with
          | some _ => rw [h_cr] at ihr; simp only [Option.elim] at ihl ihr ⊢; omega
          | none   => rw [h_cr] at ihr; simp only [Option.elim] at ihl ihr ⊢; omega

/-- Specialization of `cutForest_card_eq_numContractions_add` for the
    `rd = some` branch: `numContractions c = c.cutForest.card`. -/
theorem numContractions_eq_card_of_remainderDeletion_some
    {T : TraceTree α β} {c : CutShape T} {Q : TraceTree α β}
    (h_rd : c.remainderDeletion = some Q) :
    numContractions c = c.cutForest.card := by
  have h := cutForest_card_eq_numContractions_add c
  rw [h_rd] at h; simp only [Option.elim] at h; omega

/-- Specialization of `cutForest_card_eq_numContractions_add` for the
    `rd = none` branch: `numContractions c + 1 = c.cutForest.card`. -/
theorem numContractions_succ_eq_card_of_remainderDeletion_none
    {T : TraceTree α β} {c : CutShape T}
    (h_rd : c.remainderDeletion = none) :
    numContractions c + 1 = c.cutForest.card := by
  have h := cutForest_card_eq_numContractions_add c
  rw [h_rd] at h; simp only [Option.elim] at h; omega

/-- A single-edge cut has exactly 1 contracted vertex: the parent of the
    cut edge. Corollary of `numContractions_eq_card_of_remainderDeletion_some`
    with `cutForest.card = 1` and the singleton-implies-rd-some witness
    `remainderDeletion_ne_none_of_cutForest_singleton`. -/
theorem numContractions_singleEdge
    {T : TraceTree α β} (c : CutShape T) (β_t : TraceTree α β)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β)) :
    numContractions c = 1 := by
  have h_rd_ne := remainderDeletion_ne_none_of_cutForest_singleton c β_t h_cf
  cases h_rd : c.remainderDeletion with
  | none => exact absurd h_rd h_rd_ne
  | some Q =>
      have h := numContractions_eq_card_of_remainderDeletion_some h_rd
      rw [h_cf, Multiset.card_singleton] at h; exact h

/-- **Two-edge cut has exactly 2 contracted vertices** (MCB Prop 1.6.8
    case 3(a), book p. 70: "two edges are contracted, and hence the
    counting of (non-root) vertices decreases by 2"). Corollary of
    `numContractions_eq_card_of_remainderDeletion_some` with
    `cutForest.card = 2`. -/
theorem numContractions_twoEdge
    {T : TraceTree α β} (c : CutShape T) (Q : TraceTree α β)
    (h_card : c.cutForest.card = 2) (h_rd : c.remainderDeletion = some Q) :
    numContractions c = 2 := by
  have h := numContractions_eq_card_of_remainderDeletion_some h_rd
  omega

/-- **Single-edge-cut size relation** (MCB Lemma 1.6.3 size analog of
    eq. 1.6.7 / 1.6.9, book p. 65). For any cut `c : CutShape T` whose
    `cutForest` is the singleton `{β_t}` and whose `remainderDeletion` is
    `some Q`, the source tree `T` decomposes as
    `T.size = β_t.size + Q.size + 1`.

    Geometric reading: a single edge cut splits `T` into the extracted
    accessible term `β_t` and the binarized deletion-quotient `Q`, plus
    the contracted parent vertex of the cut edge (the `+1`).

    **Corollary of `cut_size_conservation`** with `numContractions = 1`
    (single-edge case, by `numContractions_singleEdge`).

    Used by `MinimalYield.im_pair_size_deltas_deltaD` and
    `MinimalYield.sideward_2b_size_deltas_deltaD` to discharge the
    `h_size` hypothesis from cut data. -/
theorem singleEdgeCut_size_relation
    {T : TraceTree α β} (c : CutShape T) (β_t Q : TraceTree α β)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β))
    (h_rd : c.remainderDeletion = some Q) :
    T.size = β_t.size + Q.size + 1 := by
  have h_general := cut_size_conservation c
  have h_nc := numContractions_singleEdge c β_t h_cf
  rw [h_cf, h_rd, TraceForest.sizeForest_singleton, h_nc] at h_general
  simpa using h_general

end CutShape

end ConnesKreimer
