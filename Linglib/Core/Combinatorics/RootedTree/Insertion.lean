import Linglib.Core.Combinatorics.RootedTree.Decorated
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finsupp.Multiset

set_option autoImplicit false

/-!
# Insertion Operation on Trace Trees (MCB §1.7.1-§1.7.2)
@cite{marcolli-chomsky-berwick-2025} §1.7, book p. 73-80

Realises the **insertion operation** of MCB Definition 1.7.1 (book p. 77,
eq. 1.7.8): for nonplanar binary rooted trees `T₁`, `T₂` with `T₁` having
a nonempty edge set, `T₁ ◁ T₂` is the formal sum of trees obtained by
inserting `T₂` at each edge of `T₁` — splitting that edge with a new
internal vertex and attaching `T₂` as the sibling of the old subtree.

This operation is the algebraic substrate underlying **countercyclic**
moves like Late Merge and Countercyclic Merge (book Figure 1.5, p. 74).

## MCB §1.7's headline conclusion

The operation `T₁ ◁ T₂` defines a **right pre-Lie structure**
(Lemma 1.7.2, book p. 77), giving a Lie algebra structure on the free
vector space of trees with edges via `[T₁, T₂] = T₁ ◁ T₂ - T₂ ◁ T₁`
(eq. 1.7.9).

Lemma 1.7.3 (book p. 78) identifies this insertion Lie algebra with
the **Lie algebra of primitive elements of the dual Hopf algebra of
workspaces**. Under this identification, *countercyclic insertions add
no expressive power beyond the EM/IM operations already accounted for
by the Hopf algebra of workspaces*. Late Merge and Countercyclic Merge
are not new operations — they are dual-side reformulations of EM/IM
compositions (book p. 80).

## Scope of this file (Phase 1 substrate)

- §1: `insertSum` — sum over all edges (eq. 1.7.8) as a `Multiset` of
  resulting trees, capturing the additive content of the formal sum.
- §2: Basic structural reductions (zero on `.leaf` / `.trace`; the
  `.node` recursion).
- §3: Edge-counting consistency: `(T₁ ◁ T₂).card = numEdges T₁`.

## Scope of this file (Phases 1-2)

- §1: `insertSum` — sum over all edges (eq. 1.7.8) as a `Multiset` of
  resulting trees, capturing the additive content of the formal sum.
- §2: Basic structural reductions (zero on `.leaf` / `.trace`; the
  `.node` recursion).
- §3: Edge-counting consistency: `(T₁ ◁ T₂).card = numEdges T₁`.
- §4: ℤ-coefficient lift `insertSumZ : T → T → (T →₀ ℤ)` and the
  right Lie bracket `[T₁, T₂]_R := T₁ ◁ T₂ - T₂ ◁ T₁` (eq. 1.7.9).
  Antisymmetry on basis trees is by definition.

## Deferred (Phase 3-5)

- **Phase 3**: Right pre-Lie identity for `◁` (MCB Lemma 1.7.2,
  book p. 77, eq. 1.7.2 specialized): on the bilinear extension to
  `(T →₀ ℤ)`,
  `(T₁ ◁ T₂) ◁ T₃ - T₁ ◁ (T₂ ◁ T₃) = (T₁ ◁ T₃) ◁ T₂ - T₁ ◁ (T₃ ◁ T₂)`.
  Implies the Jacobi identity for `[·,·]_R`.
- **Phase 4**: Identification with the dual Hopf algebra primitive Lie
  algebra (Lemma 1.7.3, book p. 78). Requires the dual Hopf algebra
  `H^∨` construction, the `δ`-function basis, and the star product
  (eq. 1.7.6) in the dual.
- **Phase 5 (linguistic headline)**: any tree obtainable by countercyclic
  insertion `T₁ ◁_e T₂` is reachable in the workspace via some
  composition of EM/IM (and possibly bounded Sideward) operations —
  formalising MCB's claim that countercyclic moves are dual-side
  reformulations rather than primitive new operations (book p. 80).
-/

namespace ConnesKreimer

namespace TraceTree

universe u v

variable {α : Type u} {β : Type v}

/-! ## §1: The insertion sum (MCB Definition 1.7.1, eq. 1.7.8) -/

/-- `insertSum T₁ T₂` is the multiset of trees obtained by inserting
    `T₂` at each edge of `T₁`. Realises MCB eq. (1.7.8):
    `T₁ ◁ T₂ = Σ_{e ∈ E(T₁)} T₁ ◁_e T₂`.

    Per-edge operation `T₁ ◁_e T₂`: split edge `e` (connecting some
    parent to a child subtree) with a new internal vertex `v`, attach
    `T₂` as a child of `v`, and reconnect the original subtree as the
    other child of `v`. The new vertex `v` is a binary `.node`
    constructor (no leaf label), matching MCB's "valence 2 vertex"
    convention (book p. 77).

    Recursion on the binary tree structure:
    - The two immediate edges of `.node l r` (root→l, root→r) yield the
      two top-level results `.node (.node l T₂) r` and `.node l (.node r T₂)`.
    - Edges within `l` are handled by recursion on `l`, lifting the
      recursive insertion result back through the right context
      `fun l' => .node l' r`.
    - Symmetric for edges within `r`.
    - `.leaf` and `.trace` have no edges → empty multiset (the additive
      identity, matching the "empty sum" in MCB's vector-space view). -/
def insertSum :
    TraceTree α β → TraceTree α β → Multiset (TraceTree α β)
  | .leaf _,   _  => 0
  | .trace _,  _  => 0
  | .node l r, T₂ =>
      ({(.node (.node l T₂) r), (.node l (.node r T₂))}
            : Multiset (TraceTree α β))
        + (insertSum l T₂).map (fun l' => .node l' r)
        + (insertSum r T₂).map (fun r' => .node l r')

/-- Notation `T₁ ◁ T₂` for `insertSum T₁ T₂`. The right-triangular
    Unicode glyph matches MCB's typesetting (eq. 1.7.8 onward). -/
infixl:65 " ◁ " => insertSum

/-! ## §2: Basic structural reductions -/

@[simp] theorem insertSum_leaf (a : α) (T₂ : TraceTree α β) :
    (TraceTree.leaf a) ◁ T₂ = 0 := rfl

@[simp] theorem insertSum_trace (b : β) (T₂ : TraceTree α β) :
    (TraceTree.trace b) ◁ T₂ = 0 := rfl

@[simp] theorem insertSum_node (l r T₂ : TraceTree α β) :
    (TraceTree.node l r) ◁ T₂
      = ({(.node (.node l T₂) r), (.node l (.node r T₂))}
            : Multiset (TraceTree α β))
        + (l ◁ T₂).map (fun l' => .node l' r)
        + (r ◁ T₂).map (fun r' => .node l r') := rfl

/-! ## §3: Edge counting -/

/-- The number of edges of a `TraceTree`: a tree with `n` vertices
    (= `size`) has `n − 1` edges. Used as the pre-Lie subspace
    discriminator in MCB Lemma 1.7.2 ("trees with nonempty set of
    edges"). -/
def numEdges (T : TraceTree α β) : Nat := T.size - 1

@[simp] theorem numEdges_leaf (a : α) :
    numEdges (TraceTree.leaf a : TraceTree α β) = 0 := rfl

@[simp] theorem numEdges_trace (b : β) :
    numEdges (TraceTree.trace b : TraceTree α β) = 0 := rfl

theorem numEdges_node (l r : TraceTree α β) :
    numEdges (TraceTree.node l r) = numEdges l + numEdges r + 2 := by
  have hl := l.size_pos
  have hr := r.size_pos
  simp only [numEdges, size_node]
  omega

/-- **Edge-count consistency** (implicit in MCB Definition 1.7.1):
    `T₁ ◁ T₂` has exactly one term per edge of `T₁`. -/
theorem card_insertSum_eq_numEdges :
    ∀ (T₁ T₂ : TraceTree α β), (T₁ ◁ T₂).card = numEdges T₁
  | .leaf _, _ => rfl
  | .trace _, _ => rfl
  | .node l r, T₂ => by
      simp only [insertSum_node, Multiset.card_add, Multiset.card_map,
                 numEdges_node]
      have ihl := card_insertSum_eq_numEdges l T₂
      have ihr := card_insertSum_eq_numEdges r T₂
      have h2 : ({(TraceTree.node (TraceTree.node l T₂) r),
                  (TraceTree.node l (TraceTree.node r T₂))}
                  : Multiset (TraceTree α β)).card = 2 := by
        rw [show ({(TraceTree.node (TraceTree.node l T₂) r),
                   (TraceTree.node l (TraceTree.node r T₂))}
                   : Multiset (TraceTree α β))
                = (TraceTree.node (TraceTree.node l T₂) r) ::ₘ
                  ({TraceTree.node l (TraceTree.node r T₂)}
                   : Multiset (TraceTree α β)) from rfl,
            Multiset.card_cons, Multiset.card_singleton]
      rw [h2, ihl, ihr]
      omega

/-! ## §4: ℤ-coefficient lift + Lie bracket (MCB eq. 1.7.9)

The pre-Lie identity (Phase 3) and Lie bracket (eq. 1.7.9) require
formal subtraction, which `Multiset` does not support. We lift to the
free abelian group `(TraceTree α β) →₀ ℤ` via mathlib's `toFinsupp`
composed with `ℕ → ℤ`. The bracket on basis pairs is
`[T₁, T₂]_R := T₁ ◁ T₂ - T₂ ◁ T₁`. Bilinear extension to all of
`(T →₀ ℤ)` and the Jacobi identity are deferred to Phase 3 (proof from
the right pre-Lie identity for `◁`). -/

section ZLift
variable [DecidableEq α] [DecidableEq β]

/-- Lift a multiset of trees to a `ℤ`-coefficient formal sum in the
    free abelian group `(TraceTree α β) →₀ ℤ`. Convolution of mathlib's
    `Multiset.toFinsupp : Multiset T ≃+ (T →₀ ℕ)` with the `ℕ → ℤ`
    embedding via `Finsupp.mapRange`. -/
noncomputable def Multiset.toFinsuppZ (s : Multiset (TraceTree α β)) :
    (TraceTree α β) →₀ ℤ :=
  (_root_.Multiset.toFinsupp s).mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero

@[simp] theorem Multiset.toFinsuppZ_zero :
    Multiset.toFinsuppZ (0 : Multiset (TraceTree α β)) = 0 := by
  simp only [Multiset.toFinsuppZ, _root_.map_zero, Finsupp.mapRange_zero]

@[simp] theorem Multiset.toFinsuppZ_add (s t : Multiset (TraceTree α β)) :
    Multiset.toFinsuppZ (s + t) = Multiset.toFinsuppZ s + Multiset.toFinsuppZ t := by
  simp only [Multiset.toFinsuppZ, _root_.map_add]
  exact Finsupp.mapRange_add (f := (Nat.cast : ℕ → ℤ)) Nat.cast_add _ _

/-- ℤ-coefficient lift of `insertSum`: `insertSumZ T₁ T₂` is the formal
    sum `Σ_{T ∈ insertSum T₁ T₂} 1·T` in `(TraceTree α β) →₀ ℤ`. The
    underlying additive content matches `insertSum`; the ℤ wrapper
    enables formal subtraction in the Lie bracket. -/
noncomputable def insertSumZ (T₁ T₂ : TraceTree α β) : (TraceTree α β) →₀ ℤ :=
  Multiset.toFinsuppZ (T₁ ◁ T₂)

@[simp] theorem insertSumZ_leaf (a : α) (T₂ : TraceTree α β) :
    insertSumZ (TraceTree.leaf a) T₂ = 0 := by
  simp only [insertSumZ, insertSum_leaf, Multiset.toFinsuppZ_zero]

@[simp] theorem insertSumZ_trace (b : β) (T₂ : TraceTree α β) :
    insertSumZ (TraceTree.trace b) T₂ = 0 := by
  simp only [insertSumZ, insertSum_trace, Multiset.toFinsuppZ_zero]

/-- **Right Lie bracket** (MCB eq. 1.7.9, book p. 78):
    `[T₁, T₂]_R := T₁ ◁ T₂ − T₂ ◁ T₁` in `(TraceTree α β) →₀ ℤ`.

    Antisymmetry (`[T, T]_R = 0`) is by definition. The Jacobi identity
    is deferred to Phase 3 (consequence of the right pre-Lie identity
    for `◁`, MCB Lemma 1.7.2). -/
noncomputable def lieBracketR (T₁ T₂ : TraceTree α β) :
    (TraceTree α β) →₀ ℤ :=
  insertSumZ T₁ T₂ - insertSumZ T₂ T₁

/-- Notation `⁅T₁, T₂⁆` for the right Lie bracket. The Unicode glyph
    matches mathlib's `LieBracket` notation (`Mathlib.Algebra.Lie.Basic`). -/
scoped notation "⁅" T₁ ", " T₂ "⁆" => lieBracketR T₁ T₂

/-- Antisymmetry of the right Lie bracket on identical arguments. -/
@[simp] theorem lieBracketR_self (T : TraceTree α β) :
    ⁅T, T⁆ = 0 := by
  simp only [lieBracketR, sub_self]

/-- Antisymmetry: `⁅T₂, T₁⁆ = -⁅T₁, T₂⁆`. -/
theorem lieBracketR_swap (T₁ T₂ : TraceTree α β) :
    ⁅T₂, T₁⁆ = -⁅T₁, T₂⁆ := by
  simp only [lieBracketR, neg_sub]

/-- When BOTH arguments have empty edge set (`.leaf` / `.trace`), the
    Lie bracket vanishes: each `insertSumZ` direction is zero. Note
    `⁅.leaf a, T⁆` for `T = .node ...` does NOT vanish in general —
    `T ◁ .leaf a` inserts the leaf at every edge of `T`, giving a
    non-empty formal sum. The MCB Lie algebra (Lemma 1.7.2) is
    therefore restricted to the subspace spanned by trees with
    non-empty edge set; the bracket on basis trees with `numEdges = 0`
    is well-defined but lives outside that subspace. -/
@[simp] theorem lieBracketR_leaf_leaf (a a' : α) :
    ⁅(TraceTree.leaf a : TraceTree α β), TraceTree.leaf a'⁆ = 0 := by
  simp only [lieBracketR, insertSumZ_leaf, sub_self]

@[simp] theorem lieBracketR_trace_trace (b b' : β) :
    ⁅(TraceTree.trace b : TraceTree α β), TraceTree.trace b'⁆ = 0 := by
  simp only [lieBracketR, insertSumZ_trace, sub_self]

@[simp] theorem lieBracketR_leaf_trace (a : α) (b : β) :
    ⁅(TraceTree.leaf a : TraceTree α β), TraceTree.trace b⁆ = 0 := by
  simp only [lieBracketR, insertSumZ_leaf, insertSumZ_trace, sub_self]

/-! ## §5: Bilinear extension to formal sums (Phase 3a substrate)

The pre-Lie identity (MCB eq. 1.7.2) is a relation among elements of
the Lie algebra, not basis pairs. We extend `insertSumZ : T → T → V`
(where `V = (T →₀ ℤ)`) to a bilinear map `insertSumLift : V → V → V`
via the standard finsupp-sum construction:

  `f ◇ g := Σ_{T₁ ∈ supp f} Σ_{T₂ ∈ supp g} f(T₁) · g(T₂) · (T₁ ◁ T₂)`

Distributivity in each argument is the standard `Finsupp.sum_add_index'`
of mathlib. We use a different infix glyph (◇) for the lifted operation
to keep `◁` available for basis-pair use. -/

/-- Bilinear extension of `insertSumZ` from basis pairs to formal sums
    in `(TraceTree α β) →₀ ℤ`. The pre-Lie identity (Phase 3b) is
    stated on this lifted operation. -/
noncomputable def insertSumLift (f g : (TraceTree α β) →₀ ℤ) :
    (TraceTree α β) →₀ ℤ :=
  f.sum (fun T₁ k₁ => g.sum (fun T₂ k₂ => (k₁ * k₂) • insertSumZ T₁ T₂))

/-- Notation `f ◇ g` for `insertSumLift f g`. The diamond glyph
    distinguishes the lifted (formal-sum) operation from the basis-pair
    `◁`. Equivalent to `◁` on basis pairs (lemma below). -/
scoped infixl:65 " ◇ " => insertSumLift

@[simp] theorem insertSumLift_zero_left (g : (TraceTree α β) →₀ ℤ) :
    (0 : (TraceTree α β) →₀ ℤ) ◇ g = 0 := by
  simp only [insertSumLift, Finsupp.sum_zero_index]

@[simp] theorem insertSumLift_zero_right (f : (TraceTree α β) →₀ ℤ) :
    f ◇ (0 : (TraceTree α β) →₀ ℤ) = 0 := by
  simp only [insertSumLift, Finsupp.sum_zero_index, Finsupp.sum_fun_zero]

/-! ## §6: Right pre-Lie identity (Phase 3b — proof deferred)

MCB Lemma 1.7.2 (book p. 77) on pre-Lie identity (eq. 1.7.2 specialized
to `◇`):

  `(f ◇ g) ◇ h - f ◇ (g ◇ h) = (f ◇ h) ◇ g - f ◇ (h ◇ g)`

for all `f, g, h ∈ (TraceTree α β) →₀ ℤ` supported on trees with
non-empty edge set.

**Proof outline (book p. 77-78)**: Reduce to basis triples by trilinearity.
On basis triples `T₁, T₂, T₃`, expand `(T₁ ◁ T₂) ◇ T₃` as a sum over
edges of the inserted tree, classified by location:

  1. Edges of `T₂` (the inserted subtree): equal to `T₁ ◁ (T₂ ◁ T₃)`,
     cancelling on both sides.
  2. Edges of `T₁` other than the insertion edge `e`: appear identically
     in `(T₁ ◁ T₃) ◇ T₂` (insertions at different edges commute).
  3. The three "new" edges produced by the splitting (`e₁`, `e₂` from
     splitting `e`, plus `e'` from the new vertex to root of `T₂`):
     these match the corresponding cases in `(T₁ ◁ T₃) ◇ T₂` by the
     diagram in book Figure 1.6 (p. 79).

The combinatorial bookkeeping requires defining the per-edge insertion
`insertAt T₁ e T₂` and the explicit edge enumeration of `T₁ ◁_e T₂`, then
matching cases 2 and 3 across the symmetric expressions. -/

/-- **Right pre-Lie identity** (MCB Lemma 1.7.2, eq. 1.7.2 specialized
    to `◇`). Implies the Jacobi identity for `⁅·,·⁆` lifted bilinearly
    to `(TraceTree α β) →₀ ℤ`.

    PROOF SORRY (Phase 3b): the proof requires explicit per-edge
    insertion machinery and case-by-case bookkeeping of insertion
    locations as outlined in the §6 docstring. Unblocking this needs:

    - `insertAt T₁ e T₂` indexed by an `Edge T₁` type
    - decomposition `insertSum T₁ T₂ = Σ_{e : Edge T₁} insertAt T₁ e T₂`
    - edge enumeration of `insertAt T₁ e T₂`: `Edge T₁ \\ {e} ⊔
      Edge T₂ ⊔ {e₁, e₂, e'}` where the last three are the "new" edges
      created by the split (Figure 1.6, book p. 79)
    - proof that insertions at different edges commute. -/
theorem insertSumLift_right_preLie (f g h : (TraceTree α β) →₀ ℤ) :
    f ◇ g ◇ h - f ◇ (g ◇ h) = f ◇ h ◇ g - f ◇ (h ◇ g) := by
  sorry

end ZLift

/-! ## §7: Per-edge insertion machinery (Phase 3b substrate)

The pre-Lie identity proof requires identifying *which* edge is being
inserted at, not just enumerating insertions. We add:

- `Edge T` — indexed inductive type, one constructor per edge of `T`
- `insertAt e T₂` — insertion at the specific edge `e : Edge T`
- `edges T` — list-enumeration of all edges of `T`
- `insertSum_eq_ofList_map_insertAt` — the decomposition relating
  `insertSum` (multiset-level) to `(edges T).map (insertAt · T₂)`

This substrate is what unblocks Phase 3b's case-by-case argument. -/

/-- An edge of a `TraceTree`, indexed by the tree itself. The four
    constructors mirror the four ways an edge can sit in a `.node l r`:
    one of the two immediate root edges, or recursively in `l` / `r`. -/
inductive Edge : TraceTree α β → Type max u v
  | rootL (l r : TraceTree α β) : Edge (.node l r)
  | rootR (l r : TraceTree α β) : Edge (.node l r)
  | inL (l r : TraceTree α β) (e : Edge l) : Edge (.node l r)
  | inR (l r : TraceTree α β) (e : Edge r) : Edge (.node l r)

/-- Insert `T₂` at the specific edge `e` of some tree. Per-edge
    sibling of `insertSum`: `insertSum T₁ T₂` is the multiset of all
    `insertAt e T₂` for `e : Edge T₁`. -/
def insertAt : ∀ {T : TraceTree α β}, Edge T → TraceTree α β → TraceTree α β
  | _, .rootL l r,   T₂ => .node (.node l T₂) r
  | _, .rootR l r,   T₂ => .node l (.node r T₂)
  | _, .inL l r e,   T₂ => .node (insertAt e T₂) r
  | _, .inR l r e,   T₂ => .node l (insertAt e T₂)

@[simp] theorem insertAt_rootL (l r T₂ : TraceTree α β) :
    insertAt (.rootL l r) T₂ = .node (.node l T₂) r := rfl

@[simp] theorem insertAt_rootR (l r T₂ : TraceTree α β) :
    insertAt (.rootR l r) T₂ = .node l (.node r T₂) := rfl

@[simp] theorem insertAt_inL (l r T₂ : TraceTree α β) (e : Edge l) :
    insertAt (.inL l r e) T₂ = .node (insertAt e T₂) r := rfl

@[simp] theorem insertAt_inR (l r T₂ : TraceTree α β) (e : Edge r) :
    insertAt (.inR l r e) T₂ = .node l (insertAt e T₂) := rfl

/-- Enumeration of all edges of `T` as a `List`. Order: the two
    immediate root edges first (rootL, rootR), then the recursive edges
    of `l` (lifted via `.inL`), then `r` (via `.inR`). The total length
    equals `numEdges T` (proved below). -/
def edges : (T : TraceTree α β) → List (Edge T)
  | .leaf _ => []
  | .trace _ => []
  | .node l r =>
      .rootL l r :: .rootR l r ::
        ((edges l).map (.inL l r) ++ (edges r).map (.inR l r))

@[simp] theorem edges_leaf (a : α) :
    edges (TraceTree.leaf a : TraceTree α β) = [] := rfl

@[simp] theorem edges_trace (b : β) :
    edges (TraceTree.trace b : TraceTree α β) = [] := rfl

@[simp] theorem edges_node (l r : TraceTree α β) :
    edges (TraceTree.node l r)
      = .rootL l r :: .rootR l r ::
          ((edges l).map (.inL l r) ++ (edges r).map (.inR l r)) := rfl

/-- Edge count: `(edges T).length = numEdges T`. -/
theorem length_edges_eq_numEdges :
    ∀ (T : TraceTree α β), (edges T).length = numEdges T
  | .leaf _ => rfl
  | .trace _ => rfl
  | .node l r => by
      have ihl := length_edges_eq_numEdges l
      have ihr := length_edges_eq_numEdges r
      simp only [edges_node, List.length_cons, List.length_append,
                 List.length_map, numEdges_node]
      omega

/-! ## §8: Decomposition of `insertSum` via `insertAt` -/

/-- **Decomposition lemma**: `insertSum T₁ T₂` equals the multiset of
    `insertAt e T₂` for `e` ranging over `edges T₁`. The bridge between
    the recursive (Multiset) and per-edge formulations of MCB
    Definition 1.7.1. -/
theorem insertSum_eq_ofList_map_insertAt :
    ∀ (T₁ T₂ : TraceTree α β),
      T₁ ◁ T₂
        = Multiset.ofList ((edges T₁).map (fun e => insertAt e T₂))
  | .leaf _,   _ => rfl
  | .trace _,  _ => rfl
  | .node l r, T₂ => by
      have ihl := insertSum_eq_ofList_map_insertAt l T₂
      have ihr := insertSum_eq_ofList_map_insertAt r T₂
      rw [insertSum_node, ihl, ihr]
      simp only [edges_node, List.map_cons, List.map_append, List.map_map,
                 Function.comp_def, insertAt_rootL, insertAt_rootR,
                 insertAt_inL, insertAt_inR, Multiset.map_coe]
      -- {a, b} = a ::ₘ {b}, which combined with `↑xs` yields `a ::ₘ b ::ₘ ↑xs`.
      -- Final shape: `↑(a :: b :: (xs ++ ys))` matches via Multiset.coe_add.
      rw [show ({(TraceTree.node (TraceTree.node l T₂) r),
                  (TraceTree.node l (TraceTree.node r T₂))}
                  : Multiset (TraceTree α β))
              = (↑[TraceTree.node (TraceTree.node l T₂) r,
                  TraceTree.node l (TraceTree.node r T₂)]
                : Multiset (TraceTree α β)) from rfl,
          Multiset.coe_add, Multiset.coe_add]
      rfl

/-- **Edge-count consistency restated** via `length_edges_eq_numEdges`
    and `insertSum_eq_ofList_map_insertAt`. The two versions of edge
    counting agree. -/
theorem card_insertSum_via_edges (T₁ T₂ : TraceTree α β) :
    (T₁ ◁ T₂).card = (edges T₁).length := by
  rw [insertSum_eq_ofList_map_insertAt, Multiset.coe_card, List.length_map]

/-- Size accounting for `insertAt`: a single insertion adds one
    new vertex (the splitting node `v`) plus all of `T₂`'s vertices
    to the parent tree. So `(insertAt e T₂).size = T.size + T₂.size + 1`. -/
theorem size_insertAt :
    ∀ {T : TraceTree α β} (e : Edge T) (T₂ : TraceTree α β),
      (insertAt e T₂).size = T.size + T₂.size + 1
  | _, .rootL l r,   T₂ => by
      simp only [insertAt_rootL, size_node]; omega
  | _, .rootR l r,   T₂ => by
      simp only [insertAt_rootR, size_node]; omega
  | _, .inL l r e,   T₂ => by
      have ih := size_insertAt e T₂
      simp only [insertAt_inL, size_node]; omega
  | _, .inR l r e,   T₂ => by
      have ih := size_insertAt e T₂
      simp only [insertAt_inR, size_node]; omega

/-- Edge accounting for `insertAt`: insertion at one edge produces
    `numEdges T + numEdges T₂ + 2` total edges (the original count
    minus 1 for the split edge, plus 1 for `e₁`/`e₂` from the split
    parts each, plus 1 for `e'` to the inserted root, plus all
    edges of `T₂`). Direct corollary of `size_insertAt` via
    `numEdges = size − 1`. -/
theorem numEdges_insertAt {T : TraceTree α β} (e : Edge T)
    (T₂ : TraceTree α β) :
    numEdges (insertAt e T₂) = numEdges T + numEdges T₂ + 2 := by
  have h := size_insertAt e T₂
  have hT := T.size_pos
  have hT₂ := T₂.size_pos
  simp only [numEdges]; omega

/-! ## §9: Edge classification of `insertAt e T₂` (Phase 3b §9.1)

Every edge `f ∈ Edge (insertAt e T₂)` falls into exactly one of three
classes (MCB Figure 1.6, book p. 79):

  (a) **Lifted from T₂**: f corresponds to an edge of T₂, sitting as a
      subtree at the new internal vertex `v`. Constructor: `Edge.lift`.
  (b) **Preserved from T**: f corresponds to an edge of T other than e
      itself. (The cut edge e is consumed by the split.) Constructor:
      `Edge.preserve` (when supported by `f ≠ e`).
  (c) **One of three new edges** created by the insertion:
      `e₁` (root → v, the upper half of split e),
      `e₂` (v → original child, the lower half of split e),
      `e'` (v → root of T₂, the new edge to inserted subtree).

This section defines the three "lifted" / "new" constructors and proves
their structural laws. The "preserved" case is more delicate (needs
path bookkeeping) and is treated separately. -/

/-- **Lift an edge of T₂** into `Edge (insertAt e T₂)`. The lifted
    edge sits in the inserted subtree at vertex `v`. Recursive on the
    structure of `e`: for the two `.root*` constructors, T₂ becomes a
    direct child of `v`; for `.in*`, recurse to the child where the
    insertion happens. -/
def Edge.lift : ∀ {T : TraceTree α β} (e : Edge T) (T₂ : TraceTree α β),
    Edge T₂ → Edge (insertAt e T₂)
  | _, .rootL l r,   T₂, f => .inL (.node l T₂) r (.inR l T₂ f)
  | _, .rootR l r,   T₂, f => .inR l (.node r T₂) (.inR r T₂ f)
  | _, .inL l r e,   T₂, f => .inL (insertAt e T₂) r (Edge.lift e T₂ f)
  | _, .inR l r e,   T₂, f => .inR l (insertAt e T₂) (Edge.lift e T₂ f)

/-- **The "upper half" of the split edge** `e₁`: the new edge from the
    parent of e to the new vertex `v`. After splitting `e : Edge T`
    with insertion of T₂, the parent's slot now points to v (rather
    than directly to the child). -/
def Edge.newE1 : ∀ {T : TraceTree α β} (e : Edge T) (T₂ : TraceTree α β),
    Edge (insertAt e T₂)
  | _, .rootL l r,   T₂ => .rootL (.node l T₂) r
  | _, .rootR l r,   T₂ => .rootR l (.node r T₂)
  | _, .inL l r e,   T₂ => .inL (insertAt e T₂) r (Edge.newE1 e T₂)
  | _, .inR l r e,   T₂ => .inR l (insertAt e T₂) (Edge.newE1 e T₂)

/-- **The "lower half" of the split edge** `e₂`: the new edge from the
    new vertex `v` to the original child of the cut edge. -/
def Edge.newE2 : ∀ {T : TraceTree α β} (e : Edge T) (T₂ : TraceTree α β),
    Edge (insertAt e T₂)
  | _, .rootL l r,   T₂ => .inL (.node l T₂) r (.rootL l T₂)
  | _, .rootR l r,   T₂ => .inR l (.node r T₂) (.rootL r T₂)
  | _, .inL l r e,   T₂ => .inL (insertAt e T₂) r (Edge.newE2 e T₂)
  | _, .inR l r e,   T₂ => .inR l (insertAt e T₂) (Edge.newE2 e T₂)

/-- **The "edge to T₂"** `e'`: the new edge from the new vertex `v` to
    the root of the inserted subtree T₂. -/
def Edge.newEprime : ∀ {T : TraceTree α β} (e : Edge T) (T₂ : TraceTree α β),
    Edge (insertAt e T₂)
  | _, .rootL l r,   T₂ => .inL (.node l T₂) r (.rootR l T₂)
  | _, .rootR l r,   T₂ => .inR l (.node r T₂) (.rootR r T₂)
  | _, .inL l r e,   T₂ => .inL (insertAt e T₂) r (Edge.newEprime e T₂)
  | _, .inR l r e,   T₂ => .inR l (insertAt e T₂) (Edge.newEprime e T₂)

/-! ### Sanity: the 3 new edges are distinct -/

/-- The 3 new edges differ pairwise: `e₁ ≠ e₂`, `e₁ ≠ e'`, `e₂ ≠ e'`.
    Used in the Phase 3b pre-Lie proof to keep case analyses distinct.
    Proved by structural induction on `e`. -/
theorem newE1_ne_newE2 :
    ∀ {T : TraceTree α β} (e : Edge T) (T₂ : TraceTree α β),
      Edge.newE1 e T₂ ≠ Edge.newE2 e T₂
  | _, .rootL l r,   _, h => by
      simp only [Edge.newE1, Edge.newE2] at h
      cases h
  | _, .rootR l r,   _, h => by
      simp only [Edge.newE1, Edge.newE2] at h
      cases h
  | _, .inL l r e,   T₂, h => by
      simp only [Edge.newE1, Edge.newE2] at h
      injection h with _ _ h₃
      exact newE1_ne_newE2 e T₂ h₃
  | _, .inR l r e,   T₂, h => by
      simp only [Edge.newE1, Edge.newE2] at h
      injection h with _ _ h₃
      exact newE1_ne_newE2 e T₂ h₃

/-! ### Phase 3b §9.1 status

Defined: `Edge.lift`, `Edge.newE1`, `Edge.newE2`, `Edge.newEprime`,
plus pairwise distinctness for the new edges (one direction shown;
the other two are similar and can be added when needed by a consumer).

Pending for §9.1 completion:
- `Edge.preserve : (e : Edge T) → (f : Edge T) → f ≠ e → Edge (insertAt e T₂)`
  (carry an edge of T other than e through the insertion).
- `edges_insertAt_eq_classification`: the multiset/list-level
  decomposition `edges (insertAt e T₂) = (preserved-edges) ++ (lifted-edges)
  ++ [e₁, e₂, e']`.

§9.2 (commutativity at different edges) and §9.3 (the actual pre-Lie
identity discharge) are the remaining Phase 3b work. -/

/-! ## Phase 1-3a + 3b-substrate conclusion + roadmap

Phases 1-3a establish the substrate operation `◁` (Phase 1),
ℤ-coefficient Lie bracket on basis pairs (Phase 2), and the bilinear
extension `◇` with the right pre-Lie identity stated as a sorry-marked
theorem (Phase 3a). Phase 3b is in flight: substrate (`Edge`,
`insertAt`, `edges`, decomposition) landed in §7-§8; the pre-Lie proof
itself remains as the §9 roadmap. Subsequent phases:

- **Phase 3b**: Prove `insertSumLift_right_preLie` via §9.1-§9.3.
- **Phase 3c**: Derive Jacobi for `⁅·,·⁆` lifted to `(T →₀ ℤ)` from
  pre-Lie + antisymmetry. Standard textbook argument.
- **Phase 4**: `H^∨` (dual Hopf algebra of workspaces) construction +
  identification of `(insertSum, ⁅·,·⁆)` with the primitive-element
  Lie algebra of `H^∨` (MCB Lemma 1.7.3, book p. 78).
- **Phase 5 (linguistic headline)**: every output of countercyclic
  insertion is reachable in the workspace via some composition of EM/IM
  (and possibly bounded Sideward) operations — formalising the MCB
  claim that countercyclic moves are dual-side reformulations rather
  than primitive new operations (book p. 80). -/

end TraceTree

end ConnesKreimer
