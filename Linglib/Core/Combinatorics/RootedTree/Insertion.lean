import Linglib.Core.Combinatorics.RootedTree.Decorated
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Logic.Equiv.Defs

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

    ⚠ **PROVABLY FALSE on planar `TraceTree`** ⚠

    A Lean-verified counterexample at
    `Linglib/Scratch/PreLiePlanarCheck.lean` shows
    `(T₁ ◁ T₂).bind (· ◁ T₃) ≠ (T₁ ◁ T₃).bind (· ◁ T₂)` for
    `T₁ = .node (.leaf 0) (.leaf 1)`, `T₂ = .leaf 2`, `T₃ = .leaf 3`.
    The discrepancy is the `newEprime` case at each MCB-edge: the new
    sibling pair `{T₂, T₃}` versus `{T₃, T₂}` is identical only under
    nonplanar identification, which planar `TraceTree` does not provide.

    MCB Definition 1.7.1 (book p. 77) explicitly says "two **nonplanar**
    binary rooted trees T₁, T₂ ∈ 𝔗_{SO₀}", and Definition 1.1.1 (book
    p. 22) identifies syntactic objects with the **commutative** free
    magma. The current planar carrier is at odds with §1.1 of the book.

    **Migration in progress (Phase 0 landed 2026-05-06):** the
    nonplanar carrier `FreeCommMagma α` is being introduced in
    `Linglib/Core/Algebra/Free/CommMagma.lean`. The pre-Lie identity
    on `(FreeCommMagma α) →₀ ℤ` *is* a strict equality (the (c)
    `newEprime` discrepancy collapses via `Quot.sound .swap`); see
    `docs/nonplanar-migration-plan.md` for the full migration plan.
    This `sorry` will be replaced by the nonplanar version (Phase 1b)
    rather than discharged on the current planar carrier.

    The §9.1–§9.4 substrate already landed (`Edge.classifyEquiv`,
    `edges_insertAt_eq_classification`, `insertAt_commute_diff`,
    `insertAt_lift_eq_nested`) is reusable on the nonplanar carrier;
    the migration ports rather than re-derives. -/
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

/-! ## §9: Edge classification of `insertAt e T₂` (Phase 3b)

Every edge `f ∈ Edge (insertAt e T₂)` falls into exactly one of 5
classes (cf. MCB Figure 1.6 — page citation deliberately omitted
pending verification against the book):

  (a) **Preserved from T**: f corresponds to an edge of T other than e
      itself. Constructor: `Edge.preserveOf` (option-free, takes
      `h : f ≠ e`); `Edge.preserveAux` is the option-valued sibling.
  (b) **Lifted from T₂**: f corresponds to an edge of T₂, sitting as a
      subtree at the new internal vertex `v`. Constructor: `Edge.lift`.
  (c) **`e₁`** (root → v, the upper half of split e). Constructor:
      `Edge.newE1`.
  (d) **`e₂`** (v → original child, the lower half of split e).
      Constructor: `Edge.newE2`.
  (e) **`e'`** (v → root of T₂, the new edge to inserted subtree).
      Constructor: `Edge.newEprime`.

The classification is exhibited as a bijection
`Edge (insertAt e T₂) ≃ Edge.Classify e T₂` (`Edge.classifyEquiv`,
§9.1 headline). The 3 pairwise distinctness lemmas
(`newE1_ne_newE2`, `newE1_ne_newEprime`, `newE2_ne_newEprime`) and the
multiset decomposition (§9.2 `edges_insertAt_eq_classification`)
follow as corollaries.

Layout: substrate constructors (`lift`, `newE1`, `newE2`, `newEprime`,
`preserveAux`, `preserveOf`) → equivalence (`Classify`, `fromClassify`,
`toClassify`, round-trip lemmas, `classifyEquiv`) → corollaries
(distinctness, multiset decomposition). -/

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

/-! ### Edge.preserveAux: carry a non-cut edge through the insertion

The hardest §9.1 piece: given `e f : Edge T`, we want to produce the
"corresponding" edge of `insertAt e T₂` whenever `f ≠ e`. We package
this as an `Option`-valued function `preserveAux` that returns `none`
exactly when `f = e`.

Implementation: 16-case pattern match on `(e, f)` constructor-pairs.
Each case maps `f`'s position in `T` to its position in `insertAt e T₂`
based on whether `e` is "before", "after", or "alongside" `f`. -/

/-- `preserveAux e f T₂` returns `some` of the edge of `insertAt e T₂`
    corresponding to `f`, when `f ≠ e`; `none` when `f = e`. The
    16-case pattern handles all combinations of root/in-l/in-r for
    both `e` and `f`. -/
def Edge.preserveAux : ∀ {T : TraceTree α β} (e f : Edge T)
      (T₂ : TraceTree α β), Option (Edge (insertAt e T₂))
  -- e = rootL: insertAt = .node (.node l T₂) r
  | _, .rootL _ _,   .rootL _ _,   _  => none
  | _, .rootL l _,   .rootR _ r,   T₂ => some (.rootR (.node l T₂) r)
  | _, .rootL l _,   .inL _ r f',  T₂ => some (.inL (.node l T₂) r (.inL l T₂ f'))
  | _, .rootL l _,   .inR _ r f',  T₂ => some (.inR (.node l T₂) r f')
  -- e = rootR: insertAt = .node l (.node r T₂)
  | _, .rootR l _,   .rootL _ r,   T₂ => some (.rootL l (.node r T₂))
  | _, .rootR _ _,   .rootR _ _,   _  => none
  | _, .rootR _ r,   .inL l _ f',  T₂ => some (.inL l (.node r T₂) f')
  | _, .rootR _ r,   .inR l _ f',  T₂ => some (.inR l (.node r T₂) (.inL r T₂ f'))
  -- e = inL e': insertAt = .node (insertAt e' T₂) r
  | _, .inL _ _ e',  .rootL _ r,   T₂ => some (.rootL (insertAt e' T₂) r)
  | _, .inL _ _ e',  .rootR _ r,   T₂ => some (.rootR (insertAt e' T₂) r)
  | _, .inL _ r e',  .inL _ _ f',  T₂ =>
      (Edge.preserveAux e' f' T₂).map (.inL (insertAt e' T₂) r)
  | _, .inL _ _ e',  .inR _ r f',  T₂ => some (.inR (insertAt e' T₂) r f')
  -- e = inR e': insertAt = .node l (insertAt e' T₂)
  | _, .inR _ _ e',  .rootL l _,   T₂ => some (.rootL l (insertAt e' T₂))
  | _, .inR _ _ e',  .rootR l _,   T₂ => some (.rootR l (insertAt e' T₂))
  | _, .inR _ _ e',  .inL l _ f',  T₂ => some (.inL l (insertAt e' T₂) f')
  | _, .inR l _ e',  .inR _ _ f',  T₂ =>
      (Edge.preserveAux e' f' T₂).map (.inR l (insertAt e' T₂))

/-! ### Edge.preserveOf: option-free non-cut edge carry

The Option-valued `preserveAux` becomes Option-free given a hypothesis
`f ≠ e`: the only `none` cases are the diagonal pairs `(rootL,rootL)`,
`(rootR,rootR)`, `(inL e', inL e')`, `(inR e', inR e')` — and on the
diagonal the hypothesis itself rules them out (via `absurd rfl h` for
the constructor diagonal, and a recursive disjointness lemma for the
nested case).

`preserveOf` is the constructor used by the `Equiv` below to produce
preserved edges directly, without unwrapping `Option`. -/

/-- Option-free `preserveAux`: produce the edge of `insertAt e T₂`
    corresponding to `f`, assuming `f ≠ e`. Same 16-case pattern as
    `preserveAux`; the diagonal cases use `absurd rfl h` to dispatch
    the impossibility. -/
def Edge.preserveOf : ∀ {T : TraceTree α β} (e f : Edge T) (_h : f ≠ e)
      (T₂ : TraceTree α β), Edge (insertAt e T₂)
  | _, .rootL _ _,   .rootL _ _,   h, _  => absurd rfl h
  | _, .rootL l _,   .rootR _ r,   _, T₂ => .rootR (.node l T₂) r
  | _, .rootL l _,   .inL _ r f',  _, T₂ => .inL (.node l T₂) r (.inL l T₂ f')
  | _, .rootL l _,   .inR _ r f',  _, T₂ => .inR (.node l T₂) r f'
  | _, .rootR l _,   .rootL _ r,   _, T₂ => .rootL l (.node r T₂)
  | _, .rootR _ _,   .rootR _ _,   h, _  => absurd rfl h
  | _, .rootR _ r,   .inL l _ f',  _, T₂ => .inL l (.node r T₂) f'
  | _, .rootR _ r,   .inR l _ f',  _, T₂ => .inR l (.node r T₂) (.inL r T₂ f')
  | _, .inL _ _ e',  .rootL _ r,   _, T₂ => .rootL (insertAt e' T₂) r
  | _, .inL _ _ e',  .rootR _ r,   _, T₂ => .rootR (insertAt e' T₂) r
  | _, .inL _ r e',  .inL _ _ f',  h, T₂ =>
      .inL (insertAt e' T₂) r
        (Edge.preserveOf e' f' (fun heq => h (by rw [heq])) T₂)
  | _, .inL _ _ e',  .inR _ r f',  _, T₂ => .inR (insertAt e' T₂) r f'
  | _, .inR _ _ e',  .rootL l _,   _, T₂ => .rootL l (insertAt e' T₂)
  | _, .inR _ _ e',  .rootR l _,   _, T₂ => .rootR l (insertAt e' T₂)
  | _, .inR _ _ e',  .inL l _ f',  _, T₂ => .inL l (insertAt e' T₂) f'
  | _, .inR l _ e',  .inR _ _ f',  h, T₂ =>
      .inR l (insertAt e' T₂)
        (Edge.preserveOf e' f' (fun heq => h (by rw [heq])) T₂)

/-- `preserveAux` returns `none` exactly on the diagonal `(e, e)`. -/
theorem Edge.preserveAux_self : ∀ {T : TraceTree α β} (e : Edge T)
      (T₂ : TraceTree α β),
    Edge.preserveAux e e T₂ = none
  | _, .rootL _ _, _ => rfl
  | _, .rootR _ _, _ => rfl
  | _, .inL _ _ e', T₂ => by
    show (Edge.preserveAux e' e' T₂).map _ = none
    rw [Edge.preserveAux_self e' T₂]; rfl
  | _, .inR _ _ e', T₂ => by
    show (Edge.preserveAux e' e' T₂).map _ = none
    rw [Edge.preserveAux_self e' T₂]; rfl

/-- Off the diagonal `(e, e)`, `preserveAux e f T₂` is `some (preserveOf e f h T₂)`. -/
theorem Edge.preserveAux_of_ne : ∀ {T : TraceTree α β} (e f : Edge T) (h : f ≠ e)
      (T₂ : TraceTree α β),
    Edge.preserveAux e f T₂ = some (Edge.preserveOf e f h T₂)
  | _, .rootL _ _, .rootL _ _, h, _ => absurd rfl h
  | _, .rootL _ _, .rootR _ _, _, _ => rfl
  | _, .rootL _ _, .inL _ _ _, _, _ => rfl
  | _, .rootL _ _, .inR _ _ _, _, _ => rfl
  | _, .rootR _ _, .rootL _ _, _, _ => rfl
  | _, .rootR _ _, .rootR _ _, h, _ => absurd rfl h
  | _, .rootR _ _, .inL _ _ _, _, _ => rfl
  | _, .rootR _ _, .inR _ _ _, _, _ => rfl
  | _, .inL _ _ _, .rootL _ _, _, _ => rfl
  | _, .inL _ _ _, .rootR _ _, _, _ => rfl
  | _, .inL _ _ e', .inL _ _ f', h, T₂ => by
    show (Edge.preserveAux e' f' T₂).map _
        = some (Edge.inL _ _ (Edge.preserveOf e' f' _ T₂))
    rw [Edge.preserveAux_of_ne e' f' (fun heq => h (by rw [heq])) T₂]; rfl
  | _, .inL _ _ _, .inR _ _ _, _, _ => rfl
  | _, .inR _ _ _, .rootL _ _, _, _ => rfl
  | _, .inR _ _ _, .rootR _ _, _, _ => rfl
  | _, .inR _ _ _, .inL _ _ _, _, _ => rfl
  | _, .inR _ _ e', .inR _ _ f', h, T₂ => by
    show (Edge.preserveAux e' f' T₂).map _
        = some (Edge.inR _ _ (Edge.preserveOf e' f' _ T₂))
    rw [Edge.preserveAux_of_ne e' f' (fun heq => h (by rw [heq])) T₂]; rfl

/-! ### §9.1 headline: the classification equivalence

The 5 classes from `preserveOf` / `lift` / `newE1` / `newE2` /
`newEprime` together form a *bijection* with `Edge (insertAt e T₂)`:
every edge of `insertAt e T₂` is *exactly one* of the 5 forms. The
inductive `Edge.Classify e T₂` packages the disjoint union, with
`Edge.classifyEquiv` exhibiting the bijection.

This Equiv is the structural unit of §9.1: pairwise distinctness of the
3 new edges, disjointness of preserved/lifted/new, and the multiset
decomposition (`edges_insertAt_eq_classification`, §9.2 below) all
follow from it as corollaries. -/

/-- Disjoint union of the 5 edge classes for `insertAt e T₂`:
    preserved edges of `T` (other than `e`), lifted edges of `T₂`, and
    the 3 new split edges `e₁`, `e₂`, `e'`. The Equiv `classifyEquiv`
    below exhibits the bijection with `Edge (insertAt e T₂)`. -/
inductive Edge.Classify : ∀ {T : TraceTree α β}, Edge T → TraceTree α β →
    Type max u v
  | preserved {T : TraceTree α β} {e : Edge T} {T₂ : TraceTree α β}
      (f : Edge T) (h : f ≠ e) : Edge.Classify e T₂
  | lifted {T : TraceTree α β} {e : Edge T} {T₂ : TraceTree α β}
      (g : Edge T₂) : Edge.Classify e T₂
  | newE1 {T : TraceTree α β} {e : Edge T} {T₂ : TraceTree α β} :
      Edge.Classify e T₂
  | newE2 {T : TraceTree α β} {e : Edge T} {T₂ : TraceTree α β} :
      Edge.Classify e T₂
  | newEprime {T : TraceTree α β} {e : Edge T} {T₂ : TraceTree α β} :
      Edge.Classify e T₂

/-- Realize a classification as an actual edge of `insertAt e T₂`. -/
def Edge.fromClassify : ∀ {T : TraceTree α β} {e : Edge T} {T₂ : TraceTree α β},
    Edge.Classify e T₂ → Edge (insertAt e T₂)
  | _, _, _, .preserved f h => Edge.preserveOf _ f h _
  | _, e, T₂, .lifted g => Edge.lift e T₂ g
  | _, e, T₂, .newE1 => Edge.newE1 e T₂
  | _, e, T₂, .newE2 => Edge.newE2 e T₂
  | _, e, T₂, .newEprime => Edge.newEprime e T₂

/-- Classify an edge of `insertAt e T₂` into one of the 5 classes.
    Defined by structural recursion on `e` (4 cases), with nested case
    analysis on the input edge to identify which class it belongs to. -/
def Edge.toClassify : ∀ {T : TraceTree α β} (e : Edge T) (T₂ : TraceTree α β),
    Edge (insertAt e T₂) → Edge.Classify e T₂
  | _, .rootL l r, _, .rootL _ _ => .newE1
  | _, .rootL l r, _, .rootR _ _ =>
      .preserved (.rootR l r) (by intro h; cases h)
  | _, .rootL l r, _, .inL _ _ f' =>
      match f' with
      | .rootL _ _ => .newE2
      | .rootR _ _ => .newEprime
      | .inL _ _ f'' => .preserved (.inL l r f'') (by intro h; cases h)
      | .inR _ _ f'' => .lifted f''
  | _, .rootL l r, _, .inR _ _ f' =>
      .preserved (.inR l r f') (by intro h; cases h)
  | _, .rootR l r, _, .rootL _ _ =>
      .preserved (.rootL l r) (by intro h; cases h)
  | _, .rootR l r, _, .rootR _ _ => .newE1
  | _, .rootR l r, _, .inL _ _ f' =>
      .preserved (.inL l r f') (by intro h; cases h)
  | _, .rootR l r, _, .inR _ _ f' =>
      match f' with
      | .rootL _ _ => .newE2
      | .rootR _ _ => .newEprime
      | .inL _ _ f'' => .preserved (.inR l r f'') (by intro h; cases h)
      | .inR _ _ f'' => .lifted f''
  | _, .inL l r _e', _, .rootL _ _ =>
      .preserved (.rootL l r) (by intro h; cases h)
  | _, .inL l r _e', _, .rootR _ _ =>
      .preserved (.rootR l r) (by intro h; cases h)
  | _, .inL l r e', T₂, .inL _ _ f' =>
      match Edge.toClassify e' T₂ f' with
      | .preserved g hg =>
          .preserved (.inL l r g) (by intro h; cases h; exact hg rfl)
      | .lifted g => .lifted g
      | .newE1 => .newE1
      | .newE2 => .newE2
      | .newEprime => .newEprime
  | _, .inL l r _e', _, .inR _ _ f' =>
      .preserved (.inR l r f') (by intro h; cases h)
  | _, .inR l r _e', _, .rootL _ _ =>
      .preserved (.rootL l r) (by intro h; cases h)
  | _, .inR l r _e', _, .rootR _ _ =>
      .preserved (.rootR l r) (by intro h; cases h)
  | _, .inR l r _e', _, .inL _ _ f' =>
      .preserved (.inL l r f') (by intro h; cases h)
  | _, .inR l r e', T₂, .inR _ _ f' =>
      match Edge.toClassify e' T₂ f' with
      | .preserved g hg =>
          .preserved (.inR l r g) (by intro h; cases h; exact hg rfl)
      | .lifted g => .lifted g
      | .newE1 => .newE1
      | .newE2 => .newE2
      | .newEprime => .newEprime

/-- `fromClassify ∘ toClassify = id` on `Edge (insertAt e T₂)`. -/
theorem Edge.fromClassify_toClassify : ∀ {T : TraceTree α β} (e : Edge T)
      (T₂ : TraceTree α β) (f : Edge (insertAt e T₂)),
    Edge.fromClassify (Edge.toClassify e T₂ f) = f
  | _, .rootL l r, _, .rootL _ _ => rfl
  | _, .rootL l r, _, .rootR _ _ => rfl
  | _, .rootL l r, _, .inL _ _ (.rootL _ _) => rfl
  | _, .rootL l r, _, .inL _ _ (.rootR _ _) => rfl
  | _, .rootL l r, _, .inL _ _ (.inL _ _ _) => rfl
  | _, .rootL l r, _, .inL _ _ (.inR _ _ _) => rfl
  | _, .rootL l r, _, .inR _ _ _ => rfl
  | _, .rootR l r, _, .rootL _ _ => rfl
  | _, .rootR l r, _, .rootR _ _ => rfl
  | _, .rootR l r, _, .inL _ _ _ => rfl
  | _, .rootR l r, _, .inR _ _ (.rootL _ _) => rfl
  | _, .rootR l r, _, .inR _ _ (.rootR _ _) => rfl
  | _, .rootR l r, _, .inR _ _ (.inL _ _ _) => rfl
  | _, .rootR l r, _, .inR _ _ (.inR _ _ _) => rfl
  | _, .inL l r _e', _, .rootL _ _ => rfl
  | _, .inL l r _e', _, .rootR _ _ => rfl
  | _, .inL l r e', T₂, .inL _ _ f' => by
    have ih := Edge.fromClassify_toClassify e' T₂ f'
    show Edge.fromClassify
        (match Edge.toClassify e' T₂ f' with
        | .preserved g hg => .preserved (.inL l r g) (by intro h; cases h; exact hg rfl)
        | .lifted g => .lifted g
        | .newE1 => .newE1
        | .newE2 => .newE2
        | .newEprime => .newEprime) = _
    cases hC : Edge.toClassify e' T₂ f' with
    | preserved g hg =>
      simp only [hC] at ih
      show Edge.inL (insertAt e' T₂) r (Edge.preserveOf e' g hg T₂) = _
      rw [show Edge.preserveOf e' g hg T₂ = f' from ih]
    | lifted g =>
      simp only [hC] at ih
      show Edge.inL (insertAt e' T₂) r (Edge.lift e' T₂ g) = _
      rw [show Edge.lift e' T₂ g = f' from ih]
    | newE1 =>
      simp only [hC] at ih
      show Edge.inL (insertAt e' T₂) r (Edge.newE1 e' T₂) = _
      rw [show Edge.newE1 e' T₂ = f' from ih]
    | newE2 =>
      simp only [hC] at ih
      show Edge.inL (insertAt e' T₂) r (Edge.newE2 e' T₂) = _
      rw [show Edge.newE2 e' T₂ = f' from ih]
    | newEprime =>
      simp only [hC] at ih
      show Edge.inL (insertAt e' T₂) r (Edge.newEprime e' T₂) = _
      rw [show Edge.newEprime e' T₂ = f' from ih]
  | _, .inL l r _e', _, .inR _ _ _ => rfl
  | _, .inR l r _e', _, .rootL _ _ => rfl
  | _, .inR l r _e', _, .rootR _ _ => rfl
  | _, .inR l r _e', _, .inL _ _ _ => rfl
  | _, .inR l r e', T₂, .inR _ _ f' => by
    have ih := Edge.fromClassify_toClassify e' T₂ f'
    show Edge.fromClassify
        (match Edge.toClassify e' T₂ f' with
        | .preserved g hg => .preserved (.inR l r g) (by intro h; cases h; exact hg rfl)
        | .lifted g => .lifted g
        | .newE1 => .newE1
        | .newE2 => .newE2
        | .newEprime => .newEprime) = _
    cases hC : Edge.toClassify e' T₂ f' with
    | preserved g hg =>
      simp only [hC] at ih
      show Edge.inR l (insertAt e' T₂) (Edge.preserveOf e' g hg T₂) = _
      rw [show Edge.preserveOf e' g hg T₂ = f' from ih]
    | lifted g =>
      simp only [hC] at ih
      show Edge.inR l (insertAt e' T₂) (Edge.lift e' T₂ g) = _
      rw [show Edge.lift e' T₂ g = f' from ih]
    | newE1 =>
      simp only [hC] at ih
      show Edge.inR l (insertAt e' T₂) (Edge.newE1 e' T₂) = _
      rw [show Edge.newE1 e' T₂ = f' from ih]
    | newE2 =>
      simp only [hC] at ih
      show Edge.inR l (insertAt e' T₂) (Edge.newE2 e' T₂) = _
      rw [show Edge.newE2 e' T₂ = f' from ih]
    | newEprime =>
      simp only [hC] at ih
      show Edge.inR l (insertAt e' T₂) (Edge.newEprime e' T₂) = _
      rw [show Edge.newEprime e' T₂ = f' from ih]

/-! ### Round-trip lemmas: how `toClassify` behaves on each constructor

Each of the 5 `fromClassify`-image constructors round-trips back to its
class label under `toClassify`. These compose to give
`toClassify_fromClassify` (the right inverse of the Equiv). -/

theorem Edge.toClassify_lift : ∀ {T : TraceTree α β} (e : Edge T)
      (T₂ : TraceTree α β) (g : Edge T₂),
    Edge.toClassify e T₂ (Edge.lift e T₂ g) = .lifted g
  | _, .rootL _ _, _, _ => rfl
  | _, .rootR _ _, _, _ => rfl
  | _, .inL _ _ e', T₂, g => by
    show (match Edge.toClassify e' T₂ (Edge.lift e' T₂ g) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.lifted g
    rw [Edge.toClassify_lift e' T₂ g]
  | _, .inR _ _ e', T₂, g => by
    show (match Edge.toClassify e' T₂ (Edge.lift e' T₂ g) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.lifted g
    rw [Edge.toClassify_lift e' T₂ g]

theorem Edge.toClassify_newE1 : ∀ {T : TraceTree α β} (e : Edge T)
      (T₂ : TraceTree α β),
    Edge.toClassify e T₂ (Edge.newE1 e T₂) = .newE1
  | _, .rootL _ _, _ => rfl
  | _, .rootR _ _, _ => rfl
  | _, .inL _ _ e', T₂ => by
    show (match Edge.toClassify e' T₂ (Edge.newE1 e' T₂) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.newE1
    rw [Edge.toClassify_newE1 e' T₂]
  | _, .inR _ _ e', T₂ => by
    show (match Edge.toClassify e' T₂ (Edge.newE1 e' T₂) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.newE1
    rw [Edge.toClassify_newE1 e' T₂]

theorem Edge.toClassify_newE2 : ∀ {T : TraceTree α β} (e : Edge T)
      (T₂ : TraceTree α β),
    Edge.toClassify e T₂ (Edge.newE2 e T₂) = .newE2
  | _, .rootL _ _, _ => rfl
  | _, .rootR _ _, _ => rfl
  | _, .inL _ _ e', T₂ => by
    show (match Edge.toClassify e' T₂ (Edge.newE2 e' T₂) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.newE2
    rw [Edge.toClassify_newE2 e' T₂]
  | _, .inR _ _ e', T₂ => by
    show (match Edge.toClassify e' T₂ (Edge.newE2 e' T₂) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.newE2
    rw [Edge.toClassify_newE2 e' T₂]

theorem Edge.toClassify_newEprime : ∀ {T : TraceTree α β} (e : Edge T)
      (T₂ : TraceTree α β),
    Edge.toClassify e T₂ (Edge.newEprime e T₂) = .newEprime
  | _, .rootL _ _, _ => rfl
  | _, .rootR _ _, _ => rfl
  | _, .inL _ _ e', T₂ => by
    show (match Edge.toClassify e' T₂ (Edge.newEprime e' T₂) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.newEprime
    rw [Edge.toClassify_newEprime e' T₂]
  | _, .inR _ _ e', T₂ => by
    show (match Edge.toClassify e' T₂ (Edge.newEprime e' T₂) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.newEprime
    rw [Edge.toClassify_newEprime e' T₂]

theorem Edge.toClassify_preserveOf : ∀ {T : TraceTree α β} (e f : Edge T)
      (h : f ≠ e) (T₂ : TraceTree α β),
    Edge.toClassify e T₂ (Edge.preserveOf e f h T₂) = .preserved f h
  | _, .rootL _ _, .rootL _ _, h, _ => absurd rfl h
  | _, .rootL _ _, .rootR _ _, _, _ => rfl
  | _, .rootL _ _, .inL _ _ _, _, _ => rfl
  | _, .rootL _ _, .inR _ _ _, _, _ => rfl
  | _, .rootR _ _, .rootL _ _, _, _ => rfl
  | _, .rootR _ _, .rootR _ _, h, _ => absurd rfl h
  | _, .rootR _ _, .inL _ _ _, _, _ => rfl
  | _, .rootR _ _, .inR _ _ _, _, _ => rfl
  | _, .inL _ _ _, .rootL _ _, _, _ => rfl
  | _, .inL _ _ _, .rootR _ _, _, _ => rfl
  | _, .inL l r e', .inL _ _ f', h, T₂ => by
    show (match Edge.toClassify e' T₂ (Edge.preserveOf e' f' _ T₂) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.preserved (Edge.inL l r f') h
    rw [Edge.toClassify_preserveOf e' f' (fun heq => h (by rw [heq])) T₂]
  | _, .inL _ _ _, .inR _ _ _, _, _ => rfl
  | _, .inR _ _ _, .rootL _ _, _, _ => rfl
  | _, .inR _ _ _, .rootR _ _, _, _ => rfl
  | _, .inR _ _ _, .inL _ _ _, _, _ => rfl
  | _, .inR l r e', .inR _ _ f', h, T₂ => by
    show (match Edge.toClassify e' T₂ (Edge.preserveOf e' f' _ T₂) with
          | Edge.Classify.preserved g hg => _ | Edge.Classify.lifted g => _
          | Edge.Classify.newE1 => _ | Edge.Classify.newE2 => _
          | Edge.Classify.newEprime => _)
        = Edge.Classify.preserved (Edge.inR l r f') h
    rw [Edge.toClassify_preserveOf e' f' (fun heq => h (by rw [heq])) T₂]

/-- `toClassify ∘ fromClassify = id` on `Edge.Classify e T₂`. Composes
    the 5 round-trip lemmas above. -/
theorem Edge.toClassify_fromClassify {T : TraceTree α β} (e : Edge T)
    (T₂ : TraceTree α β) (c : Edge.Classify e T₂) :
    Edge.toClassify e T₂ (Edge.fromClassify c) = c := by
  cases c with
  | preserved f h => exact Edge.toClassify_preserveOf e f h T₂
  | lifted g => exact Edge.toClassify_lift e T₂ g
  | newE1 => exact Edge.toClassify_newE1 e T₂
  | newE2 => exact Edge.toClassify_newE2 e T₂
  | newEprime => exact Edge.toClassify_newEprime e T₂

/-- **§9.1 headline equivalence**: edges of `insertAt e T₂` correspond
    bijectively to classifications. From this the multiset decomposition
    (§9.2) and the 3 pairwise distinctness corollaries follow. -/
def Edge.classifyEquiv {T : TraceTree α β} (e : Edge T) (T₂ : TraceTree α β) :
    Edge (insertAt e T₂) ≃ Edge.Classify e T₂ where
  toFun := Edge.toClassify e T₂
  invFun := Edge.fromClassify
  left_inv f := Edge.fromClassify_toClassify e T₂ f
  right_inv c := Edge.toClassify_fromClassify e T₂ c

/-! ### Pairwise distinctness of the 3 new edges (Equiv corollaries)

Now that the classification is bijective, the 3 new edges are
*automatically* pairwise distinct: their `toClassify` images are
syntactically distinct constructors of `Edge.Classify`. -/

theorem Edge.newE1_ne_newE2 {T : TraceTree α β} (e : Edge T)
    (T₂ : TraceTree α β) :
    Edge.newE1 e T₂ ≠ Edge.newE2 e T₂ := by
  intro h
  have := congrArg (Edge.toClassify e T₂) h
  rw [Edge.toClassify_newE1, Edge.toClassify_newE2] at this
  cases this

theorem Edge.newE1_ne_newEprime {T : TraceTree α β} (e : Edge T)
    (T₂ : TraceTree α β) :
    Edge.newE1 e T₂ ≠ Edge.newEprime e T₂ := by
  intro h
  have := congrArg (Edge.toClassify e T₂) h
  rw [Edge.toClassify_newE1, Edge.toClassify_newEprime] at this
  cases this

theorem Edge.newE2_ne_newEprime {T : TraceTree α β} (e : Edge T)
    (T₂ : TraceTree α β) :
    Edge.newE2 e T₂ ≠ Edge.newEprime e T₂ := by
  intro h
  have := congrArg (Edge.toClassify e T₂) h
  rw [Edge.toClassify_newE2, Edge.toClassify_newEprime] at this
  cases this

/-! ### §9.2 multiset decomposition (corollary, currently independent proof)

The central decomposition: as a multiset, the edges of `insertAt e T₂`
split into three disjoint classes:

  (a) **Preserved edges** of `T` other than `e`, transported via
      `Edge.preserveAux`.
  (b) **Lifted edges** of `T₂`, transported via `Edge.lift`.
  (c) The **three new edges** `e₁`, `e₂`, `e'` (`Edge.newE1`,
      `Edge.newE2`, `Edge.newEprime`).

Proved by structural induction on `e` (4 cases, mirror-symmetric in
pairs). The `.rootL`/`.rootR` cases are direct (no IH); the `.inL`/`.inR`
cases use the IH together with `Multiset.map_add` to push the
decomposition through the recursive structure. -/

/-- **§9.2 multiset corollary** of `Edge.classifyEquiv`: edges of
    `insertAt e T₂` decompose, as a multiset, into preserved + lifted
    + the three new edges. The three new edges (`e₁`, `e₂`, `e'`) are
    the ones created by splitting `e`; the preserved edges are the
    edges of `T` other than `e` (transported via `preserveAux`); the
    lifted edges are the edges of `T₂` carried in by the insertion.

    Currently proved by direct structural induction; could be
    re-derived from `classifyEquiv` once a `Classify.universe`
    enumeration is in scope. -/
theorem edges_insertAt_eq_classification {T : TraceTree α β}
    (e : Edge T) (T₂ : TraceTree α β) :
    (↑(edges (insertAt e T₂)) : Multiset (Edge (insertAt e T₂)))
      = (↑((edges T).filterMap (fun f => Edge.preserveAux e f T₂))
          : Multiset (Edge (insertAt e T₂)))
        + (↑((edges T₂).map (Edge.lift e T₂))
            : Multiset (Edge (insertAt e T₂)))
        + (↑[Edge.newE1 e T₂, Edge.newE2 e T₂, Edge.newEprime e T₂]
            : Multiset (Edge (insertAt e T₂))) := by
  induction e with
  | rootL l r =>
    have hLHS : edges (insertAt (Edge.rootL l r) T₂)
        = Edge.rootL (.node l T₂) r :: Edge.rootR (.node l T₂) r ::
          Edge.inL (.node l T₂) r (.rootL l T₂) ::
          Edge.inL (.node l T₂) r (.rootR l T₂) ::
          ((edges l).map (fun f' => Edge.inL (.node l T₂) r (.inL l T₂ f')) ++
           (edges T₂).map (fun f' => Edge.inL (.node l T₂) r (.inR l T₂ f'))) ++
          (edges r).map (Edge.inR (.node l T₂) r) := by
      show edges (.node (.node l T₂) r) = _
      simp only [edges_node, List.map_cons, List.map_append, List.map_map,
                 Function.comp_def, List.cons_append]
    have hPres : (edges (.node l r)).filterMap
                   (fun f => Edge.preserveAux (Edge.rootL l r) f T₂)
        = Edge.rootR (.node l T₂) r ::
          ((edges l).map (fun f' => Edge.inL (.node l T₂) r (.inL l T₂ f')) ++
           (edges r).map (Edge.inR (.node l T₂) r)) := by
      show List.filterMap _
             (Edge.rootL l r :: Edge.rootR l r ::
               ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))) = _
      show (Edge.rootR (.node l T₂) r) ::
           (((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r)).filterMap
              (fun f => Edge.preserveAux (Edge.rootL l r) f T₂)) = _
      congr 1
      rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
      simp only [Function.comp_def]
      show List.filterMap (fun x => some (Edge.inL (.node l T₂) r (Edge.inL l T₂ x))) l.edges ++
           List.filterMap (fun x => some (Edge.inR (.node l T₂) r x)) r.edges = _
      rw [List.filterMap_eq_map', List.filterMap_eq_map']
    rw [hLHS, hPres]
    show (↑(Edge.rootL (.node l T₂) r :: Edge.rootR (.node l T₂) r ::
            Edge.inL (.node l T₂) r (.rootL l T₂) ::
            Edge.inL (.node l T₂) r (.rootR l T₂) ::
            ((edges l).map (fun f' => Edge.inL (.node l T₂) r (.inL l T₂ f')) ++
             (edges T₂).map (fun f' => Edge.inL (.node l T₂) r (.inR l T₂ f'))) ++
            (edges r).map (Edge.inR (.node l T₂) r))
          : Multiset (Edge (.node (.node l T₂) r))) =
         ↑(Edge.rootR (.node l T₂) r ::
           ((edges l).map (fun f' => Edge.inL (.node l T₂) r (.inL l T₂ f')) ++
            (edges r).map (Edge.inR (.node l T₂) r))) +
         ↑((edges T₂).map (fun f => Edge.inL (.node l T₂) r (.inR l T₂ f))) +
         (Edge.rootL (.node l T₂) r ::ₘ
          Edge.inL (.node l T₂) r (.rootL l T₂) ::ₘ
          Edge.inL (.node l T₂) r (.rootR l T₂) ::ₘ 0)
    simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add]
    ac_rfl
  | rootR l r =>
    have hLHS : edges (insertAt (Edge.rootR l r) T₂)
        = Edge.rootL l (.node r T₂) :: Edge.rootR l (.node r T₂) ::
          ((edges l).map (Edge.inL l (.node r T₂)) ++
           (Edge.inR l (.node r T₂) (.rootL r T₂) ::
            Edge.inR l (.node r T₂) (.rootR r T₂) ::
            ((edges r).map (fun f' => Edge.inR l (.node r T₂) (.inL r T₂ f')) ++
             (edges T₂).map (fun f' => Edge.inR l (.node r T₂) (.inR r T₂ f'))))) := by
      show edges (.node l (.node r T₂)) = _
      simp only [edges_node, List.map_cons, List.map_append, List.map_map,
                 Function.comp_def]
    have hPres : (edges (.node l r)).filterMap
                   (fun f => Edge.preserveAux (Edge.rootR l r) f T₂)
        = Edge.rootL l (.node r T₂) ::
          ((edges l).map (Edge.inL l (.node r T₂)) ++
           (edges r).map (fun f' => Edge.inR l (.node r T₂) (.inL r T₂ f'))) := by
      show List.filterMap _
             (Edge.rootL l r :: Edge.rootR l r ::
               ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))) = _
      show (Edge.rootL l (.node r T₂)) ::
           ((Edge.rootR l r ::
              ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))).filterMap
              (fun f => Edge.preserveAux (Edge.rootR l r) f T₂)) = _
      congr 1
      show (((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r)).filterMap
              (fun f => Edge.preserveAux (Edge.rootR l r) f T₂)) = _
      rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
      simp only [Function.comp_def]
      show List.filterMap (fun x => some (Edge.inL l (.node r T₂) x)) l.edges ++
           List.filterMap (fun x => some (Edge.inR l (.node r T₂) (.inL r T₂ x))) r.edges = _
      rw [List.filterMap_eq_map', List.filterMap_eq_map']
    rw [hLHS, hPres]
    show (↑(Edge.rootL l (.node r T₂) :: Edge.rootR l (.node r T₂) ::
            ((edges l).map (Edge.inL l (.node r T₂)) ++
             (Edge.inR l (.node r T₂) (.rootL r T₂) ::
              Edge.inR l (.node r T₂) (.rootR r T₂) ::
              ((edges r).map (fun f' => Edge.inR l (.node r T₂) (.inL r T₂ f')) ++
               (edges T₂).map (fun f' => Edge.inR l (.node r T₂) (.inR r T₂ f'))))))
          : Multiset (Edge (.node l (.node r T₂)))) =
         ↑(Edge.rootL l (.node r T₂) ::
           ((edges l).map (Edge.inL l (.node r T₂)) ++
            (edges r).map (fun f' => Edge.inR l (.node r T₂) (.inL r T₂ f')))) +
         ↑((edges T₂).map (fun f => Edge.inR l (.node r T₂) (.inR r T₂ f))) +
         (Edge.rootR l (.node r T₂) ::ₘ
          Edge.inR l (.node r T₂) (.rootL r T₂) ::ₘ
          Edge.inR l (.node r T₂) (.rootR r T₂) ::ₘ 0)
    simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add]
    ac_rfl
  | inL l r e' ih =>
    change (↑(edges (.node (insertAt e' T₂) r))
              : Multiset (Edge (.node (insertAt e' T₂) r))) = _
    rw [edges_node]
    have hPres : (edges (.node l r)).filterMap
                   (fun f => Edge.preserveAux (Edge.inL l r e') f T₂)
        = Edge.rootL (insertAt e' T₂) r :: Edge.rootR (insertAt e' T₂) r ::
          (((edges l).filterMap (fun f' => Edge.preserveAux e' f' T₂)).map
              (Edge.inL (insertAt e' T₂) r) ++
           (edges r).map (Edge.inR (insertAt e' T₂) r)) := by
      show List.filterMap _
             (Edge.rootL l r :: Edge.rootR l r ::
               ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))) = _
      show Edge.rootL (insertAt e' T₂) r ::
           ((Edge.rootR l r ::
              ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))).filterMap
              (fun f => Edge.preserveAux (Edge.inL l r e') f T₂)) = _
      congr 1
      show Edge.rootR (insertAt e' T₂) r ::
           (((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r)).filterMap
              (fun f => Edge.preserveAux (Edge.inL l r e') f T₂)) = _
      congr 1
      rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
      simp only [Function.comp_def]
      show List.filterMap (fun x => (Edge.preserveAux e' x T₂).map
                                       (Edge.inL (insertAt e' T₂) r)) l.edges ++
           List.filterMap (fun x => some (Edge.inR (insertAt e' T₂) r x)) r.edges = _
      rw [← List.map_filterMap, List.filterMap_eq_map']
    rw [hPres]
    rw [show (edges T₂).map (Edge.lift (Edge.inL l r e') T₂)
            = ((edges T₂).map (Edge.lift e' T₂)).map (Edge.inL (insertAt e' T₂) r) from by
            rw [List.map_map]; rfl]
    show (↑(Edge.rootL (insertAt e' T₂) r :: Edge.rootR (insertAt e' T₂) r ::
            ((edges (insertAt e' T₂)).map (Edge.inL (insertAt e' T₂) r) ++
             (edges r).map (Edge.inR (insertAt e' T₂) r)))
          : Multiset (Edge (.node (insertAt e' T₂) r))) =
          ↑(Edge.rootL (insertAt e' T₂) r :: Edge.rootR (insertAt e' T₂) r ::
            (((edges l).filterMap (fun f' => Edge.preserveAux e' f' T₂)).map
                (Edge.inL (insertAt e' T₂) r) ++
             (edges r).map (Edge.inR (insertAt e' T₂) r))) +
          ↑(((edges T₂).map (Edge.lift e' T₂)).map (Edge.inL (insertAt e' T₂) r)) +
          ↑[Edge.inL (insertAt e' T₂) r (Edge.newE1 e' T₂),
             Edge.inL (insertAt e' T₂) r (Edge.newE2 e' T₂),
             Edge.inL (insertAt e' T₂) r (Edge.newEprime e' T₂)]
    simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add,
               ← Multiset.map_coe]
    rw [ih, Multiset.map_add, Multiset.map_add]
    simp only [Multiset.map_coe, Multiset.map_singleton, Multiset.map_add,
               List.map_map, Function.comp_def,
               ← Multiset.cons_coe, ← Multiset.singleton_add]
    ac_rfl
  | inR l r e' ih =>
    change (↑(edges (.node l (insertAt e' T₂)))
              : Multiset (Edge (.node l (insertAt e' T₂)))) = _
    rw [edges_node]
    have hPres : (edges (.node l r)).filterMap
                   (fun f => Edge.preserveAux (Edge.inR l r e') f T₂)
        = Edge.rootL l (insertAt e' T₂) :: Edge.rootR l (insertAt e' T₂) ::
          ((edges l).map (Edge.inL l (insertAt e' T₂)) ++
           ((edges r).filterMap (fun f' => Edge.preserveAux e' f' T₂)).map
              (Edge.inR l (insertAt e' T₂))) := by
      show List.filterMap _
             (Edge.rootL l r :: Edge.rootR l r ::
               ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))) = _
      show Edge.rootL l (insertAt e' T₂) ::
           ((Edge.rootR l r ::
              ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))).filterMap
              (fun f => Edge.preserveAux (Edge.inR l r e') f T₂)) = _
      congr 1
      show Edge.rootR l (insertAt e' T₂) ::
           (((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r)).filterMap
              (fun f => Edge.preserveAux (Edge.inR l r e') f T₂)) = _
      congr 1
      rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
      simp only [Function.comp_def]
      show List.filterMap (fun x => some (Edge.inL l (insertAt e' T₂) x)) l.edges ++
           List.filterMap (fun x => (Edge.preserveAux e' x T₂).map
                                       (Edge.inR l (insertAt e' T₂))) r.edges = _
      rw [List.filterMap_eq_map', ← List.map_filterMap]
    rw [hPres]
    rw [show (edges T₂).map (Edge.lift (Edge.inR l r e') T₂)
            = ((edges T₂).map (Edge.lift e' T₂)).map (Edge.inR l (insertAt e' T₂)) from by
            rw [List.map_map]; rfl]
    show (↑(Edge.rootL l (insertAt e' T₂) :: Edge.rootR l (insertAt e' T₂) ::
            ((edges l).map (Edge.inL l (insertAt e' T₂)) ++
             (edges (insertAt e' T₂)).map (Edge.inR l (insertAt e' T₂))))
          : Multiset (Edge (.node l (insertAt e' T₂)))) =
          ↑(Edge.rootL l (insertAt e' T₂) :: Edge.rootR l (insertAt e' T₂) ::
            ((edges l).map (Edge.inL l (insertAt e' T₂)) ++
             ((edges r).filterMap (fun f' => Edge.preserveAux e' f' T₂)).map
                (Edge.inR l (insertAt e' T₂)))) +
          ↑(((edges T₂).map (Edge.lift e' T₂)).map (Edge.inR l (insertAt e' T₂))) +
          ↑[Edge.inR l (insertAt e' T₂) (Edge.newE1 e' T₂),
             Edge.inR l (insertAt e' T₂) (Edge.newE2 e' T₂),
             Edge.inR l (insertAt e' T₂) (Edge.newEprime e' T₂)]
    simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add,
               ← Multiset.map_coe]
    rw [ih, Multiset.map_add, Multiset.map_add]
    simp only [Multiset.map_coe, Multiset.map_singleton, Multiset.map_add,
               List.map_map, Function.comp_def,
               ← Multiset.cons_coe, ← Multiset.singleton_add]
    ac_rfl

/-! ### §9.3: insertions at different edges commute

For two distinct edges `e ≠ f` of `T`, inserting `T₂` at `e` and
then `T₃` at the corresponding edge in the result, equals inserting
`T₃` at `f` first and then `T₂` at the corresponding edge. The
"corresponding edge" is given by `Edge.preserveOf`.

This is the per-pair commutativity that the pre-Lie identity will
exploit on the preserved-edges class of the §9.1 decomposition.

Proof: 16 cases on `(e, f)`. Two are absurd (the diagonals via `h`).
12 are `rfl` (different constructors, or same constructor on
different branches). The 2 same-child recursive cases (`.inL/.inL`,
`.inR/.inR`) reduce to the IH on the smaller subtree. -/

/-- **§9.3 commutativity** (substrate for the pre-Lie cancellation):
    inserting `T₂` at `e` then `T₃` at the `f`-image, equals
    inserting `T₃` at `f` then `T₂` at the `e`-image. Both produce
    the same tree. -/
theorem insertAt_commute_diff : ∀ {T : TraceTree α β} (e f : Edge T)
      (h : f ≠ e) (T₂ T₃ : TraceTree α β),
    insertAt (Edge.preserveOf e f h T₂) T₃
      = insertAt (Edge.preserveOf f e h.symm T₃) T₂
  | _, .rootL _ _, .rootL _ _, h, _, _ => absurd rfl h
  | _, .rootR _ _, .rootR _ _, h, _, _ => absurd rfl h
  | _, .rootL _ _, .rootR _ _, _, _, _ => rfl
  | _, .rootL _ _, .inL _ _ _, _, _, _ => rfl
  | _, .rootL _ _, .inR _ _ _, _, _, _ => rfl
  | _, .rootR _ _, .rootL _ _, _, _, _ => rfl
  | _, .rootR _ _, .inL _ _ _, _, _, _ => rfl
  | _, .rootR _ _, .inR _ _ _, _, _, _ => rfl
  | _, .inL _ _ _, .rootL _ _, _, _, _ => rfl
  | _, .inL _ _ _, .rootR _ _, _, _, _ => rfl
  | _, .inR _ _ _, .rootL _ _, _, _, _ => rfl
  | _, .inR _ _ _, .rootR _ _, _, _, _ => rfl
  | _, .inL _ _ _, .inR _ _ _, _, _, _ => rfl
  | _, .inR _ _ _, .inL _ _ _, _, _, _ => rfl
  | _, .inL _ r e', .inL _ _ f', h, T₂, T₃ => by
    show TraceTree.node (insertAt (Edge.preserveOf e' f' _ T₂) T₃) r
        = TraceTree.node (insertAt (Edge.preserveOf f' e' _ T₃) T₂) r
    congr 1
    exact insertAt_commute_diff e' f' (fun heq => h (by rw [heq])) T₂ T₃
  | _, .inR l _ e', .inR _ _ f', h, T₂, T₃ => by
    show TraceTree.node l (insertAt (Edge.preserveOf e' f' _ T₂) T₃)
        = TraceTree.node l (insertAt (Edge.preserveOf f' e' _ T₃) T₂)
    congr 1
    exact insertAt_commute_diff e' f' (fun heq => h (by rw [heq])) T₂ T₃

/-! ### §9.4 substrate: insertion at a lifted edge factors through the inserted subtree

For the pre-Lie identity, the (b) "lifted" class of edges must be
identified with nested insertions: inserting `T₃` at a lifted edge
`Edge.lift e T₂ g` of `insertAt e T₂` is the same as first inserting
`T₃` at `g` in `T₂`, then inserting the resulting tree at `e` in `T`.

Proof: 4-case structural induction on `e`. The two `.root*` cases reduce
to one-step `insertAt` evaluations (the lifted edge is `.inR ... g` in
the new vertex, and `insertAt (.inR _ _ g) T₃` directly hits T₂'s
substructure). The two `.in*` cases push the IH through the recursive
parent-tree context. -/

/-- **Lifted-equals-nested** (substrate for the pre-Lie (b) cancellation):
    inserting `T₃` at a lifted edge of `T₂` (lifted into `insertAt e T₂`)
    factors as `insertAt e (insertAt g T₃)`.

    This identifies the (b) "lifted" class of `Edge (insertAt e T₂)` with
    nested insertions over `T₂ ◁ T₃`, summed against `e ∈ Edge T₁` —
    exactly matching `T₁ ◇ (T₂ ◁ T₃)`. -/
theorem insertAt_lift_eq_nested : ∀ {T : TraceTree α β} (e : Edge T)
      (T₂ T₃ : TraceTree α β) (g : Edge T₂),
    insertAt (Edge.lift e T₂ g) T₃ = insertAt e (insertAt g T₃)
  | _, .rootL _ _, _, _, _ => rfl
  | _, .rootR _ _, _, _, _ => rfl
  | _, .inL l r e', T₂, T₃, g => by
    show TraceTree.node (insertAt (Edge.lift e' T₂ g) T₃) r
        = TraceTree.node (insertAt e' (insertAt g T₃)) r
    rw [insertAt_lift_eq_nested e' T₂ T₃ g]
  | _, .inR l r e', T₂, T₃, g => by
    show TraceTree.node l (insertAt (Edge.lift e' T₂ g) T₃)
        = TraceTree.node l (insertAt e' (insertAt g T₃))
    rw [insertAt_lift_eq_nested e' T₂ T₃ g]

/-! ### Phase 3b §9.1-§9.4-substrate status + planar/nonplanar blocker

Substrate complete:
- §9.1: `Edge.classifyEquiv` (5-class bijection).
- §9.2: `edges_insertAt_eq_classification` (multiset decomposition).
- §9.3: `insertAt_commute_diff` (insertions at distinct edges commute).
- §9.4 substrate: `insertAt_lift_eq_nested` (the (b) cancellation
  identity).
- Pairwise distinctness corollaries (`newE1_ne_newE2`,
  `newE1_ne_newEprime`, `newE2_ne_newEprime`).

**Blocker for the §6 `sorry`: planar `TraceTree` vs. nonplanar identity.**

MCB Definition 1.7.1 (book p. 77) explicitly states the operation `T₁ ◁ T₂`
on **nonplanar** binary rooted trees `T₁, T₂ ∈ 𝔗_{SO₀}`, and Lemma 1.7.2
(book p. 77–78) is the right pre-Lie identity for that nonplanar setting.
MCB's proof of case (3) in the four-case decomposition (book p. 78) reads
"The terms obtained in case (3) match, as shown in Figure 1.6" (book p.
79) — that matching uses the nonplanar identification `{T₂, T₃} = {T₃, T₂}`
of the new sibling pair under the fresh vertex. (Lemma 1.10.1, book p.
92, makes the nonplanarity / commutativity of Merge explicit: `𝔗` is the
free **commutative** nonassociative magma; planar embeddings appear only
as multiplicities in §1.10.)

Our `TraceTree` is planar — `.node l r` distinguishes left from right
child — so the strict identity in `insertSumLift_right_preLie` is FALSE
on basis triples. Per-edge bookkeeping at the basis level:

  (a) **Preserved edges** cancel via §9.3.
  (b) **Lifted edges** cancel via `insertAt_lift_eq_nested`.
  (c) **New edges**: `newE1 ↔ newE2` swap matches under T₂ ↔ T₃, but
      `newEprime` produces `.node ... (.node T₂ T₃) ...` on the LHS and
      `.node ... (.node T₃ T₂) ...` on the RHS — distinct in planar
      trees, equivalent under MCB's nonplanar Merge.

A Lean-verified counterexample (`Linglib/Scratch/PreLiePlanarCheck.lean`):
`T₁ = .node (.leaf 0) (.leaf 1)`, `T₂ = .leaf 2`, `T₃ = .leaf 3`. Both
`T₂` and `T₃` have zero edges, so `T₁ ◇ (T₂ ◁ T₃) = T₁ ◇ (T₃ ◁ T₂) = 0`
and the pre-Lie identity reduces to `(T₁ ◁ T₂) ◇ T₃ = (T₁ ◁ T₃) ◇ T₂`
at the multiset level. `decide` confirms `(T₁ ◁ T₂).bind (· ◁ T₃) ≠
(T₁ ◁ T₃).bind (· ◁ T₂)`; the discrepancy is exactly the pair of
sibling-order-swapped trees produced by the `newEprime` case at each
edge of `T₁`.

**Path forward (architectural decision needed):**

  1. **Quotient `TraceTree`** by planar-rotation equivalence
     (`Quot (planarEquiv)` with `.node l r ~ .node r l`). Faithful to
     MCB but requires lifting the entire Hopf algebra / `mergeOp`
     substrate through the quotient; affects every downstream consumer.
  2. **Symmetrize `insertSum` only** (this file). Generate both
     `.node old T₂` and `.node T₂ old` planar orderings per MCB-edge.
     Localizes the change but doubles multiset cardinality, breaks
     `numEdges = size − 1`, and requires full §7–§9 substrate refactor.
  3. **Restate pre-Lie modulo a planar equivalence on `(T →₀ ℤ)`.**
     Define a `≈` relation that identifies coefficient sums differing
     only by `.node l r ↔ .node r l` rotations, and prove
     `f ◇ g ◇ h - f ◇ (g ◇ h) ≈ f ◇ h ◇ g - f ◇ (h ◇ g)`. Loses the
     direct equality but admits a clean proof in the current setting.
  4. **Add per-MCB-edge symmetrization at insertion time.** Define
     `T₁ ◁ T₂ := Σ_e (T₁ ◁_e^L T₂ + T₁ ◁_e^R T₂)` for both sibling
     orderings; only this file changes.

The §6 `sorry` is left in place pending this decision. The substrate
proved in §9.1–§9.4 (`classifyEquiv`, edge multiset decomposition,
per-pair commutativity, lifted-equals-nested) is independent of the
planar/nonplanar choice and is reusable under any of the four paths. -/

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
