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

/-! ## Phase 1-3a conclusion + roadmap

Phases 1-3a establish the substrate operation `◁` (Phase 1),
ℤ-coefficient Lie bracket on basis pairs (Phase 2), and the bilinear
extension `◇` with the right pre-Lie identity stated as a sorry-marked
theorem (Phase 3a). Phase 3b discharges the sorry with the combinatorial
case analysis from MCB book p. 77-78. Subsequent phases:

- **Phase 3b**: Prove `insertSumLift_right_preLie` via per-edge insertion
  enumeration and the 3-case argument (Figure 1.6, book p. 79).
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
