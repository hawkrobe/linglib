import Linglib.Core.Algebra.Free
import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Free pre-Lie algebra on FreeCommMagma (MCB §1.7, Chapoton-Livernet 2001)
@cite{marcolli-chomsky-berwick-2025} §1.7, book p. 77-80
@cite{chapoton-livernet-2001}

This file constructs the **free pre-Lie algebra** on `FreeCommMagma α`,
matching MCB Definition 1.7.1 (insertion sum) and Lemma 1.7.2 (right
pre-Lie identity) on the nonplanar carrier required by the book
(Lemma 1.10.1, p. 92: ℑ is the free nonassociative commutative magma).

## Mathlib grounding

- `FreeMagma α` (planar substrate) — `Mathlib.Algebra.Free`.
- `FreeCommMagma α` (nonplanar quotient) — `Linglib.Core.Algebra.Free`.
- `RightPreLieRing` / `RightPreLieAlgebra` typeclasses —
  `Mathlib.Algebra.NonAssoc.PreLie.Basic`.
- `LieRing` / `LieAlgebra` typeclasses — `Mathlib.Algebra.Lie.Basic`.

## Architecture

The planar `FreeMagma.insertSum` is internal scaffolding for the
descent proofs; the public API lives at the FreeCommMagma level via
`Free.lean`'s `lift₂`. Downstream consumers see only:
- `FreeCommMagma.insertSum : FCM α → FCM α → Multiset (FCM α)`.
- `FreeCommMagma.InsertionAlgebra α` (wrapped `(FCM α) →₀ ℤ` per the
  `MonoidAlgebra k G := G →₀ k` mathlib pattern, to give a custom Mul
  without conflicting with Finsupp's natural multiplication).
- `RightPreLieRing` / `RightPreLieAlgebra ℤ` instances on
  `InsertionAlgebra α` (MCB Lemma 1.7.2).
- `LieRing` / `LieAlgebra ℤ` instances on `InsertionAlgebra α`
  (derived from pre-Lie + antisymmetry, standard textbook argument).

## Layer split

- §1-§2: planar `FreeMagma.insertSum` + `numEdges`.
- §3: per-edge machinery `Edge`, `insertAt`, `edges`.
- §4: edge-count consistency and `insertSum_eq_ofList_map_insertAt`.
- §5-§8: edge classification, commutativity, lift identity (planar
  substrate, ported from the legacy `TraceTree`-based file).
- §9: descent proofs `insertSum_descent_left/right` (planar-swap
  invariance under `toFCM`).
- §10: native `FreeCommMagma.insertSum` via `lift₂` + simp lemmas.
- §11: bilinear extension to `(FCM α) →₀ ℤ`.
- §12: `InsertionAlgebra` wrapper + Mul + NonUnitalNonAssocRing.
- §13: strict pre-Lie identity (MCB Lemma 1.7.2).
- §14: `RightPreLieRing` + `RightPreLieAlgebra ℤ` instances.
- §15: `LieRing` + `LieAlgebra ℤ` instances (derived).

## Out of scope (kept on `TraceTree`)

Hopf coproduct, mergeOp, Phase Theory Δ^c_Φ, Minimal Search, NCL, IM
bridge, §1.13/§1.14 coherence, Phases 7a-7d — all commutativity-agnostic
and live unchanged on `TraceTree α β` in `Linglib/Core/Combinatorics/
RootedTree/Insertion.lean`. We migrate only what genuinely needs
nonplanar (§1.7), not the whole MCB substrate.
-/

namespace FreeMagma

universe u
variable {α : Type u}

/-! ## §1: The insertion sum (MCB Definition 1.7.1, eq. 1.7.8) on `FreeMagma α`

`insertSum T₁ T₂` is the multiset of trees obtained by inserting `T₂`
at each edge of `T₁`. Per-edge operation: split edge `e` (parent → child
subtree) with a new internal vertex `v`, attach `T₂` as a child of `v`,
reconnect the original subtree as the other child.

This is the planar (FreeMagma-level) version. The nonplanar
(FreeCommMagma) version lives in §10 below. -/

/-- `insertSum T₁ T₂` on `FreeMagma α`: multiset of trees obtained by
    inserting `T₂` at each edge of `T₁`. Recursion on `T₁`'s structure:

    - `of x`: no edges, empty multiset (additive identity).
    - `l * r`: two root edges (yield `(l * T₂) * r` and `l * (r * T₂)`)
      plus recursive insertions in `l` (with `r` carried) and in `r`
      (with `l` carried). -/
def insertSum : FreeMagma α → FreeMagma α → Multiset (FreeMagma α)
  | .of _, _ => 0
  | .mul l r, T₂ =>
    ({(l * T₂) * r, l * (r * T₂)} : Multiset (FreeMagma α))
      + (insertSum l T₂).map (· * r)
      + (insertSum r T₂).map (l * ·)

/-- Notation `T₁ ◁ T₂` for `insertSum T₁ T₂`. The right-triangular
    Unicode glyph matches MCB's typesetting (eq. 1.7.8 onward).
    Scoped to avoid clashing with mathlib's `LeftPreLieRing` notation. -/
scoped infixl:65 " ◁ " => insertSum

@[simp] theorem insertSum_of (a : α) (T₂ : FreeMagma α) :
    (FreeMagma.of a) ◁ T₂ = 0 := rfl

@[simp] theorem insertSum_mul (l r T₂ : FreeMagma α) :
    (l * r) ◁ T₂
      = ({(l * T₂) * r, l * (r * T₂)} : Multiset (FreeMagma α))
        + (l ◁ T₂).map (· * r)
        + (r ◁ T₂).map (l * ·) := rfl

/-! ## §2: Edge counting

`numEdges T` counts the edges of `T`: 0 for a leaf, `numEdges l +
numEdges r + 2` for `l * r` (the two new root edges plus inherited). -/

/-- Number of edges in `T : FreeMagma α`. -/
def numEdges : FreeMagma α → Nat
  | .of _ => 0
  | .mul l r => numEdges l + numEdges r + 2

@[simp] theorem numEdges_of (a : α) :
    numEdges (FreeMagma.of a : FreeMagma α) = 0 := rfl

@[simp] theorem numEdges_mul (l r : FreeMagma α) :
    numEdges (l * r) = numEdges l + numEdges r + 2 := rfl

/-- **Edge-count consistency** (implicit in MCB Definition 1.7.1):
    `T₁ ◁ T₂` has exactly one term per edge of `T₁`. -/
theorem card_insertSum_eq_numEdges :
    ∀ (T₁ T₂ : FreeMagma α), (T₁ ◁ T₂).card = numEdges T₁
  | .of _, _ => rfl
  | .mul l r, T₂ => by
      show ((l * r) ◁ T₂).card = numEdges (l * r)
      simp only [insertSum_mul, Multiset.card_add, Multiset.card_map,
                 numEdges_mul]
      have ihl := card_insertSum_eq_numEdges l T₂
      have ihr := card_insertSum_eq_numEdges r T₂
      have h2 : (({(l * T₂) * r, l * (r * T₂)}
                  : Multiset (FreeMagma α))).card = 2 := by
        rw [show (({(l * T₂) * r, l * (r * T₂)}
                    : Multiset (FreeMagma α)))
                = ((l * T₂) * r) ::ₘ
                  (({l * (r * T₂)}
                    : Multiset (FreeMagma α))) from rfl,
            Multiset.card_cons, Multiset.card_singleton]
      rw [h2, ihl, ihr]
      omega

/-! ## §3: Per-edge insertion machinery (substrate for descent proofs)

To prove the pre-Lie identity (and the descent through `toFCM`) we need
per-edge bookkeeping: which specific edge of `T₁` is being split. We
add:

- `Edge T` — indexed inductive type, one constructor per edge of `T`.
- `insertAt e T₂` — insertion at the specific edge `e : Edge T`.
- `edges T` — list-enumeration of all edges of `T`.
- `insertSum_eq_ofList_map_insertAt` — bridge between the recursive
  Multiset formulation (§1) and the per-edge formulation. -/

/-- An edge of a `FreeMagma α`, indexed by the tree itself. The four
    constructors mirror the four ways an edge can sit in `l * r`: one
    of the two immediate root edges, or recursively in `l` / `r`. -/
inductive Edge : FreeMagma α → Type u
  | rootL (l r : FreeMagma α) : Edge (l * r)
  | rootR (l r : FreeMagma α) : Edge (l * r)
  | inL (l r : FreeMagma α) (e : Edge l) : Edge (l * r)
  | inR (l r : FreeMagma α) (e : Edge r) : Edge (l * r)

/-- Insert `T₂` at the specific edge `e` of some tree. Per-edge
    sibling of `insertSum`: `insertSum T₁ T₂` is the multiset of all
    `insertAt e T₂` for `e : Edge T₁`. -/
def insertAt : ∀ {T : FreeMagma α}, Edge T → FreeMagma α → FreeMagma α
  | _, .rootL l r,   T₂ => (l * T₂) * r
  | _, .rootR l r,   T₂ => l * (r * T₂)
  | _, .inL _ r e,   T₂ => (insertAt e T₂) * r
  | _, .inR l _ e,   T₂ => l * (insertAt e T₂)

@[simp] theorem insertAt_rootL (l r T₂ : FreeMagma α) :
    insertAt (.rootL l r) T₂ = (l * T₂) * r := rfl

@[simp] theorem insertAt_rootR (l r T₂ : FreeMagma α) :
    insertAt (.rootR l r) T₂ = l * (r * T₂) := rfl

@[simp] theorem insertAt_inL (l r T₂ : FreeMagma α) (e : Edge l) :
    insertAt (.inL l r e) T₂ = (insertAt e T₂) * r := rfl

@[simp] theorem insertAt_inR (l r T₂ : FreeMagma α) (e : Edge r) :
    insertAt (.inR l r e) T₂ = l * (insertAt e T₂) := rfl

/-- Enumeration of all edges of `T` as a `List`. Order: the two
    immediate root edges first (rootL, rootR), then the recursive edges
    of `l` (lifted via `.inL`), then `r` (via `.inR`). The total length
    equals `numEdges T` (proved below). -/
def edges : (T : FreeMagma α) → List (Edge T)
  | .of _ => []
  | .mul l r =>
      .rootL l r :: .rootR l r ::
        ((edges l).map (.inL l r) ++ (edges r).map (.inR l r))

@[simp] theorem edges_of (a : α) :
    edges (FreeMagma.of a : FreeMagma α) = [] := rfl

@[simp] theorem edges_mul (l r : FreeMagma α) :
    edges (l * r)
      = .rootL l r :: .rootR l r ::
          ((edges l).map (.inL l r) ++ (edges r).map (.inR l r)) := rfl

/-- Edge count: `(edges T).length = numEdges T`. -/
theorem length_edges_eq_numEdges :
    ∀ (T : FreeMagma α), (edges T).length = numEdges T
  | .of _ => rfl
  | .mul l r => by
      show (edges (l * r)).length = numEdges (l * r)
      have ihl := length_edges_eq_numEdges l
      have ihr := length_edges_eq_numEdges r
      simp only [edges_mul, List.length_cons, List.length_append,
                 List.length_map, numEdges_mul]
      omega

/-! ## §4: Decomposition of `insertSum` via `insertAt` -/

/-- **Decomposition lemma**: `insertSum T₁ T₂` equals the multiset of
    `insertAt e T₂` for `e` ranging over `edges T₁`. The bridge between
    the recursive (Multiset) and per-edge formulations of MCB
    Definition 1.7.1. -/
theorem insertSum_eq_ofList_map_insertAt :
    ∀ (T₁ T₂ : FreeMagma α),
      T₁ ◁ T₂
        = Multiset.ofList ((edges T₁).map (fun e => insertAt e T₂))
  | .of _, _ => rfl
  | .mul l r, T₂ => by
      show (l * r) ◁ T₂
        = Multiset.ofList ((edges (l * r)).map (fun e => insertAt e T₂))
      have ihl := insertSum_eq_ofList_map_insertAt l T₂
      have ihr := insertSum_eq_ofList_map_insertAt r T₂
      rw [insertSum_mul, ihl, ihr]
      simp only [edges_mul, List.map_cons, List.map_append, List.map_map,
                 Function.comp_def, insertAt_rootL, insertAt_rootR,
                 insertAt_inL, insertAt_inR, Multiset.map_coe]
      rw [show (({(l * T₂) * r, l * (r * T₂)}
                  : Multiset (FreeMagma α)))
              = (↑[(l * T₂) * r, l * (r * T₂)]
                : Multiset (FreeMagma α)) from rfl,
          Multiset.coe_add, Multiset.coe_add]
      rfl

/-- **Edge-count consistency restated** via `length_edges_eq_numEdges`
    and `insertSum_eq_ofList_map_insertAt`. The two versions of edge
    counting agree. -/
theorem card_insertSum_via_edges (T₁ T₂ : FreeMagma α) :
    (T₁ ◁ T₂).card = (edges T₁).length := by
  rw [insertSum_eq_ofList_map_insertAt, Multiset.coe_card, List.length_map]

/-! ## §9.1: Edge classification machinery

Per-edge bookkeeping for the descent and pre-Lie proofs: lift edges of
`T₂` into `Edge (insertAt e T₂)`, name the three new split edges
(`newE1`, `newE2`, `newEprime`), and transport non-cut edges of `T`
through the insertion (`preserveAux`/`preserveOf`).

The 5 classes (preserved + lifted + 3 new) form a *bijection* with
`Edge (insertAt e T₂)`, packaged as `Edge.classifyEquiv`. Pairwise
distinctness of the new edges and the §9.2 multiset decomposition fall
out as corollaries. -/

/-- **Lift an edge of T₂** into `Edge (insertAt e T₂)`. The lifted
    edge sits in the inserted subtree at vertex `v`. Recursive on the
    structure of `e`: for the two `.root*` constructors, T₂ becomes a
    direct child of `v`; for `.in*`, recurse to the child where the
    insertion happens. -/
def Edge.lift : ∀ {T : FreeMagma α} (e : Edge T) (T₂ : FreeMagma α),
    Edge T₂ → Edge (insertAt e T₂)
  | _, .rootL l r,   T₂, f => .inL (l * T₂) r (.inR l T₂ f)
  | _, .rootR l r,   T₂, f => .inR l (r * T₂) (.inR r T₂ f)
  | _, .inL l r e,   T₂, f => .inL (insertAt e T₂) r (Edge.lift e T₂ f)
  | _, .inR l r e,   T₂, f => .inR l (insertAt e T₂) (Edge.lift e T₂ f)

/-- **The "upper half" of the split edge** `e₁`: the new edge from the
    parent of e to the new vertex `v`. After splitting `e : Edge T`
    with insertion of T₂, the parent's slot now points to v (rather
    than directly to the child). -/
def Edge.newE1 : ∀ {T : FreeMagma α} (e : Edge T) (T₂ : FreeMagma α),
    Edge (insertAt e T₂)
  | _, .rootL l r,   T₂ => .rootL (l * T₂) r
  | _, .rootR l r,   T₂ => .rootR l (r * T₂)
  | _, .inL l r e,   T₂ => .inL (insertAt e T₂) r (Edge.newE1 e T₂)
  | _, .inR l r e,   T₂ => .inR l (insertAt e T₂) (Edge.newE1 e T₂)

/-- **The "lower half" of the split edge** `e₂`: the new edge from the
    new vertex `v` to the original child of the cut edge. -/
def Edge.newE2 : ∀ {T : FreeMagma α} (e : Edge T) (T₂ : FreeMagma α),
    Edge (insertAt e T₂)
  | _, .rootL l r,   T₂ => .inL (l * T₂) r (.rootL l T₂)
  | _, .rootR l r,   T₂ => .inR l (r * T₂) (.rootL r T₂)
  | _, .inL l r e,   T₂ => .inL (insertAt e T₂) r (Edge.newE2 e T₂)
  | _, .inR l r e,   T₂ => .inR l (insertAt e T₂) (Edge.newE2 e T₂)

/-- **The "edge to T₂"** `e'`: the new edge from the new vertex `v` to
    the root of the inserted subtree T₂. -/
def Edge.newEprime : ∀ {T : FreeMagma α} (e : Edge T) (T₂ : FreeMagma α),
    Edge (insertAt e T₂)
  | _, .rootL l r,   T₂ => .inL (l * T₂) r (.rootR l T₂)
  | _, .rootR l r,   T₂ => .inR l (r * T₂) (.rootR r T₂)
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
def Edge.preserveAux : ∀ {T : FreeMagma α} (e f : Edge T)
      (T₂ : FreeMagma α), Option (Edge (insertAt e T₂))
  -- e = rootL: insertAt = (l * T₂) * r
  | _, .rootL _ _,   .rootL _ _,   _  => none
  | _, .rootL l _,   .rootR _ r,   T₂ => some (.rootR (l * T₂) r)
  | _, .rootL l _,   .inL _ r f',  T₂ => some (.inL (l * T₂) r (.inL l T₂ f'))
  | _, .rootL l _,   .inR _ r f',  T₂ => some (.inR (l * T₂) r f')
  -- e = rootR: insertAt = l * (r * T₂)
  | _, .rootR l _,   .rootL _ r,   T₂ => some (.rootL l (r * T₂))
  | _, .rootR _ _,   .rootR _ _,   _  => none
  | _, .rootR _ r,   .inL l _ f',  T₂ => some (.inL l (r * T₂) f')
  | _, .rootR _ r,   .inR l _ f',  T₂ => some (.inR l (r * T₂) (.inL r T₂ f'))
  -- e = inL e': insertAt = (insertAt e' T₂) * r
  | _, .inL _ _ e',  .rootL _ r,   T₂ => some (.rootL (insertAt e' T₂) r)
  | _, .inL _ _ e',  .rootR _ r,   T₂ => some (.rootR (insertAt e' T₂) r)
  | _, .inL _ r e',  .inL _ _ f',  T₂ =>
      (Edge.preserveAux e' f' T₂).map (.inL (insertAt e' T₂) r)
  | _, .inL _ _ e',  .inR _ r f',  T₂ => some (.inR (insertAt e' T₂) r f')
  -- e = inR e': insertAt = l * (insertAt e' T₂)
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
def Edge.preserveOf : ∀ {T : FreeMagma α} (e f : Edge T) (_h : f ≠ e)
      (T₂ : FreeMagma α), Edge (insertAt e T₂)
  | _, .rootL _ _,   .rootL _ _,   h, _  => absurd rfl h
  | _, .rootL l _,   .rootR _ r,   _, T₂ => .rootR (l * T₂) r
  | _, .rootL l _,   .inL _ r f',  _, T₂ => .inL (l * T₂) r (.inL l T₂ f')
  | _, .rootL l _,   .inR _ r f',  _, T₂ => .inR (l * T₂) r f'
  | _, .rootR l _,   .rootL _ r,   _, T₂ => .rootL l (r * T₂)
  | _, .rootR _ _,   .rootR _ _,   h, _  => absurd rfl h
  | _, .rootR _ r,   .inL l _ f',  _, T₂ => .inL l (r * T₂) f'
  | _, .rootR _ r,   .inR l _ f',  _, T₂ => .inR l (r * T₂) (.inL r T₂ f')
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
theorem Edge.preserveAux_self : ∀ {T : FreeMagma α} (e : Edge T)
      (T₂ : FreeMagma α),
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
theorem Edge.preserveAux_of_ne : ∀ {T : FreeMagma α} (e f : Edge T) (h : f ≠ e)
      (T₂ : FreeMagma α),
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
inductive Edge.Classify : ∀ {T : FreeMagma α}, Edge T → FreeMagma α →
    Type u
  | preserved {T : FreeMagma α} {e : Edge T} {T₂ : FreeMagma α}
      (f : Edge T) (h : f ≠ e) : Edge.Classify e T₂
  | lifted {T : FreeMagma α} {e : Edge T} {T₂ : FreeMagma α}
      (g : Edge T₂) : Edge.Classify e T₂
  | newE1 {T : FreeMagma α} {e : Edge T} {T₂ : FreeMagma α} :
      Edge.Classify e T₂
  | newE2 {T : FreeMagma α} {e : Edge T} {T₂ : FreeMagma α} :
      Edge.Classify e T₂
  | newEprime {T : FreeMagma α} {e : Edge T} {T₂ : FreeMagma α} :
      Edge.Classify e T₂

/-- Realize a classification as an actual edge of `insertAt e T₂`. -/
def Edge.fromClassify : ∀ {T : FreeMagma α} {e : Edge T} {T₂ : FreeMagma α},
    Edge.Classify e T₂ → Edge (insertAt e T₂)
  | _, _, _, .preserved f h => Edge.preserveOf _ f h _
  | _, e, T₂, .lifted g => Edge.lift e T₂ g
  | _, e, T₂, .newE1 => Edge.newE1 e T₂
  | _, e, T₂, .newE2 => Edge.newE2 e T₂
  | _, e, T₂, .newEprime => Edge.newEprime e T₂

/-- Classify an edge of `insertAt e T₂` into one of the 5 classes.
    Defined by structural recursion on `e` (4 cases), with nested case
    analysis on the input edge to identify which class it belongs to. -/
def Edge.toClassify : ∀ {T : FreeMagma α} (e : Edge T) (T₂ : FreeMagma α),
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
theorem Edge.fromClassify_toClassify : ∀ {T : FreeMagma α} (e : Edge T)
      (T₂ : FreeMagma α) (f : Edge (insertAt e T₂)),
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

theorem Edge.toClassify_lift : ∀ {T : FreeMagma α} (e : Edge T)
      (T₂ : FreeMagma α) (g : Edge T₂),
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

theorem Edge.toClassify_newE1 : ∀ {T : FreeMagma α} (e : Edge T)
      (T₂ : FreeMagma α),
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

theorem Edge.toClassify_newE2 : ∀ {T : FreeMagma α} (e : Edge T)
      (T₂ : FreeMagma α),
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

theorem Edge.toClassify_newEprime : ∀ {T : FreeMagma α} (e : Edge T)
      (T₂ : FreeMagma α),
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

theorem Edge.toClassify_preserveOf : ∀ {T : FreeMagma α} (e f : Edge T)
      (h : f ≠ e) (T₂ : FreeMagma α),
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
theorem Edge.toClassify_fromClassify {T : FreeMagma α} (e : Edge T)
    (T₂ : FreeMagma α) (c : Edge.Classify e T₂) :
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
def Edge.classifyEquiv {T : FreeMagma α} (e : Edge T) (T₂ : FreeMagma α) :
    Edge (insertAt e T₂) ≃ Edge.Classify e T₂ where
  toFun := Edge.toClassify e T₂
  invFun := Edge.fromClassify
  left_inv f := Edge.fromClassify_toClassify e T₂ f
  right_inv c := Edge.toClassify_fromClassify e T₂ c

/-! ### Pairwise distinctness of the 3 new edges (Equiv corollaries)

Now that the classification is bijective, the 3 new edges are
*automatically* pairwise distinct: their `toClassify` images are
syntactically distinct constructors of `Edge.Classify`. -/

theorem Edge.newE1_ne_newE2 {T : FreeMagma α} (e : Edge T)
    (T₂ : FreeMagma α) :
    Edge.newE1 e T₂ ≠ Edge.newE2 e T₂ := by
  intro h
  have := congrArg (Edge.toClassify e T₂) h
  rw [Edge.toClassify_newE1, Edge.toClassify_newE2] at this
  cases this

theorem Edge.newE1_ne_newEprime {T : FreeMagma α} (e : Edge T)
    (T₂ : FreeMagma α) :
    Edge.newE1 e T₂ ≠ Edge.newEprime e T₂ := by
  intro h
  have := congrArg (Edge.toClassify e T₂) h
  rw [Edge.toClassify_newE1, Edge.toClassify_newEprime] at this
  cases this

theorem Edge.newE2_ne_newEprime {T : FreeMagma α} (e : Edge T)
    (T₂ : FreeMagma α) :
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
theorem edges_insertAt_eq_classification {T : FreeMagma α}
    (e : Edge T) (T₂ : FreeMagma α) :
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
        = Edge.rootL (l * T₂) r :: Edge.rootR (l * T₂) r ::
          Edge.inL (l * T₂) r (.rootL l T₂) ::
          Edge.inL (l * T₂) r (.rootR l T₂) ::
          ((edges l).map (fun f' => Edge.inL (l * T₂) r (.inL l T₂ f')) ++
           (edges T₂).map (fun f' => Edge.inL (l * T₂) r (.inR l T₂ f'))) ++
          (edges r).map (Edge.inR (l * T₂) r) := by
      show edges ((l * T₂) * r) = _
      simp only [edges_mul, List.map_cons, List.map_append, List.map_map,
                 Function.comp_def, List.cons_append]
    have hPres : (edges (l * r)).filterMap
                   (fun f => Edge.preserveAux (Edge.rootL l r) f T₂)
        = Edge.rootR (l * T₂) r ::
          ((edges l).map (fun f' => Edge.inL (l * T₂) r (.inL l T₂ f')) ++
           (edges r).map (Edge.inR (l * T₂) r)) := by
      show List.filterMap _
             (Edge.rootL l r :: Edge.rootR l r ::
               ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))) = _
      show (Edge.rootR (l * T₂) r) ::
           (((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r)).filterMap
              (fun f => Edge.preserveAux (Edge.rootL l r) f T₂)) = _
      congr 1
      rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
      simp only [Function.comp_def]
      show List.filterMap (fun x => some (Edge.inL (l * T₂) r (Edge.inL l T₂ x))) (edges l) ++
           List.filterMap (fun x => some (Edge.inR (l * T₂) r x)) (edges r) = _
      rw [List.filterMap_eq_map', List.filterMap_eq_map']
    rw [hLHS, hPres]
    show (↑(Edge.rootL (l * T₂) r :: Edge.rootR (l * T₂) r ::
            Edge.inL (l * T₂) r (.rootL l T₂) ::
            Edge.inL (l * T₂) r (.rootR l T₂) ::
            ((edges l).map (fun f' => Edge.inL (l * T₂) r (.inL l T₂ f')) ++
             (edges T₂).map (fun f' => Edge.inL (l * T₂) r (.inR l T₂ f'))) ++
            (edges r).map (Edge.inR (l * T₂) r))
          : Multiset (Edge ((l * T₂) * r))) =
         ↑(Edge.rootR (l * T₂) r ::
           ((edges l).map (fun f' => Edge.inL (l * T₂) r (.inL l T₂ f')) ++
            (edges r).map (Edge.inR (l * T₂) r))) +
         ↑((edges T₂).map (fun f => Edge.inL (l * T₂) r (.inR l T₂ f))) +
         (Edge.rootL (l * T₂) r ::ₘ
          Edge.inL (l * T₂) r (.rootL l T₂) ::ₘ
          Edge.inL (l * T₂) r (.rootR l T₂) ::ₘ 0)
    simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add]
    ac_rfl
  | rootR l r =>
    have hLHS : edges (insertAt (Edge.rootR l r) T₂)
        = Edge.rootL l (r * T₂) :: Edge.rootR l (r * T₂) ::
          ((edges l).map (Edge.inL l (r * T₂)) ++
           (Edge.inR l (r * T₂) (.rootL r T₂) ::
            Edge.inR l (r * T₂) (.rootR r T₂) ::
            ((edges r).map (fun f' => Edge.inR l (r * T₂) (.inL r T₂ f')) ++
             (edges T₂).map (fun f' => Edge.inR l (r * T₂) (.inR r T₂ f'))))) := by
      show edges (l * (r * T₂)) = _
      simp only [edges_mul, List.map_cons, List.map_append, List.map_map,
                 Function.comp_def]
    have hPres : (edges (l * r)).filterMap
                   (fun f => Edge.preserveAux (Edge.rootR l r) f T₂)
        = Edge.rootL l (r * T₂) ::
          ((edges l).map (Edge.inL l (r * T₂)) ++
           (edges r).map (fun f' => Edge.inR l (r * T₂) (.inL r T₂ f'))) := by
      show List.filterMap _
             (Edge.rootL l r :: Edge.rootR l r ::
               ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))) = _
      show (Edge.rootL l (r * T₂)) ::
           ((Edge.rootR l r ::
              ((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r))).filterMap
              (fun f => Edge.preserveAux (Edge.rootR l r) f T₂)) = _
      congr 1
      show (((edges l).map (Edge.inL l r) ++ (edges r).map (Edge.inR l r)).filterMap
              (fun f => Edge.preserveAux (Edge.rootR l r) f T₂)) = _
      rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
      simp only [Function.comp_def]
      show List.filterMap (fun x => some (Edge.inL l (r * T₂) x)) (edges l) ++
           List.filterMap (fun x => some (Edge.inR l (r * T₂) (.inL r T₂ x))) (edges r) = _
      rw [List.filterMap_eq_map', List.filterMap_eq_map']
    rw [hLHS, hPres]
    show (↑(Edge.rootL l (r * T₂) :: Edge.rootR l (r * T₂) ::
            ((edges l).map (Edge.inL l (r * T₂)) ++
             (Edge.inR l (r * T₂) (.rootL r T₂) ::
              Edge.inR l (r * T₂) (.rootR r T₂) ::
              ((edges r).map (fun f' => Edge.inR l (r * T₂) (.inL r T₂ f')) ++
               (edges T₂).map (fun f' => Edge.inR l (r * T₂) (.inR r T₂ f'))))))
          : Multiset (Edge (l * (r * T₂)))) =
         ↑(Edge.rootL l (r * T₂) ::
           ((edges l).map (Edge.inL l (r * T₂)) ++
            (edges r).map (fun f' => Edge.inR l (r * T₂) (.inL r T₂ f')))) +
         ↑((edges T₂).map (fun f => Edge.inR l (r * T₂) (.inR r T₂ f))) +
         (Edge.rootR l (r * T₂) ::ₘ
          Edge.inR l (r * T₂) (.rootL r T₂) ::ₘ
          Edge.inR l (r * T₂) (.rootR r T₂) ::ₘ 0)
    simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add]
    ac_rfl
  | inL l r e' ih =>
    change (↑(edges ((insertAt e' T₂) * r))
              : Multiset (Edge ((insertAt e' T₂) * r))) = _
    rw [edges_mul]
    have hPres : (edges (l * r)).filterMap
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
                                       (Edge.inL (insertAt e' T₂) r)) (edges l) ++
           List.filterMap (fun x => some (Edge.inR (insertAt e' T₂) r x)) (edges r) = _
      rw [← List.map_filterMap, List.filterMap_eq_map']
    rw [hPres]
    rw [show (edges T₂).map (Edge.lift (Edge.inL l r e') T₂)
            = ((edges T₂).map (Edge.lift e' T₂)).map (Edge.inL (insertAt e' T₂) r) from by
            rw [List.map_map]; rfl]
    show (↑(Edge.rootL (insertAt e' T₂) r :: Edge.rootR (insertAt e' T₂) r ::
            ((edges (insertAt e' T₂)).map (Edge.inL (insertAt e' T₂) r) ++
             (edges r).map (Edge.inR (insertAt e' T₂) r)))
          : Multiset (Edge ((insertAt e' T₂) * r))) =
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
    change (↑(edges (l * (insertAt e' T₂)))
              : Multiset (Edge (l * (insertAt e' T₂)))) = _
    rw [edges_mul]
    have hPres : (edges (l * r)).filterMap
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
      show List.filterMap (fun x => some (Edge.inL l (insertAt e' T₂) x)) (edges l) ++
           List.filterMap (fun x => (Edge.preserveAux e' x T₂).map
                                       (Edge.inR l (insertAt e' T₂))) (edges r) = _
      rw [List.filterMap_eq_map', ← List.map_filterMap]
    rw [hPres]
    rw [show (edges T₂).map (Edge.lift (Edge.inR l r e') T₂)
            = ((edges T₂).map (Edge.lift e' T₂)).map (Edge.inR l (insertAt e' T₂)) from by
            rw [List.map_map]; rfl]
    show (↑(Edge.rootL l (insertAt e' T₂) :: Edge.rootR l (insertAt e' T₂) ::
            ((edges l).map (Edge.inL l (insertAt e' T₂)) ++
             (edges (insertAt e' T₂)).map (Edge.inR l (insertAt e' T₂))))
          : Multiset (Edge (l * (insertAt e' T₂)))) =
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
theorem insertAt_commute_diff : ∀ {T : FreeMagma α} (e f : Edge T)
      (h : f ≠ e) (T₂ T₃ : FreeMagma α),
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
    show (insertAt (Edge.preserveOf e' f' _ T₂) T₃) * r
        = (insertAt (Edge.preserveOf f' e' _ T₃) T₂) * r
    congr 1
    exact insertAt_commute_diff e' f' (fun heq => h (by rw [heq])) T₂ T₃
  | _, .inR l _ e', .inR _ _ f', h, T₂, T₃ => by
    show l * (insertAt (Edge.preserveOf e' f' _ T₂) T₃)
        = l * (insertAt (Edge.preserveOf f' e' _ T₃) T₂)
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
theorem insertAt_lift_eq_nested : ∀ {T : FreeMagma α} (e : Edge T)
      (T₂ T₃ : FreeMagma α) (g : Edge T₂),
    insertAt (Edge.lift e T₂ g) T₃ = insertAt e (insertAt g T₃)
  | _, .rootL _ _, _, _, _ => rfl
  | _, .rootR _ _, _, _, _ => rfl
  | _, .inL l r e', T₂, T₃, g => by
    show (insertAt (Edge.lift e' T₂ g) T₃) * r
        = (insertAt e' (insertAt g T₃)) * r
    rw [insertAt_lift_eq_nested e' T₂ T₃ g]
  | _, .inR l r e', T₂, T₃, g => by
    show l * (insertAt (Edge.lift e' T₂ g) T₃)
        = l * (insertAt e' (insertAt g T₃))
    rw [insertAt_lift_eq_nested e' T₂ T₃ g]

/-! ## §10: Descent through `FreeCommMagma.mk`

To define `FreeCommMagma.insertSum` via `lift₂`, we need to show the
planar `(T ◁ S).map FreeCommMagma.mk` is invariant under `CommRel` on
each argument. This descent realizes MCB Lemma 1.10.1 (book p. 92):
ℑ is the free **nonassociative commutative magma**, so insertion
descends from the planar substrate to the nonplanar carrier.

- `descent_right`: per-edge equality propagates the swap of `S` through
  every `insertAt e S`. Easy: `mk` is a magma homomorphism.
- `descent_left`: structural induction on `CommRel T T'` plus FCM
  commutativity at each cell. Substantive — analogous to the §10b/§11
  swap-collapse work in the legacy `Insertion.lean`, but at the
  swap-anywhere level rather than the new-vertex level.
-/

/-- Per-edge propagation: if `mk T₂ = mk T₂'` then `mk (insertAt e T₂)
    = mk (insertAt e T₂')` for every edge `e` of `T`. By structural
    induction on `e` + `mk` being a magma homomorphism. -/
private theorem mk_insertAt_descent {T : FreeMagma α} (e : Edge T) :
    ∀ {T₂ T₂' : FreeMagma α},
    (FreeCommMagma.mk T₂ : FreeCommMagma α) = FreeCommMagma.mk T₂' →
    (FreeCommMagma.mk (insertAt e T₂) : FreeCommMagma α)
      = FreeCommMagma.mk (insertAt e T₂') := by
  induction e with
  | rootL l r =>
    intro T₂ T₂' h
    show (FreeCommMagma.mk ((l * T₂) * r) : FreeCommMagma α)
        = FreeCommMagma.mk ((l * T₂') * r)
    -- `mk (a * b) = mk a * mk b` by definition of FCM.mul (Quot.lift₂).
    show (FreeCommMagma.mk l * FreeCommMagma.mk T₂) * FreeCommMagma.mk r
        = (FreeCommMagma.mk l * FreeCommMagma.mk T₂') * FreeCommMagma.mk r
    rw [h]
  | rootR l r =>
    intro T₂ T₂' h
    show (FreeCommMagma.mk (l * (r * T₂)) : FreeCommMagma α)
        = FreeCommMagma.mk (l * (r * T₂'))
    show FreeCommMagma.mk l * (FreeCommMagma.mk r * FreeCommMagma.mk T₂)
        = FreeCommMagma.mk l * (FreeCommMagma.mk r * FreeCommMagma.mk T₂')
    rw [h]
  | inL l r e' ih =>
    intro T₂ T₂' h
    show (FreeCommMagma.mk ((insertAt e' T₂) * r) : FreeCommMagma α)
        = FreeCommMagma.mk ((insertAt e' T₂') * r)
    show FreeCommMagma.mk (insertAt e' T₂) * FreeCommMagma.mk r
        = FreeCommMagma.mk (insertAt e' T₂') * FreeCommMagma.mk r
    rw [ih h]
  | inR l r e' ih =>
    intro T₂ T₂' h
    show (FreeCommMagma.mk (l * (insertAt e' T₂)) : FreeCommMagma α)
        = FreeCommMagma.mk (l * (insertAt e' T₂'))
    show FreeCommMagma.mk l * FreeCommMagma.mk (insertAt e' T₂)
        = FreeCommMagma.mk l * FreeCommMagma.mk (insertAt e' T₂')
    rw [ih h]

/-- **Right descent**: `(T₁ ◁ T₂).map mk = (T₁ ◁ T₂').map mk` whenever
    `T₂ ~ T₂'` (CommRel). Direct corollary of `mk_insertAt_descent`
    applied per-edge. -/
private theorem insertSum_descent_right (T₁ : FreeMagma α) :
    ∀ {T₂ T₂' : FreeMagma α}, FreeMagma.CommRel T₂ T₂' →
    (T₁ ◁ T₂).map FreeCommMagma.mk = (T₁ ◁ T₂').map FreeCommMagma.mk := by
  intro T₂ T₂' h
  have hmk : (FreeCommMagma.mk T₂ : FreeCommMagma α) = FreeCommMagma.mk T₂' :=
    Quot.sound h
  rw [insertSum_eq_ofList_map_insertAt, insertSum_eq_ofList_map_insertAt,
      Multiset.map_coe, Multiset.map_coe, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  exact mk_insertAt_descent e hmk

/-- **Left descent**: `(T ◁ T₂).map mk = (T' ◁ T₂).map mk` whenever
    `T ~ T'` (CommRel). Proven by induction on the CommRel derivation
    + FCM commutativity at each cell.

    TODO (Phase 3.E.4b): substantive proof. Three CommRel cases:
    - `swap a b`: root planar swap; uses §9.2-style decomposition +
      multiset commutativity + `mul_comm` on FCM.
    - `mul_left h c`: structural propagation through left subtree;
      uses IH + `Multiset.map_map` to push through.
    - `mul_right a h`: symmetric for right subtree. -/
private theorem insertSum_descent_left :
    ∀ {T T' : FreeMagma α}, FreeMagma.CommRel T T' → ∀ (T₂ : FreeMagma α),
    (T ◁ T₂).map FreeCommMagma.mk = (T' ◁ T₂).map FreeCommMagma.mk := by
  sorry

end FreeMagma

/-! ## §11: Native `FreeCommMagma.insertSum` via `lift₂`

The public-API insertion on the FCM carrier, defined by lifting from
the planar `FreeMagma.insertSum` through `Free.lean`'s `lift₂`. The
descent proofs (§10) discharge the well-definedness obligations. -/

namespace FreeCommMagma

universe u
variable {α : Type u}

/-- **Native insertion sum on `FreeCommMagma α`** (MCB Definition 1.7.1
    on the natural nonplanar carrier). Lifted from the planar
    `FreeMagma.insertSum` via `Quot.lift₂`. The descent proofs
    `FreeMagma.insertSum_descent_left/right` discharge the
    well-definedness obligation. -/
noncomputable def insertSum : FreeCommMagma α → FreeCommMagma α →
    Multiset (FreeCommMagma α) :=
  Quot.lift₂ (fun (a b : FreeMagma α) => (FreeMagma.insertSum a b).map FreeCommMagma.mk)
    (fun a _ _ h => FreeMagma.insertSum_descent_right a h)
    (fun _ _ b h => FreeMagma.insertSum_descent_left h b)

/-- Notation `T₁ ◁ T₂` for `insertSum T₁ T₂` on `FreeCommMagma`. The
    same right-triangle glyph as the planar version, scoped to the
    `FreeCommMagma` namespace to avoid clashing. -/
scoped infixl:65 " ◁ " => insertSum

@[simp] theorem insertSum_mk (a b : FreeMagma α) :
    (FreeCommMagma.mk a : FreeCommMagma α) ◁ FreeCommMagma.mk b
      = (FreeMagma.insertSum a b).map FreeCommMagma.mk := rfl

end FreeCommMagma
