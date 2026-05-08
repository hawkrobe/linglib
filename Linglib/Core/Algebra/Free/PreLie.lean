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

end FreeMagma
