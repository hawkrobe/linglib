/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Hom.Defs
import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Selection-driven heads on the `SO` carrier

This file defines the c-selection head of a syntactic object: whichever sister's
head selects the saturated other projects — [adger-2003]'s identification of the
projecting item with the selecting item, instantiating the bare-phrase-structure
projection ([chomsky-1995-bare] §4) that [marcolli-chomsky-berwick-2025] §1.13.3
abstracts as head functions (Definition 1.13.6 / Lemma 1.13.7). Like the book's
head functions it is partial: `none` at exocentric nodes.

## Main declarations

* `Minimalist.SelState`: a constituent's selection state — the projecting head
  together with its residual selectional stack.
* `Mul SelState` and `Minimalist.selSide`: the carrier-free combinators — the
  selection product, and which daughter projects.
* `Minimalist.selNode`, `Minimalist.selCheckPlanar`, `Minimalist.SO.selCheck`:
  the selection algebra, its catamorphism, and the `SO` lift.
* `Minimalist.SO.selHead`, `Minimalist.SO.outerCatC`: the head token and its outer
  category — the foundation the Phase API consumes (`isPhaseHeadOf`).
* `Minimalist.selCheckHom`: `selCheck` as a morphism of magmas `SO →ₙ* SelState` —
  the book's algebraic frame, with `SelState` a `CommMagma`.

## Main results

* `mul_comm` (via `CommMagma SelState`) and `Minimalist.selSide_comm`:
  order-independence — the formal content of Merge's unordered output.
* `Minimalist.SO.selHead_node`: endocentricity — a node's head is one of its
  daughters' heads.

## Implementation notes

The tree recursion is the catamorphism `RoseTree.fold selNode`; the algebra is
permutation-invariant (`selNode_perm`), so invariance and the quotient lift come
from `fold_perm` — no bespoke step induction. **Index-free traces**: a bare trace
leaf gets the canonical saturated value `(mkTraceToken 0, [])`; `selCheck` reads
only the token's category and `outerSel`, both index-independent.
-/

namespace Minimalist

open RootedTree

/-! ### Carrier-free selection combinators -/

/-- The selection state of a constituent: the projecting head token together with
    its residual selectional stack (`some []` = saturated), or `none` off the
    endocentric domain. -/
abbrev SelState := Option (LIToken × List Cat)

variable (x y : SelState)

/-- The selection decision at a binary node — (which sister projects, head,
    residual), `none` at exocentric nodes; `*` and `selSide` are its projections. -/
def selCombine : SelState → SelState → Option (Bool × LIToken × List Cat)
  | some (ha, c :: rest), some (hb, []) =>
      if hb.item.outerCat = c then some (true, ha, rest) else none
  | some (ha, []), some (hb, c :: rest) =>
      if ha.item.outerCat = c then some (false, hb, rest) else none
  | _, _ => none

/-- Which daughter projects: `some true` = left, `some false` = right. -/
def selSide (x y : SelState) : Option Bool := (selCombine x y).map (·.1)

/-- Swapping the sisters flips the side and keeps the head and residual. -/
theorem selCombine_comm : selCombine x y = (selCombine y x).map fun p => (!p.1, p.2) := by
  rcases x with _ | ⟨hx, _ | ⟨cx, sx⟩⟩ <;> rcases y with _ | ⟨hy, _ | ⟨cy, sy⟩⟩ <;>
    first
    | rfl
    | (simp only [selCombine, Option.map]; split <;> rfl)

/-- S₂-equivariance: swap acts on the sisters, `Bool.not` on the side — the
    coordinate form of MCB's per-vertex edge-marking (Lemma 1.13.4); the invariant
    part of the decision is the product (hence `mul_comm`). -/
theorem selSide_comm : selSide x y = (selSide y x).map Bool.not := by
  simp only [selSide, selCombine_comm x y, Option.map_map]; rfl

/-- Multiplication of selection states — the head-and-residual of the `selCombine`
    decision, [marcolli-chomsky-berwick-2025] §1.13's Merge-local head choice. -/
instance : Mul SelState := ⟨fun x y => (selCombine x y).map (·.2)⟩

/-- `*` unfolded: the canonical accessor for the selection product. -/
theorem SelState.mul_def : x * y = (selCombine x y).map (·.2) := rfl

/-- `none` (the exocentric failure) is absorbing on the left. -/
@[simp] theorem SelState.none_mul : (none : SelState) * x = none := rfl

/-- `none` (the exocentric failure) is absorbing on the right. -/
@[simp] theorem SelState.mul_none : x * none = none := by
  rcases x with _ | ⟨h, _ | ⟨c, s⟩⟩ <;> rfl

instance : CommMagma SelState where
  mul_comm x y := by
    simp only [SelState.mul_def, selCombine_comm x y, Option.map_map]; rfl

variable {x y}

/-- The selection decision is coherent: the projected head is the head of the
    sister on the side it reports — the coherence of the two projections. The single
    raw analysis; `SelState.mul_fst` is a corollary. -/
theorem selCombine_eq_some {b : Bool} {hd : LIToken} {res : List Cat}
    (h : selCombine x y = some (b, hd, res)) :
    (bif b then x else y).map (·.1) = some hd := by
  match x, y with
  | some (ha, c :: rest'), some (hb, [])
  | some (ha, []), some (hb, c :: rest') =>
    simp only [selCombine] at h
    split_ifs at h; cases h; rfl
  | some (_, []), some (_, []) | some (_, _ :: _), some (_, _ :: _)
  | none, _ | some _, none => simp [selCombine] at h

/-- The head of `x * y` (when defined) is one of `x`/`y`'s heads. -/
theorem SelState.mul_fst {r : LIToken}
    (h : (x * y).map (·.1) = some r) :
    x.map (·.1) = some r ∨ y.map (·.1) = some r := by
  simp only [SelState.mul_def, Option.map_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨b, _, _⟩, hproj, rfl⟩ := h
  cases b
  exacts [Or.inr (selCombine_eq_some hproj), Or.inl (selCombine_eq_some hproj)]

/-! ### Selection check on the planar carrier -/

/-- The selection algebra: combine a node label with its daughters' selection
    states. Lexical leaf ↦ its token + `outerSel`; bare trace leaf ↦ canonical
    `(mkTraceToken 0, [])` (index-free); bare binary node ↦ the product of the
    daughters (the `SelState` magma multiplication); other arities ↦ `none`. -/
def selNode : SOLabel → List SelState → SelState
  | .inl tok, _     => some (tok, tok.item.outerSel)
  | .inr (), []     => some (mkTraceToken 0, [])
  | .inr (), [x, y] => x * y
  | .inr (), _      => none

/-- A daughter list of three or more has no selection value. -/
private theorem selNode_big {l : List SelState} (h : 2 < l.length) :
    selNode (Sum.inr ()) l = none := by
  match l with
  | _ :: _ :: _ :: _ => rfl
  | [] | [_] | [_, _] => simp at h

/-- A list function symmetric on pairs and constant above length two is
    `Perm`-invariant: lengths ≤ 1 are rigid under permutation, pairs by the
    symmetry, longer lists by the constancy. -/
theorem _root_.List.Perm.congr_arity₂ {β γ : Type*} {g : List β → γ} {c : γ}
    (hswap : ∀ x y, g [x, y] = g [y, x])
    (hbig : ∀ l : List β, 2 < l.length → g l = c)
    {l₁ l₂ : List β} (h : l₁.Perm l₂) : g l₁ = g l₂ := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ h _ih =>
    match l₁, l₂, h with
    | [], l₂, h => rw [show l₂ = [] from h.symm.eq_nil]
    | [y], l₂, h => rw [show l₂ = [y] from List.perm_singleton.mp h.symm]
    | _ :: _ :: _, l₂, h =>
      have hl := h.length_eq
      rw [hbig _ (by simp +arith), hbig _ (by simp only [List.length_cons] at hl ⊢; omega)]
  | swap x y l =>
    match l with
    | [] => exact hswap y x
    | _ :: _ => rw [hbig _ (by simp +arith), hbig _ (by simp +arith)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `selNode` is invariant under permutation of the daughter states: only the
    binary shape is order-sensitive, and there `mul_comm` applies. -/
theorem selNode_perm (a : SOLabel) {l₁ l₂ : List SelState} (h : l₁.Perm l₂) :
    selNode a l₁ = selNode a l₂ := by
  cases a with
  | inl tok => rfl
  | inr u => cases u; exact h.congr_arity₂ (fun x y => mul_comm x y) (fun _ h => selNode_big h)

/-- Selection check on a planar `SO`-tree: the projecting head + residual pending
    features, or `none` outside the endocentric domain — the catamorphism of
    `selNode`. -/
def selCheckPlanar : RoseTree SOLabel → SelState :=
  RoseTree.fold selNode

/-- Reduction of `selCheckPlanar` at a node: fold the algebra over the daughters. -/
theorem selCheckPlanar_node (a : SOLabel) (cs : List (RoseTree SOLabel)) :
    selCheckPlanar (RoseTree.node a cs) = selNode a (cs.map selCheckPlanar) :=
  RoseTree.fold_node ..

/-- `selCheckPlanar` is `Perm`-invariant, so it descends to the quotient. -/
theorem selCheckPlanar_perm {t s : RoseTree SOLabel} (h : RoseTree.Perm t s) :
    selCheckPlanar t = selCheckPlanar s :=
  RoseTree.fold_perm (fun a _ _ h' => selNode_perm a h') h

/-- Selection check lifted to the nonplanar carrier. -/
def selCheckN : Nonplanar SOLabel → SelState :=
  Nonplanar.lift selCheckPlanar (fun _ _ h => selCheckPlanar_perm h)

@[simp] theorem selCheckN_mk (p : RoseTree SOLabel) :
    selCheckN (Nonplanar.mk p) = selCheckPlanar p := rfl

theorem selCheckN_node (a b : Nonplanar SOLabel) :
    selCheckN (Nonplanar.node (Sum.inr ()) {a, b}) = selCheckN a * selCheckN b := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  show selCheckN (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = selCheckN (Nonplanar.mk pa) * selCheckN (Nonplanar.mk pb)
  rw [Nonplanar.node_pair_mk]; exact rfl

/-! ### The selection-driven head on `SO` -/

variable (s : SO) (tok : LIToken)

/-- **Selection-driven head check** on `SO`: the projecting head + residual
    features, or `none` off the endocentric domain. Section-free and computable;
    the selection instance of [marcolli-chomsky-berwick-2025]'s head functions. -/
def SO.selCheck : SelState := selCheckN s.val

/-- The projecting head's lexical item, by c-selection. -/
def SO.selHead : Option LIToken := s.selCheck.map (·.1)

/-- Residual pending selectional features (`some []` = saturated). -/
def SO.checkedSel : Option (List Cat) := s.selCheck.map (·.2)

/-- The projecting head's **outer category** (the phase-head selector); `none` at
    exocentric nodes. -/
def SO.outerCatC : Option Cat := s.selHead.map (·.item.outerCat)

@[simp] theorem SO.selCheck_lexLeaf :
    (SO.lexLeaf tok).selCheck = some (tok, tok.item.outerSel) := rfl

@[simp] theorem SO.selCheck_traceLeaf :
    SO.traceLeaf.selCheck = some (mkTraceToken 0, []) := rfl

@[simp] theorem SO.selCheck_node (l r : SO) :
    (SO.node l r).selCheck = l.selCheck * r.selCheck := by
  show selCheckN (SO.node l r).val = selCheckN l.val * selCheckN r.val
  rw [SO.node_val, selCheckN_node]

/-- `selCheck` as a **morphism of magmas** — [marcolli-chomsky-berwick-2025] §1.13's
    algebraic frame for head functions: Merge multiplies constituents, `selCheck`
    multiplies their selection states. Contrast the externalization *readout*, which
    is not a morphism — placing a yield needs the head
    (`Linearization/Externalization.lean`). -/
noncomputable def selCheckHom : SO →ₙ* SelState where
  toFun := SO.selCheck
  map_mul' := SO.selCheck_node

@[simp] theorem SO.selHead_lexLeaf : (SO.lexLeaf tok).selHead = some tok := rfl

/-- **Endocentricity**: a node's projecting head is one of its daughters' heads —
    bare-phrase-structure projection ([chomsky-1995-bare] §4, abstracted as
    [marcolli-chomsky-berwick-2025] Definition 1.13.6 / Lemma 1.13.7). -/
theorem SO.selHead_node {l r : SO} {h : LIToken}
    (hlr : (SO.node l r).selHead = some h) : l.selHead = some h ∨ r.selHead = some h := by
  simp only [SO.selHead, SO.selCheck_node] at hlr ⊢
  exact SelState.mul_fst hlr

@[simp] theorem SO.outerCatC_lexLeaf :
    (SO.lexLeaf tok).outerCatC = some tok.item.outerCat := rfl

end Minimalist
