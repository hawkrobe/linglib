/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
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
* `Minimalist.selStep`, `Minimalist.selSide`: the carrier-free combinators — a
  node's state from its daughters', and which daughter projects.
* `Minimalist.selCombine`, `Minimalist.selCheckPlanar`, `Minimalist.SO.selCheck`:
  the selection algebra, its catamorphism, and the `SO` lift.
* `Minimalist.SO.selHead`, `Minimalist.SO.outerCatC`: the head token and its outer
  category — the foundation the Phase API consumes (`isPhaseHeadOf`).
* `Minimalist.selCheckHom`: `selCheck` as a morphism of magmas `SO →ₙ* SelState` —
  the book's algebraic frame, with `SelState` a `CommMagma` under `selStep`.

## Main results

* `Minimalist.selStep_comm`, `Minimalist.selSide_comm`: order-independence — the
  formal content of Merge's unordered output.
* `Minimalist.SO.selHead_node`: endocentricity — a node's head is one of its
  daughters' heads.

## Implementation notes

The tree recursion is the catamorphism `RoseTree.fold selCombine`; the algebra is
permutation-invariant (`selCombine_perm`), so invariance and the quotient lift come
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

/-- Combine two sisters' selection states. Order-independent (`selStep_comm`):
    whichever sister's head c-selects the *saturated* other projects, yielding its
    residual stack; `none` at exocentric nodes (neither or both qualify). -/
def selStep : SelState → SelState → SelState
  | some (ha, c :: rest), some (hb, []) =>
      if hb.item.outerCat = c then some (ha, rest) else none
  | some (ha, []), some (hb, c :: rest) =>
      if ha.item.outerCat = c then some (hb, rest) else none
  | _, _ => none

/-- Which daughter projects at a binary node under c-selection: `some true` = the
    **left** sister is the selector, `some false` = the **right**, `none` =
    exocentric (neither uniquely selects the saturated other). Mirrors `selStep`. -/
def selSide : SelState → SelState → Option Bool
  | some (_, c :: _), some (hb, []) => if hb.item.outerCat = c then some true else none
  | some (ha, []), some (_, c :: _) => if ha.item.outerCat = c then some false else none
  | _, _ => none

theorem selStep_comm : selStep x y = selStep y x := by
  rcases x with _ | ⟨hx, _ | ⟨cx, sx⟩⟩ <;> rcases y with _ | ⟨hy, _ | ⟨cy, sy⟩⟩ <;> rfl

theorem selSide_comm : selSide x y = (selSide y x).map Bool.not := by
  rcases x with _ | ⟨hx, _ | ⟨cx, sx⟩⟩ <;> rcases y with _ | ⟨hy, _ | ⟨cy, sy⟩⟩ <;>
    first
    | rfl
    | (simp only [selSide, Option.map]; split <;> rfl)

/-- `selStep` is the multiplication of a commutative magma on `SelState`: the
    algebraic shape [marcolli-chomsky-berwick-2025] §1.13 assigns to Merge-local
    head choice (Lemma 1.13.4's binary choice at each application of `M`). -/
instance : Mul SelState := ⟨selStep⟩

instance : CommMagma SelState := { mul_comm := selStep_comm }

variable {x y}

/-- The head of `selStep x y` (when defined) is one of `x`/`y`'s heads. -/
theorem selStep_fst {r : LIToken}
    (h : (selStep x y).map (·.1) = some r) :
    x.map (·.1) = some r ∨ y.map (·.1) = some r := by
  unfold selStep at h
  split at h
  · split_ifs at h <;> simp_all
  · split_ifs at h <;> simp_all
  · simp at h

/-- When `selStep` returns a head, that head is the projecting daughter's head, and
    `selSide` agrees on which daughter projects: the bridge between the
    residual-tracking `selStep` and the order-determining `selSide`. -/
theorem selStep_eq_some {hd : LIToken} {res : List Cat}
    (h : selStep x y = some (hd, res)) :
    (selSide x y = some true ∧ x.map (·.1) = some hd) ∨
    (selSide x y = some false ∧ y.map (·.1) = some hd) := by
  match x, y with
  | some (ha, c :: rest'), some (hb, []) =>
    simp only [selStep] at h
    by_cases hcat : hb.item.outerCat = c
    · rw [if_pos hcat] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨by simp [selSide, hcat], by simp [h.1]⟩
    · simp [if_neg hcat] at h
  | some (ha, []), some (hb, c :: rest') =>
    simp only [selStep] at h
    by_cases hcat : ha.item.outerCat = c
    · rw [if_pos hcat] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨by simp [selSide, hcat], by simp [h.1]⟩
    · simp [if_neg hcat] at h
  | some (_, []), some (_, []) | some (_, _ :: _), some (_, _ :: _) => simp [selStep] at h
  | none, _ | some _, none => simp [selStep] at h

/-! ### Selection check on the planar carrier -/

/-- The selection algebra: combine a node label with its daughters' selection
    states. Lexical leaf ↦ its token + `outerSel`; bare trace leaf ↦ canonical
    `(mkTraceToken 0, [])` (index-free); bare binary node ↦ `selStep` of the
    daughters (the `SelState` magma multiplication); other arities ↦ `none`. -/
def selCombine : SOLabel → List SelState → SelState
  | .inl tok, _     => some (tok, tok.item.outerSel)
  | .inr (), []     => some (mkTraceToken 0, [])
  | .inr (), [x, y] => x * y
  | .inr (), _      => none

/-- A daughter list of three or more has no selection value. -/
private theorem selCombine_big {l : List SelState} (h : 2 < l.length) :
    selCombine (Sum.inr ()) l = none := by
  match l with
  | _ :: _ :: _ :: _ => rfl
  | [] | [_] | [_, _] => simp at h

/-- `selCombine` is invariant under permutation of the daughter states: only the
    binary shape is order-sensitive, and there `selStep_comm` applies. -/
theorem selCombine_perm (a : SOLabel) {l₁ l₂ : List SelState} (h : l₁.Perm l₂) :
    selCombine a l₁ = selCombine a l₂ := by
  cases a with
  | inl tok => rfl
  | inr u =>
    cases u
    induction h with
    | nil => rfl
    | @cons x l₁ l₂ h _ih =>
      match l₁, l₂, h with
      | [], l₂, h => rw [show l₂ = [] from h.symm.eq_nil]
      | [y], l₂, h => rw [show l₂ = [y] from List.perm_singleton.mp h.symm]
      | _ :: _ :: _, l₂, h =>
        have hl := h.length_eq
        rw [selCombine_big (by simp +arith),
            selCombine_big (by simp only [List.length_cons] at hl ⊢; omega)]
    | swap x y l =>
      cases l with
      | nil => exact mul_comm y x
      | cons z l => rfl
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Selection check on a planar `SO`-tree: the projecting head + residual pending
    features, or `none` outside the endocentric domain — the catamorphism of
    `selCombine`. -/
def selCheckPlanar : RoseTree SOLabel → SelState :=
  RoseTree.fold selCombine

/-- Reduction of `selCheckPlanar` at a node: fold the algebra over the daughters. -/
theorem selCheckPlanar_node (a : SOLabel) (cs : List (RoseTree SOLabel)) :
    selCheckPlanar (RoseTree.node a cs) = selCombine a (cs.map selCheckPlanar) :=
  RoseTree.fold_node ..

/-- `selCheckPlanar` is `Perm`-invariant, so it descends to the quotient. -/
theorem selCheckPlanar_perm {t s : RoseTree SOLabel} (h : RoseTree.Perm t s) :
    selCheckPlanar t = selCheckPlanar s :=
  RoseTree.fold_perm (fun a _ _ h' => selCombine_perm a h') h

/-- Selection check lifted to the nonplanar carrier. -/
def selCheckN : Nonplanar SOLabel → SelState :=
  Nonplanar.lift selCheckPlanar (fun _ _ h => selCheckPlanar_perm h)

@[simp] theorem selCheckN_mk (p : RoseTree SOLabel) :
    selCheckN (Nonplanar.mk p) = selCheckPlanar p := rfl

theorem selCheckN_node (a b : Nonplanar SOLabel) :
    selCheckN (Nonplanar.node (Sum.inr ()) {a, b}) = selStep (selCheckN a) (selCheckN b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (RoseTree.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]
  show selCheckN (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = selStep (selCheckN (Nonplanar.mk pa)) (selCheckN (Nonplanar.mk pb))
  rw [key]; exact rfl

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
    (SO.node l r).selCheck = selStep l.selCheck r.selCheck := by
  show selCheckN (SO.node l r).val = selStep (selCheckN l.val) (selCheckN r.val)
  rw [SO.node_val, selCheckN_node]

@[simp] theorem SO.selHead_lexLeaf : (SO.lexLeaf tok).selHead = some tok := rfl

/-- **Endocentricity**: a node's projecting head is one of its daughters' heads —
    bare-phrase-structure projection ([chomsky-1995-bare] §4, abstracted as
    [marcolli-chomsky-berwick-2025] Definition 1.13.6 / Lemma 1.13.7). -/
theorem SO.selHead_node {l r : SO} {h : LIToken}
    (hlr : (SO.node l r).selHead = some h) : l.selHead = some h ∨ r.selHead = some h := by
  simp only [SO.selHead, SO.selCheck_node] at hlr ⊢
  exact selStep_fst hlr

@[simp] theorem SO.outerCatC_lexLeaf :
    (SO.lexLeaf tok).outerCatC = some tok.item.outerCat := rfl

/-! ### `decide` demonstration -/

/-- The selection-driven head/category reduces on a concrete `mk`-built tree: a
    determiner selecting a noun projects category `D` (built planar-first, since the
    Merge node `SO.node` is noncomputable). -/
private def demoDP : SO :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .D [.N], 0⟩) [], .node (Sum.inl ⟨.simple .N [], 1⟩) []]), by decide⟩

example : demoDP.outerCatC = some .D := by decide

end Minimalist
