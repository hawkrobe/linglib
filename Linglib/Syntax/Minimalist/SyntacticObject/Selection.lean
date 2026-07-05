/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Linglib.Syntax.Minimalist.SyntacticObject.Lift

/-!
# Selection-driven heads on the `SyntacticObject` carrier

This file defines the c-selection head of a syntactic object: whichever sister's
head selects the saturated other projects — [adger-2003]'s identification of the
projecting item with the selecting item, instantiating the bare-phrase-structure
projection ([chomsky-1995-bare] §4) that [marcolli-chomsky-berwick-2025] §1.13.3
abstracts as head functions (Definition 1.13.6 / Lemma 1.13.7). Like the book's
head functions it is partial: `0` at exocentric nodes.

## Main declarations

* `Minimalist.SelectionState`: a constituent's selection state — the projecting
  head with its residual selectional stack; a `CommMagma` and `MulZeroClass`, with
  `0` the off-`Dom(h)` failure.
* `Mul SelectionState` and `Minimalist.selSide`: the carrier-free combinators —
  the selection product, and which daughter projects.
* `Minimalist.selNode`, `Minimalist.selCheckPlanar`,
  `Minimalist.SyntacticObject.selCheck`: the selection algebra
  (`SyntacticObject.mergeAlgebra`), its catamorphism, and the carrier lift.
* `Minimalist.SyntacticObject.selHead`, `Minimalist.SyntacticObject.outerCatC`:
  the head token and its outer category — the foundation the Phase API consumes
  (`isPhaseHeadOf`).
* `Minimalist.selCheckHom`: `selCheck` as a morphism of magmas
  `SyntacticObject →ₙ* SelectionState`, via `SyntacticObject.lift`.

## Main results

* `mul_comm` (via `CommMagma SelectionState`) and `Minimalist.selSide_comm`:
  order-independence — the formal content of Merge's unordered output.
* `Minimalist.SyntacticObject.selHead_node`: endocentricity — a node's head is one
  of its daughters' heads.

## Implementation notes

`SelectionState` is a one-field structure over `Option (LIToken × List Cat)`: the
`Option` is implementation, `0` is the public spelling of the exocentric failure —
the absorbing element of [marcolli-chomsky-berwick-2025]'s renormalization reading
of partial head functions (off-domain values as the "meaningless infinities" of
computation, their §1.13.2 remark). No `One` (two saturated states multiply to
`0` — exocentricity is a zero divisor) and no associativity claim, so the
structure is `CommMagma` + `MulZeroClass` only. **Index-free traces**: a bare
trace leaf gets the canonical saturated value `.of (mkTraceToken 0) []`;
`selCheck` reads only the token's category and `outerSel`, both index-independent.
-/

namespace Minimalist

open RootedTree

/-! ### The selection state -/

/-- A constituent's selection state: the projecting head with its residual stack
    (`.of tok []` = saturated), `0` off the endocentric domain. -/
structure SelectionState : Type where
  toOption : Option (LIToken × List Cat)
deriving DecidableEq

/-- A defined selection state: projecting head `tok` with residual stack `stack`. -/
def SelectionState.of (tok : LIToken) (stack : List Cat) : SelectionState :=
  ⟨some (tok, stack)⟩

instance : Zero SelectionState := ⟨⟨none⟩⟩

/-- The projecting head token; `none` off the endocentric domain. -/
def SelectionState.head (x : SelectionState) : Option LIToken := x.toOption.map (·.1)

/-- The residual selectional stack (`some []` = saturated). -/
def SelectionState.residual (x : SelectionState) : Option (List Cat) := x.toOption.map (·.2)

@[simp] theorem SelectionState.head_of (tok : LIToken) (stack : List Cat) :
    (SelectionState.of tok stack).head = some tok := rfl

@[simp] theorem SelectionState.head_zero : (0 : SelectionState).head = none := rfl

/-! ### Carrier-free selection combinators -/

variable (x y : SelectionState)

/-- The selection decision at a binary node — (which sister projects, head,
    residual), `none` at exocentric nodes; `*` and `selSide` are its projections. -/
def selCombine : SelectionState → SelectionState → Option (Bool × LIToken × List Cat)
  | ⟨some (ha, c :: rest)⟩, ⟨some (hb, [])⟩ =>
      if hb.item.outerCat = c then some (true, ha, rest) else none
  | ⟨some (ha, [])⟩, ⟨some (hb, c :: rest)⟩ =>
      if ha.item.outerCat = c then some (false, hb, rest) else none
  | _, _ => none

/-- Which daughter projects: `some true` = left, `some false` = right. -/
def selSide (x y : SelectionState) : Option Bool := (selCombine x y).map (·.1)

/-- Swapping the sisters flips the side and keeps the head and residual. -/
theorem selCombine_comm : selCombine x y = (selCombine y x).map fun p => (!p.1, p.2) := by
  rcases x with ⟨_ | ⟨hx, _ | ⟨cx, sx⟩⟩⟩ <;> rcases y with ⟨_ | ⟨hy, _ | ⟨cy, sy⟩⟩⟩ <;>
    first
    | rfl
    | (simp only [selCombine, Option.map]; split <;> rfl)

/-- S₂-equivariance: swap acts on the sisters, `Bool.not` on the side — MCB's
    per-vertex edge-marking (Lemma 1.13.4). -/
theorem selSide_comm : selSide x y = (selSide y x).map Bool.not := by
  simp only [selSide, selCombine_comm x y, Option.map_map]; rfl

/-- The selection product: the head-and-residual of the `selCombine` decision
    ([marcolli-chomsky-berwick-2025] §1.13); `0` is absorbing. -/
instance : MulZeroClass SelectionState where
  mul x y := ⟨(selCombine x y).map (·.2)⟩
  zero := ⟨none⟩
  zero_mul _ := rfl
  mul_zero x := by rcases x with ⟨_ | ⟨h, _ | ⟨c, s⟩⟩⟩ <;> rfl

/-- `*` unfolded: the canonical accessor for the selection product. -/
theorem SelectionState.mul_def : x * y = ⟨(selCombine x y).map (·.2)⟩ := rfl

instance : CommMagma SelectionState where
  mul_comm x y := by
    simp only [SelectionState.mul_def, selCombine_comm x y, Option.map_map]; rfl

/-- Exocentricity is a zero divisor: two saturated nonzero states multiply to `0`. -/
example : ∃ x y : SelectionState, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 :=
  ⟨.of (mkTraceToken 0) [], .of (mkTraceToken 0) [], by decide⟩

variable {x y}

/-- Coherence: the projected head is the head of the sister on the reported side. -/
theorem selCombine_eq_some {b : Bool} {hd : LIToken} {res : List Cat}
    (h : selCombine x y = some (b, hd, res)) :
    (bif b then x else y).head = some hd := by
  match x, y with
  | ⟨some (ha, c :: rest')⟩, ⟨some (hb, [])⟩
  | ⟨some (ha, [])⟩, ⟨some (hb, c :: rest')⟩ =>
    simp only [selCombine] at h
    split_ifs at h; cases h; rfl
  | ⟨some (_, [])⟩, ⟨some (_, [])⟩ | ⟨some (_, _ :: _)⟩, ⟨some (_, _ :: _)⟩
  | ⟨none⟩, _ | ⟨some _⟩, ⟨none⟩ => simp [selCombine] at h

/-- The head of `x * y` (when defined) is one of `x`/`y`'s heads. -/
theorem SelectionState.head_mul {r : LIToken}
    (h : (x * y).head = some r) : x.head = some r ∨ y.head = some r := by
  simp only [SelectionState.mul_def, SelectionState.head, Option.map_map,
    Option.map_eq_some_iff] at h
  obtain ⟨⟨b, _, _⟩, hproj, rfl⟩ := h
  cases b
  exacts [Or.inr (selCombine_eq_some hproj), Or.inl (selCombine_eq_some hproj)]

/-! ### Selection check on the carriers -/

/-- The selection algebra: the `SyntacticObject.mergeAlgebra` of token + `outerSel`
    leaves and the saturated, index-free trace. -/
def selNode : SOLabel → List SelectionState → SelectionState :=
  SyntacticObject.mergeAlgebra (fun tok => .of tok tok.item.outerSel)
    (.of (mkTraceToken 0) [])

/-- `selNode` is invariant under permutation of the daughter states. -/
theorem selNode_perm (a : SOLabel) {l₁ l₂ : List SelectionState} (h : l₁.Perm l₂) :
    selNode a l₁ = selNode a l₂ :=
  SyntacticObject.mergeAlgebra_perm _ _ a h

/-- Selection check on a planar tree: the catamorphism of `selNode`. -/
def selCheckPlanar : RoseTree SOLabel → SelectionState :=
  RoseTree.fold selNode

/-- Reduction of `selCheckPlanar` at a node: fold the algebra over the daughters. -/
theorem selCheckPlanar_node (a : SOLabel) (cs : List (RoseTree SOLabel)) :
    selCheckPlanar (RoseTree.node a cs) = selNode a (cs.map selCheckPlanar) :=
  RoseTree.fold_node ..

/-- `selCheckPlanar` is `Perm`-invariant, so it descends to the quotient. -/
theorem selCheckPlanar_perm {t s : RoseTree SOLabel} (h : RoseTree.Perm t s) :
    selCheckPlanar t = selCheckPlanar s :=
  RoseTree.fold_perm (fun a _ _ h' => selNode_perm a h') h

/-- Selection check on the nonplanar carrier. -/
def selCheckN : Nonplanar SOLabel → SelectionState :=
  SyntacticObject.liftN (fun tok => .of tok tok.item.outerSel) (.of (mkTraceToken 0) [])

@[simp] theorem selCheckN_mk (p : RoseTree SOLabel) :
    selCheckN (Nonplanar.mk p) = selCheckPlanar p := rfl

theorem selCheckN_node (a b : Nonplanar SOLabel) :
    selCheckN (Nonplanar.node (Sum.inr ()) {a, b}) = selCheckN a * selCheckN b :=
  SyntacticObject.liftN_node _ _ a b

/-! ### The selection-driven head on `SyntacticObject` -/

variable (s : SyntacticObject) (tok : LIToken)

/-- **Selection-driven head check**: the selection instance of
    [marcolli-chomsky-berwick-2025]'s head functions; computable. -/
def SyntacticObject.selCheck : SelectionState := selCheckN s.val

/-- The projecting head's lexical item, by c-selection. -/
def SyntacticObject.selHead : Option LIToken := s.selCheck.head

/-- Residual pending selectional features (`some []` = saturated). -/
def SyntacticObject.checkedSel : Option (List Cat) := s.selCheck.residual

/-- The projecting head's **outer category** (the phase-head selector); `none` at
    exocentric nodes. -/
def SyntacticObject.outerCatC : Option Cat := s.selHead.map (·.item.outerCat)

@[simp] theorem SyntacticObject.selCheck_lexLeaf :
    (SyntacticObject.lexLeaf tok).selCheck = .of tok tok.item.outerSel := rfl

@[simp] theorem SyntacticObject.selCheck_traceLeaf :
    SyntacticObject.traceLeaf.selCheck = .of (mkTraceToken 0) [] := rfl

@[simp] theorem SyntacticObject.selCheck_node (l r : SyntacticObject) :
    (SyntacticObject.node l r).selCheck = l.selCheck * r.selCheck :=
  SyntacticObject.liftFun_node _ _ l r

/-- `selCheck` as a morphism of magmas ([marcolli-chomsky-berwick-2025] §1.13's
    algebraic frame): the `SyntacticObject.lift` of the leaf data. -/
noncomputable def selCheckHom : SyntacticObject →ₙ* SelectionState :=
  SyntacticObject.lift (fun tok => .of tok tok.item.outerSel) (.of (mkTraceToken 0) [])

@[simp] theorem selCheckHom_apply : selCheckHom s = s.selCheck := rfl

@[simp] theorem SyntacticObject.selHead_lexLeaf :
    (SyntacticObject.lexLeaf tok).selHead = some tok := rfl

/-- **Endocentricity**: a node's projecting head is one of its daughters' heads —
    bare-phrase-structure projection ([chomsky-1995-bare] §4, abstracted as
    [marcolli-chomsky-berwick-2025] Definition 1.13.6 / Lemma 1.13.7). -/
theorem SyntacticObject.selHead_node {l r : SyntacticObject} {h : LIToken}
    (hlr : (SyntacticObject.node l r).selHead = some h) :
    l.selHead = some h ∨ r.selHead = some h := by
  simp only [SyntacticObject.selHead, SyntacticObject.selCheck_node] at hlr ⊢
  exact SelectionState.head_mul hlr

@[simp] theorem SyntacticObject.outerCatC_lexLeaf :
    (SyntacticObject.lexLeaf tok).outerCatC = some tok.item.outerCat := rfl

end Minimalist
