/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Option.NAry
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Externalization on the `SO` carrier

This file defines the selection-induced linearization of syntactic objects
([marcolli-chomsky-berwick-2025] §1.12.1, §1.13): the surface token order obtained by
placing the projecting daughter's yield on a language's harmonic head side. Lemma
1.13.5 identifies head functions on a binary tree with its planar embeddings, and
Lemma 1.13.7 identifies head functions with bare-phrase-structure projection
([chomsky-1995-bare]); composed with [adger-2003]'s identification of the projecting
item as the selecting item (a synthesis step of this formalization, not a claim of
the book), c-selection computes the planar order.

## Main declarations

* `Minimalist.linCombine`: the externalization algebra — selection state and yield
  computed together, the book's two descriptions of a head function.
* `Minimalist.linearizePlanar`: the yield of a planar `SO`-tree; `Option`-valued,
  `none` off `Dom(h)`.
* `Minimalist.SO.linearize`: the yield of a syntactic object, via the quotient lift
  `linearizeN`.
* `Minimalist.SO.phonYield`: the pronounced surface forms.

## Main results

* `Minimalist.selLinPlanar_fst`: the paired fold's selection component is
  `selCheckPlanar`.
* `Minimalist.linearizePlanar_perm`: the yield descends to the nonplanar
  quotient — by `RoseTree.fold_perm`, since the algebra is
  permutation-invariant (`linCombine_perm`).

## Implementation notes

Head functions are partial ([marcolli-chomsky-berwick-2025] §1.13.2): at exocentric
nodes no daughter projects and no order is determined — the book rejects inducing one
from a total order on labels as "not a realistic linguistic assumption" — so
linearization returns `none` there, matching the book's elimination of nonparsable
objects at externalization. Only the two harmonic sections are realized: uniform
head-side placement is right for head–complement structure but does not model
specifier placement (that needs the `headSide : Cat → ConventionDir` refinement noted
at `ConventionDir`).

Linearization is the second component of one catamorphism `RoseTree.fold`, mirroring
the book's switching "between these two descriptions without changing the notation":
the head function as a head leaf (selection state) and as the ordered leaf sequence
(yield). All `Perm`-invariance is inherited from the algebra's
permutation-invariance; there is no bespoke step induction.
-/

namespace Minimalist

open RootedTree

/-- Place the head daughter's yield on the convention side: `.initial` (head-initial)
    → head-yield first, `.final` (head-final) → head-yield last. -/
def placeYield : ConventionDir → List LIToken → List LIToken → List LIToken
  | .initial, headY, otherY => headY ++ otherY
  | .final,   headY, otherY => otherY ++ headY

/-! ### The externalization algebra -/

/-- The externalization algebra: a node's selection state (`selCombine` over the
    daughters' states) paired with its yield. A lexical leaf is pronounced, a bare
    trace leaf is silent (the cancelled `T/d` copy of [marcolli-chomsky-berwick-2025]
    §1.12), and a bare binary node places the projecting daughter's yield on the
    `side`-convention side; the yield is `none` at exocentric nodes (off `Dom(h)`,
    §1.13.2) and at bare nodes of non-`SO` arity. -/
def linCombine (side : ConventionDir) (a : SOLabel)
    (ps : List (Option (LIToken × List Cat) × Option (List LIToken))) :
    Option (LIToken × List Cat) × Option (List LIToken) :=
  (selCombine a (ps.map Prod.fst),
   match a, ps with
   | .inl tok, _ => some [tok]
   | .inr (), [] => some []
   | .inr (), [(cl, yl), (cr, yr)] =>
       match selSide cl cr with
       | some true  => Option.map₂ (placeYield side) yl yr
       | some false => Option.map₂ (placeYield side) yr yl
       | none       => none
   | .inr (), _ => none)

/-- A daughter list of three or more has no yield. -/
private theorem linCombine_snd_big (side : ConventionDir)
    {ps : List (Option (LIToken × List Cat) × Option (List LIToken))}
    (h : 2 < ps.length) : (linCombine side (Sum.inr ()) ps).2 = none := by
  match ps with
  | _ :: _ :: _ :: _ => rfl
  | [] | [_] | [_, _] => simp at h

/-- `linCombine` is invariant under permutation of the daughter values: the selection
    component by `selCombine_perm`, the yield because only the binary shape is
    order-sensitive, where `selSide_comm` swaps the placement decision with the
    arguments. -/
theorem linCombine_perm (side : ConventionDir) (a : SOLabel)
    {l₁ l₂ : List (Option (LIToken × List Cat) × Option (List LIToken))}
    (h : l₁.Perm l₂) : linCombine side a l₁ = linCombine side a l₂ := by
  refine Prod.ext (selCombine_perm a (h.map Prod.fst)) ?_
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
        rw [linCombine_snd_big side (by simp +arith),
            linCombine_snd_big side (by
              have hl := h.length_eq
              simp only [List.length_cons] at hl ⊢
              omega)]
    | swap x y l =>
      cases l with
      | nil =>
        obtain ⟨cx, yx⟩ := x
        obtain ⟨cy, yy⟩ := y
        show (match selSide cy cx with
              | some true  => Option.map₂ (placeYield side) yy yx
              | some false => Option.map₂ (placeYield side) yx yy
              | none       => none)
           = (match selSide cx cy with
              | some true  => Option.map₂ (placeYield side) yx yy
              | some false => Option.map₂ (placeYield side) yy yx
              | none       => none)
        rw [selSide_comm cy cx]
        cases selSide cx cy with
        | none => rfl
        | some b => cases b <;> rfl
      | cons z l => rfl
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Linearization on the planar carrier -/

/-- Selection state and yield of a planar `SO`-tree, computed together:
    [marcolli-chomsky-berwick-2025]'s dual description of a head function as a head
    leaf and as an ordered leaf sequence. -/
def selLinPlanar (side : ConventionDir) :
    RoseTree SOLabel → Option (LIToken × List Cat) × Option (List LIToken) :=
  RoseTree.fold (linCombine side)

/-- Selection-induced yield of a planar `SO`-tree: the yield component of
    `selLinPlanar`. -/
def linearizePlanar (side : ConventionDir) (t : RoseTree SOLabel) :
    Option (List LIToken) :=
  (selLinPlanar side t).2

/-- Fusion: the selection component of the paired fold is `selCheckPlanar`. -/
theorem selLinPlanar_fst (side : ConventionDir) (t : RoseTree SOLabel) :
    (selLinPlanar side t).1 = selCheckPlanar t := by
  induction t with
  | node a cs ih =>
    show (RoseTree.fold (linCombine side) (.node a cs)).1 = selCheckPlanar (.node a cs)
    rw [RoseTree.fold_node, selCheckPlanar_node]
    show selCombine a ((cs.map (RoseTree.fold (linCombine side))).map Prod.fst)
       = selCombine a (cs.map selCheckPlanar)
    rw [List.map_map]
    exact congrArg (selCombine a) (List.map_congr_left fun c hc => ih c hc)

/-- Reduction of the yield at a bare binary node, through the fusion theorem. -/
theorem linearizePlanar_node_pair (side : ConventionDir) (l r : RoseTree SOLabel) :
    linearizePlanar side (.node (.inr ()) [l, r]) =
      (match selSide (selCheckPlanar l) (selCheckPlanar r) with
       | some true  =>
           Option.map₂ (placeYield side) (linearizePlanar side l) (linearizePlanar side r)
       | some false =>
           Option.map₂ (placeYield side) (linearizePlanar side r) (linearizePlanar side l)
       | none       => none) := by
  show (match selSide (selLinPlanar side l).1 (selLinPlanar side r).1 with
        | some true  =>
            Option.map₂ (placeYield side) (selLinPlanar side l).2 (selLinPlanar side r).2
        | some false =>
            Option.map₂ (placeYield side) (selLinPlanar side r).2 (selLinPlanar side l).2
        | none       => none) = _
  rw [selLinPlanar_fst side l, selLinPlanar_fst side r]; exact rfl

/-- `linearizePlanar side` descends to the quotient: the surface order is
    projection-determined, not representative-determined. -/
theorem linearizePlanar_perm (side : ConventionDir) {t s : RoseTree SOLabel}
    (h : RoseTree.Perm t s) : linearizePlanar side t = linearizePlanar side s :=
  congrArg Prod.snd
    (RoseTree.fold_perm (fun a _ _ h' => linCombine_perm side a h') h)

/-- Linearization lifted to the nonplanar carrier. -/
def linearizeN (side : ConventionDir) : Nonplanar SOLabel → Option (List LIToken) :=
  Nonplanar.lift (linearizePlanar side) (fun _ _ h => linearizePlanar_perm side h)

@[simp] theorem linearizeN_mk (side : ConventionDir) (p : RoseTree SOLabel) :
    linearizeN side (Nonplanar.mk p) = linearizePlanar side p := rfl

theorem linearizeN_node (side : ConventionDir) (a b : Nonplanar SOLabel) :
    linearizeN side (Nonplanar.node (Sum.inr ()) {a, b}) =
      (match selSide (selCheckN a) (selCheckN b) with
       | some true  => Option.map₂ (placeYield side) (linearizeN side a) (linearizeN side b)
       | some false => Option.map₂ (placeYield side) (linearizeN side b) (linearizeN side a)
       | none       => none) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (RoseTree.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]
  show linearizeN side (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = (match selSide (selCheckN (Nonplanar.mk pa)) (selCheckN (Nonplanar.mk pb)) with
         | some true  =>
             Option.map₂ (placeYield side)
               (linearizeN side (Nonplanar.mk pa)) (linearizeN side (Nonplanar.mk pb))
         | some false =>
             Option.map₂ (placeYield side)
               (linearizeN side (Nonplanar.mk pb)) (linearizeN side (Nonplanar.mk pa))
         | none       => none)
  rw [key]
  simp only [linearizeN_mk, selCheckN_mk, linearizePlanar_node_pair]

/-! ### Externalization on `SO` -/

/-- The surface token order of a syntactic object under the head-side convention
    `side` ([marcolli-chomsky-berwick-2025] §1.12.1): the selection-induced harmonic
    candidate for the externalization section σ_L, defined on `Dom(h)` only — the
    book's σ_L must extend it *noncanonically* off `Dom(h)`. -/
def SO.linearize (side : ConventionDir) (s : SO) : Option (List LIToken) :=
  linearizeN side s.val

/-- The pronounced surface forms: the yield with unpronounced (empty-`phonForm`)
    tokens dropped. Traces, being the bare `Sum.inr ()` leaf, contribute nothing. -/
def SO.phonYield (side : ConventionDir) (s : SO) : Option (List String) :=
  (SO.linearize side s).map (·.filterMap LIToken.phonForm?)

@[simp] theorem SO.linearize_lexLeaf (side : ConventionDir) (tok : LIToken) :
    (SO.lexLeaf tok).linearize side = some [tok] := rfl

@[simp] theorem SO.linearize_traceLeaf (side : ConventionDir) :
    SO.traceLeaf.linearize side = some [] := rfl

theorem SO.linearize_node (side : ConventionDir) (l r : SO) :
    (SO.node l r).linearize side =
      (match selSide l.selCheck r.selCheck with
       | some true  => Option.map₂ (placeYield side) (l.linearize side) (r.linearize side)
       | some false => Option.map₂ (placeYield side) (r.linearize side) (l.linearize side)
       | none       => none) := by
  show linearizeN side (SO.node l r).val = _
  rw [SO.node_val, linearizeN_node]
  simp only [SO.selCheck, SO.linearize]

/-! ### `decide` demonstration

The order reduces on concrete `mk`-built trees, the head-side parameter flips it, and
exocentric Merge is order-undefined. -/

/-- A determiner (category `D`, selecting `N`) over a noun: `D` projects, so
    head-initial yields `the dog` and head-final yields `dog the`. -/
private def demoTheDog : SO :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

example : (demoTheDog.linearize .initial).map (·.map (·.id)) = some [0, 1] := by decide
example : (demoTheDog.linearize .final).map (·.map (·.id)) = some [1, 0] := by decide
example : demoTheDog.phonYield .initial = some ["the", "dog"] := by decide
example : demoTheDog.phonYield .final = some ["dog", "the"] := by decide

/-- Exocentric Merge — two saturated `N`s, neither selecting the other — determines
    no head and hence no order: linearization is undefined off `Dom(h)`. -/
private def demoExo : SO :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .N [] (phonForm := "cats"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dogs"), 1⟩) []]), by decide⟩

example : demoExo.linearize .initial = none := by decide
example : demoExo.linearize .final = none := by decide

end Minimalist
