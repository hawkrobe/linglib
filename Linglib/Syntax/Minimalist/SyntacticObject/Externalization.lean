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
the book), c-selection (`selSide`) computes the planar order.

## Main declarations

* `Minimalist.linearizePlanar`: the yield of a planar `SO`-tree; `Option`-valued,
  `none` off `Dom(h)`.
* `Minimalist.SO.linearize`: the yield of a syntactic object, via the quotient lift
  `linearizeN`.
* `Minimalist.SO.phonYield`: the pronounced surface forms.

## Main results

* `Minimalist.linearizePlanar_permEquiv`: the yield is invariant under sibling
  permutation, hence descends to the nonplanar quotient.

## Implementation notes

Head functions are partial ([marcolli-chomsky-berwick-2025] §1.13.2): at exocentric
nodes no daughter projects and no order is determined — the book rejects inducing one
from a total order on labels as "not a realistic linguistic assumption" — so
linearization returns `none` there, matching the book's elimination of nonparsable
objects at externalization. Only the two harmonic sections are realized: uniform
head-side placement is right for head–complement structure but does not model
specifier placement (that needs the `headSide : Cat → ConventionDir` refinement noted
at `ConventionDir`).
-/

namespace Minimalist

open RootedTree

/-- Place the head daughter's yield on the convention side: `.initial` (head-initial)
    → head-yield first, `.final` (head-final) → head-yield last. -/
def placeYield : ConventionDir → List LIToken → List LIToken → List LIToken
  | .initial, headY, otherY => headY ++ otherY
  | .final,   headY, otherY => otherY ++ headY

/-! ### Linearization on the planar carrier -/

/-- Selection-induced yield of a planar `SO`-tree: a lexical leaf is pronounced, a
    bare trace leaf is silent (the cancelled `T/d` copy of
    [marcolli-chomsky-berwick-2025] §1.12), and a bare binary node places the
    projecting daughter's yield on the `side`-convention side. `none` at exocentric
    nodes (off `Dom(h)`, §1.13.2) and at bare nodes of non-`SO` arity. -/
def linearizePlanar (side : ConventionDir) : RoseTree SOLabel → Option (List LIToken)
  | .node (.inl tok) _     => some [tok]
  | .node (.inr ()) []     => some []
  | .node (.inr ()) [l, r] =>
      match selSide (selCheckPlanar l) (selCheckPlanar r) with
      | some true  =>
          Option.map₂ (placeYield side) (linearizePlanar side l) (linearizePlanar side r)
      | some false =>
          Option.map₂ (placeYield side) (linearizePlanar side r) (linearizePlanar side l)
      | none       => none
  | .node (.inr ()) _      => none

/-- A bare node with more than two children is not an `SO` shape and has no yield. -/
private theorem linearizePlanar_node_big (side : ConventionDir)
    {cs : List (RoseTree SOLabel)} (h : 2 < cs.length) :
    linearizePlanar side (RoseTree.node (Sum.inr ()) cs) = none := by
  match cs with
  | _ :: _ :: _ :: _ => rfl
  | [] | [_] | [_, _] => simp at h

private theorem linearizePlanar_permStep (side : ConventionDir) {t s : RoseTree SOLabel}
    (hstep : RoseTree.PermStep t s) :
    linearizePlanar side t = linearizePlanar side s := by
  induction hstep with
  | @swapAtRoot a l r pre post =>
    cases a with
    | inl _ => simp only [linearizePlanar]
    | inr u =>
      cases u
      match pre, post with
      | [], [] =>
        simp only [List.nil_append, linearizePlanar,
          selSide_comm (selCheckPlanar r) (selCheckPlanar l)]
        cases selSide (selCheckPlanar l) (selCheckPlanar r) with
        | none => rfl
        | some b => cases b <;> rfl
      | [], _ :: _ | _ :: _, _ =>
        rw [linearizePlanar_node_big side (by simp +arith),
            linearizePlanar_node_big side (by simp +arith)]
  | @recurse a pre old new post _hstep ih =>
    cases a with
    | inl _ => simp only [linearizePlanar]
    | inr u =>
      cases u
      have hsc : selCheckPlanar old = selCheckPlanar new :=
        selCheckPlanar_permEquiv (RoseTree.PermEquiv.of_step _hstep)
      match pre, post with
      | [], [] => simp only [List.nil_append, linearizePlanar]
      | [], [_] => simp only [List.nil_append, linearizePlanar, hsc, ih]
      | [_], [] => simp only [List.cons_append, List.nil_append, linearizePlanar, hsc, ih]
      | [], _ :: _ :: _ | [_], _ :: _ | _ :: _ :: _, _ =>
        rw [linearizePlanar_node_big side (by simp +arith),
            linearizePlanar_node_big side (by simp +arith)]

/-- `linearizePlanar side` is `PermEquiv`-invariant, so it descends to the quotient:
    the surface order is projection-determined, not representative-determined. -/
theorem linearizePlanar_permEquiv (side : ConventionDir) {t s : RoseTree SOLabel}
    (h : RoseTree.PermEquiv t s) : linearizePlanar side t = linearizePlanar side s :=
  RoseTree.PermEquiv.lift_eq (fun _ _ h' => linearizePlanar_permStep side h') h

/-- Linearization lifted to the nonplanar carrier. -/
def linearizeN (side : ConventionDir) : Nonplanar SOLabel → Option (List LIToken) :=
  Nonplanar.lift (linearizePlanar side) (fun _ _ h => linearizePlanar_permEquiv side h)

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
  rw [key]; simp only [linearizeN_mk, linearizePlanar, selCheckN_mk]

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
