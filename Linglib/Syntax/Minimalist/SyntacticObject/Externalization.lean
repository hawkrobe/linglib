/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Option.NAry
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Externalization on the `SO` carrier (selection-induced order)

[marcolli-chomsky-berwick-2025] §1.12.1 and §1.13: externalization sends the unordered
syntactic object through a planar embedding to a surface token string. Lemma 1.13.5
identifies the head functions on a binary tree with its planar embeddings — read off
harmonically head-initial or head-final (`ConventionDir`) — and Lemma 1.13.7 identifies
abstract head functions with bare-phrase-structure projection ([chomsky-1995-bare]).
This file composes the two with [adger-2003]'s identification of the projecting item
as the selecting item (a synthesis step of the formalization, not a claim of the book):
c-selection (`selSide`, `Selection.lean`) picks the projecting daughter, so the induced
planar order — hence the linearization — is computable and `PermEquiv`-invariant.

Head functions are **partial** ([marcolli-chomsky-berwick-2025] §1.13.2–§1.13.3): at
exocentric nodes, off `Dom(h)`, no daughter projects and no order is determined — the
book rejects inducing one from a total order on labels as "not a realistic linguistic
assumption". `linearizeP` is therefore `Option`-valued, `none` off `Dom(h)`, matching
the book's elimination of nonparsable objects at externalization. Only the two
*harmonic* sections are realized: uniform head-side placement is right for
head–complement structure but does not model specifier placement; mixed placement
needs the `headSide : Cat → ConventionDir` refinement noted at `ConventionDir`.
-/

namespace Minimalist

open RootedTree

/-! ### Yield combinator -/

/-- Place the head daughter's yield on the convention side: `.initial` (head-initial)
    → head-yield first, `.final` (head-final) → head-yield last. -/
def placeYield : ConventionDir → List LIToken → List LIToken → List LIToken
  | .initial, headY, otherY => headY ++ otherY
  | .final,   headY, otherY => otherY ++ headY

/-! ### Linearization on the planar carrier -/

/-- Selection-induced externalization yield on a planar `SO`-tree: a lexical leaf is
    pronounced (`some [tok]`), a bare trace leaf is unpronounced (`some []`, the
    cancelled copy of [marcolli-chomsky-berwick-2025]'s `T/d` form), and a bare binary
    node places the projecting (selector) daughter's yield on the `side`-convention
    side. Partial: `none` at exocentric nodes (off `Dom(h)` no order is determined,
    §1.13.2) and at bare nodes of non-`SO` arity. -/
def linearizeP (side : ConventionDir) : RoseTree SOLabel → Option (List LIToken)
  | .node (.inl tok) _     => some [tok]
  | .node (.inr ()) []     => some []
  | .node (.inr ()) [l, r] =>
      match selSide (selCheckPlanar l) (selCheckPlanar r) with
      | some true  => Option.map₂ (placeYield side) (linearizeP side l) (linearizeP side r)
      | some false => Option.map₂ (placeYield side) (linearizeP side r) (linearizeP side l)
      | none       => none
  | .node (.inr ()) _      => none

/-- A bare node of arity 1 or ≥ 3 is not an `SO` shape and has no yield. The yield
    analogue of `selCheckPlanar_node_none`. -/
private theorem linearizeP_node_default (side : ConventionDir) {cs : List (RoseTree SOLabel)}
    (h0 : cs.length ≠ 0) (h2 : cs.length ≠ 2) :
    linearizeP side (RoseTree.node (Sum.inr ()) cs) = none := by
  match cs with
  | [] => exact absurd rfl h0
  | [_] => rfl
  | [_, _] => exact absurd rfl h2
  | _ :: _ :: _ :: _ => rfl

private theorem linearizeP_permStep (side : ConventionDir) {t s : RoseTree SOLabel}
    (hstep : RoseTree.PermStep t s) : linearizeP side t = linearizeP side s := by
  induction hstep with
  | @swapAtRoot a l r pre post =>
    cases a with
    | inl _ => simp only [linearizeP]
    | inr u =>
      cases u
      cases pre with
      | nil => cases post with
        | nil =>
          simp only [List.nil_append, linearizeP,
            selSide_comm (selCheckPlanar r) (selCheckPlanar l)]
          cases selSide (selCheckPlanar l) (selCheckPlanar r) with
          | none => rfl
          | some b => cases b <;> rfl
        | cons c cs =>
          have h2 : ([] ++ l :: r :: c :: cs).length ≠ 2 := by
            simp only [List.nil_append, List.length_cons]; omega
          have h2' : ([] ++ r :: l :: c :: cs).length ≠ 2 := by
            simp only [List.nil_append, List.length_cons]; omega
          rw [linearizeP_node_default side (by simp) h2,
              linearizeP_node_default side (by simp) h2']
      | cons q qs =>
        have h2 : ((q :: qs) ++ l :: r :: post).length ≠ 2 := by
          simp only [List.length_append, List.length_cons]; omega
        have h2' : ((q :: qs) ++ r :: l :: post).length ≠ 2 := by
          simp only [List.length_append, List.length_cons]; omega
        rw [linearizeP_node_default side (by simp) h2,
            linearizeP_node_default side (by simp) h2']
  | @recurse a pre old new post _hstep ih =>
    cases a with
    | inl _ => simp only [linearizeP]
    | inr u =>
      cases u
      have hsc : selCheckPlanar old = selCheckPlanar new :=
        selCheckPlanar_permEquiv (RoseTree.PermEquiv.of_step _hstep)
      cases pre with
      | nil => cases post with
        | nil => simp only [List.nil_append, linearizeP]
        | cons c cs => cases cs with
          | nil => simp only [List.nil_append, linearizeP, hsc, ih]
          | cons d ds => simp only [List.nil_append, linearizeP]
      | cons q qs => cases qs with
        | nil => cases post with
          | nil => simp only [List.cons_append, List.nil_append, linearizeP, hsc, ih]
          | cons d ds => simp only [List.cons_append, List.nil_append, linearizeP]
        | cons q2 qs2 =>
          have h2 : ((q :: q2 :: qs2) ++ old :: post).length ≠ 2 := by
            simp only [List.length_append, List.length_cons]; omega
          have h2' : ((q :: q2 :: qs2) ++ new :: post).length ≠ 2 := by
            simp only [List.length_append, List.length_cons]; omega
          rw [linearizeP_node_default side (by simp) h2,
              linearizeP_node_default side (by simp) h2']

/-- `linearizeP side` is `PermEquiv`-invariant, so it descends to the quotient: the
    surface order is projection-determined, not representative-position-determined. -/
theorem linearizeP_permEquiv (side : ConventionDir) {t s : RoseTree SOLabel}
    (h : RoseTree.PermEquiv t s) : linearizeP side t = linearizeP side s := by
  induction h with
  | rel _ _ hstep => exact linearizeP_permStep side hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Linearization lifted to the nonplanar carrier. -/
def linearizeN (side : ConventionDir) : Nonplanar SOLabel → Option (List LIToken) :=
  Nonplanar.lift (linearizeP side) (fun _ _ h => linearizeP_permEquiv side h)

@[simp] theorem linearizeN_mk (side : ConventionDir) (p : RoseTree SOLabel) :
    linearizeN side (Nonplanar.mk p) = linearizeP side p := rfl

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
  rw [key]; simp only [linearizeN_mk, linearizeP, selCheckN_mk]

/-! ### Externalization on `SO` -/

/-- **Externalization** ([marcolli-chomsky-berwick-2025] §1.12.1): the surface token
    order of a syntactic object under the head-side convention `side` — the
    selection-induced harmonic candidate for the externalization section σ_L, defined
    on `Dom(h)` only; the book's σ_L must extend it *noncanonically* off `Dom(h)`,
    so exocentric structure yields `none` here. -/
def SO.linearize (side : ConventionDir) (s : SO) : Option (List LIToken) :=
  linearizeN side s.val

/-- **Phonological yield**: the surface order, keeping only pronounced (non-empty
    `phonForm`) tokens. Traces, being the bare `Sum.inr ()` leaf, contribute nothing. -/
def SO.phonYield (side : ConventionDir) (s : SO) : Option (List String) :=
  (SO.linearize side s).map
    (·.filterMap fun tok => let p := tok.phonForm; if p.isEmpty then none else some p)

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

The selection-induced order reduces on concrete `mk`-built trees, the head-side
parameter genuinely flips the surface order, and exocentric Merge is correctly
order-undefined. A determiner `the` (category `D`, selecting `N`) over a noun `dog`:
`D` projects, so head-initial yields `the dog` and head-final yields `dog the`. -/

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
