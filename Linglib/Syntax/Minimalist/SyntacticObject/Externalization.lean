/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Selection
import Linglib.Syntax.Minimalist.SyntacticObject.RepOrder

/-!
# Externalization on the `SO` carrier (selection-induced order)

[marcolli-chomsky-berwick-2025] §1.12.1 / Lemma 1.13.5 / Lemma 1.13.7. P3c-1 of the
single-carrier program: the **externalization section** on the `SO` carrier, recast as
a **selection-induced planar order**. By Lemma 1.13.7 the externalization section σ_L
*is* the selection structure, so the surface order is computable, section-free, and
`PermEquiv`-liftable exactly like `selCheck` (P3a) — there is no `Quot.out` and the
`HeadFunction.section_ : FreeCommMagma.Section` field disappears on `SO`.

At a bare binary node the **projecting (selector) daughter** (computed by `selSide`,
`Selection.lean`) is placed on the language's convention side (`ConventionDir`: head-
initial vs head-final, Lemma 1.13.5). Exocentric nodes — off `Dom(h)`, where σ_L is
explicitly noncanonical — are ordered by the canonical `cmpList cmpTok` comparison
(`RepOrder.lean`), the list analogue of the legacy `smallerFirst`; this keeps the order
fully computable and `PermEquiv`-invariant.

The §1.13 **head function** on `SO` is the selection head (`SO.head := SO.selHead`,
already P3a); the head at an internal vertex `v` (a subterm) is `v.head`.

Out of scope (P3c-2 / P4): the structural **phase domain** (`phaseComplement`/
`phaseInterior`, via P2 subterms) and the flip `SyntacticObject := SO`.
-/

namespace Minimalist

open RootedTree

/-! ### Yield combinators -/

/-- Place the head daughter's yield on the convention side: `.initial` (head-initial)
    → head-yield first, `.final` (head-final) → head-yield last. The list-level
    analogue of `placeHead` (`Selection.lean`). -/
def placeYield : ConventionDir → List LIToken → List LIToken → List LIToken
  | .initial, headY, otherY => headY ++ otherY
  | .final,   headY, otherY => otherY ++ headY

/-- Exocentric tie-break ([marcolli-chomsky-berwick-2025] Lemma 1.13.5, the
    noncanonical case off `Dom(h)`): order the two yields by the canonical
    `cmpList cmpTok` comparison (`RepOrder.lean`) — the list analogue of
    `smallerFirst`. Commutative (`exoYield_comm`), so it descends to the quotient. -/
def exoYield (a b : List LIToken) : List LIToken :=
  if cmpList cmpTok a b = .gt then b ++ a else a ++ b

/-- `exoYield` is commutative: `cmpList cmpTok` is an antisymmetric strict-total
    comparison (`cmpList_swap`/`cmpList_eq`), so the choice is argument-order
    independent. Mirrors `smallerFirst_comm`. -/
theorem exoYield_comm (a b : List LIToken) : exoYield a b = exoYield b a := by
  unfold exoYield
  rw [cmpList_swap cmpTok_swap b a]
  cases hab : cmpList cmpTok a b
  · simp [Ordering.swap]
  · rw [cmpList_eq (fun _ _ => cmpTok_eq) _ _ hab]; simp [Ordering.swap]
  · simp [Ordering.swap]

/-! ### Linearization on the planar carrier -/

/-- Selection-induced externalization yield on a planar `SO`-tree
    ([marcolli-chomsky-berwick-2025] Lemma 1.13.5). A lexical leaf is pronounced
    (`[tok]`); a bare trace leaf is unpronounced (`[]`); a bare binary node places the
    projecting (selector) daughter on the `side`-convention side (`placeYield`), with
    the exocentric fallback `exoYield`. Section-free and **computable** (no `Quot.out`):
    the order is selection-determined, so it is `PermEquiv`-invariant. -/
def linearizeP (side : ConventionDir) : RoseTree SOLabel → List LIToken
  | .node (.inl tok) _     => [tok]
  | .node (.inr ()) []     => []
  | .node (.inr ()) [l, r] =>
      match selSide (selCheckPlanar l) (selCheckPlanar r) with
      | some true  => placeYield side (linearizeP side l) (linearizeP side r)
      | some false => placeYield side (linearizeP side r) (linearizeP side l)
      | none       => exoYield (linearizeP side l) (linearizeP side r)
  | .node (.inr ()) _      => []

/-- A non-binary, non-trace bare node has empty yield (1 or ≥3 children fall to the
    catch-all). The yield analogue of `selCheckPlanar_node_none`. -/
private theorem linearizeP_node_default (side : ConventionDir) {cs : List (RoseTree SOLabel)}
    (h0 : cs.length ≠ 0) (h2 : cs.length ≠ 2) :
    linearizeP side (RoseTree.node (Sum.inr ()) cs) = [] := by
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
          | none => exact exoYield_comm _ _
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
def linearizeN (side : ConventionDir) : Nonplanar SOLabel → List LIToken :=
  Nonplanar.lift (linearizeP side) (fun _ _ h => linearizeP_permEquiv side h)

@[simp] theorem linearizeN_mk (side : ConventionDir) (p : RoseTree SOLabel) :
    linearizeN side (Nonplanar.mk p) = linearizeP side p := rfl

theorem linearizeN_node (side : ConventionDir) (a b : Nonplanar SOLabel) :
    linearizeN side (Nonplanar.node (Sum.inr ()) {a, b}) =
      (match selSide (selCheckN a) (selCheckN b) with
       | some true  => placeYield side (linearizeN side a) (linearizeN side b)
       | some false => placeYield side (linearizeN side b) (linearizeN side a)
       | none       => exoYield (linearizeN side a) (linearizeN side b)) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (RoseTree.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]
  show linearizeN side (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = (match selSide (selCheckN (Nonplanar.mk pa)) (selCheckN (Nonplanar.mk pb)) with
         | some true  =>
             placeYield side (linearizeN side (Nonplanar.mk pa)) (linearizeN side (Nonplanar.mk pb))
         | some false =>
             placeYield side (linearizeN side (Nonplanar.mk pb)) (linearizeN side (Nonplanar.mk pa))
         | none       =>
             exoYield (linearizeN side (Nonplanar.mk pa)) (linearizeN side (Nonplanar.mk pb)))
  rw [key]; simp only [linearizeN_mk, linearizeP, selCheckN_mk]

/-! ### Externalization on `SO` -/

/-- **Externalization** ([marcolli-chomsky-berwick-2025] §1.12.1 / Lemma 1.13.5): the
    surface token order of a syntactic object under the head-side convention `side`.
    Selection-induced (the projecting daughter goes head-side), section-free, and
    computable — the `SO`-carrier replacement for the legacy `HeadFunction.linearize`
    (which composed `linearizePlanar` with a `Quot.out` `section_`). -/
def SO.linearize (side : ConventionDir) (s : SO) : List LIToken := linearizeN side s.val

/-- **Phonological yield**: the surface order, keeping only pronounced (non-empty
    `phonForm`) tokens. Traces, being the bare `Sum.inr ()` leaf, contribute nothing. -/
def SO.phonYield (side : ConventionDir) (s : SO) : List String :=
  (SO.linearize side s).filterMap
    (fun tok => let p := tok.phonForm; if p.isEmpty then none else some p)

/-- The §1.13 / §1.15 **head function** on `SO`: the projecting (selector) head, by
    c-selection ([marcolli-chomsky-berwick-2025] Lemma 1.13.7 = [adger-2003] "the item
    that projects is the item that selects"). This is the selection head (P3a) under
    the head-function name; the head at an internal vertex `v` (a subterm) is `v.head`. -/
def SO.head (s : SO) : Option LIToken := s.selHead

@[simp] theorem SO.linearize_lexLeaf (side : ConventionDir) (tok : LIToken) :
    (SO.lexLeaf tok).linearize side = [tok] := rfl

@[simp] theorem SO.linearize_traceLeaf (side : ConventionDir) :
    SO.traceLeaf.linearize side = [] := rfl

theorem SO.linearize_node (side : ConventionDir) (l r : SO) :
    (SO.node l r).linearize side =
      (match selSide l.selCheck r.selCheck with
       | some true  => placeYield side (l.linearize side) (r.linearize side)
       | some false => placeYield side (r.linearize side) (l.linearize side)
       | none       => exoYield (l.linearize side) (r.linearize side)) := by
  show linearizeN side (SO.node l r).val = _
  rw [SO.node_val, linearizeN_node]
  simp only [SO.selCheck, SO.linearize]

@[simp] theorem SO.head_lexLeaf (tok : LIToken) : (SO.lexLeaf tok).head = some tok := rfl

/-- **Head Feature Principle** on `SO` ([marcolli-chomsky-berwick-2025] Lemma 1.13.7 /
    [adger-2003]): a node's head is one of its daughters' heads — so the §1.15 head
    function labels each internal vertex by (the head of) the projecting daughter.
    The carrier analogue of the legacy `selHead_mul`. -/
theorem SO.head_node {l r : SO} {h : LIToken}
    (hlr : (SO.node l r).head = some h) : l.head = some h ∨ r.head = some h := by
  simp only [SO.head, SO.selHead, SO.selCheck_node] at hlr ⊢
  exact selStep_fst hlr

/-! ### `decide` demonstration

The selection-induced order reduces on concrete `mk`-built trees and the head-side
parameter genuinely flips the surface order. A determiner `the` (category `D`,
selecting `N`) over a noun `dog`: `D` projects, so head-initial yields `the dog` and
head-final yields `dog the`. -/

private def demoTheDog : SO :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

example : (demoTheDog.linearize .initial).map (·.id) = [0, 1] := by decide
example : (demoTheDog.linearize .final).map (·.id) = [1, 0] := by decide
example : demoTheDog.phonYield .initial = ["the", "dog"] := by decide
example : demoTheDog.phonYield .final = ["dog", "the"] := by decide

end Minimalist
