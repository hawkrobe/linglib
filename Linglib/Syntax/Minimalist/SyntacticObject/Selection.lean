/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject
import Linglib.Syntax.Minimalist.Selection

/-!
# The selection-driven head on the `SO` carrier

[marcolli-chomsky-berwick-2025] §1.13 (Lemma 1.13.7). P3a of the single-carrier
program: the **selection-driven head function** on the `SO` carrier — the
section-free, computable head ([adger-2003] "the item that projects is the item
that selects"). Re-homes `selCheck`/`selHead`/`outerCatC` onto `SO`, the foundation
the Phase API consumes (`isPhaseHeadOf`, P3b).

The combinator `selStep` (carrier-agnostic, commutative — `selStep_comm`) is reused
from the legacy `Selection`; only the tree recursion is re-homed onto `Planar SOLabel`
+ the `SO` lift, exactly as `subtreesN` (P2a-ii). **Index-free traces** (P1): a bare
trace leaf gets the canonical saturated value `(mkTraceToken 0, [])` — `selCheck`
reads only the token's category (`.N`) and `outerSel` (`[]`), both index-independent,
so this is behaviour-equivalent to the legacy `(mkTraceToken n, [])`.

Out of scope (later phases): the planar `section_`/externalization (`linearize`/
`phonYield`) — research-grade and co-dependent with the flip (P3c/P4).
-/

namespace Minimalist

open RootedTree

/-! ### Selection check on the planar carrier -/

/-- Selection check on a planar `SO`-tree: the projecting head + residual pending
    features, or `none` outside the endocentric domain. Lexical leaf ↦ its token +
    `outerSel`; bare trace leaf ↦ canonical `(mkTraceToken 0, [])` (index-free);
    bare binary node ↦ `selStep` of the daughters. -/
def selCheckPlanar : Planar SOLabel → Option (LIToken × List Cat)
  | .node (.inl tok) _     => some (tok, tok.item.outerSel)
  | .node (.inr ()) []     => some (mkTraceToken 0, [])
  | .node (.inr ()) [l, r] => selStep (selCheckPlanar l) (selCheckPlanar r)
  | .node (.inr ()) _      => none

/-- A non-binary, non-leaf bare node has no selection value. -/
private theorem selCheckPlanar_node_none {cs : List (Planar SOLabel)}
    (h0 : cs.length ≠ 0) (h2 : cs.length ≠ 2) :
    selCheckPlanar (Planar.node (Sum.inr ()) cs) = none := by
  match cs with
  | [] => exact absurd rfl h0
  | [_] => rfl
  | [_, _] => exact absurd rfl h2
  | _ :: _ :: _ :: _ => rfl

private theorem selCheckPlanar_planarStep {t s : Planar SOLabel}
    (hstep : Planar.PlanarStep t s) : selCheckPlanar t = selCheckPlanar s := by
  induction hstep with
  | @swapAtRoot a l r pre post =>
    cases a with
    | inl _ => simp only [selCheckPlanar]
    | inr u =>
      cases u
      cases pre with
      | nil => cases post with
        | nil => exact selStep_comm _ _
        | cons c cs => simp only [List.nil_append, selCheckPlanar]
      | cons q qs =>
        have h2 : ((q :: qs) ++ l :: r :: post).length ≠ 2 := by
          simp only [List.length_append, List.length_cons]; omega
        have h2' : ((q :: qs) ++ r :: l :: post).length ≠ 2 := by
          simp only [List.length_append, List.length_cons]; omega
        rw [selCheckPlanar_node_none (by simp) h2, selCheckPlanar_node_none (by simp) h2']
  | @recurse a pre old new post _hstep ih =>
    cases a with
    | inl _ => simp only [selCheckPlanar]
    | inr u =>
      cases u
      cases pre with
      | nil => cases post with
        | nil => simp only [List.nil_append, selCheckPlanar]
        | cons c cs => cases cs with
          | nil => simp only [List.nil_append, selCheckPlanar, ih]
          | cons d ds => simp only [List.nil_append, selCheckPlanar]
      | cons q qs => cases qs with
        | nil => cases post with
          | nil => simp only [List.cons_append, List.nil_append, selCheckPlanar, ih]
          | cons d ds => simp only [List.cons_append, List.nil_append, selCheckPlanar]
        | cons q2 qs2 =>
          have h2 : ((q :: q2 :: qs2) ++ old :: post).length ≠ 2 := by
            simp only [List.length_append, List.length_cons]; omega
          have h2' : ((q :: q2 :: qs2) ++ new :: post).length ≠ 2 := by
            simp only [List.length_append, List.length_cons]; omega
          rw [selCheckPlanar_node_none (by simp) h2, selCheckPlanar_node_none (by simp) h2']

/-- `selCheckPlanar` is `PlanarEquiv`-invariant, so it descends to the quotient. -/
theorem selCheckPlanar_planarEquiv {t s : Planar SOLabel}
    (h : Planar.PlanarEquiv t s) : selCheckPlanar t = selCheckPlanar s := by
  induction h with
  | rel _ _ hstep => exact selCheckPlanar_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Selection check lifted to the nonplanar carrier. -/
def selCheckN : Nonplanar SOLabel → Option (LIToken × List Cat) :=
  Nonplanar.lift selCheckPlanar (fun _ _ h => selCheckPlanar_planarEquiv h)

@[simp] theorem selCheckN_mk (p : Planar SOLabel) : selCheckN (Nonplanar.mk p) = selCheckPlanar p :=
  rfl

theorem selCheckN_node (a b : Nonplanar SOLabel) :
    selCheckN (Nonplanar.node (Sum.inr ()) {a, b}) = selStep (selCheckN a) (selCheckN b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (Planar.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_planar_list]
  show selCheckN (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = selStep (selCheckN (Nonplanar.mk pa)) (selCheckN (Nonplanar.mk pb))
  rw [key]; simp only [selCheckN_mk, selCheckPlanar]

/-! ### The selection-driven head on `SO` -/

/-- **Selection-driven head check** on `SO` ([marcolli-chomsky-berwick-2025]
    Lemma 1.13.7): the projecting head + residual features, or `none` off the
    endocentric domain. Section-free and computable. -/
def SO.selCheck (s : SO) : Option (LIToken × List Cat) := selCheckN s.val

/-- The projecting head's lexical item, by c-selection. -/
def SO.selHead (s : SO) : Option LIToken := s.selCheck.map (·.1)

/-- Residual pending selectional features (`some []` = saturated). -/
def SO.checkedSel (s : SO) : Option (List Cat) := s.selCheck.map (·.2)

/-- The projecting head's **outer category** (the phase-head selector,
    [marcolli-chomsky-berwick-2025] Lemma 1.13.7); `none` at exocentric nodes. -/
def SO.outerCatC (s : SO) : Option Cat := s.selHead.map (·.item.outerCat)

@[simp] theorem SO.selCheck_lexLeaf (tok : LIToken) :
    (SO.lexLeaf tok).selCheck = some (tok, tok.item.outerSel) := rfl

@[simp] theorem SO.selCheck_traceLeaf :
    SO.traceLeaf.selCheck = some (mkTraceToken 0, []) := rfl

@[simp] theorem SO.selCheck_node (l r : SO) :
    (SO.node l r).selCheck = selStep l.selCheck r.selCheck := by
  show selCheckN (SO.node l r).val = selStep (selCheckN l.val) (selCheckN r.val)
  rw [SO.node_val, selCheckN_node]

@[simp] theorem SO.selHead_lexLeaf (tok : LIToken) : (SO.lexLeaf tok).selHead = some tok := rfl

@[simp] theorem SO.outerCatC_lexLeaf (tok : LIToken) :
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
