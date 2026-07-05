/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# The selection-driven head on the `SO` carrier

The **selection-driven head function** on the `SO` carrier: whichever sister's head
c-selects the saturated other projects — [adger-2003]'s identification of the
projecting item with the selecting item, instantiating the bare-phrase-structure
projection ([chomsky-1995-bare] §4) that [marcolli-chomsky-berwick-2025] §1.13.3
abstracts as head functions (Definition 1.13.6 / Lemma 1.13.7). Selection induces
one head function among the tree's many (Lemma 1.13.4); like the book's, it is
partial — `none` at exocentric nodes. `selCheck`/`selHead`/`outerCatC` on `SO` are
the foundation the Phase API consumes (`isPhaseHeadOf`).

The carrier-free selection combinators `selStep`/`selSide` (commutative —
`selStep_comm`/`selSide_comm`) operate purely on selection states
(`Option (LIToken × List Cat)`); the tree recursion lives on `RoseTree SOLabel` and
lifts to `SO`, exactly as `subtreesN`. **Index-free traces**: a bare trace leaf gets
the canonical saturated value `(mkTraceToken 0, [])` — `selCheck` reads only the
token's category (`.N`) and `outerSel` (`[]`), both index-independent.
-/

namespace Minimalist

open RootedTree

/-! ### Carrier-free selection combinators

`selStep`/`selSide` combine two sisters' selection-check results into the node's
projecting head (`selStep`) and which daughter projects (`selSide`). Both are
order-independent (`selStep_comm`/`selSide_comm`) — the formal content of Merge's
unordered output — so they descend through the nonplanar quotient. -/

/-- Combine two sisters' selection-check results. Order-independent (symmetric,
    `selStep_comm`): whichever sister's head c-selects the *saturated* other
    projects, yielding its residual stack; `none` at exocentric nodes (neither
    or both qualify). -/
def selStep : Option (LIToken × List Cat) → Option (LIToken × List Cat) →
    Option (LIToken × List Cat)
  | some (ha, c :: rest), some (hb, []) =>
      if hb.item.outerCat = c then some (ha, rest) else none
  | some (ha, []), some (hb, c :: rest) =>
      if ha.item.outerCat = c then some (hb, rest) else none
  | _, _ => none

theorem selStep_comm (x y : Option (LIToken × List Cat)) :
    selStep x y = selStep y x := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some py => cases py with | mk hy sy => cases sy <;> rfl
  | some px =>
    cases px with
    | mk hx sx =>
      cases y with
      | none => cases sx <;> rfl
      | some py =>
        cases py with
        | mk hy sy => cases sx <;> cases sy <;> rfl

/-- The head of `selStep x y` (when defined) is one of `x`/`y`'s heads. -/
theorem selStep_fst {x y : Option (LIToken × List Cat)} {r : LIToken}
    (h : (selStep x y).map (·.1) = some r) :
    x.map (·.1) = some r ∨ y.map (·.1) = some r := by
  unfold selStep at h
  split at h
  · split_ifs at h <;> simp_all
  · split_ifs at h <;> simp_all
  · simp at h

/-- Which daughter projects at a binary node under c-selection: `some true` = the
    **left** sister is the selector, `some false` = the **right**, `none` =
    exocentric (neither uniquely selects the saturated other). Mirrors `selStep`. -/
def selSide : Option (LIToken × List Cat) → Option (LIToken × List Cat) → Option Bool
  | some (_, c :: _), some (hb, []) => if hb.item.outerCat = c then some true else none
  | some (ha, []), some (_, c :: _) => if ha.item.outerCat = c then some false else none
  | _, _ => none

theorem selSide_comm (x y : Option (LIToken × List Cat)) :
    selSide x y = (selSide y x).map Bool.not := by
  cases x with
  | none => cases y with
    | none => rfl
    | some py => obtain ⟨hy, sy⟩ := py; cases sy <;> rfl
  | some px => obtain ⟨hx, sx⟩ := px; cases y with
    | none => cases sx <;> rfl
    | some py => obtain ⟨hy, sy⟩ := py
                 cases sx <;> cases sy <;> simp only [selSide, Option.map] <;>
                   split <;> rfl

/-- When `selStep` returns a head, that head is the projecting daughter's head,
    and `selSide` agrees on which daughter projects. The bridge between the
    residual-tracking `selStep` and the order-determining `selSide`. -/
theorem selStep_eq_some {x y : Option (LIToken × List Cat)} {hd : LIToken}
    {res : List Cat} (h : selStep x y = some (hd, res)) :
    (selSide x y = some true ∧ x.map (·.1) = some hd) ∨
    (selSide x y = some false ∧ y.map (·.1) = some hd) := by
  match x, y with
  | some (ha, c :: rest'), some (hb, []) =>
    simp only [selStep] at h
    by_cases hcat : hb.item.outerCat = c
    · rw [if_pos hcat] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨by simp [selSide, hcat], by simp [h.1]⟩
    · rw [if_neg hcat] at h; exact absurd h (by simp)
  | some (ha, []), some (hb, c :: rest') =>
    simp only [selStep] at h
    by_cases hcat : ha.item.outerCat = c
    · rw [if_pos hcat] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨by simp [selSide, hcat], by simp [h.1]⟩
    · rw [if_neg hcat] at h; exact absurd h (by simp)
  | some (_, []), some (_, []) => simp [selStep] at h
  | some (_, _ :: _), some (_, _ :: _) => simp [selStep] at h
  | none, _ => simp [selStep] at h
  | some _, none => simp [selStep] at h

/-! ### Selection check on the planar carrier -/

/-- Selection check on a planar `SO`-tree: the projecting head + residual pending
    features, or `none` outside the endocentric domain. Lexical leaf ↦ its token +
    `outerSel`; bare trace leaf ↦ canonical `(mkTraceToken 0, [])` (index-free);
    bare binary node ↦ `selStep` of the daughters. -/
def selCheckPlanar : RoseTree SOLabel → Option (LIToken × List Cat)
  | .node (.inl tok) _     => some (tok, tok.item.outerSel)
  | .node (.inr ()) []     => some (mkTraceToken 0, [])
  | .node (.inr ()) [l, r] => selStep (selCheckPlanar l) (selCheckPlanar r)
  | .node (.inr ()) _      => none

/-- A non-binary, non-leaf bare node has no selection value. -/
private theorem selCheckPlanar_node_none {cs : List (RoseTree SOLabel)}
    (h0 : cs.length ≠ 0) (h2 : cs.length ≠ 2) :
    selCheckPlanar (RoseTree.node (Sum.inr ()) cs) = none := by
  match cs with
  | [] => exact absurd rfl h0
  | [_] => rfl
  | [_, _] => exact absurd rfl h2
  | _ :: _ :: _ :: _ => rfl

private theorem selCheckPlanar_permStep {t s : RoseTree SOLabel}
    (hstep : RoseTree.PermStep t s) : selCheckPlanar t = selCheckPlanar s := by
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

/-- `selCheckPlanar` is `PermEquiv`-invariant, so it descends to the quotient. -/
theorem selCheckPlanar_permEquiv {t s : RoseTree SOLabel}
    (h : RoseTree.PermEquiv t s) : selCheckPlanar t = selCheckPlanar s := by
  induction h with
  | rel _ _ hstep => exact selCheckPlanar_permStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Selection check lifted to the nonplanar carrier. -/
def selCheckN : Nonplanar SOLabel → Option (LIToken × List Cat) :=
  Nonplanar.lift selCheckPlanar (fun _ _ h => selCheckPlanar_permEquiv h)

@[simp] theorem selCheckN_mk (p : RoseTree SOLabel) : selCheckN (Nonplanar.mk p) = selCheckPlanar p :=
  rfl

theorem selCheckN_node (a b : Nonplanar SOLabel) :
    selCheckN (Nonplanar.node (Sum.inr ()) {a, b}) = selStep (selCheckN a) (selCheckN b) := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  have key : Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb}
           = Nonplanar.mk (RoseTree.node (Sum.inr ()) [pa, pb]) := by
    rw [show ({Nonplanar.mk pa, Nonplanar.mk pb} : Multiset (Nonplanar SOLabel))
          = Multiset.ofList ([pa, pb].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]
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

/-- The projecting head's **outer category** (the phase-head selector); `none` at
    exocentric nodes. -/
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

/-- **Endocentricity**: a node's projecting head is one of its daughters' heads —
    bare-phrase-structure projection ([chomsky-1995-bare] §4, abstracted as
    [marcolli-chomsky-berwick-2025] Definition 1.13.6 / Lemma 1.13.7). -/
theorem SO.selHead_node {l r : SO} {h : LIToken}
    (hlr : (SO.node l r).selHead = some h) : l.selHead = some h ∨ r.selHead = some h := by
  simp only [SO.selHead, SO.selCheck_node] at hlr ⊢
  exact selStep_fst hlr

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
