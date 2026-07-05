/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Derivation

/-!
# Derivation-grounded externalization (computable PF order)

[marcolli-chomsky-berwick-2025] §1.12. `SyntacticObject.Derivation.final` is an unordered
`Nonplanar` quotient, so the surface left-to-right order is not recoverable from it.
But a `Derivation` *records* the planarization choices: `emL`/`im` place material on
the LEFT edge, `emR` on the right — exactly MCB's externalization section σ_L, here
fixed by the derivation ("the language `L`") rather than a noncanonical `Quot.out`.
`externalizeP?` replays the steps on an ordered `RoseTree SOLabel` accumulator,
giving a fully **computable** PF: it never calls the noncomputable
`SyntacticObject.node`/`SyntacticObject.replace` (planar tree surgery + a `Nonplanar.mk` equality
test), so
surface orders `decide`. Traces are unpronounced, dropped by `planarYield`.

The Π-bridge faithfulness theorem `SyntacticObject.Derivation.externalizeP?_faithful` proves
`Nonplanar.mk externalizeP? = final` whenever the replay succeeds: the surface
readouts (`surfaceTokens`/`surfaceCats`/`surfacePhon`) are the word order of the
*actual* derived object. Sibling accounts of linearization: the selection-induced
harmonic order (`Linearization/Externalization.lean`) and Fox-Pesetsky cyclic
linearization (`Linearization/Cyclic.lean`).
-/

namespace Minimalist

open RootedTree

/-! ## Derivation-grounded externalization (computable PF order)

[marcolli-chomsky-berwick-2025] §1.12. `final` is an unordered `Nonplanar` quotient, so
the surface left-to-right order is not recoverable from it. But a `Derivation` *records*
the planarization choices: `emL`/`im` place material on the LEFT edge, `emR` on the
right — exactly MCB's externalization section `σ_L`, here fixed by the derivation ("the
language `L`") rather than a noncanonical `Quot.out`. The fold below replays the steps on
an **ordered `RoseTree SOLabel` accumulator**, giving a fully **computable** PF: it never
calls the noncomputable `SyntacticObject.node`/`SyntacticObject.replace` (it uses planar tree
surgery + a
`Nonplanar.mk` equality test), so surface orders `decide`. Index-free traces are sound
here: traces are unpronounced, dropped by `planarYield`.

The formal Π-bridge faithfulness theorem (`SyntacticObject.Derivation.externalizeP?_faithful`,
below)
proves `Nonplanar.mk externalizeP? = final` whenever the replay succeeds: the surface
readouts are the word order of the *actual* derived object, not just a replay that happens
to reproduce attested orders. The `decide` demos below exercise concrete derivations. -/

/-- Planar form of a leaf/trace `SyntacticObject` (the only items merged in canonical derivations);
    `none` for a complex `SyntacticObject` (no recorded internal order). -/
def SyntacticObject.toPlanarLeaf? (s : SyntacticObject) : Option (RoseTree SOLabel) :=
  match s.getLIToken with
  | some tok => some (SyntacticObject.leafP tok)
  | none     => if s = SyntacticObject.traceLeaf then some SyntacticObject.traceP else none

/-- Plain left-to-right token yield of an *already-ordered* planar tree; traces
    (`Sum.inr ()`) are unpronounced and contribute nothing. -/
def planarYield : RoseTree SOLabel → List LIToken
  | .node (.inl tok) _   => [tok]
  | .node (.inr ()) []   => []
  | .node (.inr ()) [l, r] => planarYield l ++ planarYield r
  | .node (.inr ()) _    => []

/-- "Projects to `target`": a planar subtree whose nonplanar projection is the `SyntacticObject`
    `target` — the predicate the `im` replay uses to locate a mover. Computable
    (`DecidableEq (Nonplanar …)`), so it `decide`s. -/
def projEqP (target : SyntacticObject) (s : RoseTree SOLabel) : Bool :=
  decide (Nonplanar.mk s = target.val)

/-- Leftmost (root-first) subtree satisfying `p`. -/
def planarFindP? (p : RoseTree SOLabel → Bool) : RoseTree SOLabel → Option (RoseTree SOLabel)
  | t@(.node _ [])     => if p t then some t else none
  | t@(.node _ [l, r]) => if p t then some t else (planarFindP? p l).or (planarFindP? p r)
  | t@(.node _ _)      => if p t then some t else none

/-- Replace every subtree satisfying `p` by `rep`. -/
def planarReplaceWhereP (p : RoseTree SOLabel → Bool) (rep : RoseTree SOLabel) :
    RoseTree SOLabel → RoseTree SOLabel
  | t@(.node _ [])     => if p t then rep else t
  | t@(.node a [l, r]) =>
      if p t then rep
      else .node a [planarReplaceWhereP p rep l, planarReplaceWhereP p rep r]
  | t@(.node _ _)      => if p t then rep else t

/-- Internal Merge on the ordered accumulator: raise the leftmost subtree projecting to
    `mover` to the LEFT edge, leaving the bare trace `SyntacticObject.traceP`. `none` if absent. -/
def moveLeftPlanarP (acc : RoseTree SOLabel) (mover : SyntacticObject) :
    Option (RoseTree SOLabel) :=
  (planarFindP? (projEqP mover) acc).map fun s =>
    SyntacticObject.nodeP s (planarReplaceWhereP (projEqP mover) SyntacticObject.traceP acc)

/-- One externalization step on the ordered accumulator (mirrors `SyntacticObject.Step.apply`). -/
def externStepP (acc? : Option (RoseTree SOLabel)) (step : SyntacticObject.Step) :
    Option (RoseTree SOLabel) :=
  acc?.bind fun acc => match step with
    | .emL item  => item.toPlanarLeaf?.map (fun p => SyntacticObject.nodeP p acc)
    | .emR item  => item.toPlanarLeaf?.map (fun p => SyntacticObject.nodeP acc p)
    | .im mover  => moveLeftPlanarP acc mover

namespace SyntacticObject.Derivation

/-- The derivation's ordered planar representative (MCB `σ_L` for this derivation),
    or `none` if a merged item is complex / a mover is missing. -/
def externalizeP? (d : SyntacticObject.Derivation) : Option (RoseTree SOLabel) :=
  d.initial.toPlanarLeaf?.bind fun init => d.steps.foldl externStepP (some init)

/-- Surface (pronounced) tokens, left-to-right; traces dropped. Empty if
    externalization fails. -/
def surfaceTokens (d : SyntacticObject.Derivation) : List LIToken :=
  (d.externalizeP?.map planarYield).getD []

/-- Surface category sequence — the readout used by word-order studies. -/
def surfaceCats (d : SyntacticObject.Derivation) : List Cat := d.surfaceTokens.map (·.item.outerCat)

/-- Surface phonological string: pronounced forms left-to-right (empty forms dropped). -/
def surfacePhon (d : SyntacticObject.Derivation) : List String :=
  d.surfaceTokens.filterMap LIToken.phonForm?

end SyntacticObject.Derivation

/-! ### Π-bridge faithfulness: `Nonplanar.mk externalizeP? = final`

[marcolli-chomsky-berwick-2025] §1.12. The externalization replay (`externStepP` on an
ordered `RoseTree SOLabel` accumulator) is *faithful* to the abstract derived object: each
planar op's `Nonplanar.mk` equals the corresponding noncomputable `SyntacticObject` op, so whenever
the replay succeeds its nonplanar projection is exactly `final`. This upgrades
`surfaceCats`/`surfacePhon` from "validated by `decide` demos" to "provably the word
order of the actual derived SyntacticObject" — the guarantee the word-order studies (Cinque2005,
ColeHermon2008, Chomsky1995, …) rely on. -/

/-- `isSOPlanar` of a bare binary node is the conjunction of the children's. -/
private theorem isSOPlanar_nodeP {a b : RoseTree SOLabel}
    (ha : isSOPlanar a = true) (hb : isSOPlanar b = true) :
    isSOPlanar (SyntacticObject.nodeP a b) = true := by
  simp only [isSOPlanar, isSOPlanarList, ha, hb, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceBEq, Bool.or_true, Bool.and_self]

/-- `Nonplanar.mk` of the planar binary builder is the bare binary nonplanar node. -/
private theorem mk_nodeP (a b : RoseTree SOLabel) :
    Nonplanar.mk (SyntacticObject.nodeP a b)
      = Nonplanar.node (Sum.inr ()) {Nonplanar.mk a, Nonplanar.mk b} := by
  rw [show ({Nonplanar.mk a, Nonplanar.mk b} : Multiset (Nonplanar SOLabel))
        = Multiset.ofList ([a, b].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]

/-- A bare binary node (two children) is never the trace leaf (no children). -/
private theorem SyntacticObject.node_ne_traceLeaf (l r : SyntacticObject) :
    SyntacticObject.node l r ≠ SyntacticObject.traceLeaf := by
  intro heq
  have ha : (SyntacticObject.node l r).val.rootChildren
      = SyntacticObject.traceLeaf.val.rootChildren := by rw [heq]
  rw [SyntacticObject.node_val, Nonplanar.rootChildren_node] at ha
  simp only [SyntacticObject.traceLeaf, Nonplanar.leaf_def, Nonplanar.rootChildren_mk,
    RoseTree.children, Multiset.insert_eq_cons] at ha
  exact Multiset.cons_ne_zero ha

/-- **Lemma 1.** A successful `toPlanarLeaf?` projects (under `Nonplanar.mk`) back to the
    `SyntacticObject` it came from, and is a well-formed planar leaf. -/
private theorem toPlanarLeaf?_mk {s : SyntacticObject} {ip : RoseTree SOLabel}
    (h : s.toPlanarLeaf? = some ip) :
    Nonplanar.mk ip = s.val ∧ isSOPlanar ip = true := by
  induction s using SyntacticObject.ind with
  | lex tok =>
    rw [SyntacticObject.toPlanarLeaf?, SyntacticObject.getLIToken_lexLeaf] at h
    obtain rfl : ip = SyntacticObject.leafP tok := by simpa using h.symm
    exact ⟨rfl, rfl⟩
  | trace =>
    rw [SyntacticObject.toPlanarLeaf?, SyntacticObject.getLIToken_traceLeaf, if_pos rfl] at h
    obtain rfl : ip = SyntacticObject.traceP := by simpa using h.symm
    exact ⟨rfl, rfl⟩
  | node l r _ _ =>
    rw [SyntacticObject.toPlanarLeaf?, SyntacticObject.getLIToken_node,
        if_neg (SyntacticObject.node_ne_traceLeaf l r)] at h
    exact absurd h (by simp)

/-- **Lemma 2.** `projEqP target s` certifies that `s` projects to `target`. -/
private theorem projEqP_eq {target : SyntacticObject} {s : RoseTree SOLabel}
    (h : projEqP target s = true) :
    Nonplanar.mk s = target.val := of_decide_eq_true h

/-- **Lemma 3a.** A subtree raised by `planarFindP?` satisfies the predicate. -/
private theorem planarFindP?_pred {p : RoseTree SOLabel → Bool} {t s : RoseTree SOLabel}
    (h : planarFindP? p t = some s) : p s = true := by
  fun_induction planarFindP? p t generalizing s with
  | case1 _ hp => obtain rfl := Option.some.inj h; exact hp
  | case2 => exact absurd h (by simp)
  | case3 _ _ _ hp => obtain rfl := Option.some.inj h; exact hp
  | case4 _ l r _ ihl ihr =>
    rcases hl : planarFindP? p l with _ | sl
    · rw [hl, Option.none_or] at h; exact ihr h
    · rw [hl, Option.some_or] at h; obtain rfl := Option.some.inj h; exact ihl hl
  | case5 _ _ _ _ hp => obtain rfl := Option.some.inj h; exact hp
  | case6 => exact absurd h (by simp)

/-- A bare binary node's children are both well-formed when the node is. -/
private theorem isSOPlanar_pair_children {l r : RoseTree SOLabel}
    (ht : isSOPlanar (SyntacticObject.nodeP l r) = true) :
    isSOPlanar l = true ∧ isSOPlanar r = true := by
  rw [SyntacticObject.nodeP, isSOPlanar, isSOPlanarList, isSOPlanarList, isSOPlanarList,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at ht
  exact ⟨ht.2.1, ht.2.2.1⟩

/-- **Lemma 3b.** A subtree raised by `planarFindP?` from a well-formed tree is itself
    well-formed. -/
private theorem planarFindP?_isSOPlanar {p : RoseTree SOLabel → Bool} {t s : RoseTree SOLabel}
    (h : planarFindP? p t = some s) (ht : isSOPlanar t = true) : isSOPlanar s = true := by
  fun_induction planarFindP? p t generalizing s with
  | case1 => obtain rfl := Option.some.inj h; exact ht
  | case2 => exact absurd h (by simp)
  | case3 => obtain rfl := Option.some.inj h; exact ht
  | case4 a l r _ ihl ihr =>
    have hcase : a = Sum.inr () := by
      cases a with
      | inl _ => simp [isSOPlanar] at ht
      | inr u => cases u; rfl
    subst hcase
    obtain ⟨hl', hr'⟩ := isSOPlanar_pair_children ht
    rcases hlf : planarFindP? p l with _ | sl
    · rw [hlf, Option.none_or] at h; exact ihr h hr'
    · rw [hlf, Option.some_or] at h; obtain rfl := Option.some.inj h; exact ihl hlf hl'
  | case5 => obtain rfl := Option.some.inj h; exact ht
  | case6 => exact absurd h (by simp)

/-- Under `isSOPlanar`, a node has either no children or exactly two. -/
private theorem isSOPlanar_length {a : SOLabel} {cs : List (RoseTree SOLabel)}
    (ht : isSOPlanar (RoseTree.node a cs) = true) : cs.length = 0 ∨ cs.length = 2 := by
  cases a with
  | inl _ =>
    rw [isSOPlanar] at ht
    rw [List.isEmpty_iff] at ht
    exact Or.inl (by rw [ht]; rfl)
  | inr u =>
    cases u
    rw [isSOPlanar, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at ht
    exact ht.1

/-- `projEqP` reflects (in)equality of the nonplanar projection to the target. -/
private theorem not_projEqP {target : SyntacticObject} {s : RoseTree SOLabel}
    (h : ¬ projEqP target s = true) : Nonplanar.mk s ≠ target.val := by
  rw [projEqP, decide_eq_true_eq] at h; exact h

/-- **Lemma 4 (CRUX): the replace bridge.** On a well-formed planar tree, the computable
    planar replacement (`planarReplaceWhereP (projEqP target) SyntacticObject.traceP`) projects
    under
    `Nonplanar.mk` to the abstract structural substitution `replaceN target
    SyntacticObject.traceLeaf`,
    and stays well-formed. The two `if`-conditions agree (`projEqP target s = true ↔
    Nonplanar.mk s = target.val`), and the recursive bare-binary case lines up with
    `replaceN_node`'s else branch (`{·,·}` multiset built from the two daughters). -/
private theorem replaceWhereP_mk (target : SyntacticObject) {t : RoseTree SOLabel}
    (ht : isSOPlanar t = true) :
    Nonplanar.mk (planarReplaceWhereP (projEqP target) SyntacticObject.traceP t)
        = replaceN target.val SyntacticObject.traceLeaf.val (Nonplanar.mk t)
      ∧ isSOPlanar (planarReplaceWhereP (projEqP target) SyntacticObject.traceP t) = true := by
  fun_induction planarReplaceWhereP (projEqP target) SyntacticObject.traceP t with
  | case1 _ hp =>
    refine ⟨?_, rfl⟩
    rw [projEqP_eq hp, replaceN_self]; rfl
  | case2 b hp =>
    refine ⟨?_, ht⟩
    rw [show Nonplanar.mk (RoseTree.node b []) = Nonplanar.leaf b from rfl,
      replaceN_leaf, if_neg]
    rw [show Nonplanar.leaf b = Nonplanar.mk (RoseTree.node b []) from rfl]
    exact not_projEqP hp
  | case3 _ _ _ hp =>
    refine ⟨?_, rfl⟩
    rw [projEqP_eq hp, replaceN_self]; rfl
  | case4 a l r hp ihl ihr =>
    have hcase : a = Sum.inr () := by
      cases a with
      | inl _ => simp [isSOPlanar] at ht
      | inr u => cases u; rfl
    subst hcase
    obtain ⟨hl', hr'⟩ := isSOPlanar_pair_children ht
    obtain ⟨ihle, ihls⟩ := ihl hl'
    obtain ⟨ihre, ihrs⟩ := ihr hr'
    refine ⟨?_, isSOPlanar_nodeP ihls ihrs⟩
    have hne : Nonplanar.node (Sum.inr ()) {Nonplanar.mk l, Nonplanar.mk r} ≠ target.val := by
      rw [← mk_nodeP]; exact not_projEqP hp
    rw [show RoseTree.node (Sum.inr ())
          [planarReplaceWhereP (projEqP target) SyntacticObject.traceP l,
          planarReplaceWhereP (projEqP target) SyntacticObject.traceP r]
        = SyntacticObject.nodeP (planarReplaceWhereP (projEqP target) SyntacticObject.traceP l)
          (planarReplaceWhereP (projEqP target) SyntacticObject.traceP r) from rfl,
      mk_nodeP, ihle, ihre, mk_nodeP, replaceN_node, if_neg hne]
  | case5 _ cs hnil hpair _ =>
    rcases isSOPlanar_length ht with hlen | hlen
    · exact absurd (List.length_eq_zero_iff.mp hlen) hnil
    · obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen; exact absurd rfl (hpair x y)
  | case6 _ cs hnil hpair _ =>
    rcases isSOPlanar_length ht with hlen | hlen
    · exact absurd (List.length_eq_zero_iff.mp hlen) hnil
    · obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen; exact absurd rfl (hpair x y)

/-- **Lemma 6: per-step faithfulness.** A successful replay step on a well-formed
    accumulator stays well-formed and projects to the abstract `SyntacticObject.Step.apply`. -/
private theorem externStepP_step {acc : SyntacticObject} {accp p' : RoseTree SOLabel}
    {step : SyntacticObject.Step}
    (h : externStepP (some accp) step = some p') (hwf : isSOPlanar accp = true)
    (hmk : Nonplanar.mk accp = acc.val) :
    isSOPlanar p' = true ∧ Nonplanar.mk p' = (step.apply acc).val := by
  cases step with
  | emL item =>
    change item.toPlanarLeaf?.map (fun p => SyntacticObject.nodeP p accp) = some p' at h
    rcases hip : item.toPlanarLeaf? with _ | ip
    · rw [hip, Option.map_none] at h; exact absurd h (by simp)
    · rw [hip, Option.map_some] at h
      obtain rfl := Option.some.inj h
      obtain ⟨hmkip, hwfip⟩ := toPlanarLeaf?_mk hip
      refine ⟨isSOPlanar_nodeP hwfip hwf, ?_⟩
      rw [SyntacticObject.Step.apply, SyntacticObject.merge_val, mk_nodeP, hmkip, hmk]
  | emR item =>
    change item.toPlanarLeaf?.map (fun p => SyntacticObject.nodeP accp p) = some p' at h
    rcases hip : item.toPlanarLeaf? with _ | ip
    · rw [hip, Option.map_none] at h; exact absurd h (by simp)
    · rw [hip, Option.map_some] at h
      obtain rfl := Option.some.inj h
      obtain ⟨hmkip, hwfip⟩ := toPlanarLeaf?_mk hip
      refine ⟨isSOPlanar_nodeP hwf hwfip, ?_⟩
      rw [SyntacticObject.Step.apply, SyntacticObject.merge_val, mk_nodeP, hmkip, hmk]
  | im mover =>
    change moveLeftPlanarP accp mover = some p' at h
    rw [moveLeftPlanarP] at h
    rcases hfind : planarFindP? (projEqP mover) accp with _ | s
    · rw [hfind, Option.map_none] at h; exact absurd h (by simp)
    · rw [hfind, Option.map_some] at h
      obtain rfl := Option.some.inj h
      have hmks : Nonplanar.mk s = mover.val := projEqP_eq (planarFindP?_pred hfind)
      have hwfs : isSOPlanar s = true := planarFindP?_isSOPlanar hfind hwf
      obtain ⟨hrwe, hrws⟩ := replaceWhereP_mk mover hwf
      refine ⟨isSOPlanar_nodeP hwfs hrws, ?_⟩
      rw [SyntacticObject.Step.apply, SyntacticObject.intMerge_val,
          SyntacticObject.deleteAccessible_val, mk_nodeP, hmks, hrwe, hmk]
      exact congrArg (Nonplanar.node (Sum.inr ())) (Multiset.cons_swap _ _ _)

/-- `none` is absorbing for the replay fold: once externalization fails, it stays failed. -/
private theorem foldl_externStepP_none (steps : List SyntacticObject.Step) :
    steps.foldl externStepP none = none := by
  induction steps with
  | nil => rfl
  | cons st rest ih => rw [List.foldl_cons, show externStepP none st = none from rfl]; exact ih

/-- **Lemma 7: foldl faithfulness.** A successful replay fold from a well-formed,
    faithful accumulator projects to the abstract `final`-style fold of
    `SyntacticObject.Step.apply`. -/
private theorem foldl_externStepP_mk :
    ∀ (steps : List SyntacticObject.Step) {acc : SyntacticObject} {accp p : RoseTree SOLabel},
    steps.foldl externStepP (some accp) = some p → isSOPlanar accp = true →
    Nonplanar.mk accp = acc.val →
    Nonplanar.mk p = (steps.foldl (fun so st => st.apply so) acc).val
  | [], acc, accp, p, h, _, hmk => by
      rw [List.foldl_nil] at h ⊢; obtain rfl := Option.some.inj h; exact hmk
  | st :: rest, acc, accp, p, h, hwf, hmk => by
      rw [List.foldl_cons] at h ⊢
      rcases hstep : externStepP (some accp) st with _ | accp'
      · rw [hstep, foldl_externStepP_none] at h; exact absurd h (by simp)
      · obtain ⟨hwf', hmk'⟩ := externStepP_step hstep hwf hmk
        rw [hstep] at h
        exact foldl_externStepP_mk rest h hwf' hmk'

/-- **Π-bridge faithfulness** ([marcolli-chomsky-berwick-2025] §1.12): whenever the
    computable externalization replay `externalizeP?` succeeds, its nonplanar projection
    is exactly the abstract derived object `final`. So the surface readouts
    (`surfaceTokens`/`surfaceCats`/`surfacePhon`) are provably the word order of the *actual*
    derived syntactic object — the guarantee the word-order studies depend on. The replay
    is partial by design (EM of a complex item / a missing mover ⇒ `none`, making the claim
    vacuous there); on the canonical leaf/trace derivations the studies build, it succeeds. -/
theorem SyntacticObject.Derivation.externalizeP?_faithful (d : SyntacticObject.Derivation)
    {p : RoseTree SOLabel}
    (h : d.externalizeP? = some p) : Nonplanar.mk p = d.final.val := by
  rw [SyntacticObject.Derivation.externalizeP?] at h
  rcases hinit : d.initial.toPlanarLeaf? with _ | init
  · rw [hinit] at h; exact absurd h (by simp [Option.bind])
  · rw [hinit] at h
    change d.steps.foldl externStepP (some init) = some p at h
    obtain ⟨hmkinit, hwfinit⟩ := toPlanarLeaf?_mk hinit
    exact foldl_externStepP_mk d.steps h hwfinit hmkinit

/-! ### Verification: the [cinque-2005] pied-piping contrast

Phrasal pied-piping preserves the moved constituent's internal order, so deriving
Dem-N-A-Num (raise N around A, then pied-pipe `[N A]` around Num) is distinct from
Dem-A-N-Num (pied-pipe `[A N]` around Num). Movers are built with the computable DSL so
the surface orders `decide`. (`.D` stands in for the demonstrative.) -/

private def xN : SyntacticObject := SyntacticObject.mkLeaf .N [] 1
private def xA : SyntacticObject := SyntacticObject.mkLeaf .A [] 2
private def xNum : SyntacticObject := SyntacticObject.mkLeaf .Num [] 3
private def xD : SyntacticObject := SyntacticObject.mkLeaf .D [] 4
/-- The pied-piped `[N [A t]]` mover (built planar-first, so it is computable). -/
private def xNAt : SyntacticObject :=
  SyntacticObject.ofPlanar (SyntacticObject.nodeP (SyntacticObject.leafP ⟨.simple .N [], 1⟩)
    (SyntacticObject.nodeP (SyntacticObject.leafP ⟨.simple .A [], 2⟩) SyntacticObject.traceP))
/-- The pied-piped `[A N]` mover. -/
private def xAN : SyntacticObject :=
  SyntacticObject.ofPlanar (SyntacticObject.nodeP (SyntacticObject.leafP ⟨.simple .A [], 2⟩)
    (SyntacticObject.leafP ⟨.simple .N [], 1⟩))

/-- No movement: `Dem Num A N`. -/
private def xDerivBase : SyntacticObject.Derivation :=
  ⟨xN, [.emL xA, .emL xNum, .emL xD]⟩
/-- Raise N around A, pied-pipe `[N A]` around Num: `Dem N A Num`. -/
private def xDerivO : SyntacticObject.Derivation :=
  ⟨xN, [.emL xA, .im xN, .emL xNum, .im xNAt, .emL xD]⟩
/-- Pied-pipe `[A N]` around Num, no sub-raise: `Dem A N Num`. -/
private def xDerivN : SyntacticObject.Derivation :=
  ⟨xN, [.emL xA, .emL xNum, .im xAN, .emL xD]⟩

example : xDerivBase.surfaceCats = [.D, .Num, .A, .N] := by decide
example : xDerivO.surfaceCats = [.D, .N, .A, .Num] := by decide
example : xDerivN.surfaceCats = [.D, .A, .N, .Num] := by decide
/-- Pied-piping preserves internal order: `o` and `n` diverge. -/
example : xDerivO.surfaceCats ≠ xDerivN.surfaceCats := by decide


end Minimalist
