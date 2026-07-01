/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Replace

/-!
# Derivation steps on the `SO` carrier

P4-pre-b of the single-carrier program: the ordered **derivation** layer on the `SO`
carrier — the sequence of Merge/Move operations producing a syntactic object — replacing
the legacy `FreeCommMagma`-based `Step`/`Derivation`.

**The derivation's Merge *is* the workspace Merge by construction.** Each step applies a
canonical MCB Merge operator (`Workspace.lean`): External Merge is `SO.merge` (Lemma
1.4.1), Internal Merge is `SO.intMerge` (Prop 1.4.2's `M_{T/β,β}`) on the deletion
remainder `SO.deleteAccessible mover current` (= `T/mover`). So `Step.apply` *unfolds*
to the coproduct operators (`SO.Step.apply_emL`/`apply_im`); the Δ^ρ-coproduct identity
is `SO.merge_toForest`/`SO.intMerge_toForest` — nothing is independently stipulated then
bridged.

**Index-free traces (D2):** Internal Merge leaves the bare `SO.traceLeaf`; chain identity
is **workspace-level** (`Workspace`, `chainMultiplicity`, #795, MCB Def 1.2.1), not a
per-step `Nat`. The deletion remainder is realized by `SO.replace` (#804): for a
uniquely-accessible mover this is exactly the Δ^ρ cut remainder `SO.intMerge_toForest`
extracts, and `replace`-all is its total extension to the multi-occurrence (chain) case.

Because `SO.node` is noncomputable, so are `Step.apply`/`Derivation.final` — concrete
trees are reasoned about structurally, not by `decide`. The **computable, `decide`-able
surface order** (externalization replay + the Π bridge, the Cinque-style word-order
readout) is the separate research-grade follow-up; it replays the linear choices on an
ordered planar accumulator, since `final` (a `Nonplanar` quotient) is unordered.
-/

namespace Minimalist

open RootedTree

/-! ### Steps -/

/-- A single derivation step on the `SO` carrier. **Index-free** (D2): `im` records
    only the mover; the trace it leaves is the bare `SO.traceLeaf`, and the mover ↔ trace
    chain lives at the workspace level (#795), not in a per-step index. -/
inductive SO.Step where
  /-- External Merge, new item as the left daughter. -/
  | emL (item : SO)
  /-- External Merge, new item as the right daughter. -/
  | emR (item : SO)
  /-- Internal Merge: raise `mover`, leaving the bare trace in its place. -/
  | im (mover : SO)

/-- **Internal-Merge deletion remainder** `T/mover` ([marcolli-chomsky-berwick-2025]
    Def 1.2.7, the ρ-form): the syntactic object left when the moved constituent's
    accessible occurrence is cut, with the bare `SO.traceLeaf` in its place. For a
    uniquely-accessible `mover` this is the Δ^ρ deletion remainder `p0.2` that
    `SO.intMerge_toForest` extracts from `cutSummandsN`; `SO.replace` (replace-all) is
    its total extension to the multi-occurrence case (the chain is then read at the
    workspace level, Def 1.2.1). -/
noncomputable def SO.deleteAccessible (mover current : SO) : SO :=
  current.replace mover SO.traceLeaf

@[simp] theorem SO.deleteAccessible_val (mover current : SO) :
    (SO.deleteAccessible mover current).val
      = replaceN mover.val SO.traceLeaf.val current.val := rfl

/-- Apply a derivation step to the current tree. **The derivation Merge *is* the
    workspace Merge by construction:** External Merge is `SO.merge` (Lemma 1.4.1),
    Internal Merge is `SO.intMerge` (Prop 1.4.2's `M_{T/β,β}`) applied to the deletion
    remainder `SO.deleteAccessible mover current` (= `T/mover`). The coproduct identity
    of each is `SO.merge_toForest`/`SO.intMerge_toForest`. Since `SO.merge` is commutative
    (`SO.mul_comm`), `emL`/`emR` and the mover-left/remainder-left orders give the *same*
    `SO` (`apply_emL_eq_emR`); the left/right distinction matters only for the surface
    (PF) order, recovered downstream by the externalization replay. -/
noncomputable def SO.Step.apply (step : SO.Step) (current : SO) : SO :=
  match step with
  | .emL item  => SO.merge item current
  | .emR item  => SO.merge current item
  | .im mover  => SO.intMerge mover (SO.deleteAccessible mover current)

/-- External Merge unfolds to the canonical workspace EM `SO.merge` (Lemma 1.4.1). -/
theorem SO.Step.apply_emL (item current : SO) :
    (SO.Step.emL item).apply current = SO.merge item current := rfl

/-- External Merge unfolds to the canonical workspace EM `SO.merge` (Lemma 1.4.1). -/
theorem SO.Step.apply_emR (item current : SO) :
    (SO.Step.emR item).apply current = SO.merge current item := rfl

/-- **Internal Merge unfolds to the coproduct operator by construction.** The `im` step
    *is* the canonical workspace IM `SO.intMerge` (MCB Prop 1.4.2) on the deletion
    remainder — definitionally, not via a bridge. Composing with `SO.intMerge_toForest`
    gives the Δ^ρ-coproduct identity on the workspace. -/
theorem SO.Step.apply_im (mover current : SO) :
    (SO.Step.im mover).apply current = SO.intMerge mover (SO.deleteAccessible mover current) :=
  rfl

/-- External Merge is side-indifferent on the unordered carrier: `emL` and `emR` build
    the same syntactic object (they diverge only at externalization). -/
theorem SO.Step.apply_emL_eq_emR (item current : SO) :
    (SO.Step.emL item).apply current = (SO.Step.emR item).apply current :=
  mul_comm item current

/-! ### Derivations -/

/-- An ordered derivation: an initial `SO` together with a sequence of steps. -/
structure SO.Derivation where
  /-- The initial syntactic object (a lexical item, in canonical derivations). -/
  initial : SO
  /-- The ordered sequence of Merge/Move steps. -/
  steps : List SO.Step

namespace SO.Derivation

/-- The final tree produced by applying every step in order. -/
noncomputable def final (d : SO.Derivation) : SO :=
  d.steps.foldl (fun so step => step.apply so) d.initial

/-- The intermediate tree after the first `n` steps. -/
noncomputable def stageAt (d : SO.Derivation) (n : Nat) : SO :=
  (d.steps.take n).foldl (fun so step => step.apply so) d.initial

/-- The number of derivation steps. -/
def length (d : SO.Derivation) : Nat := d.steps.length

/-- The movers — the subtrees that underwent Internal Merge. -/
def movedItems (d : SO.Derivation) : List SO :=
  d.steps.filterMap fun
    | .im mover => some mover
    | _ => none

/-- Stage `0` is the initial tree (no steps applied). -/
@[simp] theorem stageAt_zero (d : SO.Derivation) : d.stageAt 0 = d.initial := by
  simp [stageAt]

/-- The stage at full length is the final tree. -/
theorem stageAt_length (d : SO.Derivation) : d.stageAt d.steps.length = d.final := by
  simp [stageAt, final, List.take_length]

end SO.Derivation

/-! ### Worked example

The movers of a small derivation are read directly off the steps (a `filterMap`, so
this is `decide`-able even though `final` is not): a derivation that internally merges
two objects records exactly those two as moved. -/

private def demoTok (i : Nat) : SO := SO.lexLeaf ⟨.simple .N [], i⟩

example :
    (SO.Derivation.mk (demoTok 0)
      [SO.Step.emL (demoTok 1), SO.Step.im (demoTok 1), SO.Step.emR (demoTok 2),
       SO.Step.im (demoTok 2)]).movedItems
      = [demoTok 1, demoTok 2] := by
  simp [SO.Derivation.movedItems, demoTok]

example :
    (SO.Derivation.mk (demoTok 0) [SO.Step.emL (demoTok 1)]).length = 1 := rfl

/-! ## Derivation-grounded externalization (computable PF order)

[marcolli-chomsky-berwick-2025] §1.12. `final` is an unordered `Nonplanar` quotient, so
the surface left-to-right order is not recoverable from it. But a `Derivation` *records*
the planarization choices: `emL`/`im` place material on the LEFT edge, `emR` on the
right — exactly MCB's externalization section `σ_L`, here fixed by the derivation ("the
language `L`") rather than a noncanonical `Quot.out`. The fold below replays the steps on
an **ordered `RoseTree SOLabel` accumulator**, giving a fully **computable** PF: it never
calls the noncomputable `SO.node`/`SO.replace` (it uses planar tree surgery + a
`Nonplanar.mk` equality test), so surface orders `decide`. Index-free traces are sound
here: traces are unpronounced, dropped by `planarYield`.

The formal Π-bridge faithfulness theorem (`SO.Derivation.externalizeP?_faithful`, below)
proves `Nonplanar.mk externalizeP? = final` whenever the replay succeeds: the surface
readouts are the word order of the *actual* derived object, not just a replay that happens
to reproduce attested orders. The `decide` demos below exercise concrete derivations. -/

/-- Planar form of a leaf/trace `SO` (the only items merged in canonical derivations);
    `none` for a complex `SO` (no recorded internal order). -/
def SO.toPlanarLeaf? (s : SO) : Option (RoseTree SOLabel) :=
  match s.getLIToken with
  | some tok => some (SO.leafP tok)
  | none     => if s = SO.traceLeaf then some SO.traceP else none

/-- Plain left-to-right token yield of an *already-ordered* planar tree; traces
    (`Sum.inr ()`) are unpronounced and contribute nothing. -/
def planarYield : RoseTree SOLabel → List LIToken
  | .node (.inl tok) _   => [tok]
  | .node (.inr ()) []   => []
  | .node (.inr ()) [l, r] => planarYield l ++ planarYield r
  | .node (.inr ()) _    => []

/-- "Projects to `target`": a planar subtree whose nonplanar projection is the `SO`
    `target` — the predicate the `im` replay uses to locate a mover. Computable
    (`DecidableEq (Nonplanar …)`), so it `decide`s. -/
def projEqP (target : SO) (s : RoseTree SOLabel) : Bool := decide (Nonplanar.mk s = target.val)

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
    `mover` to the LEFT edge, leaving the bare trace `SO.traceP`. `none` if absent. -/
def moveLeftPlanarP (acc : RoseTree SOLabel) (mover : SO) : Option (RoseTree SOLabel) :=
  (planarFindP? (projEqP mover) acc).map fun s =>
    SO.nodeP s (planarReplaceWhereP (projEqP mover) SO.traceP acc)

/-- One externalization step on the ordered accumulator (mirrors `SO.Step.apply`). -/
def externStepP (acc? : Option (RoseTree SOLabel)) (step : SO.Step) : Option (RoseTree SOLabel) :=
  acc?.bind fun acc => match step with
    | .emL item  => item.toPlanarLeaf?.map (fun p => SO.nodeP p acc)
    | .emR item  => item.toPlanarLeaf?.map (fun p => SO.nodeP acc p)
    | .im mover  => moveLeftPlanarP acc mover

namespace SO.Derivation

/-- The derivation's ordered planar representative (MCB `σ_L` for this derivation),
    or `none` if a merged item is complex / a mover is missing. -/
def externalizeP? (d : SO.Derivation) : Option (RoseTree SOLabel) :=
  d.initial.toPlanarLeaf?.bind fun init => d.steps.foldl externStepP (some init)

/-- Surface (pronounced) tokens, left-to-right; traces dropped. Empty if
    externalization fails. -/
def surfaceTokens (d : SO.Derivation) : List LIToken :=
  (d.externalizeP?.map planarYield).getD []

/-- Surface category sequence — the readout used by word-order studies. -/
def surfaceCats (d : SO.Derivation) : List Cat := d.surfaceTokens.map (·.item.outerCat)

/-- Surface phonological string: pronounced forms left-to-right (empty forms dropped). -/
def surfacePhon (d : SO.Derivation) : List String :=
  d.surfaceTokens.filterMap fun t => let p := t.phonForm; if p.isEmpty then none else some p

end SO.Derivation

/-! ### Π-bridge faithfulness: `Nonplanar.mk externalizeP? = final`

[marcolli-chomsky-berwick-2025] §1.12. The externalization replay (`externStepP` on an
ordered `RoseTree SOLabel` accumulator) is *faithful* to the abstract derived object: each
planar op's `Nonplanar.mk` equals the corresponding noncomputable `SO` op, so whenever
the replay succeeds its nonplanar projection is exactly `final`. This upgrades
`surfaceCats`/`surfacePhon` from "validated by `decide` demos" to "provably the word
order of the actual derived SO" — the guarantee the word-order studies (Cinque2005,
ColeHermon2008, Chomsky1995, …) rely on. -/

/-- `isSOPlanar` of a bare binary node is the conjunction of the children's. -/
private theorem isSOPlanar_nodeP {a b : RoseTree SOLabel}
    (ha : isSOPlanar a = true) (hb : isSOPlanar b = true) : isSOPlanar (SO.nodeP a b) = true := by
  simp only [isSOPlanar, isSOPlanarList, ha, hb, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceBEq, Bool.or_true, Bool.and_self]

/-- `Nonplanar.mk` of the planar binary builder is the bare binary nonplanar node. -/
private theorem mk_nodeP (a b : RoseTree SOLabel) :
    Nonplanar.mk (SO.nodeP a b) = Nonplanar.node (Sum.inr ()) {Nonplanar.mk a, Nonplanar.mk b} := by
  rw [show ({Nonplanar.mk a, Nonplanar.mk b} : Multiset (Nonplanar SOLabel))
        = Multiset.ofList ([a, b].map Nonplanar.mk) from rfl, Nonplanar.node_mk_tree_list]

/-- A bare binary node (two children) is never the trace leaf (no children). -/
private theorem SO.node_ne_traceLeaf (l r : SO) : SO.node l r ≠ SO.traceLeaf := by
  intro heq
  have ha : (SO.node l r).val.rootChildren = SO.traceLeaf.val.rootChildren := by rw [heq]
  rw [SO.node_val, Nonplanar.rootChildren_node] at ha
  simp only [SO.traceLeaf, Nonplanar.leaf_def, Nonplanar.rootChildren_mk, RoseTree.children,
    Multiset.insert_eq_cons] at ha
  exact Multiset.cons_ne_zero ha

/-- **Lemma 1.** A successful `toPlanarLeaf?` projects (under `Nonplanar.mk`) back to the
    `SO` it came from, and is a well-formed planar leaf. -/
private theorem toPlanarLeaf?_mk {s : SO} {ip : RoseTree SOLabel} (h : s.toPlanarLeaf? = some ip) :
    Nonplanar.mk ip = s.val ∧ isSOPlanar ip = true := by
  induction s using SO.ind with
  | lex tok =>
    rw [SO.toPlanarLeaf?, SO.getLIToken_lexLeaf] at h
    obtain rfl : ip = SO.leafP tok := by simpa using h.symm
    exact ⟨rfl, rfl⟩
  | trace =>
    rw [SO.toPlanarLeaf?, SO.getLIToken_traceLeaf, if_pos rfl] at h
    obtain rfl : ip = SO.traceP := by simpa using h.symm
    exact ⟨rfl, rfl⟩
  | node l r _ _ =>
    rw [SO.toPlanarLeaf?, SO.getLIToken_node, if_neg (SO.node_ne_traceLeaf l r)] at h
    exact absurd h (by simp)

/-- **Lemma 2.** `projEqP target s` certifies that `s` projects to `target`. -/
private theorem projEqP_eq {target : SO} {s : RoseTree SOLabel} (h : projEqP target s = true) :
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
    (ht : isSOPlanar (SO.nodeP l r) = true) : isSOPlanar l = true ∧ isSOPlanar r = true := by
  rw [SO.nodeP, isSOPlanar, isSOPlanarList, isSOPlanarList, isSOPlanarList,
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
private theorem not_projEqP {target : SO} {s : RoseTree SOLabel}
    (h : ¬ projEqP target s = true) : Nonplanar.mk s ≠ target.val := by
  rw [projEqP, decide_eq_true_eq] at h; exact h

/-- **Lemma 4 (CRUX): the replace bridge.** On a well-formed planar tree, the computable
    planar replacement (`planarReplaceWhereP (projEqP target) SO.traceP`) projects under
    `Nonplanar.mk` to the abstract structural substitution `replaceN target SO.traceLeaf`,
    and stays well-formed. The two `if`-conditions agree (`projEqP target s = true ↔
    Nonplanar.mk s = target.val`), and the recursive bare-binary case lines up with
    `replaceN_node`'s else branch (`{·,·}` multiset built from the two daughters). -/
private theorem replaceWhereP_mk (target : SO) {t : RoseTree SOLabel} (ht : isSOPlanar t = true) :
    Nonplanar.mk (planarReplaceWhereP (projEqP target) SO.traceP t)
        = replaceN target.val SO.traceLeaf.val (Nonplanar.mk t)
      ∧ isSOPlanar (planarReplaceWhereP (projEqP target) SO.traceP t) = true := by
  fun_induction planarReplaceWhereP (projEqP target) SO.traceP t with
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
    rw [show RoseTree.node (Sum.inr ()) [planarReplaceWhereP (projEqP target) SO.traceP l,
          planarReplaceWhereP (projEqP target) SO.traceP r]
        = SO.nodeP (planarReplaceWhereP (projEqP target) SO.traceP l)
          (planarReplaceWhereP (projEqP target) SO.traceP r) from rfl,
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
    accumulator stays well-formed and projects to the abstract `SO.Step.apply`. -/
private theorem externStepP_step {acc : SO} {accp p' : RoseTree SOLabel} {step : SO.Step}
    (h : externStepP (some accp) step = some p') (hwf : isSOPlanar accp = true)
    (hmk : Nonplanar.mk accp = acc.val) :
    isSOPlanar p' = true ∧ Nonplanar.mk p' = (step.apply acc).val := by
  cases step with
  | emL item =>
    change item.toPlanarLeaf?.map (fun p => SO.nodeP p accp) = some p' at h
    rcases hip : item.toPlanarLeaf? with _ | ip
    · rw [hip, Option.map_none] at h; exact absurd h (by simp)
    · rw [hip, Option.map_some] at h
      obtain rfl := Option.some.inj h
      obtain ⟨hmkip, hwfip⟩ := toPlanarLeaf?_mk hip
      refine ⟨isSOPlanar_nodeP hwfip hwf, ?_⟩
      rw [SO.Step.apply, SO.merge_val, mk_nodeP, hmkip, hmk]
  | emR item =>
    change item.toPlanarLeaf?.map (fun p => SO.nodeP accp p) = some p' at h
    rcases hip : item.toPlanarLeaf? with _ | ip
    · rw [hip, Option.map_none] at h; exact absurd h (by simp)
    · rw [hip, Option.map_some] at h
      obtain rfl := Option.some.inj h
      obtain ⟨hmkip, hwfip⟩ := toPlanarLeaf?_mk hip
      refine ⟨isSOPlanar_nodeP hwf hwfip, ?_⟩
      rw [SO.Step.apply, SO.merge_val, mk_nodeP, hmkip, hmk]
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
      rw [SO.Step.apply, SO.intMerge_val, SO.deleteAccessible_val, mk_nodeP, hmks, hrwe, hmk]
      exact congrArg (Nonplanar.node (Sum.inr ())) (Multiset.cons_swap _ _ _)

/-- `none` is absorbing for the replay fold: once externalization fails, it stays failed. -/
private theorem foldl_externStepP_none (steps : List SO.Step) :
    steps.foldl externStepP none = none := by
  induction steps with
  | nil => rfl
  | cons st rest ih => rw [List.foldl_cons, show externStepP none st = none from rfl]; exact ih

/-- **Lemma 7: foldl faithfulness.** A successful replay fold from a well-formed,
    faithful accumulator projects to the abstract `final`-style fold of `SO.Step.apply`. -/
private theorem foldl_externStepP_mk : ∀ (steps : List SO.Step) {acc : SO} {accp p : RoseTree SOLabel},
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
theorem SO.Derivation.externalizeP?_faithful (d : SO.Derivation) {p : RoseTree SOLabel}
    (h : d.externalizeP? = some p) : Nonplanar.mk p = d.final.val := by
  rw [SO.Derivation.externalizeP?] at h
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

private def xN : SO := SO.mkLeaf .N [] 1
private def xA : SO := SO.mkLeaf .A [] 2
private def xNum : SO := SO.mkLeaf .Num [] 3
private def xD : SO := SO.mkLeaf .D [] 4
/-- The pied-piped `[N [A t]]` mover (built planar-first, so it is computable). -/
private def xNAt : SO :=
  SO.ofPlanar (SO.nodeP (SO.leafP ⟨.simple .N [], 1⟩)
    (SO.nodeP (SO.leafP ⟨.simple .A [], 2⟩) SO.traceP))
/-- The pied-piped `[A N]` mover. -/
private def xAN : SO :=
  SO.ofPlanar (SO.nodeP (SO.leafP ⟨.simple .A [], 2⟩) (SO.leafP ⟨.simple .N [], 1⟩))

/-- No movement: `Dem Num A N`. -/
private def xDerivBase : SO.Derivation :=
  ⟨xN, [.emL xA, .emL xNum, .emL xD]⟩
/-- Raise N around A, pied-pipe `[N A]` around Num: `Dem N A Num`. -/
private def xDerivO : SO.Derivation :=
  ⟨xN, [.emL xA, .im xN, .emL xNum, .im xNAt, .emL xD]⟩
/-- Pied-pipe `[A N]` around Num, no sub-raise: `Dem A N Num`. -/
private def xDerivN : SO.Derivation :=
  ⟨xN, [.emL xA, .emL xNum, .im xAN, .emL xD]⟩

example : xDerivBase.surfaceCats = [.D, .Num, .A, .N] := by decide
example : xDerivO.surfaceCats = [.D, .N, .A, .Num] := by decide
example : xDerivN.surfaceCats = [.D, .A, .N, .Num] := by decide
/-- Pied-piping preserves internal order: `o` and `n` diverge. -/
example : xDerivO.surfaceCats ≠ xDerivN.surfaceCats := by decide

end Minimalist
