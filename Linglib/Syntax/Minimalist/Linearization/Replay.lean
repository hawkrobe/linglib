/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic

/-!
# Derivation-grounded externalization

[marcolli-chomsky-berwick-2025] §1.12. `Derivation.final` is an unordered
object, so the surface left-to-right order is not recoverable from it, but a `Derivation`
records the planarization choices, each step placing its new daughter on the left or the right
edge, MCB's externalization section `σ_L` fixed by the derivation rather
than by a noncanonical choice of representative. `Derivation.replay?` replays the steps on an
ordered configuration, a `PlanarSyntacticObject` with the ordered copies extracted from it, so
surface orders `decide`; it is partial by design, `none` when a merged item is complex, a mover is
absent, or nothing is left to merge back. `Derivation.externalize?` is its object. Traces are
unpronounced, dropped by the yield. The faithfulness theorem `replay?_faithful` says the replay
commutes with forgetting the order: whenever it succeeds, its result is the derivation's own
configuration, so the surface readouts `surfaceTokens`, `surfaceCats` and `surfacePhon` are the
word order of the actual derived syntactic object. Sibling accounts of linearization: the
selection-induced harmonic order (`Linearization/Externalization.lean`) and Fox–Pesetsky cyclic
linearization (`Linearization/Cyclic.lean`).

## Main definitions

* `Minimalist.PlanarSyntacticObject.move`, `Minimalist.externStep`,
  `Minimalist.Derivation.replay?`, `externalize?`: the replay.
* `Minimalist.Derivation.surfaceTokens`, `surfaceCats`, `surfacePhon`.

## Main results

* `Minimalist.Derivation.replay?_faithful`, `externalize?_faithful`: a successful replay forgets
  to `run` and `final`.

## References

* [marcolli-chomsky-berwick-2025], §1.12
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-! ### Operations on ordered trees -/

/-- The ordered leaf of a leaf object; `none` on a complex object. -/
def SyntacticObject.toPlanarLeaf? (s : SyntacticObject) : Option PlanarSyntacticObject :=
  match s.token? with
  | some tok => some (PlanarSyntacticObject.leaf tok)
  | none     => if s = trace then some PlanarSyntacticObject.trace else none

/-- Left-to-right token yield of an ordered tree; traces are unpronounced. -/
def planarYield (t : RoseTree Vertex) : List LexicalItem.Token :=
  t.leafList.filterMap (Sum.elim id fun _ ↦ none)

/-- A subtree projects to `target` when its unordered tree is `target`'s. -/
def projEqP (target : SyntacticObject) (s : RoseTree Vertex) : Bool :=
  decide (UnorderedTree.mk s = target.val)

/-- The leftmost, root-first subtree satisfying `p`. -/
def planarFindP? (p : RoseTree Vertex → Bool) : RoseTree Vertex → Option (RoseTree Vertex)
  | t@(.node _ [])     => if p t then some t else none
  | t@(.node _ [l, r]) => if p t then some t else (planarFindP? p l).or (planarFindP? p r)
  | t@(.node _ _)      => if p t then some t else none

/-- Replace every subtree satisfying `p` by `rep`. -/
def planarReplaceWhereP (p : RoseTree Vertex → Bool) (rep : RoseTree Vertex) :
    RoseTree Vertex → RoseTree Vertex
  | t@(.node _ [])     => if p t then rep else t
  | t@(.node a [l, r]) =>
      if p t then rep
      else .node a [planarReplaceWhereP p rep l, planarReplaceWhereP p rep r]
  | t@(.node _ _)      => if p t then rep else t

private theorem projEqP_eq {target : SyntacticObject} {s : RoseTree Vertex}
    (h : projEqP target s = true) : UnorderedTree.mk s = target.val := of_decide_eq_true h

private theorem not_projEqP {target : SyntacticObject} {s : RoseTree Vertex}
    (h : ¬ projEqP target s = true) : UnorderedTree.mk s ≠ target.val := by
  rw [projEqP, decide_eq_true_eq] at h; exact h

/-- A subtree raised by `planarFindP?` satisfies the predicate. -/
private theorem planarFindP?_pred {p : RoseTree Vertex → Bool} {t s : RoseTree Vertex}
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

/-- A subtree raised by `planarFindP?` from a well-formed tree is well-formed. -/
private theorem planarFindP?_isSyntacticObject {p : RoseTree Vertex → Bool}
    {t s : RoseTree Vertex} (h : planarFindP? p t = some s)
    (ht : IsSyntacticObject (UnorderedTree.mk t)) : IsSyntacticObject (UnorderedTree.mk s) := by
  fun_induction planarFindP? p t generalizing s with
  | case1 => obtain rfl := Option.some.inj h; exact ht
  | case2 => exact absurd h (by simp)
  | case3 => obtain rfl := Option.some.inj h; exact ht
  | case4 a l r _ ihl ihr =>
    obtain rfl := eq_bare_of_ne_nil ht (by simp)
    obtain ⟨hl', hr'⟩ := (isSyntacticObject_mk_merge l r).mp ht
    rcases hlf : planarFindP? p l with _ | sl
    · rw [hlf, Option.none_or] at h; exact ihr h hr'
    · rw [hlf, Option.some_or] at h; obtain rfl := Option.some.inj h; exact ihl hlf hl'
  | case5 => obtain rfl := Option.some.inj h; exact ht
  | case6 => exact absurd h (by simp)

/-- The ordered replacement by a well-formed leaf `rep` projecting to `R` forgets to the
    structural substitution `UnorderedTree.replace target R` and stays well-formed. -/
theorem replaceWhereP_mk (target : SyntacticObject) {rep : RoseTree Vertex}
    {R : SyntacticObject} (hrep : IsSyntacticObject (UnorderedTree.mk rep))
    (hmkr : UnorderedTree.mk rep = R.val) {t : RoseTree Vertex}
    (ht : IsSyntacticObject (UnorderedTree.mk t)) :
    UnorderedTree.mk (planarReplaceWhereP (projEqP target) rep t)
        = UnorderedTree.replace target.val R.val (UnorderedTree.mk t)
      ∧ IsSyntacticObject (UnorderedTree.mk (planarReplaceWhereP (projEqP target) rep t)) := by
  fun_induction planarReplaceWhereP (projEqP target) rep t with
  | case1 _ hp =>
    refine ⟨?_, hrep⟩
    rw [projEqP_eq hp, UnorderedTree.replace_self]; exact hmkr
  | case2 b hp =>
    refine ⟨?_, ht⟩
    rw [show UnorderedTree.mk (RoseTree.node b []) = UnorderedTree.leaf b from rfl,
      UnorderedTree.replace_leaf, ite_eq_right]
    rw [show UnorderedTree.leaf b = UnorderedTree.mk (RoseTree.node b []) from rfl]
    exact not_projEqP hp
  | case3 _ _ _ hp =>
    refine ⟨?_, hrep⟩
    rw [projEqP_eq hp, UnorderedTree.replace_self]; exact hmkr
  | case4 a l r hp ihl ihr =>
    obtain rfl := eq_bare_of_ne_nil ht (by simp)
    obtain ⟨hl', hr'⟩ := (isSyntacticObject_mk_merge l r).mp ht
    obtain ⟨ihle, ihls⟩ := ihl hl'
    obtain ⟨ihre, ihrs⟩ := ihr hr'
    refine ⟨?_, (isSyntacticObject_mk_merge _ _).mpr ⟨ihls, ihrs⟩⟩
    have hne : UnorderedTree.node Vertex.bare {UnorderedTree.mk l, UnorderedTree.mk r}
      ≠ target.val := by
      rw [← merge_mk_raw]; exact not_projEqP hp
    rw [merge_mk_raw, ihle, ihre, merge_mk_raw, UnorderedTree.replace_node_pair, ite_eq_right hne]
  | case5 _ cs hnil hpair _ =>
    rcases length_eq_zero_or_two ht with hlen | hlen
    · exact absurd (List.length_eq_zero_iff.mp hlen) hnil
    · obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen; exact absurd rfl (hpair x y)
  | case6 _ cs hnil hpair _ =>
    rcases length_eq_zero_or_two ht with hlen | hlen
    · exact absurd (List.length_eq_zero_iff.mp hlen) hnil
    · obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen; exact absurd rfl (hpair x y)
where
  /-- `UnorderedTree.mk` of the ordered binary node is the unordered binary node. -/
  merge_mk_raw (a b : RoseTree Vertex) :
      UnorderedTree.mk (RoseTree.node Vertex.bare [a, b])
        = UnorderedTree.node Vertex.bare {UnorderedTree.mk a, UnorderedTree.mk b} := by
    rw [show ({UnorderedTree.mk a, UnorderedTree.mk b} : Multiset (UnorderedTree Vertex))
          = Multiset.ofList ([a, b].map UnorderedTree.mk) from rfl, UnorderedTree.node_mk_tree_list]

/-! ### The replay on ordered objects -/

namespace PlanarSyntacticObject

/-- The leftmost subtree projecting to `target`. -/
def find? (target : SyntacticObject) (acc : PlanarSyntacticObject) :
    Option PlanarSyntacticObject :=
  (planarFindP? (projEqP target) acc.val).bind fun s =>
    if h : IsSyntacticObject (UnorderedTree.mk s) then some ⟨s, h⟩ else none

/-- Every subtree projecting to `target` replaced by the leaf `rep`. -/
def replaceWhere (target : SyntacticObject) (rep acc : PlanarSyntacticObject) :
    PlanarSyntacticObject :=
  ⟨planarReplaceWhereP (projEqP target) rep.val acc.val,
    (replaceWhereP_mk target (R := rep.toSyntacticObject) rep.2 rfl acc.2).2⟩

theorem toSyntacticObject_find? {target : SyntacticObject} {acc s : PlanarSyntacticObject}
    (h : find? target acc = some s) : s.toSyntacticObject = target := by
  unfold find? at h
  rcases hf : planarFindP? (projEqP target) acc.val with _ | s'
  · rw [hf] at h; exact absurd h (by simp)
  · rw [hf] at h
    change (if h : IsSyntacticObject (UnorderedTree.mk s') then
      some (⟨s', h⟩ : PlanarSyntacticObject) else none)
      = some s at h
    split at h
    · obtain rfl := Option.some.inj h
      exact Subtype.ext (projEqP_eq (planarFindP?_pred hf))
    · exact absurd h (by simp)

/-- Replacement forgets to the structural substitution `SyntacticObject.replace`. -/
theorem toSyntacticObject_replaceWhere (target : SyntacticObject) (rep acc : PlanarSyntacticObject)
    :
    (replaceWhere target rep acc).toSyntacticObject
      = acc.toSyntacticObject.replace target rep.toSyntacticObject :=
  Subtype.ext (replaceWhereP_mk target (R := rep.toSyntacticObject) rep.2 rfl acc.2).1

end PlanarSyntacticObject

/-- The ordered trace a moved object leaves, `SyntacticObject.headTrace` with its order. -/
def SyntacticObject.tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : PlanarSyntacticObject :=
  (τ s).elim PlanarSyntacticObject.trace PlanarSyntacticObject.traceOf

@[simp] theorem SyntacticObject.toSyntacticObject_tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.tracePlanar τ).toSyntacticObject = s.headTrace τ := by
  unfold tracePlanar headTrace; cases τ s <;> rfl

namespace PlanarSyntacticObject

/-- Internal Merge on the ordered accumulator raises the leftmost subtree projecting to `mover`
    to the edge on `side`, leaving the trace of its head under `τ`; `none` if absent. -/
def move (side : Edge) (acc : PlanarSyntacticObject) (mover : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Option PlanarSyntacticObject :=
  (find? mover acc).map fun s => match side with
    | .left => merge s (replaceWhere mover (mover.tracePlanar τ) acc)
    | .right => merge (replaceWhere mover (mover.tracePlanar τ) acc) s

/-- Internal Merge on the ordered accumulator forgets to Internal Merge on the object. -/
theorem toSyntacticObject_move {side : Edge} {acc p' : PlanarSyntacticObject}
    {mover : SyntacticObject} {τ : SyntacticObject → Option LexicalItem.Token}
    (h : move side acc mover τ = some p') :
    p'.toSyntacticObject = SyntacticObject.merge
      (deleteAccessible mover acc.toSyntacticObject τ) mover := by
  unfold move at h
  rcases hf : find? mover acc with _ | s
  · rw [hf, Option.map_none] at h; exact absurd h (by simp)
  · rw [hf, Option.map_some] at h
    obtain rfl := Option.some.inj h
    cases side
    · rw [toSyntacticObject_merge, toSyntacticObject_find? hf, toSyntacticObject_replaceWhere,
        toSyntacticObject_tracePlanar, SyntacticObject.merge_comm]
      rfl
    · rw [toSyntacticObject_merge, toSyntacticObject_find? hf, toSyntacticObject_replaceWhere,
        toSyntacticObject_tracePlanar]
      rfl

end PlanarSyntacticObject

open Derivation (Cfg) in
/-- One replay step, mirroring `Step.run`, where an extraction stacks the ordered copy it
finds. -/
def externStep (τ : SyntacticObject → Option LexicalItem.Token) :
    Option (Cfg PlanarSyntacticObject) → Step → Option (Cfg PlanarSyntacticObject)
  | some ⟨acc, st⟩, .em .left item => item.toPlanarLeaf?.map fun i ↦ ⟨.merge i acc, st⟩
  | some ⟨acc, st⟩, .em .right item => item.toPlanarLeaf?.map fun i ↦ ⟨.merge acc i, st⟩
  | some ⟨acc, st⟩, .im mover side => (acc.move side mover τ).map fun p ↦ ⟨p, st⟩
  | some ⟨acc, st⟩, .extract mover => (PlanarSyntacticObject.find? mover acc).map fun s ↦
      ⟨PlanarSyntacticObject.replaceWhere mover (mover.tracePlanar τ) acc, s :: st⟩
  | some ⟨acc, m :: st⟩, .remerge .left => some ⟨.merge m acc, st⟩
  | some ⟨acc, m :: st⟩, .remerge .right => some ⟨.merge acc m, st⟩
  | some ⟨_, []⟩, .remerge _ | none, _ => none

namespace Derivation

/-- The derivation's ordered configuration under the trace encoder `τ`, or `none` if a merged item
    is complex, a mover is absent, or `remerge` finds the stack empty. -/
def replay? (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option (Cfg PlanarSyntacticObject) :=
  d.initial.toPlanarLeaf?.bind fun init => d.steps.foldl (externStep τ) (some ⟨init, []⟩)

/-- The derivation's ordered object under the trace encoder `τ`, MCB's `σ_L` for this derivation;
    copies still on the stack are not part of it. -/
def externalize? (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option PlanarSyntacticObject :=
  (d.replay? τ).map (·.current)

/-- The pronounced tokens, left to right; empty if externalization fails. -/
def surfaceTokens (d : Derivation) : List LexicalItem.Token :=
  (d.externalize?.map (planarYield ·.val)).getD []

/-- The surface category sequence, the readout of word-order studies. -/
def surfaceCats (d : Derivation) : List Cat := d.surfaceTokens.map (·.item.cat)

/-- The surface string lists the pronounced forms left to right, dropping empty forms. -/
def surfacePhon (d : Derivation) : List String :=
  d.surfaceTokens.filterMap (·.item.phonForm?)

end Derivation

/-! ### Faithfulness -/

private theorem SyntacticObject.merge_ne_trace (l r : SyntacticObject) : merge l r ≠ trace := by
  intro heq
  have ha : (merge l r).val.children = trace.val.children := by rw [heq]
  rw [merge_val, UnorderedTree.children_node] at ha
  simp only [trace, UnorderedTree.children_mk,
    RoseTree.children, Multiset.insert_eq_cons] at ha
  exact Multiset.cons_ne_zero ha

/-- A successful `toPlanarLeaf?` forgets to the object it came from. -/
private theorem toPlanarLeaf?_toSyntacticObject {s : SyntacticObject} {ip : PlanarSyntacticObject}
    (h : s.toPlanarLeaf? = some ip) : ip.toSyntacticObject = s := by
  induction s using ind with
  | leaf tok =>
    rw [toPlanarLeaf?, token?_leaf] at h
    obtain rfl : ip = PlanarSyntacticObject.leaf tok := by simpa using h.symm
    rfl
  | trace =>
    rw [toPlanarLeaf?, token?_trace, ite_eq_left rfl] at h
    obtain rfl : ip = PlanarSyntacticObject.trace := by simpa using h.symm
    rfl
  | traceOf tok =>
    rw [toPlanarLeaf?, token?_traceOf, ite_eq_right (traceOf_ne_trace tok)] at h
    exact absurd h (by simp)
  | merge l r _ _ =>
    rw [toPlanarLeaf?, token?_merge, ite_eq_right (merge_ne_trace l r)] at h
    exact absurd h (by simp)

open Derivation (Cfg) in
/-- A successful replay step forgets to `Step.run`. -/
private theorem externStep_map {τ : SyntacticObject → Option LexicalItem.Token}
    {c c' : Cfg PlanarSyntacticObject} {step : Step} (h : externStep τ (some c) step = some c') :
    c'.map PlanarSyntacticObject.toSyntacticObject
      = step.run (c.map PlanarSyntacticObject.toSyntacticObject) τ := by
  obtain ⟨acc, st⟩ := c
  cases step with
  | em side item =>
    rcases hip : item.toPlanarLeaf? with _ | ip
    · cases side <;> simp [externStep, hip] at h
    · have hi := toPlanarLeaf?_toSyntacticObject hip
      cases side <;> simp only [externStep, hip, Option.map_some,
        Option.some.injEq] at h <;> subst h <;>
        simp [Cfg.map, Step.run, Step.apply, PlanarSyntacticObject.toSyntacticObject_merge, hi]
  | im mover side =>
    rcases hm : acc.move side mover τ with _ | p'
    · simp [externStep, hm] at h
    · simp only [externStep, hm, Option.map_some, Option.some.injEq] at h
      subst h
      simp [Cfg.map, Step.run, Step.apply, PlanarSyntacticObject.toSyntacticObject_move hm]
  | extract mover =>
    rcases hf : PlanarSyntacticObject.find? mover acc with _ | f
    · simp [externStep, hf] at h
    · simp only [externStep, hf, Option.map_some, Option.some.injEq] at h
      subst h
      simp [Cfg.map, Step.run, Step.apply, deleteAccessible,
        PlanarSyntacticObject.toSyntacticObject_find? hf,
        PlanarSyntacticObject.toSyntacticObject_replaceWhere]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases side <;> simp [externStep] at h
    · cases side <;> simp only [externStep, Option.some.injEq] at h <;>
        subst h <;>
        simp [Cfg.map, Step.run, Step.apply, PlanarSyntacticObject.toSyntacticObject_merge]

open Derivation (Cfg) in
/-- `none` is absorbing for the replay fold. -/
private theorem foldl_externStep_none (τ : SyntacticObject → Option LexicalItem.Token)
    (steps : List Step) :
    steps.foldl (externStep τ) (none : Option (Cfg PlanarSyntacticObject)) = none := by
  induction steps with
  | nil => rfl
  | cons st rest ih => rw [List.foldl_cons, show externStep τ none st = none from rfl]; exact ih

open Derivation (Cfg) in
/-- A successful replay fold forgets to the fold of `Step.run`. -/
private theorem foldl_externStep_map (τ : SyntacticObject → Option LexicalItem.Token) :
    ∀ (steps : List Step) {c p : Cfg PlanarSyntacticObject},
    steps.foldl (externStep τ) (some c) = some p →
    p.map PlanarSyntacticObject.toSyntacticObject
      = steps.foldl (fun c st ↦ st.run c τ) (c.map PlanarSyntacticObject.toSyntacticObject)
  | [], c, p, h => by
      rw [List.foldl_nil] at h ⊢; obtain rfl := Option.some.inj h; rfl
  | st :: rest, c, p, h => by
      rw [List.foldl_cons] at h ⊢
      rcases hstep : externStep τ (some c) st with _ | c'
      · rw [hstep, foldl_externStep_none] at h; exact absurd h (by simp)
      · rw [hstep] at h
        rw [foldl_externStep_map τ rest h, externStep_map hstep]

/-- By **faithfulness** ([marcolli-chomsky-berwick-2025] §1.12), a successful replay forgets to
    the derivation's configuration, the object and every copy on the stack. -/
theorem Derivation.replay?_faithful (d : Derivation)
    {τ : SyntacticObject → Option LexicalItem.Token} {c : Cfg PlanarSyntacticObject}
    (h : d.replay? τ = some c) :
    c.map PlanarSyntacticObject.toSyntacticObject = d.run τ := by
  rw [Derivation.replay?] at h
  rcases hinit : d.initial.toPlanarLeaf? with _ | init
  · rw [hinit] at h; exact absurd h (by simp [Option.bind])
  · rw [hinit] at h
    change d.steps.foldl (externStep τ) (some ⟨init, []⟩) = some c at h
    rw [foldl_externStep_map τ d.steps h]
    simp [Derivation.run, Cfg.map, toPlanarLeaf?_toSyntacticObject hinit]

/-- A successful externalization forgets to the derived object, so the surface readouts are the
    word order of `final` itself. -/
theorem Derivation.externalize?_faithful (d : Derivation)
    {τ : SyntacticObject → Option LexicalItem.Token} {p : PlanarSyntacticObject}
    (h : d.externalize? τ = some p) :
    p.toSyntacticObject = d.final τ := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Derivation.final, ← d.replay?_faithful hc, Cfg.map_current]

/-- Faithfulness holds for prefixes, since a successful replay of the first `n` steps forgets to
    stage `n`. -/
theorem Derivation.externalize?_take_faithful (d : Derivation) (n : Nat)
    {τ : SyntacticObject → Option LexicalItem.Token} {p : PlanarSyntacticObject}
    (h : (d.take n).externalize? τ = some p) :
    p.toSyntacticObject = d.stageAt n τ :=
  externalize?_faithful (d.take n) h

/-! ### The [cinque-2005] pied-piping contrast

Phrasal pied-piping preserves the moved constituent's internal order: raising N around A and
pied-piping `[N A]` around Num gives Dem-N-A-Num, pied-piping `[A N]` around Num gives
Dem-A-N-Num. -/

private def xN : SyntacticObject := mkLeaf .N [] 1
private def xA : SyntacticObject := mkLeaf .A [] 2
private def xNum : SyntacticObject := mkLeaf .Num [] 3
private def xDem : SyntacticObject := mkLeaf .Dem [] 4
/-- The pied-piped `[N [A t]]` mover. -/
private def xNAt : SyntacticObject :=
  (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf ⟨.of .N [], 1⟩)
    (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf ⟨.of .A [], 2⟩)
      (PlanarSyntacticObject.traceOf ⟨.of .N [], 1⟩))).toSyntacticObject
/-- The pied-piped `[A N]` mover. -/
private def xAN : SyntacticObject :=
  (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf ⟨.of .A [], 2⟩)
    (PlanarSyntacticObject.leaf ⟨.of .N [], 1⟩)).toSyntacticObject

/-- Without movement the order is `Dem Num A N`. -/
private def xDerivBase : Derivation := ⟨xN, [.em .left xA, .em .left xNum, .em .left xDem]⟩
/-- Raising N around A and pied-piping `[N A]` around Num gives `Dem N A Num`. -/
private def xDerivO : Derivation :=
  ⟨xN, [.em .left xA, .im xN, .em .left xNum, .im xNAt, .em .left xDem]⟩
/-- Pied-piping `[A N]` around Num without a sub-raise gives `Dem A N Num`. -/
private def xDerivN : Derivation := ⟨xN, [.em .left xA, .em .left xNum, .im xAN, .em .left xDem]⟩

example : xDerivBase.surfaceCats = [.Dem, .Num, .A, .N] := by decide
example : xDerivO.surfaceCats = [.Dem, .N, .A, .Num] := by decide
example : xDerivN.surfaceCats = [.Dem, .A, .N, .Num] := by decide
example : xDerivO.surfaceCats ≠ xDerivN.surfaceCats := by decide

end Minimalist
