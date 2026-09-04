/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Derivation

/-!
# Derivation-grounded externalization

[marcolli-chomsky-berwick-2025] §1.12. `SyntacticObject.Derivation.final` is an unordered
object, so the surface left-to-right order is not recoverable from it, but a `Derivation`
records the planarization choices: `emL` and `im` place material on the left edge, `emR` on
the right, MCB's externalization section `σ_L` fixed by the derivation rather than by a
noncanonical choice of representative. `Derivation.externalize?` replays the steps on an
ordered accumulator, a `PlanarSyntacticObject`, so surface orders `decide`; it is partial by
design, `none` when a merged item is complex or a mover is absent. Traces are unpronounced,
dropped by the yield. The faithfulness theorem `externalize?_faithful` says the replay commutes
with forgetting the order: whenever it succeeds, its result is the derived object itself, so the
surface readouts `surfaceTokens`, `surfaceCats` and `surfacePhon` are the word order of the
actual derived syntactic object. Sibling accounts of linearization: the selection-induced
harmonic order (`Linearization/Externalization.lean`) and Fox–Pesetsky cyclic linearization
(`Linearization/Cyclic.lean`).

## Main definitions

* `Minimalist.PlanarSyntacticObject.moveLeft`, `Minimalist.externStep`,
  `Minimalist.SyntacticObject.Derivation.externalize?`: the replay.
* `Minimalist.SyntacticObject.Derivation.surfaceTokens`, `surfaceCats`, `surfacePhon`.

## Main results

* `Minimalist.SyntacticObject.Derivation.externalize?_faithful`: a successful replay forgets to
  `final`.

## References

* [marcolli-chomsky-berwick-2025], §1.12
-/

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-! ### Operations on ordered trees -/

/-- The ordered leaf of a leaf object; `none` on a complex object. -/
def SyntacticObject.toPlanarLeaf? (s : SyntacticObject) : Option PlanarSyntacticObject :=
  match s.getLIToken with
  | some tok => some (PlanarSyntacticObject.leaf tok)
  | none     => if s = trace then some PlanarSyntacticObject.trace else none

/-- Left-to-right token yield of an ordered tree; traces are unpronounced. -/
def planarYield : RoseTree Vertex → List LIToken
  | .node (.inl tok) _ => [tok]
  | .node (.inr none) [l, r] => planarYield l ++ planarYield r
  | .node (.inr _) _ => []

/-- The subtree projects to `target`: its unordered tree is `target`'s. -/
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

/-- The daughters of a well-formed binary node are well-formed. -/
private theorem wellFormed_pair_children {l r : RoseTree Vertex}
    (ht : wellFormed (.node (Sum.inr none) [l, r]) = true) :
    wellFormed l = true ∧ wellFormed r = true := by
  rwa [wellFormed_merge, Bool.and_eq_true] at ht

/-- A subtree raised by `planarFindP?` from a well-formed tree is well-formed. -/
private theorem planarFindP?_wellFormed {p : RoseTree Vertex → Bool} {t s : RoseTree Vertex}
    (h : planarFindP? p t = some s) (ht : wellFormed t = true) : wellFormed s = true := by
  fun_induction planarFindP? p t generalizing s with
  | case1 => obtain rfl := Option.some.inj h; exact ht
  | case2 => exact absurd h (by simp)
  | case3 => obtain rfl := Option.some.inj h; exact ht
  | case4 a l r _ ihl ihr =>
    have hcase : a = Sum.inr none := by
      match a with
      | .inr none => rfl
      | .inl _ | .inr (some _) => simp [wellFormed] at ht
    subst hcase
    obtain ⟨hl', hr'⟩ := wellFormed_pair_children ht
    rcases hlf : planarFindP? p l with _ | sl
    · rw [hlf, Option.none_or] at h; exact ihr h hr'
    · rw [hlf, Option.some_or] at h; obtain rfl := Option.some.inj h; exact ihl hlf hl'
  | case5 => obtain rfl := Option.some.inj h; exact ht
  | case6 => exact absurd h (by simp)

/-- The ordered replacement by a well-formed leaf `rep` projecting to `R` forgets to the
    structural substitution `UnorderedTree.replace target R` and stays well-formed. -/
private theorem replaceWhereP_mk (target : SyntacticObject) {rep : RoseTree Vertex}
    {R : SyntacticObject} (hrep : wellFormed rep = true) (hmkr : UnorderedTree.mk rep = R.val)
    {t : RoseTree Vertex} (ht : wellFormed t = true) :
    UnorderedTree.mk (planarReplaceWhereP (projEqP target) rep t)
        = UnorderedTree.replace target.val R.val (UnorderedTree.mk t)
      ∧ wellFormed (planarReplaceWhereP (projEqP target) rep t) = true := by
  fun_induction planarReplaceWhereP (projEqP target) rep t with
  | case1 _ hp =>
    refine ⟨?_, hrep⟩
    rw [projEqP_eq hp, UnorderedTree.replace_self]; exact hmkr
  | case2 b hp =>
    refine ⟨?_, ht⟩
    rw [show UnorderedTree.mk (RoseTree.node b []) = UnorderedTree.leaf b from rfl,
      UnorderedTree.replace_leaf, if_neg]
    rw [show UnorderedTree.leaf b = UnorderedTree.mk (RoseTree.node b []) from rfl]
    exact not_projEqP hp
  | case3 _ _ _ hp =>
    refine ⟨?_, hrep⟩
    rw [projEqP_eq hp, UnorderedTree.replace_self]; exact hmkr
  | case4 a l r hp ihl ihr =>
    have hcase : a = Sum.inr none := by
      match a with
      | .inr none => rfl
      | .inl _ | .inr (some _) => simp [wellFormed] at ht
    subst hcase
    obtain ⟨hl', hr'⟩ := wellFormed_pair_children ht
    obtain ⟨ihle, ihls⟩ := ihl hl'
    obtain ⟨ihre, ihrs⟩ := ihr hr'
    refine ⟨?_, by rw [wellFormed_merge, ihls, ihrs]; rfl⟩
    have hne : UnorderedTree.node (Sum.inr none) {UnorderedTree.mk l, UnorderedTree.mk r}
      ≠ target.val := by
      rw [← merge_mk_raw]; exact not_projEqP hp
    rw [merge_mk_raw, ihle, ihre, merge_mk_raw, UnorderedTree.replace_node_pair, if_neg hne]
  | case5 _ cs hnil hpair _ =>
    rcases wellFormed_length ht with hlen | hlen
    · exact absurd (List.length_eq_zero_iff.mp hlen) hnil
    · obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen; exact absurd rfl (hpair x y)
  | case6 _ cs hnil hpair _ =>
    rcases wellFormed_length ht with hlen | hlen
    · exact absurd (List.length_eq_zero_iff.mp hlen) hnil
    · obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen; exact absurd rfl (hpair x y)
where
  /-- `UnorderedTree.mk` of the ordered binary node is the unordered binary node. -/
  merge_mk_raw (a b : RoseTree Vertex) :
      UnorderedTree.mk (RoseTree.node (Sum.inr none) [a, b])
        = UnorderedTree.node (Sum.inr none) {UnorderedTree.mk a, UnorderedTree.mk b} := by
    rw [show ({UnorderedTree.mk a, UnorderedTree.mk b} : Multiset (UnorderedTree Vertex))
          = Multiset.ofList ([a, b].map UnorderedTree.mk) from rfl, UnorderedTree.node_mk_tree_list]

/-! ### The replay on ordered objects -/

namespace PlanarSyntacticObject

/-- The leftmost subtree projecting to `target`. -/
def find? (target : SyntacticObject) (acc : PlanarSyntacticObject) :
    Option PlanarSyntacticObject :=
  (planarFindP? (projEqP target) acc.val).bind fun s =>
    if h : wellFormed s = true then some ⟨s, h⟩ else none

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
    change (if h : wellFormed s' = true then some (⟨s', h⟩ : PlanarSyntacticObject) else none)
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
def SyntacticObject.tracePlanar (s : SyntacticObject) : PlanarSyntacticObject :=
  s.selHead.elim PlanarSyntacticObject.trace PlanarSyntacticObject.traceOf

@[simp] theorem SyntacticObject.toSyntacticObject_tracePlanar (s : SyntacticObject) :
    s.tracePlanar.toSyntacticObject = s.headTrace := by
  unfold tracePlanar headTrace; cases s.selHead <;> rfl

namespace PlanarSyntacticObject

/-- Internal Merge on the ordered accumulator: the leftmost subtree projecting to `mover` is
    raised to the left edge, leaving the trace of its head; `none` if absent. -/
def moveLeft (acc : PlanarSyntacticObject) (mover : SyntacticObject) :
    Option PlanarSyntacticObject :=
  (find? mover acc).map fun s => merge s (replaceWhere mover mover.tracePlanar acc)

/-- Internal Merge on the ordered accumulator forgets to Internal Merge on the object. -/
theorem toSyntacticObject_moveLeft {acc p' : PlanarSyntacticObject} {mover : SyntacticObject}
    (h : moveLeft acc mover = some p') :
    p'.toSyntacticObject = SyntacticObject.merge
      (deleteAccessible mover acc.toSyntacticObject) mover := by
  unfold moveLeft at h
  rcases hf : find? mover acc with _ | s
  · rw [hf, Option.map_none] at h; exact absurd h (by simp)
  · rw [hf, Option.map_some] at h
    obtain rfl := Option.some.inj h
    rw [toSyntacticObject_merge, toSyntacticObject_find? hf, toSyntacticObject_replaceWhere,
      toSyntacticObject_tracePlanar, SyntacticObject.merge_comm]
    rfl

end PlanarSyntacticObject

/-- One replay step, mirroring `SyntacticObject.Step.apply`. -/
def externStep (acc? : Option PlanarSyntacticObject) (step : Step) :
    Option PlanarSyntacticObject :=
  acc?.bind fun acc => match step with
    | .emL item => item.toPlanarLeaf?.map (PlanarSyntacticObject.merge · acc)
    | .emR item => item.toPlanarLeaf?.map (PlanarSyntacticObject.merge acc ·)
    | .im mover => acc.moveLeft mover

namespace SyntacticObject.Derivation

/-- The derivation's ordered object, MCB's `σ_L` for this derivation, or `none` if a merged
    item is complex or a mover is absent. -/
def externalize? (d : Derivation) : Option PlanarSyntacticObject :=
  d.initial.toPlanarLeaf?.bind fun init => d.steps.foldl externStep (some init)

/-- The pronounced tokens, left to right; empty if externalization fails. -/
def surfaceTokens (d : Derivation) : List LIToken :=
  (d.externalize?.map (planarYield ·.val)).getD []

/-- The surface category sequence, the readout of word-order studies. -/
def surfaceCats (d : Derivation) : List Cat := d.surfaceTokens.map (·.item.outerCat)

/-- The surface string: pronounced forms left to right, empty forms dropped. -/
def surfacePhon (d : Derivation) : List String :=
  d.surfaceTokens.filterMap LIToken.phonForm?

end SyntacticObject.Derivation

/-! ### Faithfulness -/

private theorem SyntacticObject.merge_ne_trace (l r : SyntacticObject) : merge l r ≠ trace := by
  intro heq
  have ha : (merge l r).val.rootChildren = trace.val.rootChildren := by rw [heq]
  rw [merge_val, UnorderedTree.rootChildren_node] at ha
  simp only [trace, UnorderedTree.leaf_def, UnorderedTree.rootChildren_mk,
    RoseTree.children, Multiset.insert_eq_cons] at ha
  exact Multiset.cons_ne_zero ha

/-- A successful `toPlanarLeaf?` forgets to the object it came from. -/
private theorem toPlanarLeaf?_toSyntacticObject {s : SyntacticObject} {ip : PlanarSyntacticObject}
    (h : s.toPlanarLeaf? = some ip) : ip.toSyntacticObject = s := by
  induction s using ind with
  | leaf tok =>
    rw [toPlanarLeaf?, getLIToken_leaf] at h
    obtain rfl : ip = PlanarSyntacticObject.leaf tok := by simpa using h.symm
    rfl
  | trace =>
    rw [toPlanarLeaf?, getLIToken_trace, if_pos rfl] at h
    obtain rfl : ip = PlanarSyntacticObject.trace := by simpa using h.symm
    rfl
  | traceOf tok =>
    rw [toPlanarLeaf?, getLIToken_traceOf, if_neg (traceOf_ne_trace tok)] at h
    exact absurd h (by simp)
  | merge l r _ _ =>
    rw [toPlanarLeaf?, getLIToken_merge, if_neg (merge_ne_trace l r)] at h
    exact absurd h (by simp)

/-- A successful replay step forgets to `Step.apply`. -/
private theorem externStep_toSyntacticObject {acc p' : PlanarSyntacticObject} {step : Step}
    (h : externStep (some acc) step = some p') :
    p'.toSyntacticObject = step.apply acc.toSyntacticObject := by
  cases step with
  | emL item =>
    change item.toPlanarLeaf?.map (PlanarSyntacticObject.merge · acc) = some p' at h
    rcases hip : item.toPlanarLeaf? with _ | ip
    · rw [hip, Option.map_none] at h; exact absurd h (by simp)
    · rw [hip, Option.map_some] at h
      obtain rfl := Option.some.inj h
      rw [Step.apply, PlanarSyntacticObject.toSyntacticObject_merge,
        toPlanarLeaf?_toSyntacticObject hip]
  | emR item =>
    change item.toPlanarLeaf?.map (PlanarSyntacticObject.merge acc ·) = some p' at h
    rcases hip : item.toPlanarLeaf? with _ | ip
    · rw [hip, Option.map_none] at h; exact absurd h (by simp)
    · rw [hip, Option.map_some] at h
      obtain rfl := Option.some.inj h
      rw [Step.apply, PlanarSyntacticObject.toSyntacticObject_merge,
        toPlanarLeaf?_toSyntacticObject hip]
  | im mover =>
    change acc.moveLeft mover = some p' at h
    rw [Step.apply]; exact PlanarSyntacticObject.toSyntacticObject_moveLeft h

/-- `none` is absorbing for the replay fold. -/
private theorem foldl_externStep_none (steps : List Step) :
    steps.foldl externStep none = none := by
  induction steps with
  | nil => rfl
  | cons st rest ih => rw [List.foldl_cons, show externStep none st = none from rfl]; exact ih

/-- A successful replay fold forgets to the fold of `Step.apply`. -/
private theorem foldl_externStep_toSyntacticObject :
    ∀ (steps : List Step) {acc p : PlanarSyntacticObject},
    steps.foldl externStep (some acc) = some p →
    p.toSyntacticObject = steps.foldl (fun so st => st.apply so) acc.toSyntacticObject
  | [], acc, p, h => by
      rw [List.foldl_nil] at h ⊢; obtain rfl := Option.some.inj h; rfl
  | st :: rest, acc, p, h => by
      rw [List.foldl_cons] at h ⊢
      rcases hstep : externStep (some acc) st with _ | acc'
      · rw [hstep, foldl_externStep_none] at h; exact absurd h (by simp)
      · rw [hstep] at h
        rw [foldl_externStep_toSyntacticObject rest h, externStep_toSyntacticObject hstep]

/-- **Faithfulness** ([marcolli-chomsky-berwick-2025] §1.12): a successful replay forgets to the
    derived object, so the surface readouts are the word order of `final` itself. -/
theorem SyntacticObject.Derivation.externalize?_faithful (d : Derivation)
    {p : PlanarSyntacticObject} (h : d.externalize? = some p) : p.toSyntacticObject = d.final := by
  rw [Derivation.externalize?] at h
  rcases hinit : d.initial.toPlanarLeaf? with _ | init
  · rw [hinit] at h; exact absurd h (by simp [Option.bind])
  · rw [hinit] at h
    change d.steps.foldl externStep (some init) = some p at h
    rw [foldl_externStep_toSyntacticObject d.steps h, toPlanarLeaf?_toSyntacticObject hinit]
    rfl

/-- Faithfulness for a prefix: a successful replay of the first `n` steps forgets to stage `n`. -/
theorem SyntacticObject.Derivation.externalize?_take_faithful (d : Derivation) (n : Nat)
    {p : PlanarSyntacticObject} (h : (d.take n).externalize? = some p) :
    p.toSyntacticObject = d.stageAt n :=
  externalize?_faithful (d.take n) h

/-! ### The [cinque-2005] pied-piping contrast

Phrasal pied-piping preserves the moved constituent's internal order: raising N around A and
pied-piping `[N A]` around Num gives Dem-N-A-Num, pied-piping `[A N]` around Num gives
Dem-A-N-Num. `.D` stands in for the demonstrative. -/

private def xN : SyntacticObject := mkLeaf .N [] 1
private def xA : SyntacticObject := mkLeaf .A [] 2
private def xNum : SyntacticObject := mkLeaf .Num [] 3
private def xD : SyntacticObject := mkLeaf .D [] 4
/-- The pied-piped `[N [A t]]` mover. -/
private def xNAt : SyntacticObject :=
  (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf ⟨.simple .N [], 1⟩)
    (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf ⟨.simple .A [], 2⟩)
      (PlanarSyntacticObject.traceOf ⟨.simple .N [], 1⟩))).toSyntacticObject
/-- The pied-piped `[A N]` mover. -/
private def xAN : SyntacticObject :=
  (PlanarSyntacticObject.merge (PlanarSyntacticObject.leaf ⟨.simple .A [], 2⟩)
    (PlanarSyntacticObject.leaf ⟨.simple .N [], 1⟩)).toSyntacticObject

/-- No movement: `Dem Num A N`. -/
private def xDerivBase : Derivation := ⟨xN, [.emL xA, .emL xNum, .emL xD]⟩
/-- Raise N around A, pied-pipe `[N A]` around Num: `Dem N A Num`. -/
private def xDerivO : Derivation := ⟨xN, [.emL xA, .im xN, .emL xNum, .im xNAt, .emL xD]⟩
/-- Pied-pipe `[A N]` around Num, no sub-raise: `Dem A N Num`. -/
private def xDerivN : Derivation := ⟨xN, [.emL xA, .emL xNum, .im xAN, .emL xD]⟩

example : xDerivBase.surfaceCats = [.D, .Num, .A, .N] := by decide
example : xDerivO.surfaceCats = [.D, .N, .A, .Num] := by decide
example : xDerivN.surfaceCats = [.D, .A, .N, .Num] := by decide
example : xDerivO.surfaceCats ≠ xDerivN.surfaceCats := by decide

end Minimalist
