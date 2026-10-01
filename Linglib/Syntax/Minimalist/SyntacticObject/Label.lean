/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# The labeling algorithm

The labeling algorithm of [chomsky-2013] is minimal search for the head that tells the interfaces
what kind of object a constituent is. A head merged with a phrase labels the result. Two phrases
do not: minimal search finds two heads, and the object is labeled only if one of the phrases
raises, its lower copy being invisible to the search, or if the two heads share an agreed
feature. [marcolli-chomsky-berwick-2025] (Definition 1.15.2) state the algorithm over a partial
head function: label by the head where it is defined, and where a term has raised, by the head of
the object with the lower copy deleted. Here the head function is the selection head `selHead`
and a lower copy is the trace of a token: it still satisfies the selection of whatever selected
the phrase it copies (`traceState`), and is otherwise invisible. So the labeling state of a
constituent is its selection state, or a lower copy (`LabelState`), and the label extends the
selection head (`label_eq_of_selHead`): a lower copy beside a saturated phrase leaves the phrase
to label their sum (`label_merge_traceOf`), and two saturated phrases leave it unlabeled
(`label_merge_eq_none`), the configuration [chomsky-2013] takes to force successive-cyclic
movement.

## Implementation notes

[marcolli-chomsky-berwick-2025] require the head function to be raising (Definition 1.15.1): the
object Internal Merge forms is headed by the head of what it raised out of, so the landing site of
a wh-phrase in the specifier of a C would be headed by C. The selection head is not raising, and
leaves that object, two saturated phrases, without a head, as [chomsky-2013]'s (21) requires of
an intermediate landing site.

## Main definitions

* `Minimalist.LabelState`: a selection state or a lower copy, a commutative magma with zero.
* `Minimalist.SyntacticObject.labelCheck`, `Minimalist.SyntacticObject.label`: the labeling state
  and the label of a syntactic object.

## TODO

The labeling of two phrases by a feature their heads share, the interrogative feature of an
indirect question or the φ-features of subject and predicate, which [chomsky-2013] requires to be
agreed rather than merely matched, needs Agree and is not formalized. The trace of a token is the
lower copy of the phrase the token heads; a moved head, whose lower copy would still select, is
not distinguished.

## References

* [chomsky-2013]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

/-- A constituent's labeling state: its selection state, or a lower copy of the phrase a token
heads, which satisfies selection as that phrase and is otherwise invisible to the labeling
algorithm. -/
inductive LabelState where
  /-- The selection state of a constituent the labeling algorithm sees. -/
  | sel (x : SelectionState)
  /-- A lower copy of the phrase `tok` heads. -/
  | copy (tok : LIToken)
  deriving DecidableEq

namespace LabelState

instance : Zero LabelState := ⟨sel 0⟩

/-- A lower copy satisfies the selection of a sister selecting the phrase it copies and is
otherwise invisible; two lower copies leave nothing to see. -/
instance : Mul LabelState where
  mul
    | sel x, sel y => sel (x * y)
    | copy a, sel y => if SelectionState.of a [] * y = 0 then sel y else sel (.of a [] * y)
    | sel x, copy a => if x * SelectionState.of a [] = 0 then sel x else sel (x * .of a [])
    | copy _, copy _ => 0

@[simp] theorem sel_mul_sel (x y : SelectionState) : sel x * sel y = sel (x * y) := rfl

theorem copy_mul_sel (a : LIToken) (y : SelectionState) :
    copy a * sel y = if SelectionState.of a [] * y = 0 then sel y else sel (.of a [] * y) := rfl

theorem sel_mul_copy (x : SelectionState) (a : LIToken) :
    sel x * copy a = if x * SelectionState.of a [] = 0 then sel x else sel (x * .of a []) := rfl

instance : CommMagma LabelState where
  mul_comm
    | sel x, sel y => congrArg sel (mul_comm x y)
    | copy a, sel y | sel y, copy a => by
      show (if _ = _ then _ else _) = (if _ = _ then _ else _)
      rw [mul_comm y]
    | copy _, copy _ => rfl

instance : MulZeroClass LabelState where
  zero_mul
    | sel _ => rfl
    | copy a => by rw [show (0 : LabelState) = sel 0 from rfl, sel_mul_copy]; simp
  mul_zero
    | sel x => congrArg sel (mul_zero x)
    | copy a => by rw [show (0 : LabelState) = sel 0 from rfl, copy_mul_sel]; simp

/-- The label a labeling state provides: the head of a visible constituent, none for a lower
copy. -/
def label : LabelState → Option LIToken
  | sel x => x.head
  | copy _ => none

end LabelState

/-- The labeling state of a trace: the lower copy of the phrase its token heads, and for the bare
trace, which remembers no token and belongs to no chain, its selection state. -/
def labelTraceState : Option LIToken → LabelState
  | some tok => .copy tok
  | none => .sel (traceState none)

namespace SyntacticObject

variable (s : SyntacticObject)

/-- The labeling state of a syntactic object. -/
def labelCheck : LabelState :=
  liftFun (fun tok ↦ .sel (.of tok tok.item.outerSel)) labelTraceState s

/-- The label of a syntactic object, `none` where the labeling algorithm finds none. -/
def label : Option LIToken := s.labelCheck.label

@[simp] theorem labelCheck_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).labelCheck = .sel (.of tok tok.item.outerSel) := rfl

@[simp] theorem labelCheck_traceOf (tok : LIToken) : (traceOf tok).labelCheck = .copy tok := rfl

@[simp] theorem labelCheck_trace : trace.labelCheck = .sel (traceState none) := rfl

@[simp] theorem labelCheck_merge (l r : SyntacticObject) :
    (merge l r).labelCheck = l.labelCheck * r.labelCheck :=
  liftFun_merge _ _ l r

/-- Where the selection head is defined, the labeling algorithm sees the selection state, unless
the object is itself a lower copy. -/
theorem labelCheck_eq_sel_or (h : s.selCheck ≠ 0) :
    s.labelCheck = .sel s.selCheck ∨ ∃ tok, s = traceOf tok := by
  induction s using SyntacticObject.ind with
  | leaf tok => exact .inl rfl
  | trace => exact .inl rfl
  | traceOf tok => exact .inr ⟨tok, rfl⟩
  | merge l r ihl ihr =>
    left
    rw [selCheck_node] at h
    have hl : l.selCheck ≠ 0 := fun h0 ↦ h (by rw [h0, zero_mul])
    have hr : r.selCheck ≠ 0 := fun h0 ↦ h (by rw [h0, mul_zero])
    rw [labelCheck_merge, selCheck_node]
    rcases ihl hl with hl' | ⟨a, rfl⟩ <;> rcases ihr hr with hr' | ⟨b, rfl⟩
    · rw [hl', hr']; rfl
    · rw [selCheck_traceOf] at h ⊢
      rw [hl', labelCheck_traceOf, LabelState.sel_mul_copy]
      simp [h]
    · rw [selCheck_traceOf] at h ⊢
      rw [hr', labelCheck_traceOf, LabelState.copy_mul_sel]
      simp [h]
    · exact absurd rfl h

/-- The label extends the selection head: where [marcolli-chomsky-berwick-2025]'s head function
is defined, it labels. -/
theorem label_eq_of_selHead {h : LIToken} (hs : s.selHead = some h) (hc : ∀ tok, s ≠ traceOf tok) :
    s.label = some h := by
  have h0 : s.selCheck ≠ 0 := fun h0 ↦ by simp [selHead, h0] at hs
  rcases s.labelCheck_eq_sel_or h0 with hl | ⟨tok, rfl⟩
  · rw [label, hl]; exact hs
  · exact absurd rfl (hc tok)

/-- A lower copy beside a saturated phrase is invisible, so the phrase labels their sum. -/
theorem label_merge_traceOf (a : LIToken) {r : SyntacticObject} {h : LIToken}
    (hr : r.labelCheck = .sel (.of h [])) : (merge (traceOf a) r).label = some h := by
  rw [label, labelCheck_merge, labelCheck_traceOf, hr]
  rfl

/-- Two saturated phrases leave their sum unlabeled. -/
theorem label_merge_eq_none {l r : SyntacticObject} {a b : LIToken}
    (hl : l.labelCheck = .sel (.of a [])) (hr : r.labelCheck = .sel (.of b [])) :
    (merge l r).label = none := by
  rw [label, labelCheck_merge, hl, hr, LabelState.sel_mul_sel]
  rfl

end SyntacticObject

end Minimalist
