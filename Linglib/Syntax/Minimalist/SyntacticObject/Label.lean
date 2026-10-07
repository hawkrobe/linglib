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

[marcolli-chomsky-berwick-2025] also require the head function to be raising (Definition 1.15.1):
the object Internal Merge forms is headed by the head of what it raised out of, so the landing site
of a wh-phrase in the specifier of a C is headed by C. The raising head `raisingHead` reads this
off the finished object: where two phrases merge and the head of one has a lower copy inside the
other, the first has raised out of the second, which projects. It extends the label
(`raisingHead_eq_of_label`).

## Implementation notes

* The selection head and the label are not raising: they leave a landing site, two saturated
  phrases, without a head, as [chomsky-2013]'s (21) requires of an intermediate landing site.
* The raising head reads Definition 1.15.1 on the finished object, a lower copy recording the token
  that heads the phrase it copies; the phases of `SyntacticObject/Phase.lean` are delimited by it.

## Main definitions

* `Minimalist.LabelState`: a selection state or a lower copy, a commutative magma with zero.
* `Minimalist.SyntacticObject.labelCheck`, `Minimalist.SyntacticObject.label`: the labeling state
  and the label of a syntactic object.
* `Minimalist.RaisingState`, `Minimalist.SyntacticObject.raisingHead`: the raising state and the
  raising head of a syntactic object.

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

/-- A constituent's labeling state is its selection state, or a lower copy of the phrase a token
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

/-- The label a labeling state provides is the head of a visible constituent, and none for a lower
copy. -/
def label : LabelState → Option LIToken
  | sel x => x.head
  | copy _ => none

/-- A labeling state never combines with itself. -/
@[simp] theorem mul_self (l : LabelState) : l * l = 0 := by
  rcases l with x | a
  · show sel (x * x) = sel 0
    rw [SelectionState.mul_self]
  · rfl

/-- The head of a labeling product is a daughter's head. -/
theorem label_mul {x y : LabelState} {h : LIToken} (hxy : (x * y).label = some h) :
    x.label = some h ∨ y.label = some h := by
  rcases x with x | a <;> rcases y with y | b
  · exact SelectionState.head_mul hxy
  · rw [sel_mul_copy] at hxy
    split_ifs at hxy with h0
    · exact .inl hxy
    · change (x * SelectionState.of b []).head = some h at hxy
      rw [_root_.mul_comm x] at hxy
      exact .inl (SelectionState.head_of_mul_of hxy)
  · rw [copy_mul_sel] at hxy
    split_ifs at hxy with h0
    · exact .inr hxy
    · exact .inr (SelectionState.head_of_mul_of hxy)
  · cases hxy

end LabelState

/-- A trace's labeling state is the lower copy of the phrase its token heads; the bare trace, which
remembers no token and belongs to no chain, keeps its selection state. -/
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

/-! ### The raising head -/

/-- The raising state of a constituent pairs its labeling state with the tokens whose lower copies
it contains. -/
structure RaisingState where
  /-- The labeling state. -/
  label : LabelState
  /-- The tokens heading the phrases of which the constituent contains a lower copy. -/
  copies : Multiset LIToken
  deriving DecidableEq

namespace RaisingState

instance : Zero RaisingState := ⟨⟨0, 0⟩⟩

/-- Under raising, two merged constituents take the labeling product where it is defined, and
otherwise the labeling state of the one containing a lower copy of the other's head, since the
other raised out of it and it projects. -/
def raise (x y : RaisingState) : LabelState :=
  if x.label * y.label ≠ 0 then x.label * y.label else
  match x.label.label, y.label.label with
  | some a, some b =>
    if a ∈ y.copies ∧ b ∉ x.copies then y.label
    else if b ∈ x.copies ∧ a ∉ y.copies then x.label else 0
  | _, _ => 0

instance : Mul RaisingState := ⟨fun x y ↦ ⟨raise x y, x.copies + y.copies⟩⟩

theorem mul_def (x y : RaisingState) : x * y = ⟨raise x y, x.copies + y.copies⟩ := rfl

theorem raise_comm (x y : RaisingState) : raise x y = raise y x := by
  unfold raise
  rw [mul_comm y.label]
  split_ifs with h₁
  · rfl
  · rcases hx : x.label.label with _ | a <;> rcases hy : y.label.label with _ | b <;> simp only
    grind

instance : CommMagma RaisingState where
  mul_comm x y := by simp only [mul_def, raise_comm, add_comm]

end RaisingState

/-- A trace's raising state is the lower copy of the phrase its token heads, with the token recorded
among the copies; the bare trace remembers no token. -/
def raisingTraceState : Option LIToken → RaisingState
  | some tok => ⟨.copy tok, {tok}⟩
  | none => ⟨.sel (traceState none), 0⟩

namespace SyntacticObject

variable (s : SyntacticObject)

/-- The raising state of a syntactic object. -/
def raisingCheck : RaisingState :=
  liftFun (fun tok ↦ ⟨.sel (.of tok tok.item.outerSel), 0⟩) raisingTraceState s

/-- The raising head of a syntactic object, [marcolli-chomsky-berwick-2025]'s raising head
function: the label where there is one, and at a landing site the head of the phrase moved out
of. -/
def raisingHead : Option LIToken := s.raisingCheck.label.label

@[simp] theorem raisingCheck_merge (l r : SyntacticObject) :
    (merge l r).raisingCheck = l.raisingCheck * r.raisingCheck :=
  liftFun_merge _ _ l r

/-- The raising state refines the labeling state. -/
theorem raisingCheck_label_eq_or : s.raisingCheck.label = s.labelCheck ∨ s.labelCheck = 0 := by
  induction s using SyntacticObject.ind with
  | leaf tok => exact .inl rfl
  | trace => exact .inl rfl
  | traceOf tok => exact .inl rfl
  | merge l r ihl ihr =>
    rw [raisingCheck_merge, labelCheck_merge, RaisingState.mul_def]
    rcases ihl with hl | hl
    · rcases ihr with hr | hr
      · simp only [RaisingState.raise, hl, hr]
        split_ifs with h0
        · exact .inl rfl
        · exact .inr (not_not.1 h0)
      · exact .inr (by rw [hr, mul_zero])
    · exact .inr (by rw [hl, zero_mul])

/-- The raising head extends the label. -/
theorem raisingHead_eq_of_label {a : LIToken} (hs : s.label = some a) : s.raisingHead = some a := by
  rcases s.raisingCheck_label_eq_or with hl | hl
  · rw [raisingHead, hl]; exact hs
  · rw [label, hl] at hs
    exact absurd (show (none : Option LIToken) = some a from hs) (Option.some_ne_none a).symm

/-- The raising head of a merge is a daughter's raising head
([marcolli-chomsky-berwick-2025] Lemma 1.13.7). -/
theorem raisingHead_merge {l r : SyntacticObject} {h : LIToken}
    (hlr : (merge l r).raisingHead = some h) : l.raisingHead = some h ∨ r.raisingHead = some h := by
  simp only [raisingHead, raisingCheck_merge, RaisingState.mul_def, RaisingState.raise] at hlr ⊢
  split_ifs at hlr with h0
  · exact LabelState.label_mul hlr
  · rcases hx : l.raisingCheck.label.label with _ | a <;>
      rcases hy : r.raisingCheck.label.label with _ | b <;> simp only [hx, hy] at hlr ⊢
    · cases hlr
    · cases hlr
    · cases hlr
    · split_ifs at hlr
      · right; simp_all
      · left; simp_all
      · exact absurd (show (none : Option LIToken) = some h from hlr) (by simp)

/-- An object merged with itself has no raising head. -/
@[simp] theorem raisingHead_merge_self (x : SyntacticObject) : (merge x x).raisingHead = none := by
  rw [raisingHead, raisingCheck_merge, RaisingState.mul_def]
  simp only [RaisingState.raise, LabelState.mul_self, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases x.raisingCheck.label.label with _ | a
  · rfl
  · dsimp only
    split_ifs with h₁ <;> first | rfl | exact (h₁.2 h₁.1).elim

end SyntacticObject

end Minimalist
