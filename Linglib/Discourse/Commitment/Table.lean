import Linglib.Discourse.Commitment.Basic
import Linglib.Discourse.CommonGround
import Linglib.Semantics.Mood.Defs

/-!
# The Table Model
[farkas-bruce-2010]

n-agent table-model substrate: a stack of at-issue items, per-agent
commitment slates, and a common ground.

## Main definitions

* `Item A W` — speaker, addressee, mood, alternatives.
* `DiscourseState A W I` — ⟨table, dc, cg⟩, polymorphic in the
  table-element type `I` (full model: `I := Item A W`).
* `DiscourseState.IsStable` — empty-table predicate.
* `pushItem`, `popItem`, `addCommit`, `addToCG` — primitive updates.

## TODO

* Projected set `ps(CommonGround)`, highlighting ([farkas-roelofsen-2017]),
  item identity (for withdrawal).
-/

namespace Discourse.Commitment.Table

open Discourse.Commitment (TaggedSlate CommitmentSource CommitmentForce)
open CommonGround (HasContextSet)
open Semantics.Mood (Illocutionary)

/-- An at-issue item on the conversational table. -/
structure Item (A W : Type*) where
  /-- Speaker of the utterance. -/
  speaker : A
  /-- Addressee. -/
  addressee : A
  /-- Illocutionary force. -/
  mood : Illocutionary
  /-- Alternatives at issue: `[p]` for assertion, `[p, ¬p]` for
      polar question, the answer set for wh-questions. -/
  alternatives : List (W → Prop)

/-- The discourse structure (DS) of [farkas-bruce-2010], polymorphic
    in the table-element type `I` (full model: `I := Item A W`). -/
structure DiscourseState (A W I : Type*) where
  /-- Stack of unresolved items, head = most recent. -/
  table : List I
  /-- Per-agent discourse commitments. -/
  dc : A → TaggedSlate W
  /-- The common ground. -/
  cg : CommonGround W

namespace DiscourseState
variable {A W I : Type*}

/-- Initial state: empty table, empty commitments, trivial CommonGround. -/
def empty : DiscourseState A W I :=
  ⟨[], fun _ => TaggedSlate.empty, CommonGround.empty⟩

instance : Inhabited (DiscourseState A W I) := ⟨empty⟩

/-- The state is stable when the table is empty. -/
def IsStable (s : DiscourseState A W I) : Prop := s.table.isEmpty = true

instance (s : DiscourseState A W I) : Decidable s.IsStable :=
  inferInstanceAs (Decidable (_ = _))

/-- Worlds compatible with the common ground. -/
def contextSet (s : DiscourseState A W I) : Set W := s.cg.contextSet

/-! ### Commitment accessors

First-class views of an agent's commitments, collapsing the `(s.dc a).proj`
two-step that recurs across consumers. -/

/-- Agent `a`'s doxastic (act-as-if-believe) commitments, untagged. -/
def doxasticOf (s : DiscourseState A W I) (a : A) : List (W → Prop) :=
  (s.dc a).doxasticContents

/-- `a` is doxastically committed to `p`. -/
def Commits (s : DiscourseState A W I) (a : A) (p : W → Prop) : Prop :=
  p ∈ s.doxasticOf a

/-- The common-ground propositions. -/
def cgPropositions (s : DiscourseState A W I) : List (Set W) :=
  s.cg.propositions

/-! ### Primitive updates -/

def pushItem (s : DiscourseState A W I) (i : I) : DiscourseState A W I :=
  { s with table := i :: s.table }

def popItem (s : DiscourseState A W I) : DiscourseState A W I :=
  { s with table := s.table.tail }

def addToCG (s : DiscourseState A W I) (p : W → Prop) : DiscourseState A W I :=
  { s with cg := s.cg.add p }

/-- Add `(p, src, force)` to agent `a`'s slate. Defaults: self-generated,
    doxastic — the standard assertion-driven cell. -/
def addCommit [DecidableEq A] (s : DiscourseState A W I) (a : A)
    (p : W → Prop)
    (src : CommitmentSource := .selfGenerated)
    (force : CommitmentForce := .doxastic) : DiscourseState A W I :=
  { s with dc := Function.update s.dc a ((s.dc a).add p src force) }

/-! ### Basic theorems -/

@[simp] theorem empty_table : (empty : DiscourseState A W I).table = [] := rfl
@[simp] theorem empty_dc (a : A) :
    (empty : DiscourseState A W I).dc a = TaggedSlate.empty := rfl
@[simp] theorem empty_cg : (empty : DiscourseState A W I).cg = CommonGround.empty := rfl
@[simp] theorem empty_isStable : (empty : DiscourseState A W I).IsStable := rfl

@[simp] theorem pushItem_table (s : DiscourseState A W I) (i : I) :
    (s.pushItem i).table = i :: s.table := rfl
@[simp] theorem pushItem_dc (s : DiscourseState A W I) (i : I) :
    (s.pushItem i).dc = s.dc := rfl
@[simp] theorem pushItem_cg (s : DiscourseState A W I) (i : I) :
    (s.pushItem i).cg = s.cg := rfl

@[simp] theorem popItem_table (s : DiscourseState A W I) :
    s.popItem.table = s.table.tail := rfl
@[simp] theorem popItem_dc (s : DiscourseState A W I) : s.popItem.dc = s.dc := rfl
@[simp] theorem popItem_cg (s : DiscourseState A W I) : s.popItem.cg = s.cg := rfl

@[simp] theorem addToCG_cg (s : DiscourseState A W I) (p : W → Prop) :
    (s.addToCG p).cg = s.cg.add p := rfl
@[simp] theorem addToCG_table (s : DiscourseState A W I) (p : W → Prop) :
    (s.addToCG p).table = s.table := rfl
@[simp] theorem addToCG_dc (s : DiscourseState A W I) (p : W → Prop) :
    (s.addToCG p).dc = s.dc := rfl

@[simp] theorem addCommit_table [DecidableEq A] (s : DiscourseState A W I)
    (a : A) (p : W → Prop) (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).table = s.table := rfl
@[simp] theorem addCommit_cg [DecidableEq A] (s : DiscourseState A W I)
    (a : A) (p : W → Prop) (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).cg = s.cg := rfl

@[simp] theorem addCommit_dc_self [DecidableEq A] (s : DiscourseState A W I)
    (a : A) (p : W → Prop) (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).dc a = (s.dc a).add p src force := by
  simp [addCommit]

@[simp] theorem addCommit_dc_of_ne [DecidableEq A] (s : DiscourseState A W I)
    {a b : A} (h : b ≠ a) (p : W → Prop)
    (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).dc b = s.dc b := by
  simp [addCommit, Function.update_of_ne h]

/-! ### Accessor reductions -/

@[simp] theorem doxasticOf_addCommit_self [DecidableEq A] (s : DiscourseState A W I)
    (a : A) (p : W → Prop) (src : CommitmentSource) :
    (s.addCommit a p src .doxastic).doxasticOf a = p :: s.doxasticOf a := by
  simp [doxasticOf]

@[simp] theorem doxasticOf_addCommit_of_ne [DecidableEq A] (s : DiscourseState A W I)
    {a b : A} (h : b ≠ a) (p : W → Prop) (src : CommitmentSource)
    (force : CommitmentForce) :
    (s.addCommit a p src force).doxasticOf b = s.doxasticOf b := by
  simp [doxasticOf, h]

@[simp] theorem doxasticOf_pushItem (s : DiscourseState A W I) (i : I) (a : A) :
    (s.pushItem i).doxasticOf a = s.doxasticOf a := rfl

@[simp] theorem doxasticOf_popItem (s : DiscourseState A W I) (a : A) :
    s.popItem.doxasticOf a = s.doxasticOf a := rfl

@[simp] theorem cgPropositions_popItem (s : DiscourseState A W I) :
    s.popItem.cgPropositions = s.cgPropositions := rfl

@[simp] theorem doxasticOf_addToCG (s : DiscourseState A W I) (p : W → Prop) (a : A) :
    (s.addToCG p).doxasticOf a = s.doxasticOf a := rfl

@[simp] theorem cgPropositions_addToCG (s : DiscourseState A W I) (p : W → Prop) :
    (s.addToCG p).cgPropositions = p :: s.cgPropositions := rfl

@[simp] theorem cgPropositions_addCommit [DecidableEq A] (s : DiscourseState A W I)
    (a : A) (p : W → Prop) (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).cgPropositions = s.cgPropositions := rfl

@[simp] theorem cgPropositions_pushItem (s : DiscourseState A W I) (i : I) :
    (s.pushItem i).cgPropositions = s.cgPropositions := rfl

@[simp] theorem empty_doxasticOf (a : A) :
    (empty : DiscourseState A W I).doxasticOf a = [] := rfl

@[simp] theorem empty_cgPropositions :
    (empty : DiscourseState A W I).cgPropositions = [] := rfl

theorem pushItem_not_isStable (s : DiscourseState A W I) (i : I) :
    ¬ (s.pushItem i).IsStable := by
  simp [IsStable]

end DiscourseState

instance {A W I : Type*} : HasContextSet (DiscourseState A W I) W where
  toContextSet := DiscourseState.contextSet

/-- The full Farkas-Bruce model: the table holds rich speech-act `Item`s. -/
abbrev ItemState (A W : Type*) := DiscourseState A W (Item A W)

/-! ### Farkas-Bruce dynamics

The [farkas-bruce-2010] discourse moves — assertion, polar question,
acceptance — over the 2-participant specialisation `State W`, with the plain
speaker/listener commitment views (`dcS`/`dcL`) recovered from the per-agent
slate so an F&B trace yields one-line equational facts. -/

/-- The 2-participant Farkas-Bruce state, specialised over `DiscourseRole`. -/
abbrev State (W : Type*) := ItemState DiscourseRole W

variable {W : Type*}

/-- Speaker asserts `p`: doxastically commits to `p` and pushes a declarative
    item `[p]` onto the table. -/
def assert (ds : State W) (p : W → Prop) : State W :=
  ds.addCommit .speaker p |>.pushItem ⟨.speaker, .addressee, .declarative, [p]⟩

/-- Speaker poses the polar question `?p`: push interrogative item `[p, ¬p]`.
    No commitments added. -/
def polarQuestion (ds : State W) (p : W → Prop) : State W :=
  ds.pushItem ⟨.speaker, .addressee, .interrogative, [p, fun w => ¬ p w]⟩

/-- Addressee accepts the head alternative of the top item: other-generated
    doxastic commit, add to common ground, pop. -/
def acceptTop (ds : State W) : State W :=
  match ds.table with
  | [] => ds
  | item :: _ =>
    match item.alternatives.head? with
    | none => ds.popItem
    | some p =>
      ds.addCommit .addressee p .otherGenerated |>.addToCG p |>.popItem

/-- Speaker's discourse commitments (F&B `dcS`); dot-accessible on `State`. -/
def DiscourseState.dcS (ds : State W) : List (W → Prop) := ds.doxasticOf .speaker

/-- Addressee's discourse commitments (F&B `dcL`). -/
def DiscourseState.dcL (ds : State W) : List (W → Prop) := ds.doxasticOf .addressee

@[simp] theorem assert_cg (ds : State W) (p : W → Prop) :
    (assert ds p).cg = ds.cg := by simp [assert]

@[simp] theorem assert_table (ds : State W) (p : W → Prop) :
    (assert ds p).table =
      ⟨.speaker, .addressee, .declarative, [p]⟩ :: ds.table := by
  simp [assert]

theorem assert_dc_speaker_doxasticContents (ds : State W) (p : W → Prop) :
    p ∈ ((assert ds p).dc .speaker).doxasticContents := by
  simp [assert, TaggedSlate.doxasticContents, TaggedSlate.add]

theorem assert_not_isStable (ds : State W) (p : W → Prop) :
    ¬ (assert ds p).IsStable :=
  DiscourseState.pushItem_not_isStable _ _

@[simp] theorem polarQuestion_cg (ds : State W) (p : W → Prop) :
    (polarQuestion ds p).cg = ds.cg := by simp [polarQuestion]

@[simp] theorem polarQuestion_table (ds : State W) (p : W → Prop) :
    (polarQuestion ds p).table =
      ⟨.speaker, .addressee, .interrogative, [p, fun w => ¬ p w]⟩ :: ds.table := by
  simp [polarQuestion]

@[simp] theorem polarQuestion_dc (ds : State W) (p : W → Prop) (a : DiscourseRole) :
    (polarQuestion ds p).dc a = ds.dc a := by simp [polarQuestion]

theorem polarQuestion_not_isStable (ds : State W) (p : W → Prop) :
    ¬ (polarQuestion ds p).IsStable :=
  DiscourseState.pushItem_not_isStable _ _

theorem accept_after_assert_cg (ds : State W) (p : W → Prop) :
    (acceptTop (assert ds p)).cg = ds.cg.add p := by
  show (acceptTop (assert ds p)).cg = _
  unfold acceptTop
  rw [show (assert ds p).table =
      ⟨.speaker, .addressee, .declarative, [p]⟩ :: ds.table from rfl]
  rfl

@[simp] theorem empty_dcS : (DiscourseState.empty : State W).dcS = [] := rfl
@[simp] theorem empty_dcL : (DiscourseState.empty : State W).dcL = [] := rfl

@[simp] theorem assert_dcS (ds : State W) (p : W → Prop) :
    (assert ds p).dcS = p :: ds.dcS := rfl
@[simp] theorem assert_dcL (ds : State W) (p : W → Prop) :
    (assert ds p).dcL = ds.dcL := rfl
@[simp] theorem assert_cgPropositions (ds : State W) (p : W → Prop) :
    (assert ds p).cgPropositions = ds.cgPropositions := rfl
@[simp] theorem polarQuestion_dcS (ds : State W) (p : W → Prop) :
    (polarQuestion ds p).dcS = ds.dcS := rfl
@[simp] theorem polarQuestion_dcL (ds : State W) (p : W → Prop) :
    (polarQuestion ds p).dcL = ds.dcL := rfl
@[simp] theorem pushItem_dcS (ds : State W) (i : Item DiscourseRole W) :
    (ds.pushItem i).dcS = ds.dcS := rfl
@[simp] theorem pushItem_dcL (ds : State W) (i : Item DiscourseRole W) :
    (ds.pushItem i).dcL = ds.dcL := rfl

/-- After asserting `p` and accepting it, `p` reaches the common ground. -/
@[simp] theorem accept_after_assert_cgPropositions (ds : State W) (p : W → Prop) :
    (acceptTop (assert ds p)).cgPropositions = p :: ds.cgPropositions := by
  show (acceptTop (assert ds p)).cg.propositions = _
  unfold acceptTop
  rw [show (assert ds p).table =
      ⟨.speaker, .addressee, .declarative, [p]⟩ :: ds.table from rfl]
  rfl

/-- Acceptance adds `p` to the addressee's commitments. -/
@[simp] theorem accept_after_assert_dcL (ds : State W) (p : W → Prop) :
    (acceptTop (assert ds p)).dcL = p :: ds.dcL := by
  show (acceptTop (assert ds p)).doxasticOf .addressee = _
  unfold acceptTop
  rw [show (assert ds p).table =
      ⟨.speaker, .addressee, .declarative, [p]⟩ :: ds.table from rfl]
  rfl

/-- The speaker's assertion commitment survives acceptance. -/
@[simp] theorem accept_after_assert_dcS (ds : State W) (p : W → Prop) :
    (acceptTop (assert ds p)).dcS = p :: ds.dcS := by
  show (acceptTop (assert ds p)).doxasticOf .speaker = _
  unfold acceptTop
  rw [show (assert ds p).table =
      ⟨.speaker, .addressee, .declarative, [p]⟩ :: ds.table from rfl]
  rfl

/-- After acceptance the table returns to its pre-assertion state. -/
@[simp] theorem accept_after_assert_table (ds : State W) (p : W → Prop) :
    (acceptTop (assert ds p)).table = ds.table := by
  show (acceptTop (assert ds p)).table = _
  unfold acceptTop
  rw [show (assert ds p).table =
      ⟨.speaker, .addressee, .declarative, [p]⟩ :: ds.table from rfl]
  rfl

end Discourse.Commitment.Table
