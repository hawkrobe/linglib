import Linglib.Discourse.Commitment
import Linglib.Discourse.CommonGround
import Linglib.Semantics.Mood.IllocutionaryMood

/-!
# The Table Model
@cite{farkas-bruce-2010}

n-agent table-model substrate: a stack of at-issue items, per-agent
commitment slates, and a common ground.

## Main definitions

* `Item A W` — speaker, addressee, mood, alternatives.
* `DiscourseState A W` — ⟨table, dc, cg⟩.
* `DiscourseState.IsStable` — empty-table predicate.
* `pushItem`, `popItem`, `addCommit`, `addToCG` — primitive updates.

## TODO

* Projected set `ps(CG)`, highlighting (@cite{farkas-roelofsen-2017}),
  item identity (for withdrawal).
-/

namespace Discourse.Table

open Discourse.Commitment (TaggedSlate CommitmentSource CommitmentForce)
open Discourse.CommonGround (CG HasContextSet)
open Semantics.Mood (IllocutionaryMood)

/-- An at-issue item on the conversational table. -/
structure Item (A W : Type*) where
  /-- Speaker of the utterance. -/
  speaker : A
  /-- Addressee. -/
  addressee : A
  /-- Illocutionary force. -/
  mood : IllocutionaryMood
  /-- Alternatives at issue: `[p]` for assertion, `[p, ¬p]` for
      polar question, the answer set for wh-questions. -/
  alternatives : List (W → Prop)

/-- The discourse structure (DS) of @cite{farkas-bruce-2010}. -/
structure DiscourseState (A W : Type*) where
  /-- Stack of unresolved items, head = most recent. -/
  table : List (Item A W)
  /-- Per-agent discourse commitments. -/
  dc : A → TaggedSlate W
  /-- The common ground. -/
  cg : CG W

namespace DiscourseState
variable {A W : Type*}

/-- Initial state: empty table, empty commitments, trivial CG. -/
def empty : DiscourseState A W :=
  ⟨[], fun _ => TaggedSlate.empty, CG.empty⟩

instance : Inhabited (DiscourseState A W) := ⟨empty⟩

/-- The state is stable when the table is empty. -/
def IsStable (s : DiscourseState A W) : Prop := s.table.isEmpty = true

instance (s : DiscourseState A W) : Decidable s.IsStable :=
  inferInstanceAs (Decidable (_ = _))

/-- Worlds compatible with the common ground. -/
def contextSet (s : DiscourseState A W) : Set W := s.cg.contextSet

/-! ### Primitive updates -/

def pushItem (s : DiscourseState A W) (i : Item A W) : DiscourseState A W :=
  { s with table := i :: s.table }

def popItem (s : DiscourseState A W) : DiscourseState A W :=
  { s with table := s.table.tail }

def addToCG (s : DiscourseState A W) (p : W → Prop) : DiscourseState A W :=
  { s with cg := s.cg.add p }

/-- Add `(p, src, force)` to agent `a`'s slate. Defaults: self-generated,
    doxastic — the standard assertion-driven cell. -/
def addCommit [DecidableEq A] (s : DiscourseState A W) (a : A)
    (p : W → Prop)
    (src : CommitmentSource := .selfGenerated)
    (force : CommitmentForce := .doxastic) : DiscourseState A W :=
  { s with dc := Function.update s.dc a ((s.dc a).add p src force) }

/-! ### Basic theorems -/

@[simp] theorem empty_table : (empty : DiscourseState A W).table = [] := rfl
@[simp] theorem empty_dc (a : A) :
    (empty : DiscourseState A W).dc a = TaggedSlate.empty := rfl
@[simp] theorem empty_cg : (empty : DiscourseState A W).cg = CG.empty := rfl
@[simp] theorem empty_isStable : (empty : DiscourseState A W).IsStable := rfl

@[simp] theorem pushItem_table (s : DiscourseState A W) (i : Item A W) :
    (s.pushItem i).table = i :: s.table := rfl
@[simp] theorem pushItem_dc (s : DiscourseState A W) (i : Item A W) :
    (s.pushItem i).dc = s.dc := rfl
@[simp] theorem pushItem_cg (s : DiscourseState A W) (i : Item A W) :
    (s.pushItem i).cg = s.cg := rfl

@[simp] theorem popItem_table (s : DiscourseState A W) :
    s.popItem.table = s.table.tail := rfl
@[simp] theorem popItem_dc (s : DiscourseState A W) : s.popItem.dc = s.dc := rfl
@[simp] theorem popItem_cg (s : DiscourseState A W) : s.popItem.cg = s.cg := rfl

@[simp] theorem addToCG_cg (s : DiscourseState A W) (p : W → Prop) :
    (s.addToCG p).cg = s.cg.add p := rfl
@[simp] theorem addToCG_table (s : DiscourseState A W) (p : W → Prop) :
    (s.addToCG p).table = s.table := rfl
@[simp] theorem addToCG_dc (s : DiscourseState A W) (p : W → Prop) :
    (s.addToCG p).dc = s.dc := rfl

@[simp] theorem addCommit_table [DecidableEq A] (s : DiscourseState A W)
    (a : A) (p : W → Prop) (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).table = s.table := rfl
@[simp] theorem addCommit_cg [DecidableEq A] (s : DiscourseState A W)
    (a : A) (p : W → Prop) (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).cg = s.cg := rfl

@[simp] theorem addCommit_dc_self [DecidableEq A] (s : DiscourseState A W)
    (a : A) (p : W → Prop) (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).dc a = (s.dc a).add p src force := by
  simp [addCommit]

@[simp] theorem addCommit_dc_of_ne [DecidableEq A] (s : DiscourseState A W)
    {a b : A} (h : b ≠ a) (p : W → Prop)
    (src : CommitmentSource) (force : CommitmentForce) :
    (s.addCommit a p src force).dc b = s.dc b := by
  simp [addCommit, Function.update_of_ne h]

theorem pushItem_not_isStable (s : DiscourseState A W) (i : Item A W) :
    ¬ (s.pushItem i).IsStable := by
  simp [IsStable]

end DiscourseState

instance {A W : Type*} : HasContextSet (DiscourseState A W) W where
  toContextSet := DiscourseState.contextSet

end Discourse.Table
