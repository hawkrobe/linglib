import Linglib.Discourse.Commitment.Table
import Linglib.Discourse.Roles

/-!
# Farkas & Bruce 2010 dynamics
@cite{farkas-bruce-2010}

Discourse-update operations (assertion, polar question, acceptance)
specialised to the 2-participant case via `DiscourseRole`. The
substrate (`Item`, `DiscourseState`, primitive updates) lives in
`Discourse/Table.lean`.

## Main definitions

* `assert`, `polarQuestion`, `acceptTop` — F&B moves over
  `FBState W`.
* `assert_preserves_cg` — F&B's assertion does not touch CommonGround (the
  load-bearing thesis that diverges from @cite{stalnaker-1978}).
-/

namespace FarkasBruce2010

open Discourse (DiscourseRole)
open Discourse.Commitment.Table (DiscourseState Item ItemState)
open Discourse.Commitment (TaggedSlate)
open Semantics.Mood (IllocutionaryMood)

variable {W : Type*}

/-- The 2-participant Farkas-Bruce state, specialised over `DiscourseRole`. -/
abbrev FBState (W : Type*) := ItemState DiscourseRole W

/-- Speaker asserts `p`: doxastically commits to `p` and pushes a
    declarative item `[p]` onto the table. -/
def assert (ds : FBState W) (p : W → Prop) :
    FBState W :=
  ds.addCommit .speaker p |>.pushItem
    ⟨.speaker, .addressee, .declarative, [p]⟩

/-- Speaker poses the polar question `?p`: push interrogative item
    `[p, ¬p]`. No commitments added. -/
def polarQuestion (ds : FBState W) (p : W → Prop) :
    FBState W :=
  ds.pushItem ⟨.speaker, .addressee, .interrogative, [p, fun w => ¬ p w]⟩

/-- Addressee accepts the head alternative of the top item:
    other-generated doxastic commit, add to CommonGround, pop. -/
def acceptTop (ds : FBState W) :
    FBState W :=
  match ds.table with
  | [] => ds
  | item :: _ =>
    match item.alternatives.head? with
    | none => ds.popItem
    | some p =>
      ds.addCommit .addressee p .otherGenerated
        |>.addToCG p
        |>.popItem

/-! ### Basic properties -/

@[simp] theorem assert_cg (ds : FBState W) (p : W → Prop) :
    (assert ds p).cg = ds.cg := by simp [assert]

@[simp] theorem assert_table (ds : FBState W) (p : W → Prop) :
    (assert ds p).table =
      ⟨.speaker, .addressee, .declarative, [p]⟩ :: ds.table := by
  simp [assert]

theorem assert_dc_speaker_doxasticContents
    (ds : FBState W) (p : W → Prop) :
    p ∈ ((assert ds p).dc .speaker).doxasticContents := by
  simp [assert, TaggedSlate.doxasticContents, TaggedSlate.add]

theorem assert_not_isStable (ds : FBState W) (p : W → Prop) :
    ¬ (assert ds p).IsStable :=
  DiscourseState.pushItem_not_isStable _ _

@[simp] theorem polarQuestion_cg (ds : FBState W) (p : W → Prop) :
    (polarQuestion ds p).cg = ds.cg := by simp [polarQuestion]

@[simp] theorem polarQuestion_dc (ds : FBState W) (p : W → Prop)
    (a : DiscourseRole) : (polarQuestion ds p).dc a = ds.dc a := by
  simp [polarQuestion]

theorem polarQuestion_not_isStable
    (ds : FBState W) (p : W → Prop) :
    ¬ (polarQuestion ds p).IsStable :=
  DiscourseState.pushItem_not_isStable _ _

theorem accept_after_assert_cg (ds : FBState W) (p : W → Prop) :
    (acceptTop (assert ds p)).cg = ds.cg.add p := by
  show (acceptTop (assert ds p)).cg = _
  unfold acceptTop
  rw [show (assert ds p).table =
      ⟨.speaker, .addressee, .declarative, [p]⟩ :: ds.table from rfl]
  rfl

/-! ### Divergence from Stalnaker -/

/-- F&B's assertion does **not** narrow the common ground, in
    contrast to @cite{stalnaker-1978} where assertion is direct CommonGround
    update. The pre-assertion `cg` is preserved exactly; acceptance
    is a separate move (`acceptTop`). -/
theorem assert_preserves_cg (ds : FBState W) (p : W → Prop) :
    (assert ds p).cg = ds.cg :=
  assert_cg ds p

end FarkasBruce2010
