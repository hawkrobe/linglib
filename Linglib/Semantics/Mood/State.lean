/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Setoid.Basic
public import Linglib.Discourse.QUD.Issue
public import Linglib.Semantics.Mood.Defs
public import Linglib.Semantics.Dynamic.Expectation
public import Linglib.Semantics.Modality.Kratzer.Operators
public import Linglib.Semantics.Questions.Partition.Inquisitive

/-!
# The mood state

This file defines the mood state, an expectation state extended with a coordinate that records
the open question, together with its three updates and the modal that reads the new coordinate.

Portner's mood state is a partially ordered set of worlds, a context set with an ordering, which
is Veltman's expectation state under a modal reading. Here it carries a third coordinate,
`inquiry : Setoid W`, that partitions the worlds into answers, as in the partition theory of
Groenendijk and Stokhof and the tradition of questions under discussion after Roberts. Portner
considers two interrogative extensions. One replaces the context set with a partition of it.
The other, which he credits to Roberts and to his own earlier work, adds a separate question
coordinate, and that is the design here. The separate coordinate keeps the targets of the
updates disjoint, so `assert`, `promote` and `inquire` each touch one coordinate, each update is
a meet in the lattice of its coordinate, and the facts about commutation and acceptance are
one-line facts about `⊓`.

## Main declarations

* `State`: an `ExpState` together with `inquiry : Setoid W`.
* `inquire`, `State.assert`, `State.promote`: the updates, each on a single coordinate.
* `boxAns`: the third modal, holding of what the question settles.
* `polarSetoid`: the partition that a single proposition contributes.
* `stateAt`: the state that a Kratzer pair induces at a world.
* The `HasAssertion` and `Discourse.HasIssue` instances: the context set as common ground and
  the inquiry partition as the current issue.

## Main statements

* `le_inquire_iff`: a state accepts `?` exactly when its inquiry already refines the question.
* `boxAns_of_inquiry_le_polarSetoid`, `inquiry_le_polarSetoid_iff_boxAns_of_univ`: support
  against answerhood.
* `boxAns_not_reducible_to_boxCs`: the inquiry coordinate does genuine work.
* `simpleNecessity_iff_boxCs`, `necessity_iff_boxLe`: Kratzer's simple and human necessity are
  the informational and preferential modals of the induced state.

## Implementation notes

The `?`-update, `boxAns` and the interrogative column are additions of this library and do not
appear in Portner's book. Inquiry is a partition and not a general inquisitive content.
Phenomena that are not partitions, such as mention-some readings and intermediate exhaustivity
(`Studies/TheilerRoelofsenAloni2018.lean`), live in `Question W`, with `Question.fromSetoid`
(`Semantics/Questions/Partition/Inquisitive.lean`) as the faithful embedding.

## References

* [P. Portner, *Mood* (2018)][portner-2018]
* [F. Veltman, *Defaults in Update Semantics* (1996)][veltman-1996]
* [J. Groenendijk and M. Stokhof, *Studies on the Semantics of Questions and the Pragmatics of
  Answers* (1984)][groenendijk-stokhof-1984]
* [C. Roberts, *Information Structure in Discourse: Towards an Integrated Formal Theory of
  Pragmatics* (1996)][roberts-1996]
* [C. Roberts, *Information Structure in Discourse: Towards an Integrated Formal Theory of
  Pragmatics* (2012)][roberts-2012]
* [P. Portner, *The Semantics of Imperatives within a Theory of Clause Types*
  (2004)][portner-2004]
* [N. Theiler, F. Roelofsen and M. Aloni, *A uniform semantics for declarative and interrogative
  complements* (2018)][theiler-etal-2018]
-/

@[expose] public section

namespace Mood

open DynamicSemantics

/-- A mood state is an `ExpState` enriched with an inquiry partition recording the open question,
where `⊤` stands for no question. -/
structure State (W : Type*) extends ExpState W where
  /-- In the inquiry partition `inquiry.r w v` means that the worlds `w` and `v` are
  indistinguishable answers to the open question. -/
  inquiry : Setoid W

namespace State

variable {W : Type*}

/-! ### Constructors -/

/-- The State with no question under discussion. -/
def ofExpState (σ : ExpState W) : State W :=
  { σ with inquiry := ⊤ }

@[simp] theorem ofExpState_toExpState (σ : ExpState W) :
    (ofExpState σ).toExpState = σ := rfl

@[simp] theorem ofExpState_inquiry (σ : ExpState W) :
    (ofExpState σ).inquiry = (⊤ : Setoid W) := rfl

/-- The polar setoid of a proposition makes two worlds equivalent iff they agree on `q`. It differs
from `Setoid.ker q`, which uses `=` on propositions where this uses `↔`. -/
def polarSetoid (q : W → Prop) : Setoid W where
  r w v := q w ↔ q v
  iseqv :=
    { refl := fun _ ↦ Iff.rfl
      symm := fun h ↦ h.symm
      trans := fun h₁ h₂ ↦ h₁.trans h₂ }

@[simp] theorem polarSetoid_r (q : W → Prop) (w v : W) :
    (polarSetoid q).r w v ↔ (q w ↔ q v) := Iff.rfl

@[simp] theorem polarSetoid_top : polarSetoid (W := W) (fun _ ↦ True) = ⊤ := by
  ext w v
  simp

/-! ### The third update: `?` (inquiry refinement) -/

/-- The `?`-update refines the inquiry partition by meet with `q` and touches no other coordinate.
-/
def inquire (c : State W) (q : Setoid W) : State W :=
  { c with inquiry := c.inquiry ⊓ q }

@[simp] theorem inquire_toExpState (c : State W) (q : Setoid W) :
    (c.inquire q).toExpState = c.toExpState := rfl

@[simp] theorem inquire_info (c : State W) (q : Setoid W) :
    (c.inquire q).info = c.info := rfl

@[simp] theorem inquire_order (c : State W) (q : Setoid W) :
    (c.inquire q).order = c.order := rfl

/-- The `?`-update is meet in the `Setoid` lattice. -/
@[simp] theorem inquire_inquiry_eq_inf (c : State W) (q : Setoid W) :
    (c.inquire q).inquiry = c.inquiry ⊓ q := rfl

/-! ### Discourse-state projections -/

/-- The inquiry partition, read as an issue. -/
instance : Discourse.HasIssue (State W) W := ⟨fun c ↦ Question.fromSetoid c.inquiry⟩

@[simp] theorem toIssue_eq (c : State W) :
    Discourse.HasIssue.toIssue c = Question.fromSetoid c.inquiry := rfl

@[simp] theorem toIssue_inquire (c : State W) (q : Setoid W) :
    Discourse.HasIssue.toIssue (c.inquire q) = Question.fromSetoid (c.inquiry ⊓ q) := rfl

/-! ### The third modal: `boxAns` (informational answerhood) -/

/-- Informational answerhood holds of `p` when the question settles it, that is, when `p` has a
constant truth value on every inquiry cell within `info`, in the manner of Groenendijk and Stokhof.
It is not upward-monotone in `p`, unlike `boxCs` and `boxLe`, and its natural monotonicity is
`boxAns_anti` in the state. -/
def boxAns (c : State W) (p : W → Prop) : Prop :=
  ∀ w v, w ∈ c.info → v ∈ c.info → c.inquiry.r w v → (p w ↔ p v)

/-! ### Refinement preorder -/

instance : Preorder (State W) where
  le c₁ c₂ := c₁.toExpState ≤ c₂.toExpState ∧ c₁.inquiry ≤ c₂.inquiry
  le_refl c := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2 h₂₃.2⟩

theorem le_iff (c₁ c₂ : State W) :
    c₁ ≤ c₂ ↔ c₁.toExpState ≤ c₂.toExpState ∧ c₁.inquiry ≤ c₂.inquiry :=
  Iff.rfl

/-- The `?`-update lands below the input. -/
theorem inquire_le_self (c : State W) (q : Setoid W) : c.inquire q ≤ c :=
  ⟨le_refl _, inf_le_left⟩

/-- `?`-update is monotone in the underlying State. -/
theorem inquire_mono {c₁ c₂ : State W} (h : c₁ ≤ c₂) (q : Setoid W) :
    c₁.inquire q ≤ c₂.inquire q :=
  ⟨h.1, inf_le_inf_right q h.2⟩

/-- A state accepts its own `?`-update iff its inquiry already refines the question, which is
Veltman's acceptance at the third coordinate. -/
theorem le_inquire_iff (c : State W) (q : Setoid W) :
    c ≤ c.inquire q ↔ c.inquiry ≤ q :=
  ⟨fun h ↦ le_trans h.2 inf_le_right,
   fun h ↦ ⟨le_refl _, le_inf (le_refl _) h⟩⟩

/-- Support implies answerhood, since an inquiry that refines the polar partition of `p` settles
`p`. -/
theorem boxAns_of_inquiry_le_polarSetoid (c : State W) (p : W → Prop)
    (h : c.inquiry ≤ polarSetoid p) : c.boxAns p :=
  fun _ _ _ _ hwv ↦ h hwv

/-- With total information, answerhood *is* polar-partition support:
the `info`-guards are the only gap. -/
theorem inquiry_le_polarSetoid_iff_boxAns_of_univ (c : State W)
    (p : W → Prop) (h : c.info = Set.univ) :
    c.inquiry ≤ polarSetoid p ↔ c.boxAns p :=
  ⟨fun hle ↦ c.boxAns_of_inquiry_le_polarSetoid p hle,
   fun hbox w v hwv ↦
     hbox w v (h ▸ Set.mem_univ w) (h ▸ Set.mem_univ v) hwv⟩

/-- Refining the state strengthens answerhood (the counterpart of
`ExpState.boxCs_anti`). -/
theorem boxAns_anti (c₁ c₂ : State W) (h : c₁ ≤ c₂) (p : W → Prop) :
    c₂.boxAns p → c₁.boxAns p :=
  fun hbox w v hw hv hwv ↦
    hbox w v (h.1.1 hw) (h.1.1 hv) (h.2 hwv)

/-! ### Closure properties of `boxAns`

Constant-on-cell propositions are closed under the Boolean
operations: answers combine like ordinary propositions. -/

/-- Negation preserves answerhood. -/
theorem boxAns_not (c : State W) (p : W → Prop) :
    c.boxAns p → c.boxAns (fun w ↦ ¬ p w) :=
  fun hp w v hw hv hwv ↦ not_congr (hp w v hw hv hwv)

/-- Conjunction preserves answerhood. -/
theorem boxAns_and (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w ∧ q w) :=
  fun hp hq w v hw hv hwv ↦
    and_congr (hp w v hw hv hwv) (hq w v hw hv hwv)

/-- Disjunction preserves answerhood. -/
theorem boxAns_or (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w ∨ q w) :=
  fun hp hq w v hw hv hwv ↦
    or_congr (hp w v hw hv hwv) (hq w v hw hv hwv)

/-- Material implication preserves answerhood. -/
theorem boxAns_imp (c : State W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w ↦ p w → q w) :=
  fun hp hq w v hw hv hwv ↦
    imp_congr (hp w v hw hv hwv) (hq w v hw hv hwv)

/-! ### Three-coordinate update disjointness -/

/-- The inquiry-preserving lift of `ExpState.assert`. -/
def assert (c : State W) (p : W → Prop) : State W :=
  { c.toExpState.assert p with inquiry := c.inquiry }

/-- The inquiry-preserving lift of `ExpState.promote`. -/
def promote (c : State W) (p : W → Prop) : State W :=
  { c.toExpState.promote p with inquiry := c.inquiry }

@[simp] theorem assert_toExpState (c : State W) (p : W → Prop) :
    (c.assert p).toExpState = c.toExpState.assert p := rfl

@[simp] theorem assert_inquiry (c : State W) (p : W → Prop) :
    (c.assert p).inquiry = c.inquiry := rfl

@[simp] theorem promote_toExpState (c : State W) (p : W → Prop) :
    (c.promote p).toExpState = c.toExpState.promote p := rfl

@[simp] theorem promote_inquiry (c : State W) (p : W → Prop) :
    (c.promote p).inquiry = c.inquiry := rfl

/-- `assert` and `promote` commute. -/
@[simp] theorem assert_promote_comm (c : State W) (p q : W → Prop) :
    (c.assert p).promote q = (c.promote q).assert p := rfl

/-- The context set is the common ground, and `assert` is Stalnakerian on it. -/
instance : HasAssertion (State W) W where
  commonGround c := Filter.principal c.info
  initial := ofExpState .init
  assert c φ := c.assert (· ∈ φ)
  commonGround_initial := Filter.principal_univ
  commonGround_assert c φ :=
    show Filter.principal {w ∈ c.info | w ∈ φ} = Filter.principal c.info ⊓ Filter.principal φ by
      rw [Set.sep_mem_eq, Filter.inf_principal]

@[simp] theorem commonGround_eq (c : State W) :
    HasCommonGround.commonGround c = Filter.principal c.info := rfl

@[simp] theorem contextSet_eq (c : State W) : HasCommonGround.contextSet c = c.info := by
  simp [HasCommonGround.contextSet]

@[simp] theorem toIssue_assert (c : State W) (p : W → Prop) :
    Discourse.HasIssue.toIssue (c.assert p) = Discourse.HasIssue.toIssue c := rfl

@[simp] theorem commonGround_inquire (c : State W) (q : Setoid W) :
    HasCommonGround.commonGround (c.inquire q) = HasCommonGround.commonGround c := by
  simp

/-- `assert` and `inquire` commute. -/
@[simp] theorem assert_inquire_comm (c : State W) (p : W → Prop) (s : Setoid W) :
    (c.assert p).inquire s = (c.inquire s).assert p := rfl

/-- `promote` and `inquire` commute. -/
@[simp] theorem promote_inquire_comm (c : State W) (p : W → Prop) (s : Setoid W) :
    (c.promote p).inquire s = (c.inquire s).promote p := rfl

/-- The `?`-update is idempotent. -/
theorem inquire_inquire_self (c : State W) (s : Setoid W) :
    ((c.inquire s).inquire s).inquiry = (c.inquire s).inquiry := by
  show (c.inquiry ⊓ s) ⊓ s = c.inquiry ⊓ s
  rw [inf_assoc, inf_idem]

/-! ### Separation: `boxAns` is not `boxCs` -/

/-- A two-cell inquiry over `Bool` with total information and the
discrete inquiry. -/
def sepInquiry : State Bool where
  info := Set.univ
  order := ⊤
  inquiry := ⊥

/-- A proposition constant on each cell but not throughout `info`. -/
def sepProp : Bool → Prop := fun w ↦ w = false

theorem boxAns_sepInquiry_sepProp : sepInquiry.boxAns sepProp := by
  intro w v _ _ hwv
  rw [show w = v from hwv]

theorem not_boxCs_sepInquiry_sepProp : ¬ sepInquiry.toExpState.boxCs sepProp :=
  fun h ↦ Bool.noConfusion (h true trivial)

/-- The inquiry coordinate does genuine work, since `boxAns` holds where `boxCs` fails. -/
theorem boxAns_not_reducible_to_boxCs :
    ∃ (c : State Bool) (p : Bool → Prop),
      c.boxAns p ∧ ¬ c.toExpState.boxCs p :=
  ⟨sepInquiry, sepProp, boxAns_sepInquiry_sepProp, not_boxCs_sepInquiry_sepProp⟩

end State

/-! ### The modal projection -/

variable {W : Type*}

/-- The necessity modal quantifying over a component is `boxCs`, `boxLe` or `boxAns`. Mood
interpretations factor through it as `boxOn ∘ target` (`VerbalOp.interp`, `SpeechEvent.modal`). -/
def Component.boxOn : Component → State W → (W → Prop) → Prop
  | .informational, c, p => c.toExpState.boxCs p
  | .preferential,  c, p => c.toExpState.boxLe p
  | .inquisitive,   c, p => c.boxAns p

@[simp] theorem boxOn_informational (c : State W) (p : W → Prop) :
    Component.informational.boxOn c p = c.toExpState.boxCs p := rfl

@[simp] theorem boxOn_preferential (c : State W) (p : W → Prop) :
    Component.preferential.boxOn c p = c.toExpState.boxLe p := rfl

@[simp] theorem boxOn_inquisitive (c : State W) (p : W → Prop) :
    Component.inquisitive.boxOn c p = c.boxAns p := rfl

/-! ### Kratzer backgrounds induce states

[portner-2018]'s gloss on his (3): reading the mood state's components
as a modal base and ordering source ([kratzer-1981]), `□_cs` expresses
simple necessity and `□_≤` human necessity. `stateAt` is that
identification read in the other direction — a Kratzer pair is a
world-indexed family of expectation states — and the theorems below
are his (3a)/(3b). -/

open Modality.Kratzer

/-- The expectation state that a modal base and ordering source induce at a world has the accessible
worlds as information and the ordering-source ranking as pattern. -/
def stateAt (f : ModalBase W) (g : OrderingSource W) (w : W) :
    ExpState W :=
  ⟨accessibleWorlds f w, kratzerPreorder (g w)⟩

@[simp] theorem stateAt_info (f : ModalBase W) (g : OrderingSource W) (w : W) :
    (stateAt f g w).info = accessibleWorlds f w := rfl

@[simp] theorem stateAt_order (f : ModalBase W) (g : OrderingSource W) (w : W) :
    (stateAt f g w).order = kratzerPreorder (g w) := rfl

/-- Kratzer's best worlds are the induced state's optimal worlds. -/
theorem bestWorlds_eq_optimal (f : ModalBase W) (g : OrderingSource W)
    (w : W) :
    bestWorlds f g w = (stateAt f g w).optimal := rfl

/-- Simple necessity is informational necessity over the induced state, where the ordering source is
irrelevant. -/
theorem simpleNecessity_iff_boxCs (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    simpleNecessity f p w ↔ (stateAt f g w).boxCs p :=
  Iff.rfl

/-- Kratzer necessity is preferential necessity over the induced state, so human necessity is `□_≤`.
-/
theorem necessity_iff_boxLe (f : ModalBase W) (g : OrderingSource W)
    (p : W → Prop) (w : W) :
    necessity f g p w ↔ (stateAt f g w).boxLe p :=
  Iff.rfl

/-- The state induced by a Kratzer frame supports asserting `p` iff `p` is a simple necessity. -/
theorem le_assert_iff_simpleNecessity (f : ModalBase W)
    (g : OrderingSource W) (p : W → Prop) (w : W) :
    stateAt f g w ≤ (stateAt f g w).assert p ↔ simpleNecessity f p w :=
  ((stateAt f g w).le_assert_iff p).trans
    (simpleNecessity_iff_boxCs f g p w).symm

/-- Kratzer realism is fiber-reflexivity, so a modal base is realistic iff every world belongs to
its own induced information state. -/
theorem isRealistic_iff_mem_stateAt_info (f : ModalBase W)
    (g : OrderingSource W) :
    isRealistic f ↔ ∀ w, w ∈ (stateAt f g w).info :=
  isRealistic_iff_mem_accessible f

end Mood
