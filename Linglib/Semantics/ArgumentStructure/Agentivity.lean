import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Pi

/-!
# The agentivity cube ([grimm-2011] §2.1)

[grimm-2011] reformulates [dowty-1991]'s Proto-Agent entailments as four
**privative features**: Proto-Patient is not a separate cluster but the
underspecified (∅) pole of each feature, and Dowty's relational "causation"
is decomposed into participant-bound "instigation" (p.521). `Agentivity` is
the Boolean cube on `Agentivity.Feature`, ordered by feature-set inclusion;
Grimm's Fig. 1 lattice is its 12-element `Agentivity.Valid` subset.

The persistence axis is `PersistenceLevel.lean`; the product object is
`ParticipantType.lean`; the projection from [dowty-1991]'s profiles is
`Projection.lean`.
-/

namespace ArgumentStructure

/-- The four agentivity primitives (Table 2 (agentive properties), p.520).

    Each has an agentive (+) and non-agentive (∅) pole; the non-agentive
    pole is simply the absence of the property — the **privative
    opposition** that replaces Dowty's two independent clusters. -/
inductive Agentivity.Feature where
  /-- +volition: the participant intends to bring about the event. -/
  | volition
  /-- +sentience: conscious involvement in the action or state. -/
  | sentience
  /-- +instigation: prior independent action whose effects can be
      attributed to this argument. Replaces Dowty's "causation" (p.521). -/
  | instigation
  /-- +motion: the argument is in motion during the event. -/
  | motion
  deriving DecidableEq, Repr, Fintype

/-- An argument's agentivity: which of the four primitives it bears, as a
    point of the Boolean cube on `Agentivity.Feature`. Order, lattice, and
    Boolean-algebra structure are pointwise, so `a ≤ b` is feature-set
    inclusion; Grimm's Fig. 1 lattice is the 12-element `Valid` subset of
    the 16-element cube. -/
def Agentivity := Agentivity.Feature → Bool

namespace Agentivity

instance : DecidableEq Agentivity :=
  inferInstanceAs (DecidableEq (Feature → Bool))

instance : Fintype Agentivity := inferInstanceAs (Fintype (Feature → Bool))

instance : BooleanAlgebra Agentivity :=
  inferInstanceAs (BooleanAlgebra (Feature → Bool))

instance : DecidableRel (α := Agentivity) (· ≤ ·) := fun a b =>
  decidable_of_iff (∀ f, a f ≤ b f) Iff.rfl

instance : DecidableRel (α := Agentivity) (· < ·) := fun _ _ =>
  decidable_of_iff' _ lt_iff_le_not_ge

/-- Build an agentivity value from the four indicators, in Table 2 order. -/
def mk (volition sentience instigation motion : Bool) : Agentivity
  | .volition => volition
  | .sentience => sentience
  | .instigation => instigation
  | .motion => motion

instance : Repr Agentivity :=
  ⟨fun a _ => repr (a .volition, a .sentience, a .instigation, a .motion)⟩

@[simp] theorem mk_inj {v s i m v' s' i' m' : Bool} :
    mk v s i m = mk v' s' i' m' ↔ v = v' ∧ s = s' ∧ i = i' ∧ m = m' := by
  constructor
  · intro h
    exact ⟨congrFun h .volition, congrFun h .sentience,
      congrFun h .instigation, congrFun h .motion⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- Volition indicator. -/
def volition (a : Agentivity) : Bool := a .volition

/-- Sentience indicator. -/
def sentience (a : Agentivity) : Bool := a .sentience

/-- Instigation indicator. -/
def instigation (a : Agentivity) : Bool := a .instigation

/-- Motion indicator. -/
def motion (a : Agentivity) : Bool := a .motion

/-- Validity: volition presupposes sentience (p.521, following
    [dowty-1991] p.607). Carves Grimm's 12-element Fig. 1 lattice out of
    the 16-element cube. -/
def Valid (a : Agentivity) : Prop := a.volition = true → a.sentience = true

instance (a : Agentivity) : Decidable a.Valid := by
  unfold Valid; infer_instance

/-- Number of positive features (= height in the cube). -/
def featureCount (a : Agentivity) : Nat :=
  a.volition.toNat + a.sentience.toNat + a.instigation.toNat + a.motion.toNat

/-- The inclusion order, componentwise. -/
theorem le_iff (a b : Agentivity) :
    a ≤ b ↔
      (a.volition = true → b.volition = true) ∧
      (a.sentience = true → b.sentience = true) ∧
      (a.instigation = true → b.instigation = true) ∧
      (a.motion = true → b.motion = true) := by
  revert a b; decide

end Agentivity

end ArgumentStructure
