import Mathlib.Order.WithBot

/-!
# Strong Kleene Three-Valued Logic

Three-valued truth values and propositional logic following Strong Kleene semantics.

`TVal = WithBot Bool` gives us `tt`, `ff`, and `unk` (undefined/gap).
`Prop3 W = W → TVal` lifts this to propositions over possible worlds.

## References

- Kleene, S.C. (1952). Introduction to Metamathematics.
-/

namespace Core.Kleene

/-- Three-valued truth values using Mathlib's `WithBot Bool`. -/
abbrev TVal := WithBot Bool

namespace TVal

/-- The true value. -/
abbrev tt : TVal := some true

/-- The false value. -/
abbrev ff : TVal := some false

/-- The undefined value (presupposition failure). -/
abbrev unk : TVal := none

/-- Convert Bool to TVal. -/
def ofBool (b : Bool) : TVal := some b

/-- Check if defined (not ⊥). -/
def isDefined (v : TVal) : Bool := v.isSome

/-- Convert to Bool if defined, else default to false. -/
def toBoolOrFalse : TVal -> Bool
  | some b => b
  | none => false

/-- Strong Kleene negation. -/
def neg : TVal -> TVal
  | some b => some (!b)
  | none => none

/-- Strong Kleene conjunction. -/
def and : TVal -> TVal -> TVal
  | some false, _ => ff
  | _, some false => ff
  | some true, some true => tt
  | _, _ => unk

/-- Strong Kleene disjunction. -/
def or : TVal -> TVal -> TVal
  | some true, _ => tt
  | _, some true => tt
  | some false, some false => ff
  | _, _ => unk

/-- Negation is involutive. -/
theorem neg_neg (v : TVal) : neg (neg v) = v := by
  cases v with
  | none => rfl
  | some b => simp [neg, Bool.not_not]

/-- Negation preserves ⊥. -/
theorem neg_unk : neg unk = unk := rfl

/-- Conjunction is commutative. -/
theorem and_comm (a b : TVal) : and a b = and b a := by
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> rfl

/-- Disjunction is commutative. -/
theorem or_comm (a b : TVal) : or a b = or b a := by
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> rfl

/-- ff is absorbing for conjunction. -/
theorem and_ff_left (a : TVal) : and ff a = ff := rfl
theorem and_ff_right (a : TVal) : and a ff = ff := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- tt is absorbing for disjunction. -/
theorem or_tt_left (a : TVal) : or tt a = tt := rfl
theorem or_tt_right (a : TVal) : or a tt = tt := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- tt is identity for conjunction. -/
theorem and_tt_left (a : TVal) : and tt a = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl
theorem and_tt_right (a : TVal) : and a tt = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- ff is identity for disjunction. -/
theorem or_ff_left (a : TVal) : or ff a = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl
theorem or_ff_right (a : TVal) : or a ff = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

/-- ⊥ propagates in conjunction (when not dominated by ff). -/
theorem and_unk_left (a : TVal) (h : a ≠ ff) : and unk a = unk := by
  cases a with
  | none => rfl
  | some b => cases b with
    | true => rfl
    | false => simp [ff] at h

/-- ⊥ propagates in disjunction (when not dominated by tt). -/
theorem or_unk_left (a : TVal) (h : a ≠ tt) : or unk a = unk := by
  cases a with
  | none => rfl
  | some b => cases b with
    | false => rfl
    | true => simp [tt] at h

/-- Conjunction agrees with Bool when both defined. -/
theorem and_ofBool (a b : Bool) :
    and (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Disjunction agrees with Bool when both defined. -/
theorem or_ofBool (a b : Bool) :
    or (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- Negation agrees with Bool. -/
theorem neg_ofBool (a : Bool) : neg (ofBool a) = ofBool (!a) := rfl

/-- Conjunction is associative. -/
theorem and_assoc (a b c : TVal) : and (and a b) c = and a (and b c) := by
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> rcases c with _ | ⟨_ | _⟩ <;> rfl

/-- Disjunction is associative. -/
theorem or_assoc (a b c : TVal) : or (or a b) c = or a (or b c) := by
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;> rcases c with _ | ⟨_ | _⟩ <;> rfl

end TVal

/-- Three-valued propositions: functions from worlds to TVal. -/
abbrev Prop3 (W : Type*) := W -> TVal

namespace Prop3

variable {W : Type*}

/-- Pointwise negation. -/
def neg (p : Prop3 W) : Prop3 W := λ w => TVal.neg (p w)

/-- Pointwise Strong Kleene conjunction. -/
def and (p q : Prop3 W) : Prop3 W := λ w => TVal.and (p w) (q w)

/-- Pointwise Strong Kleene disjunction. -/
def or (p q : Prop3 W) : Prop3 W := λ w => TVal.or (p w) (q w)

/-- Always true. -/
def top : Prop3 W := λ _ => TVal.tt

/-- Always false. -/
def bot : Prop3 W := λ _ => TVal.ff

/-- Always undefined. -/
def unk : Prop3 W := λ _ => TVal.unk

/-- Convert BProp to Prop3 (always defined). -/
def ofBProp (p : W → Bool) : Prop3 W := λ w => TVal.ofBool (p w)

end Prop3

end Core.Kleene
