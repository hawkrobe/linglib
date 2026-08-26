import Mathlib.Tactic.TypeStar

/-!
# De re attitudes by acquaintance

This file defines the centered-world rule for de re attitude ascription. The object of an
attitude is a centered proposition — a property of the holder's self, now, and world — and a de re
construal replaces the res by whatever the self is uniquely acquainted with, through a contextually
given acquaintance relation, at the now of each alternative; the res itself enters only through the
base-world condition that the holder actually bears the relation to it. With the identity relation
on times the rule collapses to evaluation at the now, which is what makes the simultaneous reading
of a past tense embedded under a past attitude a de re reading.

## Main definitions

* `Acquaintance.CenteredProp`, `Acquaintance.Rel`: centered propositions and acquaintance
  relations to a res of any type.
* `Acquaintance.deRe`: the centered proposition ascribed by a de re construal.
* `Acquaintance.BaseCondition`: the base-world condition on the res.

## Main statements

* `Acquaintance.deRe_identity`: de re construal through identity with the now evaluates the
  property at the now.

## References

* [lewis-1979-attitudes]
* [cresswell-vonstechow-1982]
* [abusch-1997]
-/

namespace Acquaintance

variable {α E T W : Type*}

/-- A centered proposition: a property of the holder's self, now, and world. -/
abbrev CenteredProp (E T W : Type*) := E → T → W → Prop

/-- An acquaintance relation: `R y x t w` holds when the self `x` at `t` in `w` is acquainted
with the res `y`. -/
abbrev Rel (α E T W : Type*) := α → E → T → W → Prop

/-- The centered proposition that the res the self is uniquely acquainted with at the now has
the property `P` there. -/
def deRe (R : Rel α E T W) (P : α → T → W → Prop) : CenteredProp E T W :=
  fun x t w => ∃ y, (∀ y', R y' x t w ↔ y' = y) ∧ P y t w

/-- The base-world condition of a de re construal: the holder actually bears the acquaintance
relation to the res. -/
def BaseCondition (R : Rel α E T W) (res : α) (x : E) (t : T) (w : W) : Prop := R res x t w

/-- Acquaintance with a time by identity with the now. -/
def identity : Rel T E T W := fun y _ t _ => y = t

theorem deRe_identity (P : T → T → W → Prop) :
    deRe (identity (E := E)) P = fun _ t w => P t t w := by
  funext x t w
  refine propext ⟨fun ⟨y, hy, hP⟩ => ?_, fun h => ⟨t, fun _ => Iff.rfl, h⟩⟩
  obtain rfl := (hy t).1 rfl
  exact hP

end Acquaintance
