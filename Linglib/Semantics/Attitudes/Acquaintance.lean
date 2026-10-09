module

public import Mathlib.Tactic.TypeStar

/-!
# De re attitudes by acquaintance

On the centered-world rule for de re attitude ascription, the object of an attitude is a centered
proposition, a property of the holder's self, now, and world, and a de re construal replaces the res
by whatever the self is uniquely acquainted with, through a contextually given acquaintance
relation, at the now of each alternative; the res itself enters only through the base-world
condition that the holder actually bears the relation to it. A concept, a way of picking out a res
from each center, is a functional acquaintance relation, and through it the rule evaluates the
property at the res the concept picks out; Heim's time-concepts are the temporal case. With identity
to the now, the concept of the now, the rule collapses to evaluation at the now, which is what makes
the simultaneous reading of a past tense embedded under a past attitude a de re reading.

## Main definitions

* `Acquaintance.deRe`: the centered proposition ascribed by a de re construal.
* `Acquaintance.BaseCondition`: the base-world condition on the res.
* `Acquaintance.ofConcept`: the acquaintance relation of a concept.

## Main statements

* `Acquaintance.deRe_ofConcept`: de re construal through a concept evaluates the property at the
  res the concept picks out.
* `Acquaintance.deRe_identity`: de re construal through identity with the now evaluates the
  property at the now.

## References

* [lewis-1979-attitudes]
* [cresswell-vonstechow-1982]
* [abusch-1997]
* [heim-1994-comments]
-/

@[expose] public section

namespace Acquaintance

variable {α E T W : Type*}

/-- The centered proposition that the res the self is uniquely acquainted with at the now has
the property `P` there, where the acquaintance relation `R y x t w` says that the self `x` at `t`
in `w` is acquainted with the res `y`. -/
def deRe (R : α → E → T → W → Prop) (P : α → T → W → Prop) : E → T → W → Prop :=
  fun x t w ↦ ∃ y, (∀ y', R y' x t w ↔ y' = y) ∧ P y t w

/-- The base-world condition of a de re construal holds when the holder actually bears the
acquaintance relation to the res. -/
def BaseCondition (R : α → E → T → W → Prop) (res : α) (x : E) (t : T) (w : W) : Prop :=
  R res x t w

/-- The acquaintance relation of a concept `c` relates each center only to the res `c` picks out
there. -/
def ofConcept (c : E → T → W → α) : α → E → T → W → Prop := fun y x t w ↦ y = c x t w

/-- Through a concept, de re construal evaluates the property at the res the concept picks out. -/
theorem deRe_ofConcept (c : E → T → W → α) (P : α → T → W → Prop) :
    deRe (ofConcept c) P = fun x t w ↦ P (c x t w) t w := by
  funext x t w
  refine propext ⟨fun ⟨y, hy, hP⟩ ↦ ?_, fun h ↦ ⟨c x t w, fun _ ↦ Iff.rfl, h⟩⟩
  obtain rfl := (hy _).1 rfl
  exact hP

/-- Acquaintance with a time by identity with the now. -/
def identity : T → E → T → W → Prop := ofConcept fun _ t _ ↦ t

theorem deRe_identity (P : T → T → W → Prop) :
    deRe (identity (E := E)) P = fun _ t w ↦ P t t w :=
  deRe_ofConcept _ P

end Acquaintance
