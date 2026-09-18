import Linglib.Semantics.Presupposition.Defs
import Mathlib.Order.Max

/-!
# Repetitive *again*

This file defines the meaning of the repetitive presupposition trigger *again*. Following the
simplification of von Stechow's entry that Beavers and Koontz-Garboden use, *again* takes a
predicate `P` of eventualities and a precedence relation `r` between them. It asserts `P` of an
eventuality and presupposes that `P` held of an `r`-earlier one. The eventualities may be events
ordered by their run times, states, or times themselves, so the relation is a parameter.

The readings of *again* differ in the constituent it modifies. Attached to a change-of-state
predicate it is repetitive, and attached to the result state inside it, restitutive. A
predicate that entails another gives the stronger presupposition (`again_presup_mono`), which
is why the repetitive reading entails the restitutive one.

## Main definitions

* `Presupposition.again`: the partial proposition asserting `P` and presupposing an earlier
  eventuality of which `P` holds.

## Main results

* `Presupposition.again_presup_mono`: the presupposition is monotone in the predicate.
* `Presupposition.not_again_presup_of_isMin`: nothing happens again at a first eventuality.

## References

* [von-stechow-1996]
* [beavers-koontz-garboden-2020]
-/

namespace Presupposition

variable {ι : Type*} {r r' : ι → ι → Prop} {P Q : ι → Prop} {e : ι}

/-- `again r P` asserts `P` of an eventuality and presupposes that `P` holds of an eventuality
that `r`-precedes it. -/
def again (r : ι → ι → Prop) (P : ι → Prop) : PartialProp ι where
  presup e := ∃ e', r e' e ∧ P e'
  assertion := P

@[simp] theorem again_assertion : (again r P).assertion = P := rfl

@[simp] theorem again_presup : (again r P).presup e ↔ ∃ e', r e' e ∧ P e' := Iff.rfl

theorem holds_again : (again r P).holds e ↔ (∃ e', r e' e ∧ P e') ∧ P e := Iff.rfl

/-- The presupposition of *again* is monotone in the predicate it modifies. -/
theorem again_presup_mono (h : P ≤ Q) : (again r P).presup ≤ (again r Q).presup :=
  fun _ ⟨e', hr, hP⟩ ↦ ⟨e', hr, h e' hP⟩

/-- The presupposition of *again* is monotone in the precedence relation. -/
theorem again_presup_mono_left (h : r ≤ r') : (again r P).presup ≤ (again r' P).presup :=
  fun e ⟨e', hr, hP⟩ ↦ ⟨e', h e' e hr, hP⟩

/-- Over a transitive precedence, whatever happens again at an eventuality happens again at
every later one. -/
theorem again_presup_of_rel [IsTrans ι r] {e₁ e₂ : ι} (h : r e₁ e₂)
    (h₁ : (again r P).presup e₁) : (again r P).presup e₂ :=
  let ⟨e', hr, hP⟩ := h₁; ⟨e', _root_.trans hr h, hP⟩

/-- Nothing happens again at a first eventuality. -/
theorem not_again_presup_of_isMin [Preorder ι] (h : IsMin e) :
    ¬ (again (· < ·) P).presup e :=
  fun ⟨_, hlt, _⟩ ↦ h.not_lt hlt

end Presupposition
