module

public import Linglib.Semantics.Presupposition.Defs
public import Mathlib.Order.Max

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

*Again* is an instance of a more general shape, an assertion about an index with a presupposition
about an earlier one (`prior`), which the phasal verbs *stop*, *start* and *continue* share
(`Semantics/Aspect/Phasal.lean`).

## Main definitions

* `Presupposition.prior`: the partial proposition asserting one thing of an index and
  presupposing another of an earlier index.
* `Presupposition.again`: the partial proposition asserting `P` and presupposing an earlier
  eventuality of which `P` holds.

## Main results

* `Presupposition.again_presup_mono`: the presupposition is monotone in the predicate.
* `Presupposition.not_again_presup_of_isMin`: nothing happens again at a first eventuality.

## References

* [von-stechow-1996]
* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace Presupposition

variable {ι : Type*} {r r' : ι → ι → Prop} {P Q Q' A : ι → Prop} {e : ι}

/-! ### A presupposition about an earlier index -/

/-- `prior r Q A` asserts `A` of an index and presupposes that `Q` holds of an index that
`r`-precedes it. -/
def prior (r : ι → ι → Prop) (Q A : ι → Prop) : PartialProp ι where
  presup e := ∃ e', r e' e ∧ Q e'
  assertion := A

@[simp] theorem prior_assertion : (prior r Q A).assertion = A := rfl

@[simp] theorem prior_presup : (prior r Q A).presup e ↔ ∃ e', r e' e ∧ Q e' := Iff.rfl

theorem holds_prior : (prior r Q A).holds e ↔ (∃ e', r e' e ∧ Q e') ∧ A e := Iff.rfl

/-- The presupposition is monotone in what is presupposed of the earlier index. -/
theorem prior_presup_mono (h : Q ≤ Q') : (prior r Q A).presup ≤ (prior r Q' A).presup :=
  fun _ ⟨e', hr, hQ⟩ ↦ ⟨e', hr, h e' hQ⟩

/-- The presupposition is monotone in the precedence relation. -/
theorem prior_presup_mono_left (h : r ≤ r') : (prior r Q A).presup ≤ (prior r' Q A).presup :=
  fun e ⟨e', hr, hQ⟩ ↦ ⟨e', h e' e hr, hQ⟩

/-- Over a transitive precedence, what is presupposed at an index is presupposed at every later
one. -/
theorem prior_presup_of_rel [IsTrans ι r] {e₁ e₂ : ι} (h : r e₁ e₂)
    (h₁ : (prior r Q A).presup e₁) : (prior r Q A).presup e₂ :=
  let ⟨e', hr, hQ⟩ := h₁; ⟨e', _root_.trans hr h, hQ⟩

/-- Nothing is presupposed of an earlier index at a first index. -/
theorem not_prior_presup_of_isMin [Preorder ι] (h : IsMin e) :
    ¬ (prior (· < ·) Q A).presup e :=
  fun ⟨_, hlt, _⟩ ↦ h.not_lt hlt

/-! ### Repetitive *again* -/

/-- `again r P` asserts `P` of an eventuality and presupposes that `P` holds of an eventuality
that `r`-precedes it. -/
def again (r : ι → ι → Prop) (P : ι → Prop) : PartialProp ι := prior r P P

@[simp] theorem again_assertion : (again r P).assertion = P := rfl

@[simp] theorem again_presup : (again r P).presup e ↔ ∃ e', r e' e ∧ P e' := Iff.rfl

theorem holds_again : (again r P).holds e ↔ (∃ e', r e' e ∧ P e') ∧ P e := Iff.rfl

/-- The presupposition of *again* is monotone in the predicate it modifies. -/
theorem again_presup_mono (h : P ≤ Q) : (again r P).presup ≤ (again r Q).presup :=
  prior_presup_mono h

/-- The presupposition of *again* is monotone in the precedence relation. -/
theorem again_presup_mono_left (h : r ≤ r') : (again r P).presup ≤ (again r' P).presup :=
  prior_presup_mono_left h

/-- Over a transitive precedence, whatever happens again at an eventuality happens again at
every later one. -/
theorem again_presup_of_rel [IsTrans ι r] {e₁ e₂ : ι} (h : r e₁ e₂)
    (h₁ : (again r P).presup e₁) : (again r P).presup e₂ :=
  prior_presup_of_rel h h₁

/-- Nothing happens again at a first eventuality. -/
theorem not_again_presup_of_isMin [Preorder ι] (h : IsMin e) :
    ¬ (again (· < ·) P).presup e :=
  not_prior_presup_of_isMin h

end Presupposition
