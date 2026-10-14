module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.Iterative

/-!
# Phasal verbs

This file defines the meaning of the phasal verbs *stop*, *start* and *continue*. Such a verb
takes a state description `P` and relates two indices: it asserts that `P` holds, or fails, at
the index of evaluation, and presupposes that `P` held, or failed, at an earlier one. The
indices may be times, eventualities or world-time pairs, so the relation `R` of an index to the
earlier ones is a parameter, as it is for the repetitive presupposition of *again*, and the
presupposition is possibility along it, `◇[R]` of `Logic/Modal`.

The three classes differ only in the polarity they require of the prior state and of the result
state (`Phasal.Prior`, `Phasal.Result`). An inception that is defined and true is Dowty's
BECOME, a state that holds having failed before (`holds_denote_inception`). A cessation
is the inception of the complementary state (`denote_cessation_eq_inception`) and the negation
of a continuation (`denote_cessation_eq_neg`), and a continuation is *again* applied to the
state (`denote_continuation`). Where `R` relates an index to every earlier one a state may have
both held and failed before, so that a cessation and an inception of it are both defined; the
two exclude one another exactly where the prior index is unique
(`forall_not_presup_cessation_and_inception_iff`).

## Main definitions

* `Aspect.Phasal`: the three classes of phasal verb, cessation, inception and continuation.
* `Aspect.Phasal.Transition`: the truth condition of a class on a prior and a result state.
* `Aspect.Phasal.denote`: the partial proposition of a class, a relation to the earlier indices
  and a state description.
* `Aspect.Become`: a state holds at an index and fails at an earlier one.

## Main results

* `Aspect.Phasal.holds_denote_iff`: a phasal verb is defined and true where some earlier index
  and the index of evaluation stand in its transition.
* `Aspect.Phasal.result_iff_not_prior`: the classes other than continuation are changes, the
  result state having the opposite polarity to the prior state.
* `Aspect.Phasal.forall_not_presup_cessation_and_inception_iff`: no state can both stop and
  start at an index exactly when the index has at most one earlier index.

## References

* [dowty-1979]
* [von-stechow-1996]
-/

@[expose] public section

namespace Aspect

open Presupposition ModalLogic
open scoped SetRel

/-- The classes of phasal verb by the prior state presupposed and the result state asserted,
which are cessation (*stop*, *quit*, *cease*), inception (*start*, *begin*) and continuation
(*continue*, *keep*). -/
inductive Phasal
  | cessation
  | inception
  | continuation
  deriving DecidableEq, Repr, Inhabited

variable {ι : Type*} {R : SetRel ι ι} {P : ι → Prop} {i : ι} {p q : Prop}

/-- `Become R P` holds at an index where `P` holds and which `R` relates to an index where `P`
fails, an earlier one. -/
def Become (R : SetRel ι ι) (P : ι → Prop) (i : ι) : Prop :=
  ◇[R] (fun i' ↦ ¬ P i') i ∧ P i

namespace Phasal

/-- `t.Prior p` is what the class `t` requires of the prior state `p`, that it held or, for an
inception, that it did not. -/
def Prior : Phasal → Prop → Prop
  | cessation, p => p
  | inception, p => ¬ p
  | continuation, p => p

/-- `t.Result p` is what the class `t` requires of the result state `p`, that it holds or, for a
cessation, that it does not. -/
def Result : Phasal → Prop → Prop
  | cessation, p => ¬ p
  | inception, p => p
  | continuation, p => p

/-- `t.Transition p q` is the truth condition of the class `t` on a prior state `p` and a result
state `q`. -/
def Transition (t : Phasal) (p q : Prop) : Prop := t.Prior p ∧ t.Result q

instance : ∀ (t : Phasal) (p : Prop) [Decidable p], Decidable (t.Prior p)
  | cessation, _, h => h
  | inception, p, _ => inferInstanceAs (Decidable (¬ p))
  | continuation, _, h => h

instance : ∀ (t : Phasal) (p : Prop) [Decidable p], Decidable (t.Result p)
  | cessation, p, _ => inferInstanceAs (Decidable (¬ p))
  | inception, _, h => h
  | continuation, _, h => h

instance (t : Phasal) [Decidable p] [Decidable q] : Decidable (t.Transition p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem prior_cessation : cessation.Prior p ↔ p := Iff.rfl
@[simp] theorem prior_inception : inception.Prior p ↔ ¬ p := Iff.rfl
@[simp] theorem prior_continuation : continuation.Prior p ↔ p := Iff.rfl
@[simp] theorem result_cessation : cessation.Result p ↔ ¬ p := Iff.rfl
@[simp] theorem result_inception : inception.Result p ↔ p := Iff.rfl
@[simp] theorem result_continuation : continuation.Result p ↔ p := Iff.rfl

theorem transition_iff (t : Phasal) : t.Transition p q ↔ t.Prior p ∧ t.Result q := Iff.rfl

/-- A cessation and an inception are changes, the result state having the opposite polarity to
the prior state. -/
theorem result_iff_not_prior {t : Phasal} (ht : t ≠ continuation) :
    t.Result p ↔ ¬ t.Prior p := by
  cases t
  · exact Iff.rfl
  · exact not_not.symm
  · exact absurd rfl ht

/-- A continuation is no change, the result state having the polarity of the prior state. -/
theorem result_continuation_eq_prior : continuation.Result = continuation.Prior := rfl

/-- No state is left by one transition and continued by another. -/
theorem not_transition_cessation_of_continuation (h : continuation.Transition p q) :
    ¬ cessation.Transition p q :=
  fun h' ↦ h'.2 h.2

/-- `t.denote R P` asserts the result state of `P` at an index and presupposes its prior state
at one of the indices that `R` relates it to, the earlier ones. -/
def denote (t : Phasal) (R : SetRel ι ι) (P : ι → Prop) : PartialProp ι where
  presup := ◇[R] fun i ↦ t.Prior (P i)
  assertion i := t.Result (P i)

@[simp] theorem denote_presup {t : Phasal} :
    (t.denote R P).presup = ◇[R] fun i ↦ t.Prior (P i) := rfl

@[simp] theorem denote_assertion {t : Phasal} :
    (t.denote R P).assertion i ↔ t.Result (P i) := Iff.rfl

/-- A phasal verb is defined and true where an earlier index and the index of evaluation stand
in its transition. -/
theorem holds_denote_iff {t : Phasal} :
    (t.denote R P).holds i ↔ ∃ i', i ~[R] i' ∧ t.Transition (P i') (P i) :=
  ⟨fun ⟨⟨i', hr, hp⟩, hq⟩ ↦ ⟨i', hr, hp, hq⟩, fun ⟨i', hr, hp, hq⟩ ↦ ⟨⟨i', hr, hp⟩, hq⟩⟩

/-- An inception that is defined and true is a becoming. -/
theorem holds_denote_inception : (inception.denote R P).holds i ↔ Become R P i := Iff.rfl

/-- A continuation is *again* applied to the state. -/
theorem denote_continuation : continuation.denote R P = again R P := rfl

/-- A cessation is the negation of a continuation, the two sharing the presupposition that the
state held. -/
theorem denote_cessation_eq_neg : cessation.denote R P = (continuation.denote R P).neg := rfl

/-- A cessation is the inception of the complementary state. -/
theorem denote_cessation_eq_inception :
    cessation.denote R P = inception.denote R (fun i ↦ ¬ P i) := by
  ext i
  · simp only [denote_presup, prior_cessation, prior_inception, not_not]
  · rfl

/-- A cessation that is defined and true is the becoming of the complementary state. -/
theorem holds_denote_cessation :
    (cessation.denote R P).holds i ↔ Become R (fun i ↦ ¬ P i) i := by
  rw [denote_cessation_eq_inception, holds_denote_inception]

/-- A cessation and an inception presuppose contradictory prior states, though possibly of
different earlier indices, so that for no state are both defined at an index exactly when the
index has at most one earlier index. -/
theorem forall_not_presup_cessation_and_inception_iff :
    (∀ P : ι → Prop, ¬ ((cessation.denote R P).presup i ∧ (inception.denote R P).presup i)) ↔
      ∀ ⦃j⦄, i ~[R] j → ∀ ⦃k⦄, i ~[R] k → j = k := by
  rw [← diamond_le_box_at_iff]
  refine forall_congr' fun P ↦ ?_
  simp only [denote_presup, prior_cessation, prior_inception, not_and, not_diamond, not_not]

end Phasal

end Aspect
