module

public import Linglib.Semantics.Exhaustification.Finite
public import Linglib.Logic.Trivalent.Prop3

/-!
# Trivalent exhaustification

This file defines [spector-sudo-2017]'s two trivalent exhaustification operators. Both assert
the prejacent and deny its innocently excludable alternatives, computed by [fox-2007]'s
algorithm on the classical truth conditions; they differ in the negation applied to a denied
alternative. `exh1` uses weak negation, under which an undefined alternative counts as denied,
so the operator is undefined exactly where the prejacent is (`exh1_eq_indet_iff`). `exh2` uses
strong negation, under which an undefined alternative leaves the whole undefined, so the
operator inherits the presuppositions of the alternatives it denies (`exh2_eq_indet_iff`).

## Implementation notes

The innocently excludable alternatives are `Exhaustification.innocent.excluded` applied to the
classical parts of the trivalent propositions, where the classical part sends `true` to `true`
and both `false` and `indet` to `false`.

## References

* [spector-sudo-2017]
* [fox-2007]
-/

@[expose] public section

namespace Exhaustification.Trivalent

open Exhaustification

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The classical truth conditions of a trivalent proposition: `true` to `true`, `false` and
`indet` to `false`. -/
def classicalPart (p : W → _root_.Trivalent) : W → Bool :=
  _root_.Trivalent.toBoolOrFalse ∘ p

/-- The innocently excludable alternatives of a trivalent prejacent, computed classically. -/
def excluded (alts : List (W → _root_.Trivalent)) (p : W → _root_.Trivalent) :
    Finset (Finset W) :=
  innocent.excluded (altsFromPreds (alts.map classicalPart)) (predToFinset (classicalPart p))

/-- Weak-negation exhaustification: true where the prejacent is true and no excludable
alternative is true, false where the prejacent is false or some excludable alternative is true,
undefined where the prejacent is. -/
def exh1 (alts : List (W → _root_.Trivalent)) (p : W → _root_.Trivalent) :
    W → _root_.Trivalent :=
  λ w => match p w with
    | .indet => .indet
    | .false => .false
    | .true =>
      if alts.all λ q =>
        if predToFinset (classicalPart q) ∈ excluded alts p then q w != .true else true
      then .true
      else .false

/-- Strong-negation exhaustification: undefined where the prejacent or some excludable
alternative is, true where the prejacent is true and every excludable alternative false, and
false otherwise. -/
def exh2 (alts : List (W → _root_.Trivalent)) (p : W → _root_.Trivalent) :
    W → _root_.Trivalent :=
  λ w =>
    if alts.any λ q => predToFinset (classicalPart q) ∈ excluded alts p ∧ q w == .indet
    then .indet
    else match p w with
      | .indet => .indet
      | .false => .false
      | .true =>
        if alts.all λ q =>
          if predToFinset (classicalPart q) ∈ excluded alts p then q w == .false else true
        then .true
        else .false

variable (alts : List (W → _root_.Trivalent)) (p : W → _root_.Trivalent) (w : W)

/-- `exh1` presupposes exactly what its prejacent presupposes. -/
theorem exh1_eq_indet_iff : exh1 alts p w = .indet ↔ p w = .indet := by
  unfold exh1; split <;> (try split) <;> simp_all

/-- `exh2` presupposes what its prejacent and its excludable alternatives presuppose. -/
theorem exh2_eq_indet_iff :
    exh2 alts p w = .indet ↔
      p w = .indet ∨
        ∃ q ∈ alts, predToFinset (classicalPart q) ∈ excluded alts p ∧ q w = .indet := by
  unfold exh2
  simp only [List.any_eq_true, decide_eq_true_eq, beq_iff_eq]
  split
  · exact iff_of_true rfl (Or.inr ‹_›)
  · split <;> (try split) <;> simp_all

theorem exh1_preserves_presup (h : p w = .indet) : exh1 alts p w = .indet :=
  (exh1_eq_indet_iff alts p w).2 h

theorem exh2_preserves_presup (h : p w = .indet) : exh2 alts p w = .indet :=
  (exh2_eq_indet_iff alts p w).2 (Or.inl h)

end Exhaustification.Trivalent
