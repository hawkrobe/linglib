module

public import Linglib.Logic.Trivalent.Prop3

/-!
# Partial propositions

A partial proposition is defined at some evaluation points and not at others. `PartialProp W`
records where it is defined, its presupposition, and what it asserts there, both as predicates on
`W`. Evaluation sends it to a three-valued proposition and forgets the assertion outside the
presupposition.

## Main declarations

* `PartialProp W`: partial propositions, with `presup, assertion : W → Prop`.
* `PartialProp.eval`: evaluation into `Prop3 W`, with `eval_eq_true_iff`, `eval_eq_false_iff` and
  `eval_eq_indet_iff`; `eval_surjective` and `eval_eq_eval_iff` show that `PartialProp` presents
  `Prop3` by total representatives.

The connectives on `PartialProp` live in `Presupposition.Basic` (classical, filtering,
entailment) and `Presupposition.Trivalent` (rival trivalent families).

## Implementation notes

`PartialProp W` is parametric over the evaluation point: `PartialProp World` for possible worlds,
`PartialProp (Possibility W ℕ E)` for dynamic world-assignment pairs. `open Classical` is in scope
in the namespace because most theorems case-split on the `Prop`-valued fields, as in mathlib's
`Order/Filter/Basic.lean`.

## References

* [heim-1983]
* [belnap-1970]
-/

@[expose] public section

namespace Presupposition

open Trivalent (Prop3)

/-! ### `PartialProp`: Prop-based partial propositions -/

/-- A presuppositional proposition pairs an assertion with the presupposition under which it is
defined. Construct one directly with `{ presup := ..., assertion := ... }`. -/
@[ext]
structure PartialProp (W : Type*) where
  /-- The presupposition (must hold for definedness). -/
  presup : W → Prop
  /-- The at-issue content (assertion). -/
  assertion : W → Prop

namespace PartialProp

open Classical

variable {W : Type*}

/-! ### Constructors -/

/-- Create a presuppositionless proposition from a `W → Prop`. -/
def ofProp (p : W → Prop) : PartialProp W where
  presup := fun _ => True
  assertion := p

/-- Convert a three-valued proposition to a PartialProp.
    Inverse of `PartialProp.eval`: defined iff value ≠ indet,
    assertion iff value = true. -/
def ofProp3 (p : Prop3 W) : PartialProp W where
  presup := fun w => p w ≠ .indet
  assertion := fun w => p w = .true

/-- Belnap's conditional assertion `(A/B)` asserts `B` on condition `A`.

    Assertive_w iff A is true at w; what is asserted = B.
    [belnap-1970], (3): "(A/B) is assertive_w just in case
    A is true_w. (A/B)_w = B_w." -/
def condAssert (A B : W → Prop) : PartialProp W where
  presup := A
  assertion := B

/-! ### Satisfaction relations -/

/-- `p` holds at `w` when both its presupposition and its assertion do. -/
def holds (w : W) (p : PartialProp W) : Prop := p.presup w ∧ p.assertion w

/-- `p` is defined at `w` when its presupposition holds there. -/
def defined (w : W) (p : PartialProp W) : Prop := p.presup w

/-- The worlds where `p` is defined and true. -/
def truthSet (p : PartialProp W) : Set W := {w | p.holds w}

@[simp] theorem mem_truthSet {p : PartialProp W} {w : W} : w ∈ p.truthSet ↔ p.holds w := Iff.rfl

/-! ### Constants -/

/-- Create a tautological presupposition. -/
def top : PartialProp W where
  presup := fun _ => True
  assertion := fun _ => True

/-- Create a contradictory presupposition. -/
def bot : PartialProp W where
  presup := fun _ => True
  assertion := fun _ => False

/-- Create a presupposition failure (never defined). -/
def undefined : PartialProp W where
  presup := fun _ => False
  assertion := fun _ => False

/-! ### Evaluation -/

/-- Evaluate a presuppositional proposition to three-valued truth.
    Noncomputable because it decides Prop-valued presupposition and
    assertion via classical logic. -/
noncomputable def eval (p : PartialProp W) : Prop3 W := fun w =>
  if p.presup w then
    if p.assertion w then .true else .false
  else .indet

/-! The simp-normal interface to `eval`: consumers reason through the three value
characterizations rather than the classical `if`-nest. -/

@[simp] theorem eval_eq_true_iff (p : PartialProp W) (w : W) :
    p.eval w = .true ↔ p.presup w ∧ p.assertion w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

@[simp] theorem eval_eq_false_iff (p : PartialProp W) (w : W) :
    p.eval w = .false ↔ p.presup w ∧ ¬p.assertion w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

@[simp] theorem eval_eq_indet_iff (p : PartialProp W) (w : W) :
    p.eval w = .indet ↔ ¬p.presup w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;> simp [eval, hp, ha]

/-- Evaluation is defined iff presupposition holds. -/
@[simp] theorem eval_isDefined (p : PartialProp W) (w : W) :
    (p.eval w).isDefined ↔ p.presup w := by
  by_cases hp : p.presup w <;> by_cases ha : p.assertion w <;>
    simp [eval, hp, ha, Trivalent.isDefined]

/-! ### Round-trip: `Prop3` ↔ `PartialProp` -/

/-- `Prop3 → PartialProp → Prop3` round-trip is the identity. -/
theorem eval_ofProp3 (p : Prop3 W) : (ofProp3 p).eval = p := by
  funext w; simp only [eval, ofProp3]
  by_cases h1 : p w ≠ .indet
  · rw [ite_eq_left h1]
    by_cases h2 : p w = .true
    · rw [ite_eq_left h2, h2]
    · rw [ite_eq_right h2]; symm
      exact match p w, h1, h2 with | .false, _, _ => rfl
  · rw [ite_eq_right h1]; symm; exact not_not.mp h1

/-- `eval` is surjective — every three-valued proposition has a total representative,
    `ofProp3` being a section. -/
theorem eval_surjective : Function.Surjective (eval : PartialProp W → Prop3 W) :=
  fun p ↦ ⟨ofProp3 p, eval_ofProp3 p⟩

/-- `eval` identifies exactly agreement on definedness and, where defined, on assertion:
    `PartialProp` is the *total-representative* presentation of `Prop3 W`, carrying
    (linguistically inert) assertion values outside the presupposition that `eval`
    forgets — so `ofProp3 ∘ eval` is not the identity, only `eval ∘ ofProp3` is
    (`eval_ofProp3`). -/
theorem eval_eq_eval_iff (p q : PartialProp W) :
    p.eval = q.eval ↔
      ∀ w, (p.presup w ↔ q.presup w) ∧ (p.presup w → (p.assertion w ↔ q.assertion w)) := by
  constructor
  · intro h w
    have hw : p.eval w = q.eval w := congrFun h w
    have hpq : p.presup w ↔ q.presup w := by
      rw [← eval_isDefined p w, ← eval_isDefined q w, hw]
    refine ⟨hpq, fun hp ↦ ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩⟩
    · exact ((eval_eq_true_iff q w).mp
        (hw.symm.trans ((eval_eq_true_iff p w).mpr ⟨hp, ha⟩))).2
    · exact ((eval_eq_true_iff p w).mp
        (hw.trans ((eval_eq_true_iff q w).mpr ⟨hpq.mp hp, ha⟩))).2
  · intro h
    funext w
    obtain ⟨hpq, himp⟩ := h w
    by_cases hp : p.presup w
    · by_cases ha : p.assertion w
      · simp [eval, hp, ha, hpq.mp hp, (himp hp).mp ha]
      · have hqa : ¬q.assertion w := fun hqa ↦ ha ((himp hp).mpr hqa)
        simp [eval, hp, ha, hpq.mp hp, hqa]
    · have hq : ¬q.presup w := fun hq ↦ hp (hpq.mpr hq)
      simp [eval, hp, hq]

end PartialProp

end Presupposition
